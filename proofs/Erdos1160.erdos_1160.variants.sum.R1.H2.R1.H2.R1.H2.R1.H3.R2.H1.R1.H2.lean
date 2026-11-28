import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1
import Mathlib
-- MULT3 (Li-Qiao Prop 13.1-13.2, class 3, delta = 0): the H2Dev library closure in one file; comments
-- stripped, unused declarations pruned, local names shortened (Q*), Mathlib aliases (Z*), whitespace compacted.
open Subgroup renaming closure → ZA, subset_closure → ZD, closure_le → ZE, mem_sup_left → ZK, mem_sup_right → ZL, mem_top → ZO, closure_mono → ZS, mem_subgroupOf → ZT, mem_map → Zj, commutator_mem_commutator → Zo, mem_comap → Zp, card_mul_index → Z4, commutator_le → Z7, card_subgroup_dvd_card → YC, card_le_of_le → YG, zpowers → YQ, eq_of_le_of_card_ge → YS, nilpotent_iff_lowerCentralSeries → Yh, one_mem → Yl, card_top → Yn, mul_mem → Yq, commutator_mono → XE, subgroupOfEquivOfLe → XM, mem_zpowers → Xc, pow_mem → Xm, closure_univ → X4, mem_bot → WB, card_dvd_of_le → WU, list_prod_mem → Wb, card_bot → Wf, mul_mem_cancel_right → Ww, card_eq_card_quotient_mul_card_subgroup → VO, mem_zpowers_iff → VZ, mem_map_of_mem → Vi, comap_map_eq → V8, mul_mem_sup → UE, coe_subtype → UF, closure_eq → UR, zpowers_le → UU, relIndex_mul_index → T7, card_le_card_group → T9, commutator_comm → SX, map_commutator → Sa, subgroupOf_inj → Sb, closure_empty → Sz, closure_union → S7, rank_congr → Ri, zpow_mem → Ry, inv_mem → PH, mem_sup → PS
open Nat renaming card → ZB, mul_le_mul_right → Za, pow_right_injective → Zd, prime_two → Ze, pow_le_pow_right → Zk, mul_le_mul → Zr, zero_le → Zv, card_eq_fintype_card → YA, card_congr → YJ, card_le_card_of_surjective → YO, log → YZ, add_sub_cancel_left → Yb, eq_of_mul_eq_mul_right → Yc, eq_zero_or_pos → Yj, dvd_prime_pow → Yp, card_le_card_of_injective → Yy, add_sub_cancel → XI, zero_add → XL, pow_le_pow_left → XR, lt_or_ge → XU, le_succ → XV, lt_succ_self → XZ, not_lt_zero → Xg, card_pos → Xi, card_fin → Xk, card_fun → Xl, card_coe_set_eq → Xt, mod_eq_of_lt → Xw, pos_of_ne_zero → X7, pow_dvd_pow_iff_le_right → X8, sInf_le → WK, eq_of_mul_eq_mul_left → WR, div_add_mod → Wa, sInf_mem → Wr, lt_succ_of_le → Ws, add_sub_of_le → Wt, div_lt_iff_lt_mul → W2, mod_lt → W3, le_add_right → W5, card_prod → W7, add_lt_add_left → VN, mul_le_mul_left → VR, Prime → Vd, sub_add_cancel → Vf, lt_pow_succ_log_self → V6, strong_induction_on → V9, cast_smul_eq_nsmul → UJ, sub_zero → UK, cast_sub → UN, choose_succ_succ' → Uq, choose_one_right → U6, bijective_iff_surjective_and_card → TB, add_le_add_left → TE, card_zmod → TP, add_zero → T8, le_induction → SJ, findGreatest → SO, sub_le → S9, exists_eq_add_of_le → Rw, cast_one → Rz, zero_mul → R8, findGreatest_spec → PI, card_pi → Pa, div_mul_cancel → OC, gcd_eq_gcd_ab → OE, lt_succ_of_lt → OF, card_zpowers → OU, cast_nonneg → Om
open Additive renaming ofMul → ZC, toMul → ZW
open Set renaming range → ZF, Iio → ZH, toFinite → Zl, ncard_le_ncard_of_injOn → YM, ncard_le_ncard → Yk, ncard_eq_toFinset_card → Yt, mem_Iio → Yw, ncard_empty → Y3, range_comp → WJ, InjOn → WP, mem_singleton_iff → Wz, ncard_coe_finset → VF, mem_iUnion₂ → VJ, singleton_subset_iff → V0, mem_setOf_eq → UA, mem_insert_of_mem → Uk, image_mono → Uw, ncard_union_le → Tj, mem_range_self → Tk, ncard_image_le → Tm, mem_singleton → Tx, mk_mem_prod → Sj, mem_insert → RA, image_univ → RD, univ → RG, ncard_prod → RM, mem_empty_iff_false → Rm, mem_Ici → PY, ncard_singleton → P5, mem_insert_iff → P9, finite_range → OY, image_empty → Ob
open QuotientGroup renaming mk' → ZG, mk_surjective → Z3, mk → Z6, mk'_surjective → YI, ker_mk' → YV, mk'_apply → YY, eq_one_iff → Yf, quotientKerEquivOfSurjective → Xj, eq → WX, mk_pow → Wg
open Finset renaming mem_filter → ZI, range → ZM, univ → ZU, mem_univ → Zb, mem_range → Zt, sum_congr → Zw, sum_le_sum → Z9, card_univ → Y4, sum_const → Y5, mem_coe → Y9, prod_pow_eq_pow_sum → XB, card_image_of_injective → XG, mem_product → XH, card_sdiff_add_card_eq_card → XX, sum_filter → Xd, card_range → Xf, induction_on → Xn, mem_of_mem_erase → Xo, mem_image → Xp, mem_sdiff → Xq, ne_of_mem_erase → Xx, sum_add_distrib → Xy, filter_eq_empty_iff → WC, mem_erase → WI, card_eq_sum_card_fiberwise → Wd, sum_mul → Wi, coe_univ → W8, card_le_card → VB, range_orderEmbOfFin → VL, coe_insert → Ve, mem_image_of_mem → Vr, exists_max_image → Vt, mul_prod_erase → UC, card_image_le → UZ, prod_le_prod' → Ud, sum_eq_single → Ue, card_filter_add_card_filter_not → Uh, prod_congr → TQ, sum_insert → TV, coe_image → Tu, card_pos → SF, card_insert_eq_ite → Se, set_biUnion_insert → Sh, card_erase_of_mem → Sm, exists_min_image → RB, sum_sub_distrib → RZ, card_filter_le → Rd, disjoint_left → Rr, card_eq_zero → R5, filter_congr → R6, card_filter → PN, Ico → PV, mem_insert → PZ, card_empty → Pk, sum_apply → Py, sum_empty → P7, sum_comm → OD, mul_sum → OH, mem_Ico → OL, le_sup → OV
open Abelianization renaming of → ZJ, lift → YN, ker_of → WV, hom_ext → Tv
open QuotientAddGroup renaming mk → ZP, mk_surjective → UG, eq → Od, lift → Oe, mk_zero → Oi, mk_add → Oj, mk_zsmul → Ol
open Submodule renaming span → ZQ, subset_span → Z1, span_le → YU, mem_top → XK, mem_map → WZ, zero_mem → VA, smul_mem → VE, mem_bot → VS, mem_map_of_mem → VY, finrank_sup_add_finrank_inf_eq → V5, mem_inf → U7, map_subtype_top → SG, map_eq_top_iff → SP, exists_isCompl → SU, finrank_le → RI, map_span → Rh, add_mem → Rj, neg_mem → Rk, mem_sup → Ru, map → Pw
open List renaming ofFn → ZR, mem_ofFn' → XC, prod_eq_one → Xv, map_ofFn → Vv, ofFn_succ → Ut, prod_cons → S5, ofFn_zero → S6, ofFn_injective → Pd, prod_append → OI, prod_ofFn → Oc
open Group renaming rank → ZV, IsNilpotent → XN, rank_spec → SN
open Multiplicative renaming ofAdd → Zi, toAdd → Vk
open MonoidHom renaming mem_ker → Zm, flip_apply → YB, comp_apply → Y0, mul_apply → Y8, eq_of_eqOn_dense → XS, map_closure → XT, mk' → WL, one_apply → UL, fst → SK, snd → SM, comap_ker → RQ, mem_range → RW
open Function renaming Surjective → Zn, Injective → Z8, Bijective → Ur, comp_def → U9
open Fintype renaming card → Zq, card_fin → Zz, card_coe → WG, card_sigma → U4, sum_sigma → TD, card_prod → TI, ofFinite → Tf, card_le_of_injective → Tz, card_subtype → Rg, card_pi → P6
open Subtype renaming ext → Zu, val → XJ
open Finite renaming of_surjective → Zy, of_injective → YH, equivFin → Xz, of_equiv → SI
open CategoryTheory renaming isIsomorphicSetoid → YF
open IsPGroup renaming of_card → YK
open Fin renaming ext → YL, sum_univ_eq_sum_range → XF, lt_def → XO, sum_univ_three → Vh, succ_lt_succ_iff → Uz, cast → U5, le_def → TZ, val → Ty, castLE → RJ, sum_univ_castSucc → PL, sum_univ_zero → OJ, coe_castSucc → OW, not_lt_zero → Oa
open Quotient renaming mk → Yd, sound → Pt
open Classical renaming choose_spec → Ym, choose → XP, epsilon_spec → Sd, epsilon → Rq
open DFunLike renaming coe_injective → Yr
open MulEquiv renaming symm_apply_apply → Yv, ofBijective → RU, toGrpIso → R7
open Module renaming Finite → Yx, finrank → WA, finBasisOfFinrankEq → WD, finrank_fin_fun → Wh, natCard_eq_pow_finrank → W0
open Pi renaming single → Yz, add_apply → Vc, basisFun → Vz, single_apply → Um, smul_apply → Te, sub_apply → SH, basisFun_apply → OX
open Or renaming inl → Y7, inr → XQ
open SetLike renaming mem_coe → Xb, coe_injective → X6
open LinearMap renaming add_apply → WH, smul_apply → RK, mem_range → Ra, mem_ker → Ro, range → PX, mk₂ → Pz
open CategoryTheory.InducedCategory renaming isoMk → Wj
open Real renaming rpow_natCast → Wl, rpow_le_rpow_of_exponent_le → Wm, rpow_add → Vw, logb → OM
open LinearEquiv renaming finrank_map_eq → W6, range → RV
open Prod renaming fst → W9, ext → V7, mk → Tn, snd → PO
open AddCommGroup renaming zmodModule → VK
open SubgroupClass renaming coe_pow → Vg
open Equiv renaming symm_apply_apply → UB, range_eq_univ → U3, apply_symm_apply → Rb, ofBijective → Pq
open Iff renaming rfl → U8
open And renaming intro → TA
open Subgroup.Normal renaming conj_mem → TJ
open Nat.Prime renaming coprime_iff_not_dvd → TK
open Module.Free renaming of_divisionRing → TN
open AddSubgroup renaming toZModSubmodule → TU
open Subgroup.NormalizerCondition renaming normal_of_coatom → Sl
open OneMemClass renaming coe_one → S8
open Composition renaming blocks → RH
open AddMonoidHom renaming mk' → RY
open ZMod renaming natCast_zmod_val → R4
open Sigma renaming mk → R9
open RingHom renaming id_apply → Pe
open Matrix renaming mulVec_add → Ph
open Int renaming emod_lt_of_pos → P8, emod_nonneg → OZ
alias Z5:=le_sup_right
alias YD:=le_rfl
alias YP:=map_mul
alias YW:=map_commutatorElement
alias Yo:=eq_top_iff
alias Y6:=pow_zero
alias XD:=pow_pos
alias Xh:=pow_add
alias Xr:=pow_succ
alias X5:=pow_mul
alias X9:=map_one
alias WE:=commutator_def
alias WM:=le_sup_left
alias WO:=zpow_natCast
alias WS:=le_trans
alias WT:=le_of_eq
alias Wn:=one_mul
alias Wq:=map_inv
alias VG:=pow_succ'
alias VT:=lt_of_le_of_lt
alias Vm:=mul_right_cancel
alias Vq:=lt_trichotomy
alias UH:=mul_one
alias UO:=lt_irrefl
alias UQ:=mul_assoc
alias Uj:=lt_trans
alias Uv:=eq_inv_of_mul_eq_one_left
alias TW:=zpow_mul
alias TY:=pow_card_eq_one'
alias Tw:=le_refl
alias SD:=sup_le_sup_left
alias SY:=finrank_top
alias SZ:=pow_ne_zero
alias RO:=map_list_prod
alias RP:=coe_basisOfTopLeSpanOfCardEqFinrank
alias ON:=zpow_add
alias OO:=zpow_mem
alias OP:=inv_mul_cancel
alias OQ:=top_sup_eq
alias OT:=add_dotProduct
namespace OMA.SimsLite
universe u v
section NF
variable {G:Type u} [Group G] {H:Type v} [Group H]
def nf:List G→(ℕ→ℕ)→G
  | [],_=>1
  | b::l,e=>nf l (fun k=>e (k+1))*b^(e 0)
@[simp] lemma aeJ (e:ℕ→ℕ):nf ([]:List G) e=1:=rfl
@[simp] lemma aeG (b:G) (l:List G) (e:ℕ→ℕ):
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
lemma Ld (n:ℕ):lcs D (n+1)=⁅(⊤:Subgroup D),lcs D n⁆:=by
 rw[lcs_succ,SX]
lemma bC {a b:ℕ} (h:a≤b):lcs D b≤lcs D a:=
  Subgroup.lowerCentralSeries_antitone (⊤:Subgroup D) h
lemma a8 {n:ℕ} {x:D} (hx:x∈lcs D n) (g:D):
    ⁅x,g⁆∈lcs D (n+1):=by
 rw[lcs_succ]
 exact Zo hx (ZO g)
lemma bF {n:ℕ} (g:D) {x:D} (hx:x∈lcs D n):
    ⁅g,x⁆∈lcs D (n+1):=by
 rw[Ld]
 exact Zo (ZO g) hx
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
lemma mD {N:Subgroup D} [N.Normal] {x g:D}:g∈zn N x↔⁅x,g⁆∈N:=U8
lemma b8 {N:Subgroup D} {x g:D} (h:⁅x,g⁆∈N):⁅g,x⁆∈N:=by
 rw[← commutatorElement_inv]
 exact N.inv_mem h
lemma i6 {N:Subgroup D} [N.Normal] {A B:Set D}
    (h:∀ a∈A,∀ b∈B,⁅a,b⁆∈N):
    ⁅ZA A,ZA B⁆≤N:=by
 have hB:∀ a∈A,ZA B≤zn N a:= fun a ha=>
   (ZE (zn N a)).mpr fun b hb=>h a ha b hb
 rw[Z7]
 intro x hx y hy
 have hA:ZA A≤zn N y:=
   (ZE (zn N y)).mpr fun a ha=>b8 (hB a ha hy)
 exact b8 (hA hx)
lemma d6 {K:Subgroup D} {n:ℕ} (h1:lcs D (n+1)≤K) (h2:K≤lcs D n):
    K.Normal:=by
 constructor
 intro k hk g
 have e:g*k*g⁻¹=⁅g,k⁆*k:=by
  simp only[commutatorElement_def]
  group
 rw[e]
 exact K.mul_mem (h1 (bF g (h2 hk))) hk
lemma qC {K:Subgroup D} (h1:lcs D 1≤K):K.Normal:=
  d6 (n:=0) h1 le_top
lemma s6 (N:Subgroup D) [N.Normal] {A B C:Subgroup D}
    (h1:⁅⁅B,C⁆,A⁆≤N) (h2:⁅⁅C,A⁆,B⁆≤N):⁅⁅A,B⁆,C⁆≤N:=by
 have key:∀ X Y Z:Subgroup D,⁅⁅X,Y⁆,Z⁆≤N↔
     ⁅⁅X.map (ZG N),Y.map (ZG N)⁆,
       Z.map (ZG N)⁆=⊥:=by
  intro X Y Z
  rw [← Sa, ← Sa,Subgroup.map_eq_bot_iff,
    YV]
 rw[key]at h1 h2⊢
 exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
lemma yT:∀ (b a:ℕ),⁅lcs D a,lcs D b⁆≤lcs D (a+b+1)
  | 0,a=>by rw[lcs_zero, ← lcs_succ]
  | b +1,a=>by
    rw[lcs_succ b,SX]
    have h1:⁅⁅(⊤:Subgroup D),lcs D a⁆,lcs D b⁆≤lcs D (a+(b+1)+1):=by
     rw[← Ld]
     have:=yT b (a+1)
     rwa[show a+1+b+1=a+(b+1)+1 by omega]at this
    have h2:⁅⁅lcs D a,lcs D b⁆,(⊤:Subgroup D)⁆≤lcs D (a+(b+1)+1):=by
     rw[show a+(b+1)+1=a+b+1+1 by omega,lcs_succ]
     exact XE (yT b a) YD
    exact s6 _ h1 h2
lemma d5 {a b:ℕ} {x y:D} (hx:x∈lcs D a) (hy:y∈lcs D b):
    ⁅x,y⁆∈lcs D (a+b+1):=
  yT b a (Zo hx hy)
lemma jF (x y z:D):⁅x,y *z⁆=⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,z⁆:=by
 simp only[commutatorElement_def]
 group
lemma gX (x y z:D):⁅y *z,x⁆=⁅y,⁅z,x⁆⁆*⁅z,x⁆*⁅y,x⁆:=by
 simp only[commutatorElement_def]
 group
lemma wR {W:Subgroup D} (hW:lcs D 2≤W) {x y z:D} (hxz:⁅x,z⁆∈W):
    ⁅x,y *z⁆∈W↔⁅x,y⁆∈W:=by
 have h3:⁅y,⁅x,z⁆⁆∈W:=
   hW (bF y (bF (n:=0) x (ZO z)))
 rw [jF,Ww W hxz,
   Ww W h3]
lemma zo {W:Subgroup D} (hW:lcs D 2≤W) {x y z:D} (Qg:⁅y,x⁆∈W):
    ⁅y *z,x⁆∈W↔⁅z,x⁆∈W:=by
 have h3:⁅y,⁅z,x⁆⁆∈W:=
   hW (bF y (bF (n:=0) z (ZO x)))
 rw [gX,Ww W Qg,
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
noncomputable def Shape.Qv (s:Shape m):ℕ:=ZB {i:Fin m//(s.cidx i).isSome}
structure Shape.Valid (s:Shape m):Prop where
  mono:∀ i j:Fin m,i≤j→s.lv i≤ s.lv j
  free:∀ i,s.df i=none→s.lv i=0
  pow:∀ i,s.df i=some none→∃ h:0< i.val,
    s.lv ⟨i.val - 1,VT (S9 _ _) i.isLt⟩=s.lv i∧(s.lv i=1→s.st i=s.st ⟨i.val - 1,VT (S9 _ _) i.isLt⟩)
  comm : ∀ i a b,s.df i=some (some (a,b))→
    a < i∧b< i∧(s.cidx b).isSome∧s.lv i=s.lv a+1∧
      (s.lv i=1→∃ ka kb:Fin m,s.cidx a=some ka∧s.cidx b=some kb∧ka<kb∧
        kb.val=s.st i)
  core:∀ i (k:Fin m),s.cidx i=some k→s.df i=none∧k.val<s.Qv
  adu:∀ i j (k:Fin m),s.cidx i=some k→s.cidx j=some k→i=j
  steps:∀ β,1≤β→β<s.Qv→∃ i,s.lv i=1∧s.st i=β
  aey:∀ i,s.lv i=1→1≤ s.st i∧s.st i<s.Qv
def Shape.aer (s:Shape m):Fin 4×Fin m×Fin m×Fin m→Prop
  | (κ,i,k,j)=>
    (κ.val=0∧k=i∧i<j)∨
    (κ.val=1∧s.lv i=0∧s.lv k=0∧i<k∧1≤ s.lv j)∨
    (κ.val=2∧s.lv i=1∧(∃ c:Fin m,s.cidx k=some c∧c.val≤ s.st i)∧2≤ s.lv j)∨
    (κ.val=3∧2≤ s.lv i∧(s.cidx k).isSome∧s.lv i+1≤ s.lv j)
def Shape.Idx (s:Shape m):Type:={q:Fin 4×Fin m×Fin m×Fin m//s.aer q}
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
abbrev iJ (E:ℕ→ Set D) (l:ℕ):Subgroup D:=ZA (E l)⊔lcs D (l+1)
lemma jz {E:ℕ→ Set D} {l:ℕ} {x:D} (h:x∈lcs D (l+1)):
    x∈iJ E l:=
  ZL h
lemma ab8 {E:ℕ→ Set D} (Dh:∀ w,1≤w→ZA (E w)≤lcs D w)
    {l:ℕ} (hl:1≤l):iJ E l≤lcs D l:=
  sup_le (Dh l hl) (bC (XV l))
lemma Os {E:ℕ→ Set D} (Dh:∀ w,1≤w→ZA (E w)≤lcs D w)
    {l:ℕ} (hl:1≤l):(iJ E l).Normal:=
  d6 (n:=l) Z5 (ab8 Dh hl)
lemma kF {N:Subgroup D} [N.Normal] {S:Set D} {L:Subgroup D} {g:D}
    (hS:∀ x∈S,⁅x,g⁆∈N) (hL:∀ x∈L,⁅x,g⁆∈N):
    ∀ x∈ZA S⊔L,⁅x,g⁆∈N:=by
 have cO:ZA S⊔L≤zn N g:=
   sup_le ((ZE (zn N g)).mpr fun y hy=>mD.mpr (b8 (hS y hy)))
     fun y hy=>mD.mpr (b8 (hL y hy))
 intro x hx
 exact b8 (mD.mp (cO hx))
lemma sK {N:Subgroup D} [N.Normal] {S:Set D} {L:Subgroup D} {x:D}
    (hS:∀ g∈S,⁅x,g⁆∈N) (hL:∀ g∈L,⁅x,g⁆∈N):
    ∀ g∈ZA S⊔L,⁅x,g⁆∈N:= fun g hg=>
  b8 (kF (N:=N) (S:=S) (L:=L) (g:=x)
    (fun y hy=>b8 (hS y hy)) (fun y hy=>b8 (hL y hy)) g hg)
lemma rE {N:Subgroup D} [N.Normal] {K:Subgroup D} {S:Set D}
    (h:∀ x∈K,∀ s∈S,⁅x,s⁆∈N):⁅K,ZA S⁆≤N:=by
 have h':=i6 (N:=N) (A:=(K:Set D)) (B:=S)
   (fun x hx s hs=>h x (Xb.mp hx) s hs)
 rwa[UR]at h'
lemma sW (N K K':Subgroup D) [N.Normal] [K.Normal] [K'.Normal] {a b c:D}
    (hbc:⁅b,c⁆∈K) (hKa:∀ z∈K,⁅z,a⁆∈N) (hca:⁅c,a⁆∈K')
    (aev:∀ z∈K',⁅z,b⁆∈N):⁅⁅a,b⁆,c⁆∈N:=by
 have hBC:⁅ZA ({b}:Set D),ZA ({c}:Set D)⁆≤K:=
   i6 fun x hx y hy=>by
     rw[Wz]at hx hy
     rw[hx,hy]
     exact hbc
 have hCA:⁅ZA ({c}:Set D),ZA ({a}:Set D)⁆≤K':=
   i6 fun x hx y hy=>by
     rw[Wz]at hx hy
     rw[hx,hy]
     exact hca
 have h1:⁅⁅ZA ({b}:Set D),ZA ({c}:Set D)⁆,
     ZA ({a}:Set D)⁆≤N:=
   (XE hBC YD).trans (rE fun z hz s hs=>by
     rw[Wz]at hs
     rw[hs]
     exact hKa z hz)
 have h2:⁅⁅ZA ({c}:Set D),ZA ({a}:Set D)⁆,
     ZA ({b}:Set D)⁆≤N:=
   (XE hCA YD).trans (rE fun z hz s hs=>by
     rw[Wz]at hs
     rw[hs]
     exact aev z hz)
 have h3:=s6 N h1 h2
 exact h3 (Zo
   (Zo (ZD (Tx a))
     (ZD (Tx b)))
   (ZD (Tx c)))
lemma Nr (t:ℕ) (u:ℕ→D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (E9:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (lU:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆):
    ∀ w,1≤w→ZA (E w)≤lcs D w:=by
  intro w hw
  induction w,hw using SJ with
  | base=>
    refine (ZE (lcs D 1)).mpr ?_
    intro x hx
    rw[E9]at hx
    obtain ⟨ab, -,rfl⟩:=hx
    exact a8 (n:=0) (ZO (u ab.1)) (u ab.2)
  | succ w hw ih=>
    refine (ZE (lcs D (w+1))).mpr ?_
    intro x hx
    obtain ⟨y,hy,b, -,rfl⟩:=lU w hw x hx
    exact a8 (ih hy) (u b)
lemma K7 (t:ℕ) (u:ℕ→D) (H1:Set D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (hP:∀ ab∈P,ab.1<ab.2∧ab.2<t)
    (E9:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (lU:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆)
    (zv:ZA H1⊔lcs D 1=⊤)
    (hH1:∀ x∈H1,∀ y∈H1,⁅x,y⁆∈ZA (E 1)⊔lcs D 2)
    (hH2:∀ ab∈P,∀ k≤ab.2,⁅⁅u ab.1,u ab.2⁆,u k⁆∈ZA (E 2)⊔lcs D 3)
    (hH3:∀ w,2≤w→∀ x∈E w,∀ k<t,
      ⁅x,u k⁆∈ZA (E (w+1))⊔lcs D (w+2)):
    ∀ w,1≤w→lcs D w≤ZA (E w)⊔lcs D (w+1):=by
  have Dh:=Nr t u P E E9 lU
  have EE:∀ l,1≤l→(iJ E l).Normal:= fun l hl=>Os Dh hl
  have lT:∀ a b:D,⁅a,b⁆∈lcs D 1:= fun a b=>
    a8 (n:=0) (ZO a) b
  have hg:∀ g:D,g∈ZA H1⊔lcs D 1:= fun g=>by
    rw[zv]
    exact ZO g
  have BJ:lcs D 1≤ iJ E 1:=by
   have:=EE 1 YD
   rw[show lcs D 1=⁅(⊤:Subgroup D),⊤⁆ from lcs_succ 0,Z7]
   intro x _ g _
   refine kF ?_ ?_ x (hg x)
   · intro y hy
     refine sK ?_ ?_ g (hg g)
     · intro h hh
       exact hH1 y hy h hh
     · intro h hh
       exact jz (bF y hh)
   · intro y hy
     exact jz (a8 hy g)
  have hB1 :∀ k,k<t→∀ x∈iJ E 1,⁅x,u k⁆∈iJ E 2:=by
   have:=EE 1 YD
   have:=EE 2 (by omega)
   intro k
   induction k using V9 with
   | _ k ih =>
     intro hk
     refine kF ?_ ?_
     · intro z hz
       rw[E9]at hz
       obtain ⟨ab,hab,rfl⟩:=hz
       obtain ⟨adZ,acg⟩:=hP ab hab
       show ⁅⁅u ab.1,u ab.2⁆,u k⁆∈iJ E 2
       by_cases hkb:k≤ab.2
       · exact hH2 ab hab k hkb
       · exact sW (iJ E 2) (iJ E 1) (iJ E 1) (a:=u ab.1) (b:=u ab.2) (c:=u k)
           (BJ (lT _ _)) (ih ab.1 (by omega) (by omega)) (BJ (lT _ _))
           (ih ab.2 (by omega) (by omega))
     · intro z hz
       exact jz (a8 hz (u k))
  have hB:∀ l,1≤l→∀ k,k<t→∀ x∈iJ E l,⁅x,u k⁆∈iJ E (l+1):=by
   intro l hl k hk
   rcases XU l 2 with h | h
   · have HR:l=1:=by omega
     subst HR
     exact hB1 k hk
   · have:=EE (l+1) (by omega)
     refine kF ?_ ?_
     · intro z hz
       exact hH3 l h z hz k hk
     · intro z hz
       exact jz (a8 hz (u k))
  have acE:∀ l,1≤l→(∀ x∈E l,∀ h∈H1,⁅x,h⁆∈iJ E (l+1))→
      ∀ x∈iJ E l,∀ g:D,⁅x,g⁆∈iJ E (l+1):=by
   intro l hl dV x hx g
   have:=EE (l+1) (by omega)
   refine kF ?_ ?_ x hx
   · intro y hy
     refine sK ?_ ?_ g (hg g)
     · intro h hh
       exact dV y hy h hh
     · intro h hh
       exact jz (d5 (Dh l hl (ZD hy)) hh)
   · intro y hy
     exact jz (a8 hy g)
  have hA :∀ l,1≤l→∀ x∈iJ E l,∀ g:D,⁅x,g⁆∈iJ E (l+1):=by
   intro l hl
   induction l,hl using SJ with
   | base=>
     refine acE 1 YD ?_
     have:=EE 1 YD
     have:=EE 2 (by omega)
     intro x hx h _
     rw[E9]at hx
     obtain ⟨ab,hab,rfl⟩:=hx
     obtain ⟨adZ,acg⟩:=hP ab hab
     exact sW (iJ E 2) (iJ E 1) (iJ E 1) (a:=u ab.1) (b:=u ab.2) (c:=h)
       (BJ (lT _ _)) (hB 1 YD ab.1 (by omega)) (BJ (lT _ _)) (hB 1 YD ab.2 acg)
   | succ j hj ih=>
     refine acE (j+1) (by omega) ?_
     have:=EE 1 YD
     have:=EE (j+1) (by omega)
     have:=EE (j+1+1) (by omega)
     intro x hx h _
     obtain ⟨y,hy,bi,hbi,rfl⟩:=lU j hj x hx
     have hyM:y∈iJ E j:=ZK hy
     have hyl:y∈lcs D j:=Dh j hj hy
     have h5b:∀ z∈iJ E 1,⁅z,y⁆∈iJ E (j+1+1):=by
      refine kF ?_ ?_
      · intro z hz
        rw[E9]at hz
        obtain ⟨cd,hcd,rfl⟩:=hz
        obtain ⟨aeY,ab_⟩:=hP cd hcd
        exact sW (iJ E (j+1+1)) (iJ E (j+1)) (iJ E (j+1))
          (a:=u cd.1) (b:=u cd.2) (c:=y)
          (b8 (hB j hj cd.2 ab_ y hyM)) (hB (j+1) (by omega) cd.1 (by omega))
          (hB j hj cd.1 (by omega) y hyM) (hB (j+1) (by omega) cd.2 ab_)
      · intro z hz
        exact jz (bC (by omega) (d5 hz hyl))
     exact sW (iJ E (j+1+1)) (iJ E 1) (iJ E (j+1)) (a:=y) (b:=u bi) (c:=h)
       (BJ (lT _ _)) h5b (b8 (ih y hyM h)) (hB (j+1) (by omega) bi hbi)
  have A6:∀ l,1≤l→lcs D l≤ iJ E l:=by
   intro l hl
   induction l,hl using SJ with
   | base=>exact BJ
   | succ j hj ih=>
     rw[lcs_succ,Z7]
     intro x hx g _
     exact hA j hj x (ih hx) g
  exact A6
lemma Km (t:ℕ) (u:ℕ→D) (H1:Set D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (hP:∀ ab∈P,ab.1<ab.2∧ab.2<t)
    (E9:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (lU:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆)
    (zv:ZA H1⊔lcs D 1=⊤)
    (hH1:∀ x∈H1,∀ y∈H1,⁅x,y⁆∈ZA (E 1)⊔lcs D 2)
    (hH2:∀ ab∈P,∀ k≤ab.2,⁅⁅u ab.1,u ab.2⁆,u k⁆∈ZA (E 2)⊔lcs D 3)
    (hH3:∀ w,2≤w→∀ x∈E w,∀ k<t,
      ⁅x,u k⁆∈ZA (E (w+1))⊔lcs D (w+2))
    (N:ℕ) (hN:lcs D N=⊥):
    ∀ w,1≤w→lcs D w≤ZA (⋃ v∈Set.Ici w,E v):=by
  have hL:=K7 t u H1 P E hP E9 lU zv hH1 hH2 hH3
  have key:∀ d w,1≤w→N≤w+d→
      lcs D w≤ZA (⋃ v∈Set.Ici w,E v):=by
   intro d
   induction d with
   | zero=>
     intro w _ hw
     calc lcs D w≤lcs D N:=bC (by omega)
       _=⊥:=hN
       _≤_:=bot_le
   | succ d ih=>
     intro w hw hwd
     have h1:=ih (w+1) (by omega) (by omega)
     refine (hL w hw).trans (sup_le ?_ (h1.trans ?_))
     · exact ZS (Set.subset_biUnion_of_mem (u:=E) (PY.mpr YD))
     · refine ZS (Set.biUnion_subset_biUnion_left ?_)
       intro v hv
       rw[PY]at hv⊢
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
def Ew (u:ℕ→G) (t:ℕ):Prop:=∀ k,2≤k→k≤t→ Wk u (k - 1)≠Wk u k
lemma Ew.rS {u:ℕ→G} {t:ℕ} (h:Ew u t) {k:ℕ} (hk:1≤k)
    (qB:k+1≤t):Wk u k≠Wk u (k+1):=by
 have:=h (k+1) (by omega) qB
 rw[XI]at this
 exact this
end StrictStmt
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section RigidityAux
lemma JS {m:ℕ} {C:Fin m→Prop}
    (h:∀ i:Fin m,(∀ j:Fin m,j.val< i.val→ C j)→ C i):∀ i,C i:=by
 have key:∀ n,∀ i:Fin m,i.val=n→ C i:=by
  intro n
  induction n using V9 with
  | _ n ih=>
    intro i hi
    exact h i (fun j hj=>ih j.val (by omega) j rfl)
 exact fun i=>key _ i rfl
variable {D:Type u} [Group D]
end RigidityAux
section Diag
variable {G G':Type u} [Group G] [Group G'] {m:ℕ}
abbrev diagSub (X:Fin m→G) (X':Fin m→G'):Subgroup (G×G'):=
  ZA (ZF fun i=> (X i,X' i))
def jA (X:Fin m→G) (X':Fin m→G') (i:Fin m):diagSub X X':=
  ⟨(X i,X' i),ZD ⟨i,rfl⟩⟩
def p9 (X:Fin m→G) (X':Fin m→G'):diagSub X X'→*G:=
  (SK G G').comp (diagSub X X').subtype
def pW (X:Fin m→G) (X':Fin m→G'):diagSub X X'→*G':=
  (SM G G').comp (diagSub X X').subtype
lemma oP (X:Fin m→G) (X':Fin m→G') (i:Fin m):
    p9 X X' (jA X X' i)=X i:=rfl
lemma oX (X:Fin m→G) (X':Fin m→G') (i:Fin m):
    pW X X' (jA X X' i)=X' i:=rfl
lemma MU (X:Fin m→G) (X':Fin m→G') {x y:diagSub X X'}
    (h1:p9 X X' x =p9 X X' y) (h2:pW X X' x =pW X X' y):x =y:=
  Zu (V7 h1 h2)
lemma GF (X:Fin m→G) (X':Fin m→G'):
    ZA (ZF (jA X X'))=⊤:=by
 have aet:ZF (jA X X')=
     ((↑):diagSub X X'→G×G') ⁻¹' (ZF fun i=> (X i,X' i)):=by
   ext x
   constructor
   · rintro ⟨i,rfl⟩
     exact Set.mem_preimage.mpr ⟨i,rfl⟩
   · rintro ⟨i,hi⟩
     exact ⟨i,Zu hi⟩
 rw[aet]
 exact Subgroup.closure_closure_coe_preimage
lemma ME (X:Fin m→G) (X':Fin m→G')
    (hX:ZA (ZF X)=⊤):Zn (p9 X X'):=by
 intro y
 have hy:y∈(diagSub X X').map (SK G G'):=by
  rw[XT, ← WJ]
  have hr :(⇑(SK G G')∘fun i=> (X i,X' i))=X:=rfl
  rw[hr,hX]
  exact ZO y
 obtain ⟨z,hz,rfl⟩:=Zj.mp hy
 exact ⟨⟨z,hz⟩,rfl⟩
lemma MH (X:Fin m→G) (X':Fin m→G')
    (hX:ZA (ZF X')=⊤):Zn (pW X X'):=by
 intro y
 have hy:y∈(diagSub X X').map (SM G G'):=by
  rw[XT, ← WJ]
  have hr :(⇑(SM G G')∘fun i=> (X i,X' i))=X':=rfl
  rw[hr,hX]
  exact ZO y
 obtain ⟨z,hz,rfl⟩:=Zj.mp hy
 exact ⟨⟨z,hz⟩,rfl⟩
end Diag
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CoreFlag
variable {G:Type u} [Group G]
def dO (N:Subgroup G) (u:ℕ→G) (k:ℕ):Subgroup G:=
  ZA {x | ∃ a b,a<b∧b<k∧x =⁅u a,u b⁆}⊔N
def cD (N:Subgroup G) (u:ℕ→G) (t:ℕ):Prop:=
  ∀ k,2≤k→k≤t→dO N u (k - 1)≠dO N u k
lemma kD (N:Subgroup G) (u:ℕ→G) (k:ℕ):N≤dO N u k:=by
 unfold dO
 exact Z5
lemma gI (N:Subgroup G) (u:ℕ→G) {a b k:ℕ} (hab:a<b) (oN:b<k):
    ⁅u a,u b⁆∈dO N u k:=by
 unfold dO
 exact ZK (ZD ⟨a,b,hab,oN,rfl⟩)
lemma qA (N:Subgroup G) {u:ℕ→G} {k:ℕ} {H:Subgroup G} (h3:N≤H)
    (h:∀ a b,a<b→ b<k→⁅u a,u b⁆∈H):dO N u k≤H:=by
 unfold dO
 refine sup_le ?_ h3
 rw[ZE]
 rintro _ ⟨a,b,hab,oN,rfl⟩
 exact h a b hab oN
lemma AQ (N:Subgroup G) (u:ℕ→G) {k l:ℕ} (hkl:k≤l):
    dO N u k≤dO N u l:=
  qA N (kD N u l) fun a b hab oN=>gI N u hab (by omega)
lemma rO (N:Subgroup G) (Cd:N≤lcs G 1) (u:ℕ→G) (k:ℕ):
    dO N u k≤lcs G 1:=
  qA N Cd fun a b _ _=>a8 (n:=0) (ZO (u a)) (u b)
lemma Q0 (N:Subgroup G) (G7:lcs G 2≤N) (Cd:N≤lcs G 1) (u:ℕ→G)
    (k:ℕ):(dO N u k).Normal:=
  d6 (n:=1) (G7.trans (kD N u k)) (rO N Cd u k)
lemma B9 (N:Subgroup G) {u v:ℕ→G} {k:ℕ} (h:∀ i<k,u i=v i):
    dO N u k≤dO N v k:=
  qA N (kD N v k) fun a b hab oN=>by
    rw[h a (by omega),h b oN]
    exact gI N v hab oN
lemma KO (N:Subgroup G) {u v:ℕ→G} {k:ℕ} (h:∀ i<k,u i=v i):
    dO N u k=dO N v k:=
  le_antisymm (B9 N h) (B9 N fun i hi=> (h i hi).symm)
lemma y4 (N:Subgroup G) {u:ℕ→G} {k:ℕ} (h:∀ a<k,⁅u a,u k⁆∈dO N u k):
    dO N u (k+1)≤dO N u k:=by
 refine qA N (kD N u k) ?_
 intro a b hab oN
 by_cases hb:b<k
 · exact gI N u hab hb
 · rw[show b=k by omega]
   exact h a (by omega)
lemma vT (N:Subgroup G) {u:ℕ→G} {k:ℕ}
    (h:dO N u k≠dO N u (k+1)):∃ a<k,⁅u a,u k⁆∉dO N u k:=by
 by_contra hc
 apply h
 refine le_antisymm (AQ N u (show k≤k+1 by omega)) (y4 N ?_)
 intro a ha
 by_contra hn
 exact hc ⟨a,ha,hn⟩
lemma N4 (N:Subgroup G) (v:ℕ→G) (t:ℕ):
    dO N v t≤⁅ZA (v '' ZH t),ZA (v '' ZH t)⁆⊔N:=
  qA N Z5 fun a b hab hbt=>
    ZK (Zo
      (ZD ⟨a,Yw.mpr (by omega),rfl⟩)
      (ZD ⟨b,Yw.mpr hbt,rfl⟩))
lemma qE (N:Subgroup G) {u:ℕ→G} {t:ℕ}
    (h:∀ k,1≤k→k+1≤t→dO N u k≠dO N u (k+1)):cD N u t:=by
 intro k hk qB
 obtain ⟨j,rfl⟩:∃ j,k=j+1:=⟨k - 1,by omega⟩
 rw[XI]
 exact h j (by omega) qB
lemma cD.rS {N:Subgroup G} {u:ℕ→G} {t:ℕ} (h:cD N u t) {k:ℕ}
    (hk:1≤k) (qB:k+1≤t):dO N u k≠dO N u (k+1):=by
 have:=h (k+1) (by omega) qB
 rw[XI]at this
 exact this
lemma D7 (N:Subgroup G) (u:ℕ→G):cD N u 0:=by
 intro k hk qB
 omega
lemma o7 {A B:Subgroup G} {z:G} (hB:z∈B) (hA:z∉A):A≠B:=by
 rintro rfl
 exact hA hB
lemma NL (N:Subgroup G) {u:ℕ→G} {x y:G} (e0:u 0=x) (e1:u 1=y)
    (Cu:⁅x,y⁆∉N):cD N u 2:=by
 apply qE
 intro k hk qB
 rw[show k=1 by omega]
 have hm:⁅u 0,u 1⁆∈dO N u (1+1):=gI N u (by norm_num) (by norm_num)
 have h1:dO N u 1≤N:=qA N YD fun a b hab hb=>by
   exfalso
   omega
 rw[e0,e1]at hm
 exact o7 hm fun h=>Cu (h1 h)
lemma Kq (N:Subgroup G) {u u':ℕ→G} {t a:ℕ} {v:G}
    (hu:cD N u t) (ha:a<t)
    (e1:∀ i<t,u' i=u i) (e2:u' t=v) (hv:⁅u a,v⁆∉dO N u t):
    cD N u' (t+1):=by
 have hW:∀ k≤t,dO N u' k=dO N u k:= fun k hk=>
   KO N fun i hi=>e1 i (by omega)
 apply qE
 intro k hk qB
 rcases XU k t with aeC | aeC
 · rw[hW k (by omega),hW (k+1) (by omega)]
   exact hu.rS hk (by omega)
 · rw[show k=t by omega,hW t YD]
   have hm:⁅u' a,u' t⁆∈dO N u' (t+1):=gI N u' ha (by omega)
   rw[e1 a ha,e2]at hm
   exact o7 hm hv
lemma F7 (N:Subgroup G) {u u':ℕ→G} {s:ℕ} {w y:G}
    (hu:cD N u (s+1))
    (hcw:∀ a<s,⁅u a,w⁆∈dO N u (s+1))
    (e1:∀ i<s,u' i=u i) (e2:u' s=w) (e3:u' (s+1)=y)
    (Fd:∃ a<s,⁅u a,w⁆∉dO N u s) (H_:⁅w,y⁆∉dO N u (s+1)):
    cD N u' (s+1+1):=by
 have hW:∀ k≤ s,dO N u' k=dO N u k:= fun k hk=>
   KO N fun i hi=>e1 i (by omega)
 have cO:dO N u' (s+1)≤dO N u (s+1):=by
  refine qA N (kD N u (s+1)) ?_
  intro a b hab hb
  by_cases KZ:b<s
  · rw[e1 a (by omega),e1 b KZ]
    exact gI N u hab (by omega)
  · rw[show b=s by omega,e1 a (by omega),e2]
    exact hcw a (by omega)
 apply qE
 intro k hk qB
 by_cases BG:k<s
 · rw[hW k (by omega),hW (k+1) (by omega)]
   exact hu.rS hk (by omega)
 · by_cases lQ:k=s
   · rw[lQ]
     obtain ⟨a,ha,wJ⟩:=Fd
     have hm:⁅u' a,u' s⁆∈dO N u' (s+1):=gI N u' ha (by omega)
     rw[e1 a ha,e2]at hm
     rw[hW s YD]
     exact o7 hm wJ
   · rw [show k=s+1 by omega]
     have hm:⁅u' s,u' (s+1)⁆∈dO N u' (s+1+1):=
       gI N u' (by omega) (by omega)
     rw[e2,e3]at hm
     exact o7 hm fun h=>H_ (cO h)
lemma zK (N:Subgroup G) (hN:lcs G 2≤N) {H:Subgroup G} {u:ℕ→G} {t:ℕ}
    (ht:2≤t) (hu:cD N u t) (Dv:∀ i<t,u i∈H) {x y:G}
    (hx:x∈H) (hy:y∈H) (Cu:⁅x,y⁆∉dO N u t):
    ∃ u':ℕ→G,cD N u' (t+1)∧∀ i<t+1,u' i∈H:=by
 by_cases hc:∃ a<t,∃ v∈H,⁅u a,v⁆∉dO N u t
 · obtain ⟨a,ha,v,hv,hav⟩:=hc
   refine ⟨fun i=>if i<t then u i else v,?_,?_⟩
   · refine Kq N (u':= fun i=>if i<t then u i else v) hu ha ?_ ?_ hav
     · intro i hi
       exact if_pos hi
     · show (if t<t then u t else v)=v
       exact if_neg (UO t)
   · intro i hi
     show (if i<t then u i else v)∈H
     by_cases h:i<t
     · rw[if_pos h]
       exact Dv i h
     · rw[if_neg h]
       exact hv
 · have hc':∀ a<t,∀ v∈H,⁅u a,v⁆∈dO N u t:= fun a ha v hv=>by
     by_contra hn
     exact hc ⟨a,ha,v,hv,hn⟩
   obtain ⟨s,rfl⟩:∃ s,t=s+1:=⟨t - 1,by omega⟩
   obtain ⟨a0,ML,abp⟩:=
     vT N (hu.rS (k:=s) (by omega) YD)
   have hw :∃ w∈H,(∃ a<s,⁅u a,w⁆∉dO N u s)∧⁅w,y⁆∉dO N u (s+1):=by
    by_cases oQ:∃ a<s,⁅u a,x⁆∉dO N u s
    · exact ⟨x,hx,oQ,Cu⟩
    · refine ⟨u s*x,H.mul_mem (Dv s (by omega)) hx,⟨a0,ML,?_⟩,?_⟩
      · have hax:⁅u a0,x⁆∈dO N u s:=by
          by_contra hn
          exact oQ ⟨a0,ML,hn⟩
        rw[wR (hN.trans (kD N u s)) hax]
        exact abp
      · rw[zo (hN.trans (kD N u (s+1))) (hc' s (by omega) y hy)]
        exact Cu
   obtain ⟨w,hwH,Fd,H_⟩:=hw
   refine ⟨fun i=>if i<s then u i else if i=s then w else y,?_,?_⟩
   · refine F7 N (u':= fun i=>if i<s then u i else if i=s then w else y)
       hu (fun a ha=>hc' a (by omega) w hwH) ?_ ?_ ?_ Fd H_
     · intro i hi
       exact if_pos hi
     · show (if s<s then u s else if s=s then w else y)=w
       rw[if_neg (UO s),if_pos rfl]
     · show (if s+1<s then u (s+1) else if s+1=s then w else y)=y
       rw[if_neg (show ¬ (s+1<s) by omega),if_neg (show ¬ (s+1=s) by omega)]
   · intro i hi
     show (if i<s then u i else if i=s then w else y)∈H
     by_cases h1:i<s
     · rw[if_pos h1]
       exact Dv i (by omega)
     · rw [if_neg h1]
       by_cases h2:i=s
       · rw[if_pos h2]
         exact hwH
       · rw[if_neg h2]
         exact hy
lemma Bv (N M:Subgroup G) (G7:lcs G 2≤N) (Cd:N≤lcs G 1)
    (hMN:∀ g m:G,m∈M→⁅g,m⁆∈N) (u:ℕ→G) (t:ℕ) (h:cD N u t)
    (ht:2≤t):∀ k<t,u k∉ZA (u '' ZH k)⊔M:=by
 intro k hk cI
 rcases Yj k with Br | Br
 · subst Br
   have cO:ZA (u '' ZH 0)⊔M≤M:=by
    refine sup_le ?_ YD
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Yw.mp hi) (Xg i)
   have h0:u 0∈M:= cO cI
   refine h.rS (k:=1) YD (by omega)
     (le_antisymm (AQ N u (show 1≤1+1 by omega)) (y4 N ?_))
   intro a ha
   obtain rfl:a=0:=by omega
   exact kD N u 1 (b8 (hMN (u 1) (u 0) h0))
 · haveI :=Q0 N G7 Cd u k
   refine h.rS (k:=k) (by omega) (by omega)
     (le_antisymm (AQ N u (show k≤k+1 by omega)) (y4 N ?_))
   intro a ha
   have cO:ZA (u '' ZH k)⊔M≤zn (dO N u k) (u a):=by
    refine sup_le ?_ ?_
    · rw [ZE]
      rintro _ ⟨b,hb,rfl⟩
      rw[Xb,mD]
      rcases Vq a b with hab | hab | hab
      · exact gI N u hab (Yw.mp hb)
      · rw[hab,commutatorElement_self]
        exact (dO N u k).one_mem
      · exact b8 (gI N u hab ha)
    · intro z hz
      exact mD.mpr (kD N u k (hMN (u a) z hz))
   exact mD.mp (cO cI)
lemma Mv (a b k k':G):a*k*(b*k')=a*b*(b⁻¹*k*b⁻¹⁻¹*k'):=by
 group
lemma M8 (a k:G):(a*k)⁻¹=a⁻¹*(a*k⁻¹*a⁻¹):=by
 group
def ace (K:Subgroup G) [hK:K.Normal] (x:G):Subgroup G where
  carrier :={g | ∃ e:ℤ,∃ k∈K,g=x^e *k}
  one_mem':=by
    show ∃ e:ℤ,∃ k∈K,(1:G)=x^e *k
    exact ⟨0,1,K.one_mem,by simp⟩
  mul_mem':=by
    rintro _ _ ⟨e,k,hk,rfl⟩ ⟨f,k',lQ,rfl⟩
    show ∃ e':ℤ,∃ k''∈K,x^e *k*(x^f*k')=x^e'*k''
    refine ⟨e+f,(x^f)⁻¹*k*(x^f)⁻¹⁻¹*k',
      K.mul_mem (hK.conj_mem k hk _) lQ,?_⟩
    rw[ON]
    exact Mv _ _ _ _
  inv_mem':=by
    rintro _ ⟨e,k,hk,rfl⟩
    show ∃ e':ℤ,∃ k''∈K,(x^e *k)⁻¹=x^e'*k''
    refine ⟨-e,x^e *k⁻¹*(x^e)⁻¹,hK.conj_mem _ (K.inv_mem hk) _,?_⟩
    rw[zpow_neg]
    exact M8 _ _
lemma Gq {K:Subgroup G} [K.Normal] {x g:G}:
    g∈ace K x↔∃ e:ℤ,∃ k∈K,g=x^e *k:=U8
lemma zg {K:Subgroup G} [K.Normal] {x:G} {p:ℕ} (hp:0<p)
    (hx:x^p∈K) {g:G} (hg:g∈K⊔YQ x):
    ∃ e:ℕ,e<p∧∃ k∈K,g=x^e *k:=by
 have cO:K⊔YQ x≤ace K x:=by
  refine sup_le (fun k hk=>Gq.mpr ⟨0,k,hk,by simp⟩) ?_
  rw[UU]
  exact Gq.mpr ⟨1,1,K.one_mem,by simp⟩
 obtain ⟨e,k,hk,rfl⟩:=Gq.mp (cO hg)
 have Ou:(0:ℤ)<p:=by exact_mod_cast hp
 obtain ⟨r,hr⟩:=Int.eq_ofNat_of_zero_le (OZ e Ou.ne')
 have hrp:r<p:=by
  have:=P8 e Ou
  rw[hr]at this
  exact_mod_cast this
 refine ⟨r,hrp,(x^p)^(e/(p:ℤ))*k,K.mul_mem (OO hx _) hk,?_⟩
 have he:e=(r :ℤ)+(p:ℤ)*(e/(p:ℤ)):=by
  rw[← hr]
  have:=Int.emod_add_mul_ediv e (p:ℤ)
  linarith
 calc x^e *k=x^((r :ℤ)+(p:ℤ)*(e/(p:ℤ)))*k:=by rw[← he]
   _ =x^r*((x^p)^(e/(p:ℤ))*k):=by
     rw[ON,TW,WO,WO,UQ]
variable [Finite G]
lemma rH {K:Subgroup G} [K.Normal] {x:G} {p:ℕ} (hp:0<p)
    (hx:x^p∈K):ZB (K⊔YQ x:Subgroup G)≤p*ZB K:=by
 have cI:∀ q:Fin p×K,x^(q.1:ℕ)*(q.2:G)∈K⊔YQ x:=
   fun q=>mul_mem (pow_mem (ZL (Xc x)) _)
     (ZK q.2.2)
 let f:Fin p×K→(K⊔YQ x:Subgroup G):= fun q=> ⟨_,cI q⟩
 have hf:Zn f:=by
  rintro ⟨g,hg⟩
  obtain ⟨e,he,k,hk,rfl⟩:=zg hp hx hg
  exact ⟨(⟨e,he⟩,⟨k,hk⟩),rfl⟩
 have h:=YO f hf
 rwa[W7,(YA:ZB (Fin p)=Zq (Fin p)),
   Zz]at h
variable {p n:ℕ}
lemma BH (hp:p.Prime) (hG:ZB G=p^n) {K L:Subgroup G} (cO:K≤L)
    (d8:K≠L):p*ZB K≤ZB L:=by
 have h2:ZB L∣p^n:=by
  rw[← hG]
  exact YC L
 have h1:ZB K∣ZB L:=WU cO
 obtain ⟨b, -,hb⟩:=(Yp hp).mp h2
 obtain ⟨a, -,ha⟩:=(Yp hp).mp (h1.trans h2)
 have hab:a≤b:=by
  rw[ha,hb]at h1
  exact (X8 hp.one_lt).mp h1
 have aeU:a≠b:=by
  rintro rfl
  exact d8 (YS cO (by rw[ha,hb]))
 rw[ha,hb, ← VG]
 exact Zk hp.pos (by omega)
lemma q9 (hp:0<p) {M:Subgroup G} (O0:lcs G 1≤M)
    (Lb:∀ g:G,g^p∈M) (x:ℕ→G):
    ∀ j,ZB (ZA (x '' ZH j)⊔M:Subgroup G)≤p^j*ZB M:=by
 intro j
 induction j with
 | zero=>
   have cO:ZA (x '' ZH 0)⊔M≤M:=by
    refine sup_le ?_ YD
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Yw.mp hi) (Xg i)
   rw[Y6,Wn]
   exact YG cO
 | succ j ih=>
   have:(ZA (x '' ZH j)⊔M).Normal:=
     qC (O0.trans Z5)
   have cO:ZA (x '' ZH (j+1))⊔M≤
       (ZA (x '' ZH j)⊔M)⊔YQ (x j):=by
    refine sup_le ?_ (Z5.trans WM)
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    have gJ:i<j+1:=Yw.mp hi
    by_cases hij:i<j
    · exact ZK (ZK
        (ZD ⟨i,Yw.mpr hij,rfl⟩))
    · rw[show i=j by omega]
      exact ZL (Xc (x j))
   have h1:=YG cO
   have h2:=rH (K:=ZA (x '' ZH j)⊔M) hp
     (ZL (Lb (x j)))
   have h3:p*ZB (ZA (x '' ZH j)⊔M:Subgroup G)≤
       p*(p^j*ZB M):=Zr YD ih
   have e:p*(p^j*ZB M)=p^(j+1)*ZB M:=by
    rw[Xr]
    ring
   rw[← e]
   exact h1.trans (h2.trans h3)
lemma r6 (hp:p.Prime) (hG:ZB G=p^n) (M:Subgroup G) {v:ℕ→G}:
    ∀ t,(∀ k<t,v k∉ZA (v '' ZH k)⊔M)→
      p^t *ZB M≤ZB (ZA (v '' ZH t)⊔M:Subgroup G):=by
 intro t
 induction t with
 | zero=>
   intro _
   rw[Y6,Wn]
   exact YG Z5
 | succ t ih=>
   intro gO
   have h1:=ih fun k hk=>gO k (by omega)
   have cO:ZA (v '' ZH t)⊔M≤ZA (v '' ZH (t+1))⊔M:=
     sup_le_sup_right (ZS
       (Uw (Set.Iio_subset_Iio (XV t)))) M
   have d8:ZA (v '' ZH t)⊔M≠
       ZA (v '' ZH (t+1))⊔M:=by
    intro h
    apply gO t (XZ t)
    rw[h]
    exact ZK
      (ZD ⟨t,Yw.mpr (XZ t),rfl⟩)
   have h2:=BH hp hG cO d8
   have h3:p*(p^t *ZB M)≤
       p*ZB (ZA (v '' ZH t)⊔M:Subgroup G):=Zr YD h1
   have e:p*(p^t *ZB M)=p^(t+1)*ZB M:=by
    rw[Xr]
    ring
   rw[← e]
   exact h3.trans h2
lemma GS (hp:p.Prime) (hG:ZB G=p^n) {M:Subgroup G}
    (O0:lcs G 1≤M) (Lb:∀ g:G,g^p∈M) (x:ℕ→G) (s:ℕ) {v:ℕ→G} {t:ℕ}
    (gO:∀ k<t,v k∉ZA (v '' ZH k)⊔M)
    (hvH:∀ i<t,v i∈ZA (x '' ZH s)):t≤ s:=by
 have h1:=r6 hp hG M t gO
 have h2:ZB (ZA (v '' ZH t)⊔M:Subgroup G)≤
     ZB (ZA (x '' ZH s)⊔M:Subgroup G):=by
  refine YG (sup_le ?_ Z5)
  rw[ZE]
  rintro _ ⟨i,hi,rfl⟩
  exact ZK (hvH i (Yw.mp hi))
 have h3:=q9 hp.pos O0 Lb x s
 have hc:0<ZB M:=Xi
 by_contra hts
 have h4:p^(s+1)≤p^t:=Zk hp.pos (by omega)
 have h6:0<p^s:=XD hp.pos s
 rw[Xr]at h4
 have h7:p^s*p*ZB M≤p^t *ZB M:=Zr h4 YD
 have h8:p^s*2*ZB M≤p^s*p*ZB M:=
   Zr (Zr YD hp.two_le) YD
 have h9:0<p^s*ZB M:=Nat.mul_pos h6 hc
 linarith
lemma Ju (hp:p.Prime) (hG:ZB G=p^n) (N:Subgroup G) {u:ℕ→G}
    {t:ℕ} (hu:cD N u t):
    ∀ k,1≤k→k≤t→p^(k - 1)*ZB N≤ZB (dO N u k):=by
 intro k
 induction k with
 | zero=>intro hk _; omega
 | succ j ih=>
   intro _ qB
   rcases Yj j with hj | hj
   · subst hj
     rw[show 0+1 - 1=0 by omega,Y6,Wn]
     exact YG (kD N u 1)
   · obtain ⟨i,rfl⟩:∃ i,j=i+1:=⟨j - 1,by omega⟩
     have h1:=ih (by omega) (by omega)
     rw[show i+1 - 1=i by omega]at h1
     have h2:=BH hp hG (AQ N u (show i+1≤ i+1+1 by omega))
       (hu.rS (k:=i+1) (by omega) qB)
     rw[show i+1+1 - 1=i+1 by omega,VG]
     have h3:p*(p^i*ZB N)≤p*ZB (dO N u (i+1)):=
       Zr YD h1
     rw[UQ]
     exact h3.trans h2
omit [Finite G] in
lemma m9 {N H W:Subgroup G} (dG:lcs G 1≤⁅H,H⁆⊔N) (hNW:N≤W)
    (hW:¬ lcs G 1≤W):∃ x∈H,∃ y∈H,⁅x,y⁆∉W:=by
 by_contra hc
 apply hW
 refine dG.trans (sup_le ?_ hNW)
 rw[Z7]
 intro x hx y hy
 by_contra hn
 exact hc ⟨x,hx,y,hy,hn⟩
lemma aav (hp:p.Prime) (hG:ZB G=p^n) (N M:Subgroup G)
    (G7:lcs G 2≤N) (Cd:N≤lcs G 1) (O0:lcs G 1≤M) (Lb:∀ g:G,g^p∈M)
    (hMN:∀ g m:G,m∈M→⁅g,m⁆∈N) (s:ℕ) (x:ℕ→G)
    (dG:lcs G 1≤
      ⁅ZA (x '' ZH s),ZA (x '' ZH s)⁆⊔N)
    (nU:∀ t<s,∀ v:ℕ→G,(∀ i<t,v i∈ZA (x '' ZH s))→
      ¬ lcs G 1≤⁅ZA (v '' ZH t),ZA (v '' ZH t)⁆⊔N):
    ∃ u:ℕ→G,(∀ i<s,u i∈ZA (x '' ZH s))∧
      cD N u s∧dO N u s=lcs G 1∧
      (∀ k<s,u k∉ZA (u '' ZH k)⊔M)∧
      ZA (u '' ZH s)⊔M=ZA (x '' ZH s)⊔M∧
      (∀ k,1≤k→k≤ s→p^(k - 1)*ZB N≤ZB (dO N u k)):=by
 have Nj:s≤1→
     ⁅ZA (x '' ZH s),ZA (x '' ZH s)⁆≤N:=by
  intro O9
  have:=d6 (n:=1) G7 Cd
  apply i6
  rintro _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩
  have gJ:i<s:=Yw.mp hi
  have mC:j<s:=Yw.mp hj
  obtain rfl:i=0:=by omega
  obtain rfl:j=0:=by omega
  rw[commutatorElement_self]
  exact N.one_mem
 rcases (show s=0∨s=1∨2≤ s by omega) with hs | hs | hs
 · subst hs
   refine ⟨x,fun i hi=>absurd hi (Xg i),D7 N x,?_,
     fun k hk=>absurd hk (Xg k),rfl,fun k hk BG=>absurd BG (by omega)⟩
   exact le_antisymm (rO N Cd x 0)
     (dG.trans (sup_le ((Nj (by omega)).trans (kD N x 0)) (kD N x 0)))
 · subst hs
   exfalso
   exact nU 0 (by omega) x (fun i hi=>absurd hi (Xg i))
     ((dG.trans (sup_le (Nj YD) YD)).trans Z5)
 · have stepA:∀ j,j+2≤ s→∃ u:ℕ→G,cD N u (j+2)∧
       ∀ i<j+2,u i∈ZA (x '' ZH s):=by
     intro j
     induction j with
     | zero =>
       intro bU
       have h0:¬ lcs G 1≤N:= fun h=>
         nU 0 (by omega) x (fun i hi=>absurd hi (Xg i)) (h.trans Z5)
       obtain ⟨a,ha,b,hb,hab⟩:=m9 dG YD h0
       refine ⟨fun i=>if i=0 then a else b,?_,?_⟩
       · refine NL N (u:= fun i=>if i=0 then a else b) ?_ ?_ hab
         · show (if (0:ℕ)=0 then a else b)=a
           exact if_pos rfl
         · show (if (1:ℕ)=0 then a else b)=b
           exact if_neg (by norm_num)
       · intro i hi
         show (if i=0 then a else b)∈ZA (x '' ZH s)
         by_cases h:i=0
         · rw[if_pos h]
           exact ha
         · rw[if_neg h]
           exact hb
     | succ j ih=>
       intro bU
       obtain ⟨u,hu,Dv⟩:=ih (by omega)
       have hnc:¬ lcs G 1≤dO N u (j+2):= fun h=>
         nU (j+2) (by omega) u Dv (h.trans (N4 N u (j+2)))
       obtain ⟨a,ha,b,hb,hab⟩:=m9 dG (kD N u _) hnc
       obtain ⟨u',oF,abr⟩:=zK N G7 (by omega) hu Dv ha hb hab
       rw[show j+1+2=j+2+1 by omega]
       exact ⟨u',oF,abr⟩
   obtain ⟨u,hu,Dv⟩:=stepA (s - 2) (by omega)
   rw[show s - 2+2=s by omega]at hu Dv
   have Ep:lcs G 1≤dO N u s:=by
    by_contra hc
    obtain ⟨a,ha,b,hb,hab⟩:=m9 dG (kD N u s) hc
    obtain ⟨u',oF,abr⟩:=zK N G7 (by omega) hu Dv ha hb hab
    have:=GS hp hG O0 Lb x s
      (Bv N M G7 Cd hMN u' (s+1) oF (by omega)) abr
    omega
   have gO:=Bv N M G7 Cd hMN u s hu (by omega)
   refine ⟨u,Dv,hu,le_antisymm (rO N Cd u s) Ep,gO,?_,
     Ju hp hG N hu⟩
   have cO:ZA (u '' ZH s)⊔M≤ZA (x '' ZH s)⊔M:=by
    refine sup_le ?_ Z5
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    exact ZK (Dv i (Yw.mp hi))
   refine YS cO ?_
   exact (q9 hp.pos O0 Lb x s).trans (r6 hp hG M s gO)
end CoreFlag
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CommForm
variable {G:Type u} [Group G]
abbrev cE (p:ℕ) (G:Type u) [Group G]:Subgroup G:=
  ZA (ZF (fun g:G=>g^p))⊔commutator G
abbrev pN (p:ℕ) (G:Type u) [Group G]:Subgroup G:=
  lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p))
lemma eO:commutator G=lcs G 1:=by
 rw[WE]
 rfl
lemma b7 (x y:G):⁅x,y⁆∈lcs G 1:=
  a8 (n:=0) (ZO x) y
lemma eo (p:ℕ):lcs G 2≤pN p G:=WM
lemma kO (p:ℕ):pN p G≤lcs G 1:=by
 refine sup_le (bC (by norm_num)) ?_
 rw[ZE]
 rintro _ ⟨g,rfl⟩
 exact Xm _ g.2 p
lemma s4 (p:ℕ):(pN p G).Normal:=
  d6 (n:=1) (eo p) (kO p)
lemma zz (g y:G) (n:ℕ):⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹∈lcs G 2:=by
 induction n with
 | zero=>simp
 | succ n ih=>
   have hc:⁅g,⁅g^n,y⁆⁆∈lcs G 2:=
     bF (n:=1) g (b7 _ _)
   have e:⁅g^(n+1),y⁆*(⁅g,y⁆^(n+1))⁻¹=
       ⁅g,⁅g^n,y⁆⁆*(⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹):=by
    rw[VG g n,gX,Xr]
    group
   rw[e]
   exact Yq _ hc ih
lemma vQ (p:ℕ) (g y:G):⁅g^p,y⁆∈pN p G:=by
 have h1:=eo p (zz g y p)
 have h2:⁅g,y⁆^p∈pN p G:=by
  refine (Z5:_≤pN p G) (ZD ?_)
  exact ⟨⟨⁅g,y⁆,b7 g y⟩,rfl⟩
 have e:⁅g^p,y⁆=⁅g^p,y⁆*(⁅g,y⁆^p)⁻¹*⁅g,y⁆^p:=by group
 rw[e]
 exact Yq _ h1 h2
lemma u7 (p:ℕ) {φ:G} (hφ:φ∈cE p G) (y:G):⁅φ,y⁆∈pN p G:=by
 haveI:=s4 (G:=G) p
 suffices h:cE p G≤zn (pN p G) y from b8 (h hφ)
 refine sup_le ?_ ?_
 · rw[ZE]
   rintro _ ⟨g,rfl⟩
   exact b8 (vQ p g y)
 · intro c hc
   rw[eO]at hc
   exact eo p (bF (n:=1) y hc)
lemma vX (p:ℕ) (x x' y:G)
    (h:x'*x⁻¹∈ZA (ZF (fun g:G=>g^p))⊔commutator G):
    ⁅x',y⁆*⁅x,y⁆⁻¹∈
      lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p)):=by
  haveI:=s4 (G:=G) p
  obtain ⟨φ,hφ,rfl⟩:∃ φ∈cE p G,x'=φ*x:=⟨x'*x⁻¹,h,by group⟩
  have h1:⁅φ,⁅x,y⁆⁆∈pN p G:=
    eo p (bF (n:=1) φ (b7 _ _))
  have h2:⁅x,y⁆*⁅φ,y⁆*⁅x,y⁆⁻¹∈pN p G:=
    (s4 (G:=G) p).conj_mem _ (u7 p hφ y) _
  have e:⁅φ*x,y⁆*⁅x,y⁆⁻¹=⁅φ,⁅x,y⁆⁆*(⁅x,y⁆*⁅φ,y⁆*⁅x,y⁆⁻¹):=by
   rw[gX]
   group
  rw[e]
  exact Yq _ h1 h2
lemma D4 (p:ℕ) (x y y':G)
    (h:y'*y⁻¹∈ZA (ZF (fun g:G=>g^p))⊔commutator G):
    ⁅x,y'⁆*⁅x,y⁆⁻¹∈
      lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p)):=by
  have hu:=vX p y y' x h
  have e:⁅x,y'⁆*⁅x,y⁆⁻¹=⁅y',x⁆⁻¹*(⁅y',x⁆*⁅y,x⁆⁻¹)⁻¹*⁅y',x⁆⁻¹⁻¹:=by
   rw[← commutatorElement_inv y' x, ← commutatorElement_inv y x]
   group
  rw[e]
  exact (s4 (G:=G) p).conj_mem _ (PH _ hu) _
lemma D9 (p:ℕ) (x x' y:G):
    ⁅x *x',y⁆*(⁅x,y⁆*⁅x',y⁆)⁻¹∈
      lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p)):=by
  have h1:⁅x,⁅x',y⁆⁆∈lcs G 2:=
    bF (n:=1) x (b7 _ _)
  have h2:⁅⁅x',y⁆,⁅x,y⁆⁆∈lcs G 2:=
    a8 (n:=1) (b7 _ _) _
  have e:⁅x*x',y⁆*(⁅x,y⁆*⁅x',y⁆)⁻¹=⁅x,⁅x',y⁆⁆*⁅⁅x',y⁆,⁅x,y⁆⁆:=by
   rw[gX]
   simp only[commutatorElement_def]
   group
  rw[e]
  exact eo p (Yq _ h1 h2)
lemma Dt (p:ℕ) (x y y':G):
    ⁅x,y *y'⁆*(⁅x,y⁆*⁅x,y'⁆)⁻¹∈
      lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p)):=by
  have h1:⁅y,⁅x,y'⁆⁆∈lcs G 2:=
    bF (n:=1) y (b7 _ _)
  have e:⁅x,y *y'⁆*(⁅x,y⁆*⁅x,y'⁆)⁻¹=
      ⁅x,y⁆*⁅y,⁅x,y'⁆⁆*⁅x,y⁆⁻¹:=by
   rw[jF]
   group
  rw[e]
  exact (s4 (G:=G) p).conj_mem _ (eo p h1) _
lemma LO (p:ℕ):
    lcs G 1≤ZA (ZF (fun xy:G×G=> ⁅xy.1,xy.2⁆))⊔
      (lcs G 2⊔ZA (ZF (fun g:lcs G 1=> (g:G)^p))):=by
  show ⁅lcs G 0,⊤⁆≤_
  rw[Z7]
  intro a _ b _
  exact ZK (ZD ⟨(a,b),rfl⟩)
end CommForm
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section BurnsideGeneral
variable {G:Type u} [Group G]
lemma wQ {H:Subgroup G} (h:commutator G≤H):H.Normal:=
  ⟨fun n hn g=>by
    have hc:⁅g,n⁆∈H:=h (by
     rw[WE]
     exact Zo (ZO g) (ZO n))
    have e:g*n*g⁻¹=⁅g,n⁆*n:=by
     rw[commutatorElement_def]
     group
    rw[e]
    exact H.mul_mem hc hn⟩
lemma BZ {M:Subgroup G} [M.Normal] (hM:IsCoatom M) (x:G⧸M):
    x =1∨YQ x =⊤:=by
 obtain ⟨g,rfl⟩:=Z3 x
 obtain ⟨K,hK⟩:∃ K:Subgroup G,
     K=Subgroup.comap (ZG M) (YQ (g:G⧸M)):=⟨_,rfl⟩
 have hMK:M≤K:=by
  intro m hm
  rw[hK,Zp,YY,(Yf m).mpr hm]
  exact Yl _
 have MO:g∈K:=by
  rw[hK,Zp,YY]
  exact Xc _
 rcases eq_or_lt_of_le hMK with h | h
 · left
   rw[Yf,h]
   exact MO
 · right
   have hKt:=hM.2 K h
   rw[Yo]
   intro y _
   obtain ⟨y,rfl⟩:=Z3 y
   have hy:y∈K:=by
    rw[hKt]
    exact ZO y
   rw[hK,Zp,YY]at hy
   exact hy
lemma gG (p:ℕ) (y:G):y^p∈cE p G:=
  ZK (ZD ⟨y,rfl⟩)
abbrev aaP (G:Type u) [Group G]:Subgroup (Abelianization G):=
  (frattini G).map ZJ
abbrev jf (G:Type u) [Group G]:Type u:=Abelianization G⧸aaP G
def dL (G:Type u) [Group G]:G→*jf G:=
  (ZG (aaP G)).comp ZJ
lemma jX:Zn (dL G):=by
 intro x
 obtain ⟨a,rfl⟩:=Z3 x
 obtain ⟨g,hg⟩:=Z3 (a:G⧸commutator G)
 refine ⟨g,?_⟩
 rw[← hg]
 rfl
end BurnsideGeneral
section Burnside
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G] [Finite G]
lemma Lv (hG:IsPGroup p G) {M:Subgroup G} (hM:IsCoatom M):M.Normal:=by
 have:=hG.isNilpotent
 exact Sl M Group.normalizerCondition_of_isNilpotent hM
lemma J6 (hG:IsPGroup p G) {M:Subgroup G} (hM:IsCoatom M):
    cE p G≤M:=by
 have:=Lv hG hM
 have hQ:IsPGroup p (G⧸M):=hG.to_quotient M
 have hnt:ZB (G⧸M)≠1:=by
  intro h1
  apply hM.1
  rw[← Subgroup.index_eq_one]
  exact h1
 have v5:p∣ZB (G⧸M):=hQ.card_eq_or_dvd.resolve_left hnt
 obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' p v5
 have Lg:x≠1:=by
  intro h
  rw[h,orderOf_one]at hx
  exact hp.out.one_lt.ne hx
 have hxt:YQ x =⊤:=(BZ hM x).resolve_left Lg
 have dS:ZB (G⧸M)=p:=by
  rw[← hx, ← OU,hxt,Yn]
 have vG:∀ a b:G⧸M,a*b=b*a:=by
  intro a b
  have ha:a∈YQ x:=by
   rw[hxt]
   exact ZO a
  have hb:b∈YQ x:=by
   rw[hxt]
   exact ZO b
  obtain ⟨i,rfl⟩:=VZ.mp ha
  obtain ⟨j,rfl⟩:=VZ.mp hb
  exact (Commute.zpow_zpow_self x i j).eq
 refine sup_le ?_ ?_
 · rw[ZE]
   rintro _ ⟨g,rfl⟩
   rw[Xb, ← Yf,Wg, ← dS]
   exact TY
 · rw[WE,Z7]
   intro a _ b _
   have e:=YW (ZG M) a b
   simp only[YY]at e
   rw[← Yf,e,commutatorElement_eq_one_iff_mul_comm]
   exact vG _ _
lemma z7 {g:G} (hg:g∉cE p G):
    ∃ H:Subgroup G,IsCoatom H∧g∉H:=by
 have:Finite (Subgroup G):=
   YH (fun H:Subgroup G=> (H:Set G)) X6
 obtain ⟨H,⟨hPH,hgH⟩,FJ⟩:=(wellFounded_gt (α:=Subgroup G)).has_min
   {H:Subgroup G | cE p G≤H∧g∉H} ⟨cE p G,YD,hg⟩
 have key:∀ K:Subgroup G,H<K→ g∈K:=by
  intro K hK
  by_contra MO
  exact FJ K ⟨hPH.trans hK.le,MO⟩ hK
 have:H.Normal:=wQ (Z5.trans hPH)
 refine ⟨H,⟨fun h=>hgH (by rw[h]; exact ZO g),fun K hK=>?_⟩,hgH⟩
 rw[Yo]
 intro y _
 by_cases hyH:y∈H
 · exact hK.le hyH
 · have f5:H<H⊔YQ y:=by
     refine lt_of_le_of_ne WM (fun h=>hyH ?_)
     rw[h]
     exact ZL (Xc y)
   have hgs:=key _ f5
   rw[Subgroup.mem_sup_of_normal_left]at hgs
   obtain ⟨h,hh,z,hz,hhz⟩:=hgs
   obtain ⟨k,rfl⟩:=VZ.mp hz
   have MO:=key K hK
   by_cases hpk:(p:ℤ)∣k
   · exfalso
     obtain ⟨m,rfl⟩:=hpk
     apply hgH
     rw[← hhz]
     refine H.mul_mem hh (hPH ?_)
     rw[TW,WO]
     exact Ry _ (gG p y) m
   · have hyk:y^k∈K:=by
       have e:y^k=h⁻¹*g:=by
        rw[← hhz]
        group
       rw[e]
       exact K.mul_mem (K.inv_mem (hK.le hh)) MO
     have hyp:y^(p:ℤ)∈K:=by
      rw[WO]
      exact hK.le (hPH (gG p y))
     have abh:Int.gcd k (p:ℤ)=1:=by
      have hnd:¬ p∣k.natAbs:= fun h'=>hpk (Int.ofNat_dvd_left.mpr h')
      have hc:Nat.Coprime p k.natAbs:=(TK hp.out).mpr hnd
      exact hc.symm
     have e:y=(y^k)^(Int.gcdA k (p:ℤ))*(y^(p:ℤ))^(Int.gcdB k (p:ℤ)):=by
      rw[← TW, ← TW, ← ON, ← Int.gcd_eq_gcd_ab,abh,Rz,zpow_one]
     rw[e]
     exact K.mul_mem (K.zpow_mem hyk _) (K.zpow_mem hyp _)
lemma ew (hG:IsPGroup p G):frattini G= cE p G:=by
 apply le_antisymm
 · intro g hg
   by_contra hgn
   obtain ⟨H,hH,hgH⟩:=z7 hgn
   exact hgH (frattini_le_coatom hH hg)
 · show cE p G≤ ⨅ a∈{H:Subgroup G | IsCoatom H},a
   exact le_iInf₂ fun M hM=>J6 hG hM
lemma G8 (hG:IsPGroup p G):(dL G).ker= frattini G:=by
 have hc:commutator G≤frattini G:=by
  rw[ew hG]
  exact Z5
 rw [dL, ← RQ,YV,V8,
   WV,sup_eq_left.mpr hc]
lemma eD {s:Set G}
    (h:ZA s⊔frattini G=⊤):ZA s=⊤:=by
 have:Finite (Subgroup G):=
   YH (fun H:Subgroup G=> (H:Set G)) X6
 exact frattini_nongenerating h
lemma k5 (hG:IsPGroup p G):
    ZB (G⧸frattini G)=p^ZV G:=by
 classical
 have:NeZero p:=⟨hp.out.ne_zero⟩
 have j3:=G8 hG
 have hpow:∀ x:Additive (jf G),p•x =0:=by
  intro x
  obtain ⟨g,hg⟩:=jX (ZW x)
  have h1:ZW x^p=1:=by
   rw[← hg, ← map_pow, ← Zm,j3,ew hG]
   exact gG p g
  show ZC (ZW x^p)=ZC 1
  rw[h1]
 have:Module (ZMod p) (Additive (jf G)):=VK hpow
 have:Finite (jf G):=Zy (dL G) jX
 have:Finite (Additive (jf G)):=inferInstance
 have:Module.Free (ZMod p) (Additive (jf G)):=
   TN (ZMod p) (Additive (jf G))
 have:Yx (ZMod p) (Additive (jf G)):=inferInstance
 have acI:ZB (G⧸frattini G)=ZB (Additive (jf G)):=by
  have e:=YJ
    (Xj (dL G) jX).toEquiv
  rw[j3]at e
  exact e
 have dS:ZB (Additive (jf G))=
     p^WA (ZMod p) (Additive (jf G)):=by
  rw[W0 (K:=ZMod p) (V:=Additive (jf G)),TP]
 rw[acI,dS]
 congr 1
 apply le_antisymm
 ·
   obtain ⟨S,hSc,hS⟩:=SN G
   let T:Finset (Additive (jf G)):=S.image (fun g=>ZC (dL G g))
   have qU : ZQ (ZMod p) (T:Set (Additive (jf G)))=⊤:=by
    rw[Submodule.eq_top_iff']
    intro v
    obtain ⟨g,hg⟩:=jX (ZW v)
    let K : Subgroup G:=
      { carrier :={x | ZC (dL G x)∈
          ZQ (ZMod p) (T:Set (Additive (jf G)))}
        mul_mem':= fun {a b} ha hb=>by
          show ZC (dL G (a*b))∈
            ZQ (ZMod p) (T:Set (Additive (jf G)))
          rw[YP,ofMul_mul]
          exact Rj _ ha hb
        one_mem':=by
          show ZC (dL G 1)∈
            ZQ (ZMod p) (T:Set (Additive (jf G)))
          rw[X9,ofMul_one]
          exact VA _
        inv_mem':= fun {a} ha=>by
          show ZC (dL G a⁻¹)∈
            ZQ (ZMod p) (T:Set (Additive (jf G)))
          rw[Wq,ofMul_inv]
          exact Rk _ ha }
    have hK:ZA (S:Set G)≤K:=by
     rw[ZE]
     intro x hx
     exact Z1 (Y9.mpr
       (Vr (fun g:G=>ZC (dL G g)) hx))
    have MO:g∈K:=hK (by rw[hS]; exact ZO g)
    have hv:v=ZC (dL G g):=by rw[hg,ofMul_toMul]
    rw[hv]
    exact MO
   have h1:(T:Set (Additive (jf G))).finrank (ZMod p)≤T.card:=
     finrank_span_finset_le_card T
   unfold Set.finrank at h1
   rw[qU,SY]at h1
   exact h1.trans (UZ.trans hSc.le)
 ·
   let b:=Module.finBasis (ZMod p) (Additive (jf G))
   choose lift hlift using fun i=>jX (G:=G) (ZW (b i))
   let S:Finset G:=ZU.image lift
   have dV :ZA (S:Set G)=⊤:=by
    apply eD
    rw[Yo]
    intro x _
    let W :Submodule (ZMod p) (Additive (jf G)):=
      { carrier :={v | ∃ y∈ZA (S:Set G)⊔frattini G,
          ZC (dL G y)=v}
        add_mem':=by
          rintro _ _ ⟨y1,h1,rfl⟩ ⟨y2,h2,rfl⟩
          exact ⟨y1*y2,Yq _ h1 h2,by rw[YP,ofMul_mul]⟩
        zero_mem':=⟨1,Yl _,by rw[X9,ofMul_one]⟩
        smul_mem':=by
          rintro c _ ⟨y,hy,rfl⟩
          refine ⟨y^c.val,Xm _ hy _,?_⟩
          conv_rhs=>rw[← R4 c]
          rw[UJ,map_pow,ofMul_pow] }
    have hW:(⊤:Submodule (ZMod p) (Additive (jf G)))≤W:=by
     rw[← b.span_eq,YU]
     rintro _ ⟨i,rfl⟩
     show ∃ y∈ZA (S:Set G)⊔frattini G,
       ZC (dL G y)=b i
     refine ⟨lift i,ZK (ZD ?_),?_⟩
     · exact Y9.mpr (Vr lift (Zb i))
     · rw[hlift i,ofMul_toMul]
    have cI:∃ y∈ZA (S:Set G)⊔frattini G,
        ZC (dL G y)=ZC (dL G x):=
      hW (XK (x:=ZC (dL G x)))
    obtain ⟨y,hy,Qg⟩:= cI
    have adx:dL G y=dL G x:=ZC.injective Qg
    have hk:y⁻¹*x∈(dL G).ker :=by
     rw[Zm,YP,Wq,adx,OP]
    rw[j3]at hk
    have e:x =y *(y⁻¹*x):=by group
    rw[e]
    exact Yq _ hy (ZL hk)
   calc Group.rank G≤S.card:=Group.rank_le dV
     _≤ (ZU :Finset (Fin (WA (ZMod p)
           (Additive (jf G))))).card:=UZ
     _=_:=by rw[Y4,Zz]
lemma oA (hG:IsPGroup p G):
    ZB (G⧸cE p G)=p^ZV G:=by
 rw[← k5 hG,ew hG]
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
lemma KY (K:Subgroup D):∀ (n:ℕ) (f:Fin n→D),(∀ i,f i∈K)→sprod n f∈K
  | 0,_,_=>by
    show (1:D)∈K
    exact K.one_mem
  | n+1,f,h=>by
    show f 0*sprod n (fun i=>f i.succ)∈K
    exact K.mul_mem (h 0) (KY K n _ (fun i=>h i.succ))
lemma KX {E:Type v} [Group E] (φ:D→*E):∀ (n:ℕ) (f:Fin n→D),
    φ (sprod n f)=sprod n (fun i=>φ (f i))
  | 0,_=>by
    show φ 1=1
    exact X9 φ
  | n+1,f=>by
    show φ (f 0*sprod n (fun i=>f i.succ))=φ (f 0)*sprod n (fun i=>φ (f i.succ))
    rw[YP,KX φ n]
def gN {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ):D:=sprod n (fun t=>X t^e t)
lemma O3 {E:Type v} [Group E] (φ:D→*E) {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ):
    φ (gN X e)=gN (fun t=>φ (X t)) e:=by
  unfold gN
  rw[KX]
  simp only[map_pow]
lemma vI {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ) (T:Set (Fin n))
    (h:∀ t,e t≠0→t∈T):gN X e∈ZA (X '' T):=by
 unfold gN
 apply KY
 intro t
 show X t^e t∈_
 by_cases ht:e t=0
 · rw[ht,Y6]
   exact one_mem _
 · have cI:X t∈ZA (X '' T):=ZD ⟨t,h t ht,rfl⟩
   exact pow_mem cI _
lemma w5:∀ (n:ℕ) (f:Fin n→D),(∀ i,f i=1)→sprod n f=1
  | 0,_,_=>rfl
  | n+1,f,h=>by
    show f 0*sprod n (fun i=>f i.succ)=1
    rw[h 0,w5 n _ (fun i=>h i.succ),Wn]
lemma CR:∀ (n:ℕ) (f:Fin n→D) (t:Fin n),(∀ i,i≠t→ f i=1)→
    sprod n f= f t
  | 0,_,t,_=>t.elim0
  | n +1,f,t,h=>by
    show f 0*sprod n (fun i=>f i.succ)= f t
    by_cases ht:t=0
    · rw[w5 n _ (fun i=>h i.succ (by rw[ht]; exact Fin.succ_ne_zero i)),UH,ht]
    · obtain ⟨t',rfl⟩:=Fin.exists_succ_eq.mpr ht
      rw[h 0 (fun h0=>ht h0.symm),Wn]
      exact CR n _ t' (fun i hi=>h i.succ (fun h'=>hi (Fin.succ_injective _ h')))
lemma KR :∀ (n:ℕ) (f g:Fin n→D),(∀ i j,f i≠1→ g j≠1→i<j)→
    sprod n f*sprod n g=sprod n (fun i=>f i*g i)
  | 0,_,_,_=>by
    show (1:D)*1=1
    rw[Wn]
  | n + 1,f,g,h=>by
    show f 0*sprod n (fun i=>f i.succ)*(g 0*sprod n (fun i=>g i.succ))=
      f 0*g 0*sprod n (fun i=>f i.succ*g i.succ)
    by_cases hg:g 0=1
    · rw[hg,Wn,UH,UQ]
      congr 1
      exact KR n _ _ (fun i j hi hj=>Uz.mp (h _ _ hi hj))
    · have hf:∀ i,f i=1:=by
        intro i
        by_contra hi
        exact absurd (h i 0 hi hg) (Oa i)
      rw[w5 n _ (fun i=>hf i.succ),hf 0]
      simp only[Wn]
      congr 1
      congr 1
      funext i
      rw[hf i.succ,Wn]
lemma Kp {n:ℕ} (X:Fin n→D) (e1 e2:Fin n→ℕ)
    (h:∀ u v,e1 u≠0→e2 v≠0→u<v):gN X e1*gN X e2=gN X (e1+e2):=by
 unfold gN
 rw[KR]
 · congr 1
   funext i
   rw[Vc,Xh]
 · intro i j hi hj
   refine h i j (fun h0=>hi ?_) (fun h0=>hj ?_)
   · simp only[h0,Y6]
   · simp only[h0,Y6]
def delta {n:ℕ} (t:Fin n) (k:ℕ):Fin n→ℕ:= fun u=>if u=t then k else 0
lemma KV {n:ℕ} (X:Fin n→D) (t:Fin n) (k:ℕ):gN X (delta t k)=X t^k:=by
 unfold gN
 rw[CR n _ t]
 · show X t^(if t=t then k else 0)=X t^k
   rw[if_pos rfl]
 · intro i hi
   show X i^(if i=t then k else 0)=1
   rw[if_neg hi,Y6]
lemma aa5 {n:ℕ} (X:Fin n→D):gN X (fun _=> 0)=1:=by
  unfold gN
  exact w5 n _ (fun i=>Y6 _)
end SProd
section CardLe
variable {D:Type u} [Group D]
lemma pQ (K:Subgroup D) (x:D) (q:ℕ) (hq:0<q)
    (sw:∀ y∈K,x*y *x⁻¹∈K) (hpow:x^q∈K) (S:Set D)
    (hS:S⊆insert x (K:Set D)):
    ∀ z∈ZA S,∃ y∈K,∃ k:ℕ,z=y *x^k:=by
 have acw:∀ m:ℕ,∀ y∈K,x^m*y *(x^m)⁻¹∈K:=by
  intro m
  induction m with
  | zero=>intro y hy; simpa using hy
  | succ m ih=>
    intro y hy
    have:=sw _ (ih y hy)
    convert this using 1
    group
 intro z hz
 induction hz using Subgroup.closure_induction_left with
 | one=>exact ⟨1,one_mem _,0,by simp⟩
 | mul_left g hg z hz ih=>
   obtain ⟨y,hy,k,rfl⟩:=ih
   rcases P9.mp (hS hg) with rfl | hg'
   · exact ⟨g*y *g⁻¹,sw y hy,k+1,by group⟩
   · exact ⟨g*y,mul_mem hg' hy,k,by group⟩
 | inv_mul_cancel g hg z hz ih=>
   obtain ⟨y,hy,k,rfl⟩:=ih
   rcases P9.mp (hS hg) with rfl | hg'
   · obtain ⟨q',rfl⟩:∃ q',q=q'+1:=⟨q - 1,by omega⟩
     refine ⟨g^q'*((g^(q'+1))⁻¹*y)*(g^q')⁻¹,
       acw q' _ (mul_mem (inv_mem hpow) hy),q'+k,?_⟩
     group
   · exact ⟨g⁻¹*y,mul_mem (inv_mem hg') hy,k,by group⟩
lemma B7 [Finite D] (K:Subgroup D) (x:D) (q:ℕ) (hq:0<q)
    (sw:∀ y∈K,x*y *x⁻¹∈K) (hpow:x^q∈K) (S:Set D)
    (hS:S⊆insert x (K:Set D)):
    ZB (ZA S)≤ZB K*q:=by
 have key:∀ z∈ZA S,∃ yk:K×Fin q,z=(yk.1:D)*x^(yk.2:ℕ):=by
  intro z hz
  obtain ⟨y,hy,k,rfl⟩:=pQ K x q hq sw hpow S hS z hz
  refine ⟨(⟨y *(x^q)^(k/q),mul_mem hy (pow_mem hpow _)⟩,⟨k % q,W3 _ hq⟩),?_⟩
  show y *x^k=y *(x^q)^(k/q)*x^(k % q)
  rw[UQ, ← X5, ← Xh,Wa]
 choose F hF using key
 have eW:Z8 (fun z:ZA S=>F z.1 z.2):=by
   intro z z' h
   have h':F z.1 z.2=F z'.1 z'.2:=h
   apply Zu
   calc z.1=((F z.1 z.2).1:D)*x^((F z.1 z.2).2:ℕ):=hF _ _
     _=((F z'.1 z'.2).1:D)*x^((F z'.1 z'.2).2:ℕ):=by rw[h']
     _=z'.1:=(hF _ _).symm
 have hc:=Yy _ eW
 rwa[W7,Xk]at hc
lemma JG (T:Set D) (x:D) (h:∀ z∈T,x*z*x⁻¹∈ZA T):
    ∀ y∈ZA T,x*y *x⁻¹∈ZA T:=by
 intro y hy
 have cO:ZA T≤(ZA T).comap (MulAut.conj x).toMonoidHom:=by
  rw[ZE]
  intro z hz
  exact h z hz
 simpa using cO hy
lemma xd [Finite D] {n:ℕ} (X:Fin n→D) (q:Fin n→ℕ)
    (hq:∀ t,0<q t) (prec:Fin n→Fin n→Prop)
    (Mb:∀ t,¬ prec t t) (NC:∀ t u,prec t u→¬ prec u t)
    (nU:∀ S:Finset (Fin n),S.Nonempty→∃ t∈S,∀ u∈S,u≠t→prec t u)
    (hpow:∀ t,X t^q t∈ZA (X '' {u | prec t u}))
    (sw:∀ t u,prec t u→X t *X u*(X t)⁻¹∈ZA (X '' {u | prec t u})):
    ∀ S:Finset (Fin n),(∀ t∈S,∀ u,prec t u→u∈S)→
      ZB (ZA (X '' (S:Set (Fin n))))≤∏ t∈S,q t:=by
  suffices h:∀ k,∀ S:Finset (Fin n),S.card=k→(∀ t∈S,∀ u,prec t u→u∈S)→
      ZB (ZA (X '' (S:Set (Fin n))))≤∏ t∈S,q t from
    fun S hS=>h _ S rfl hS
  intro k
  induction k with
  | zero=>
    intro S hS _
    rw[R5.mp hS]
    simp
  | succ k ih=>
    intro S hS O4
    have d8:S.Nonempty:=SF.mp (by omega)
    obtain ⟨t,Jb,IT⟩:=nU S d8
    have abz:∀ t'∈S.erase t,∀ u,prec t' u→u∈S.erase t:=by
     intro t' iQ u hu
     have MW:=Xo iQ
     have abi:=Xx iQ
     refine WI.mpr ⟨?_,O4 t' MW u hu⟩
     rintro rfl
     exact NC _ _ (IT t' MW abi) hu
    have dS:(S.erase t).card=k:=by
     rw[Sm Jb]
     omega
    have hK:=ih (S.erase t) dS abz
    have abJ:ZA (X '' {u | prec t u})≤
        ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
      apply ZS
      rintro _ ⟨u,hu,rfl⟩
      have oF:prec t u:=hu
      refine ⟨u,?_,rfl⟩
      rw[Y9]
      refine WI.mpr ⟨?_,O4 t Jb u oF⟩
      rintro rfl
      exact Mb _ oF
    have acz:=JG (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))) (X t) (by
     rintro _ ⟨u,hu,rfl⟩
     rw[Y9]at hu
     have pJ:=Xx hu
     have huS:=Xo hu
     exact abJ (sw t u (IT u huS pJ)))
    have hS':X '' (S:Set (Fin n))⊆
        insert (X t) ((ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):
          Subgroup D):Set D):=by
     rintro _ ⟨u,hu,rfl⟩
     rw[Y9]at hu
     by_cases pJ:u=t
     · rw[pJ]
       exact RA _ _
     · refine Uk _ (ZD ⟨u,?_,rfl⟩)
       rw[Y9]
       exact WI.mpr ⟨pJ,hu⟩
    have ac4:=B7 _ (X t) (q t) (hq t) acz (abJ (hpow t)) _ hS'
    calc ZB (ZA (X '' (S:Set (Fin n))))
        ≤ ZB (ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))))*q t:=
          ac4
      _≤(∏ u∈S.erase t,q u)*q t:=Za _ hK
      _=∏ u∈S,q u:=by rw[mul_comm,UC S q Jb]
lemma GG [Finite D] {n:ℕ} (X:Fin n→D) (q:Fin n→ℕ)
    (prec:Fin n→Fin n→Prop) (NC:∀ t u,prec t u→¬ prec u t)
    (nU:∀ S:Finset (Fin n),S.Nonempty→∃ t∈S,∀ u∈S,u≠t→prec t u)
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
    rw[R5.mp hS]
    simp
  | succ k ih =>
    intro S hS O4
    have d8:S.Nonempty:=SF.mp (by omega)
    obtain ⟨t,Jb,IT⟩:=nU S d8
    have abz:∀ t'∈S.erase t,∀ u,prec t' u→u∈S.erase t:=by
     intro t' iQ u hu
     have MW:=Xo iQ
     have abi:=Xx iQ
     refine WI.mpr ⟨?_,O4 t' MW u hu⟩
     rintro rfl
     exact NC _ _ (IT t' MW abi) hu
    have dS:(S.erase t).card=k:=by
     rw[Sm Jb]
     omega
    have hK:=ih (S.erase t) dS abz
    have hKL:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))≤
        ZA (X '' (S:Set (Fin n))):=by
     apply ZS
     rintro _ ⟨u,hu,rfl⟩
     exact ⟨u,Y9.mpr (Xo (Y9.mp hu)),rfl⟩
    have hKs:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))≤
        ZA (X '' {u | prec t u}):=by
      apply ZS
      rintro _ ⟨u,hu,rfl⟩
      have oF:=Y9.mp hu
      exact ⟨u,IT u (Xo oF) (Xx oF),rfl⟩
    have hxL:X t∈ZA (X '' (S:Set (Fin n))):=
      ZD ⟨t,Y9.mpr Jb,rfl⟩
    have eW : Z8
        (fun yk:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))×
            Fin (q t)=>
          (⟨(yk.1:D)*X t^(yk.2:ℕ),mul_mem (hKL yk.1.2) (pow_mem hxL _)⟩:
            ZA (X '' (S:Set (Fin n))))):=by
      intro a b h
      have heq:(a.1:D)*X t^(a.2:ℕ)=(b.1:D)*X t^(b.2:ℕ):=
        congrArg XJ h
      have hkk:(a.2:ℕ)=b.2:=by
       by_contra d8
       rcases Nat.lt_or_gt_of_ne d8 with f5 | f5
       · have e1:X t^((b.2:ℕ) - a.2)=(b.1:D)⁻¹*a.1:=by
           rw[pow_sub _ f5.le,eq_mul_inv_of_mul_eq heq]
           group
         have cI:X t^((b.2:ℕ) - a.2)∈
             ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
          rw[e1]
          exact mul_mem (inv_mem b.1.2) a.1.2
         have uj:=b.2.isLt
         exact hnot t _ (by omega) (by omega) (hKs cI)
       · have e1:X t^((a.2:ℕ) - b.2)=(a.1:D)⁻¹*b.1:=by
           rw[pow_sub _ f5.le,eq_mul_inv_of_mul_eq heq.symm]
           group
         have cI:X t^((a.2:ℕ) - b.2)∈
             ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
          rw[e1]
          exact mul_mem (inv_mem a.1.2) b.1.2
         have ha2:=a.2.isLt
         exact hnot t _ (by omega) (by omega) (hKs cI)
      have hy:(a.1:D)=b.1:=by
       rw[hkk]at heq
       exact Vm heq
      exact V7 (Zu hy) (YL hkk)
    have hc:=Yy _ eW
    rw[W7,Xk]at hc
    calc ∏ u∈S,q u=(∏ u∈S.erase t,q u)*q t:=by
          rw[mul_comm,UC S q Jb]
      _ ≤ ZB (ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))))*q t:=
          Za _ hK
      _≤_:=hc
end CardLe
section Data
structure aO where
  n:ℕ
  s:ℕ
  lv:Fin n→ℕ
  df:Fin n→Fin n×Fin n
  a:Fin n→ℕ
  b:Fin n→Fin n→ℕ
  c:Fin n→Fin n→Fin n→ℕ
namespace aO
def prec (d:aO) (t u:Fin d.n):Prop:=
  d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val)
def q8 (d:aO) (t k:Fin d.n):Prop:=
  (d.lv t=0∧d.lv k=0∧t<k)∨(d.lv t=1∧k.val≤(d.df t).2.val)∨
    (2≤d.lv t∧k.val<d.s)
structure qN (d:aO):Prop where
  mono:∀ t u:Fin d.n,t≤u→d.lv t≤d.lv u
  yA:d.s≤d.n
  core:∀ t:Fin d.n,t.val<d.s→d.lv t=0
  wY:∀ t,1≤d.lv t→d.lv (d.df t).1+1=d.lv t
  kR:∀ t,1≤d.lv t→(d.df t).2.val<d.s
  oR:∀ t,d.lv t=1→(d.df t).1< (d.df t).2
structure Valid (d:aO):Prop extends qN d where
  GZ:∀ t u,d.b t u≠0→d.prec t u
  Aa:∀ t k u,d.c t k u≠0→d.lv t<d.lv u
def Bounded (p:ℕ) (d:aO):Prop:=
  (∀ t u,d.b t u<p^d.a u)∧(∀ t k u,d.c t k u<p^d.a u)
lemma Fh (d:aO) (t:Fin d.n):¬ d.prec t t:=by
 unfold prec
 omega
lemma A5 (d:aO) (t u:Fin d.n) (h:d.prec t u):¬ d.prec u t:=by
 unfold prec at *
 omega
lemma Gb (d:aO) (S:Finset (Fin d.n)) (hS:S.Nonempty):
    ∃ t∈S,∀ u∈S,u≠t→d.prec t u:=by
 obtain ⟨t0,ht0,ade⟩:=RB S d.lv hS
 have hT:(S.filter (fun u=>d.lv u=d.lv t0)).Nonempty:=
   ⟨t0,ZI.mpr ⟨ht0,rfl⟩⟩
 obtain ⟨t,htT,FJ⟩:=Vt _ (fun u:Fin d.n=>u.val) hT
 obtain ⟨Jb,htl⟩:=ZI.mp htT
 refine ⟨t,Jb,fun u huS pJ=>?_⟩
 have h1:=ade u huS
 unfold prec
 by_cases hl:d.lv u=d.lv t0
 · have h2:=FJ u (ZI.mpr ⟨huS,hl⟩)
   have h3:u.val≠t.val:= fun h=>pJ (YL h)
   right
   constructor
   · omega
   · have jM:u.val≤t.val:=h2
     omega
 · left
   omega
end aO
structure h_ (p:ℕ) (d:aO) {G:Type u} [Group G] (X:Fin d.n→G):Prop where
  card:ZB G=p^(∑ t,d.a t)
  gen:ZA (ZF X)=⊤
  Fk:∀ t,1≤d.lv t→X t=⁅X (d.df t).1,X (d.df t).2⁆
  pow:∀ t,X t^(p^d.a t)=gN X (d.b t)
  DZ:∀ t k,d.lv t=0→d.lv k=0→t<k→⁅X t,X k⁆=gN X (d.c t k)
  Iq:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→⁅X t,X k⁆=gN X (d.c t k)
  IG:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→⁅X t,X k⁆=gN X (d.c t k)
end Data
section CardData
variable {D:Type u} [Group D]
abbrev iO (d:aO) (Z:Fin d.n→D) (v:ℕ):Set D:=Z '' {t | d.lv t=v}
def dE (d:aO) (Z:Fin d.n→D) (k:ℕ):D:=if h:k<d.n then Z ⟨k,h⟩ else 1
lemma r7 (d:aO) (Z:Fin d.n→D) {k:ℕ} (h:k<d.n):
    dE d Z k=Z ⟨k,h⟩:=by
 unfold dE
 rw[dif_pos h]
lemma K_ (d:aO) (Z:Fin d.n→D) (k:Fin d.n):dE d Z k.val=Z k:=
  r7 d Z k.isLt
def Jw (d:aO):Set (ℕ×ℕ):=
  {ab | ∃ t,d.lv t=1∧ab=((d.df t).1.val,(d.df t).2.val)}
lemma xh (d:aO) {ab:ℕ×ℕ}:
    ab∈Jw d↔∃ t,d.lv t=1∧ab=((d.df t).1.val,(d.df t).2.val):=U8
lemma aaI (d:aO) (hd:d.qN) (t:Fin d.n) (ht:1≤d.lv t):
    (d.df t).1.val<t.val:=by
 have h1:=hd.wY t ht
 by_contra aeW
 have h2:=hd.mono t (d.df t).1 (TZ.mpr (by omega))
 omega
lemma ow (d:aO) (hd:d.qN) (Z:Fin d.n→D)
    (lH:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆):
    ∀ t,Z t∈lcs D (d.lv t):=by
 refine JS ?_
 intro t ih
 by_cases h0:d.lv t=0
 · rw[h0,lcs_zero]
   exact ZO _
 · have h1:1≤d.lv t:=by omega
   have ac_:=ih (d.df t).1 (aaI d hd t h1)
   rw[← hd.wY t h1,lH t h1]
   exact a8 ac_ _
lemma BV (d:aO) (hd:d.qN) (Z:Fin d.n→D)
    (dV:ZA (ZF Z)=⊤) (hN:∃ N,lcs D N=⊥)
    (lH:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆)
    (abl:∀ i k,d.lv i=0→d.lv k=0→
      ⁅Z i,Z k⁆∈ZA (iO d Z 1)⊔lcs D 2)
    (aa1:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (iO d Z 2)⊔lcs D 3)
    (aaY:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (iO d Z (d.lv t+1))⊔lcs D (d.lv t+2)):
    ∀ w,1≤w→lcs D w≤ZA (Z '' {u | w≤d.lv u}):=by
  have jV:= ow d hd Z lH
  have hu:∀ k:Fin d.n,dE d Z k.val=Z k:=K_ d Z
  have hP:∀ ab∈Jw d,ab.1<ab.2∧ab.2<d.s:=by
   intro ab hab
   obtain ⟨t,ht,rfl⟩:=(xh d).mp hab
   exact ⟨XO.mp (hd.oR t ht),hd.kR t (by omega)⟩
  have E9:iO d Z 1=(fun ab:ℕ×ℕ=> ⁅dE d Z ab.1,dE d Z ab.2⁆) '' Jw d:=by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      have iQ:d.lv t=1:=ht
      refine ⟨((d.df t).1.val,(d.df t).2.val),(xh d).mpr ⟨t,iQ,rfl⟩,?_⟩
      show ⁅dE d Z (d.df t).1.val,dE d Z (d.df t).2.val⁆=Z t
      rw[hu,hu,lH t (by omega)]
    · rintro ⟨ab,hab,rfl⟩
      obtain ⟨t,ht,rfl⟩:=(xh d).mp hab
      refine ⟨t,ht,?_⟩
      show Z t=⁅dE d Z (d.df t).1.val,dE d Z (d.df t).2.val⁆
      rw[hu,hu]
      exact lH t (by omega)
  have lU:∀ w,1≤w→∀ x∈iO d Z (w+1),∃ y∈ZA (iO d Z w),
      ∃ b<d.s,x =⁅y,dE d Z b⁆:=by
   intro w hw x hx
   obtain ⟨t,ht,rfl⟩:=hx
   have iQ:d.lv t=w+1:=ht
   have h1:1≤d.lv t:=by omega
   have ha:d.lv (d.df t).1=w:=by have:=hd.wY t h1; omega
   refine ⟨Z (d.df t).1,ZD ⟨(d.df t).1,ha,rfl⟩,(d.df t).2.val,
     hd.kR t h1,?_⟩
   rw[hu]
   exact lH t h1
  have zv:ZA (iO d Z 0)⊔lcs D 1=⊤:=by
   rw[Yo, ← dV,ZE]
   rintro _ ⟨t,rfl⟩
   by_cases h0:d.lv t=0
   · exact ZK (ZD ⟨t,h0,rfl⟩)
   · exact ZL (bC (D:=D) (show 1≤d.lv t by omega) (jV t))
  have hH1:∀ x∈iO d Z 0,∀ y∈iO d Z 0,
      ⁅x,y⁆∈ZA (iO d Z 1)⊔lcs D 2:=by
   rintro _ ⟨i,hi,rfl⟩ _ ⟨k,hk,rfl⟩
   exact abl i k hi hk
  have hH2:∀ ab∈Jw d,∀ k≤ab.2,⁅⁅dE d Z ab.1,dE d Z ab.2⁆,dE d Z k⁆∈
      ZA (iO d Z 2)⊔lcs D 3:=by
   intro ab hab k hk
   obtain ⟨t,ht,rfl⟩:=(xh d).mp hab
   have lQ:k≤(d.df t).2.val:=hk
   have BG:k<d.n:=by
    have:=hd.kR t (by omega)
    have:=hd.yA
    omega
   show ⁅⁅dE d Z (d.df t).1.val,dE d Z (d.df t).2.val⁆,dE d Z k⁆∈_
   rw[hu,hu, ← lH t (by omega),r7 d Z BG]
   exact aa1 t ⟨k,BG⟩ ht lQ
  have hH3:∀ w,2≤w→∀ x∈iO d Z w,∀ k<d.s,
      ⁅x,dE d Z k⁆∈ZA (iO d Z (w+1))⊔lcs D (w+2):=by
   rintro w hw _ ⟨t,ht,rfl⟩ k hk
   have iQ:d.lv t=w:=ht
   have BG:k<d.n:=lt_of_lt_of_le hk hd.yA
   rw[r7 d Z BG]
   have abt:=aaY t ⟨k,BG⟩ (by omega) hk
   rwa[iQ]at abt
  obtain ⟨N,hN⟩:=hN
  have L7:=Km d.s (dE d Z) (iO d Z 0) (Jw d) (iO d Z) hP E9 lU zv hH1 hH2 hH3 N hN
  intro w hw
  refine WS (L7 w hw) ?_
  rw[ZE]
  intro x hx
  simp only[Set.mem_iUnion,PY,exists_prop]at hx
  obtain ⟨v,hv,t,ht,rfl⟩:=hx
  have iQ:d.lv t=v:=ht
  exact ZD ⟨t,(show w≤d.lv t by omega),rfl⟩
lemma Ja [Finite D] {p:ℕ} (hp:0<p) (d:aO) (hd:d.Valid)
    (Z:Fin d.n→D) (dV:ZA (ZF Z)=⊤) (hN:∃ N,lcs D N=⊥)
    (lH:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆)
    (hpow:∀ t,Z t^(p^d.a t)∈ZA (Z '' {u | d.prec t u}))
    (hc0:∀ t k,d.lv t=0→d.lv k=0→t<k→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u}))
    (lT:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u}))
    (uL:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u})):
    ZB D ≤p^(∑ t,d.a t):=by
  have jV:= ow d hd.toqN Z lH
  have o4:∀ (P Q:Fin d.n→Prop),(∀ u,P u→Q u)→
      ZA (Z '' {u | P u})≤ZA (Z '' {u | Q u}):=
    fun P Q h=>ZS (by rintro _ ⟨u,hu,rfl⟩; exact ⟨u,h u hu,rfl⟩)
  have L8:∀ w,1≤w→ZA (Z '' {u | w≤d.lv u})≤
      ZA (iO d Z w)⊔lcs D (w+1):=by
    intro w hw
    rw[ZE]
    rintro _ ⟨t,ht,rfl⟩
    have iQ:w≤d.lv t:=ht
    rcases XU w (d.lv t) with aeR | Ep
    · exact ZL (bC (D:=D) (show w+1≤d.lv t by omega) (jV t))
    · exact ZK (ZD ⟨t,le_antisymm Ep iQ,rfl⟩)
  have abl:∀ i k,d.lv i=0→d.lv k=0→
      ⁅Z i,Z k⁆∈ZA (iO d Z 1)⊔lcs D 2:=by
   intro i k gJ lQ
   rcases Vq i k with hik | rfl | hki
   · exact L8 1 YD (o4 _ _ (fun u hu=>by omega) (hc0 i k gJ lQ hik))
   · rw[commutatorElement_self]
     exact one_mem _
   · rw[← commutatorElement_inv]
     exact inv_mem (L8 1 YD (o4 _ _ (fun u hu=>by omega) (hc0 k i lQ gJ hki)))
  have aa1:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (iO d Z 2)⊔lcs D 3:= fun t k ht hk=>
    L8 2 (by omega) (o4 _ _ (fun u hu=>by omega) (lT t k ht hk))
  have aaY:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (iO d Z (d.lv t+1))⊔lcs D (d.lv t+2):=by
   intro t k ht hk
   have abt:=L8 (d.lv t+1) (by omega)
     (o4 _ _ (fun u hu=>by omega) (uL t k ht hk))
   rwa[show d.lv t+1+1=d.lv t+2 by omega]at abt
  have f6:=BV d hd.toqN Z dV hN lH abl aa1 aaY
  have sw:∀ t u,d.prec t u→
      Z t *Z u*(Z t)⁻¹∈ZA (Z '' {u | d.prec t u}):=by
    intro t u htu
    have he:Z t *Z u*(Z t)⁻¹=⁅Z t,Z u⁆*Z u:=by
     simp only[commutatorElement_def]
     group
    rw[he]
    refine mul_mem ?_ (ZD ⟨u,htu,rfl⟩)
    have h1:= f6 (d.lv u+1) (by omega) (bF (Z t) (jV u))
    refine o4 _ _ (fun u' oF=>?_) h1
    have aei:d.lv u+1≤d.lv u':= oF
    have aeo:d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val):=htu
    exact Y7 (by omega)
  have dS:=xd Z (fun t=>p^d.a t) (fun t=>XD hp _) d.prec
    d.Fh d.A5 d.Gb hpow sw ZU (fun _ _ _ _=>Zb _)
  have o5:∏ t∈(ZU:Finset (Fin d.n)),(fun t=>p^d.a t) t=
      p^(∑ t,d.a t):=XB _ _ _
  rw[W8,RD,dV,Yn]at dS
  exact dS.trans (WT o5)
end CardData
section Rigid
variable {G G':Type u} [Group G] [Group G']
lemma El [Finite G] [Finite G'] [XN G] [XN G']
    {p:ℕ} (hp:0<p) (d:aO) (hd:d.Valid) (X:Fin d.n→G) (X':Fin d.n→G')
    (h:h_ p d X) (h':h_ p d X'):
    ZB (diagSub X X')≤p^(∑ t,d.a t):=by
 have hF:∀ e,p9 X X' (gN (jA X X') e)=gN X e:= fun e=>O3 _ _ _
 have hS:∀ e,pW X X' (gN (jA X X') e)=gN X' e:= fun e=>O3 _ _ _
 have m_:∀ (x:diagSub X X') (e:Fin d.n→ℕ),p9 X X' x =gN X e→
     pW X X' x =gN X' e→x =gN (jA X X') e:=by
  intro x e h1 h2
  apply MU X X'
  · rw[h1,hF]
  · rw[h2,hS]
 refine Ja hp d hd (jA X X') (GF X X') ?_ ?_ ?_ ?_ ?_ ?_
 · exact Yh.mp inferInstance
 · intro t ht
   apply MU X X'
   · simp only[YW,oP]
     exact h.Fk t ht
   · simp only[YW,oX]
     exact h'.Fk t ht
 · intro t
   rw [m_ (jA X X' t^(p^d.a t)) (d.b t) (by simp only[map_pow,oP]; exact h.pow t)
     (by simp only[map_pow,oX]; exact h'.pow t)]
   exact vI _ _ _ (fun u hu=>hd.GZ t u hu)
 · intro t k ht hk Ml
   rw [m_ ⁅jA X X' t,jA X X' k⁆ (d.c t k) (by simp only[YW,oP]; exact h.DZ t k ht hk Ml)
     (by simp only[YW,oX]; exact h'.DZ t k ht hk Ml)]
   exact vI _ _ _ (fun u hu=>hd.Aa t k u hu)
 · intro t k ht hk
   rw [m_ ⁅jA X X' t,jA X X' k⁆ (d.c t k) (by simp only[YW,oP]; exact h.Iq t k ht hk)
     (by simp only[YW,oX]; exact h'.Iq t k ht hk)]
   exact vI _ _ _ (fun u hu=>hd.Aa t k u hu)
 · intro t k ht hk
   rw [m_ ⁅jA X X' t,jA X X' k⁆ (d.c t k) (by simp only[YW,oP]; exact h.IG t k ht hk)
     (by simp only[YW,oX]; exact h'.IG t k ht hk)]
   exact vI _ _ _ (fun u hu=>hd.Aa t k u hu)
lemma LI {p:ℕ} (hp:p.Prime) [Finite G] [Finite G'] (d:aO)
    (hd:d.Valid) (X:Fin d.n→G) (X':Fin d.n→G') (h:h_ p d X)
    (h':h_ p d X'):Nonempty (G≃*G'):=by
 have:Fact p.Prime:=⟨hp⟩
 have:XN G:=(YK h.card).isNilpotent
 have:XN G':=(YK h'.card).isNilpotent
 have hK:=El hp.pos d hd X X' h h'
 have s8:Ur (p9 X X'):=
   (ME X X' h.gen).bijective_of_nat_card_le (by rw[h.card]; exact hK)
 have uj:Ur (pW X X'):=
   (MH X X' h'.gen).bijective_of_nat_card_le (by rw[h'.card]; exact hK)
 exact ⟨(RU (p9 X X') s8).symm.trans
   (RU (pW X X') uj)⟩
end Rigid
section Layers
variable {G:Type u} [Group G]
def jw (d:aO) (w j:ℕ):Set (Fin d.n):=
  {u | w<d.lv u∨(w=d.lv u∧u.val<j)}
lemma dY (d:aO) {w j:ℕ} {u:Fin d.n}:
    u∈jw d w j↔w<d.lv u∨(w=d.lv u∧u.val<j):=U8
noncomputable def e8 (p:ℕ) (d:aO) (X:Fin d.n→G) (t:Fin d.n):ℕ:=
  sInf {a:ℕ | X t^(p^a)∈ZA (X '' jw d (d.lv t) t.val)}
def Bq (p:ℕ) (d:aO) (X:Fin d.n→G) (w j:ℕ):Prop:=
  ∀ z∈ZA (X '' jw d w j),∃ e:Fin d.n→ℕ,
    (∀ u,e u≠0→u∈jw d w j)∧(∀ u,e u<p^e8 p d X u)∧z=gN X e
variable {p m:ℕ} (d:aO) (X:Fin d.n→G)
lemma oZ [Finite G] (hG:ZB G=p^m) (t:Fin d.n):
    X t^(p^e8 p d X t)∈ZA (X '' jw d (d.lv t) t.val):=by
 have d8:{a:ℕ | X t^(p^a)∈ZA (X '' jw d (d.lv t) t.val)}.Nonempty:=by
   refine ⟨m,?_⟩
   show X t^(p^m)∈ZA (X '' jw d (d.lv t) t.val)
   rw[← hG,TY]
   exact one_mem _
 exact Wr d8
lemma Qo [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (t:Fin d.n) (k:ℕ)
    (Br :0<k) (hk:k<p^e8 p d X t):
    X t^k∉ZA (X '' jw d (d.lv t) t.val):=by
 intro cI
 have h2:X t^(p^m)∈ZA (X '' jw d (d.lv t) t.val):=by
  rw[← hG,TY]
  exact one_mem _
 obtain ⟨e, -,he⟩:=(Yp hp).mp (Nat.gcd_dvd_right k (p^m))
 have h3:X t^(Nat.gcd k (p^m))∈ZA (X '' jw d (d.lv t) t.val):=by
  have h4:X t^((Nat.gcd k (p^m):ℕ):ℤ)∈
      ZA (X '' jw d (d.lv t) t.val):=by
   rw[OE,ON,TW,TW,WO,WO]
   exact mul_mem (OO cI _) (OO h2 _)
  rwa[WO]at h4
 rw[he]at h3
 have cO:e8 p d X t≤e:=WK h3
 have v5:p^e∣k:=by
  rw[← he]
  exact Nat.gcd_dvd_left k (p^m)
 have h5:p^e≤k:=Nat.le_of_dvd Br v5
 have h6:p^e8 p d X t≤p^e:=Zk hp.pos cO
 exact absurd (lt_of_lt_of_le (VT h5 hk) h6) (UO _)
lemma EO (jV:∀ t,X t∈lcs G (d.lv t))
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})) (w j:ℕ):
    (ZA (X '' jw d w j)).Normal:=by
  refine d6 (n:=w) ?_ ?_
  · refine (f6 (w+1) (by omega)).trans (ZS ?_)
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,Y7 hu,rfl⟩
  · rw[ZE]
    rintro _ ⟨u,hu,rfl⟩
    have oF:=(dY d).mp hu
    exact bC (D:=G) (show w≤d.lv u by omega) (jV u)
lemma KQ {w j w' j':ℕ} (h:jw d w j=jw d w' j') (H:Bq p d X w' j'):
    Bq p d X w j:=by
 unfold Bq at *
 rw[h]
 exact H
lemma aap (hp:0<p) {w:ℕ} (j:ℕ) (h:∀ u:Fin d.n,d.lv u<w):
    Bq p d X w j:=by
 intro z hz
 have acP:jw d w j= ∅ :=by
  ext u
  simp only[dY,Rm,iff_false]
  have:=h u
  omega
 rw[acP,Ob,Sz,WB]at hz
 refine ⟨fun _=> 0,fun u hu=> (hu rfl).elim,fun u=>XD hp _,?_⟩
 rw[hz,aa5]
lemma aby {w:ℕ} (H:Bq p d X (w+1) d.n):Bq p d X w 0:=by
 refine KQ d X ?_ H
 ext u
 simp only[dY]
 have:=u.isLt
 constructor
 · intro h
   omega
 · intro h
   omega
lemma aaW [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.qN)
    (jV:∀ t,X t∈lcs G (d.lv t))
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})) {w j:ℕ}
    (hj:Bq p d X w j) (h0:Bq p d X w 0):Bq p d X w (j+1):=by
  have f5:∀ u v:Fin d.n,d.lv u<d.lv v→u<v:=by
   intro u v h
   by_contra hc
   have:=hd.mono v u (not_lt.mp hc)
   omega
  by_cases qX:∃ t:Fin d.n,t.val=j∧d.lv t=w
  swap
  · refine KQ d X ?_ hj
    ext u
    simp only[dY]
    constructor
    · rintro (h | ⟨h1,h2⟩)
      · exact Y7 h
      · refine XQ ⟨h1,?_⟩
        rcases XU u.val j with h3 | h3
        · exact h3
        · exact absurd ⟨u,by omega,h1.symm⟩ qX
    · rintro (h | ⟨h1,h2⟩)
      · exact Y7 h
      · exact XQ ⟨h1,by omega⟩
  obtain ⟨t,rfl,rfl⟩:=qX
  intro z hz
  have hq:0<p^e8 p d X t:=XD hp.pos _
  have hK:=EO d X jV f6 (d.lv t) t.val
  have hS:X '' jw d (d.lv t) (t.val+1)⊆
      insert (X t) ((ZA (X '' jw d (d.lv t) t.val):Subgroup G):Set G):=by
   rintro _ ⟨u,hu,rfl⟩
   by_cases pJ:u=t
   · rw[pJ]
     exact RA _ _
   · refine Uk _ (ZD ⟨u,?_,rfl⟩)
     have oF:=(dY d).mp hu
     have d8:u.val≠t.val:= fun h=>pJ (YL h)
     exact (dY d).mpr (by omega)
  obtain ⟨y,hy,k,rfl⟩:=pQ _ (X t) _ hq (fun y hy=>hK.conj_mem y hy (X t))
    (oZ d X hG t) _ hS z hz
  obtain ⟨y',IE,k',lQ,hyk⟩:∃ y'∈ZA (X '' jw d (d.lv t) t.val),
      ∃ k'<p^e8 p d X t,y *X t^k=y'*X t^k':=
    ⟨y *(X t^(p^e8 p d X t))^(k/p^e8 p d X t),
      mul_mem hy (pow_mem (oZ d X hG t) _),k % p^e8 p d X t,W3 _ hq,
      by rw[UQ, ← X5, ← Xh,Wa]⟩
  rw[hyk]
  obtain ⟨e',Nd,adD,rfl⟩:=hj y' IE
  have qO :gN X e'=gN X (fun u=>if d.lv u=d.lv t then e' u else 0)*
      gN X (fun u=>if d.lv u=d.lv t then 0 else e' u):=by
    rw[Kp]
    · congr 1
      funext u
      simp only[Vc]
      split_ifs<;>simp
    · intro u v hu hv
      apply f5
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
      have:=(dY d).mp (Nd v hv1.2)
      omega
  have acZ:gN X (fun u=>if d.lv u=d.lv t then 0 else e' u)∈
      ZA (X '' jw d (d.lv t) 0):=by
    refine vI X _ _ (fun v hv=>?_)
    have hv1:d.lv v≠d.lv t∧e' v≠0:=by
     by_cases hc:d.lv v=d.lv t
     · exfalso
       apply hv
       show (if d.lv v=d.lv t then 0 else e' v)=0
       rw[if_pos hc]
     · refine ⟨hc,fun h0=>hv ?_⟩
       show (if d.lv v=d.lv t then 0 else e' v)=0
       rw[if_neg hc,h0]
    have:=(dY d).mp (Nd v hv1.2)
    exact (dY d).mpr (by omega)
  have hh:(X t^k')⁻¹*gN X (fun u=>if d.lv u=d.lv t then 0 else e' u)*X t^k'∈
      ZA (X '' jw d (d.lv t) 0):=by
    have:=(EO d X jV f6 (d.lv t) 0).conj_mem _ acZ (X t^k')⁻¹
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
    have:=(dY d).mp (Nd u hu1.2)
    rw[hvt,XO]
    omega
  have h2:∀ u v,((fun u=>if d.lv u=d.lv t then e' u else 0)+delta t k') u≠0→
      eH v≠0→u<v:=by
    intro u v hu hv
    apply f5
    have K9:=(dY d).mp (hHS v hv)
    have oF:d.lv u=d.lv t:=by
     by_contra hc
     have pJ:u≠t:= fun h=>hc (by rw[h])
     apply hu
     simp only[Vc,delta,if_neg hc,if_neg pJ,add_zero]
    omega
  refine ⟨(fun u=>if d.lv u=d.lv t then e' u else 0)+delta t k'+eH,?_,?_,?_⟩
  · intro u hu
    rw[dY]
    by_cases h3:eH u=0
    · by_cases pJ:u=t
      · right
        rw[pJ]
        exact ⟨rfl,by omega⟩
      · have hL:(if d.lv u=d.lv t then e' u else 0)≠0:=by
          intro h0
          apply hu
          simp only[Vc,delta,if_neg pJ,h3,add_zero,h0]
        by_cases hc:d.lv u=d.lv t
        · rw[if_pos hc]at hL
          have:=(dY d).mp (Nd u hL)
          omega
        · rw[if_neg hc]at hL
          exact absurd rfl hL
    · have:=(dY d).mp (hHS u h3)
      omega
  · intro u
    show (if d.lv u=d.lv t then e' u else 0)+delta t k' u+eH u<p^e8 p d X u
    by_cases hc:d.lv u=d.lv t
    · have hH0:eH u=0:=by
        by_contra d8
        have:=(dY d).mp (hHS u d8)
        omega
      by_cases pJ:u=t
      · have he0:e' u=0:=by
          by_contra d8
          have:=(dY d).mp (Nd u d8)
          rw[pJ]at this
          omega
        rw[if_pos hc,he0,hH0,pJ]
        simpa[delta] using lQ
      · rw[if_pos hc,hH0]
        simpa[delta,pJ] using adD u
    · have pJ:u≠t:= fun h=>hc (by rw[h])
      rw[if_neg hc]
      simpa[delta,pJ] using hHb u
  · rw[← Kp X _ eH h2, ← Kp X _ (delta t k') h1,KV, ← hH,qO]
    group
lemma JZ [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.qN)
    (jV:∀ t,X t∈lcs G (d.lv t))
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∀ w j,Bq p d X w j:=by
  obtain ⟨M,hM⟩:∃ M,∀ u:Fin d.n,d.lv u<M:=
    ⟨ZU.sup d.lv+1,fun u=>Ws (OV (Zb u))⟩
  have key:∀ k w,M≤w+k→∀ j,Bq p d X w j:=by
   intro k
   induction k with
   | zero=>
     intro w hw j
     exact aap d X hp.pos j (fun u=>lt_of_lt_of_le (hM u) (by omega))
   | succ k ih=>
     intro w hw
     have h0:Bq p d X w 0:=aby d X (ih (w+1) (by omega) d.n)
     intro j
     induction j with
     | zero=>exact h0
     | succ j ihj=>exact aaW d X hp hG hd jV f6 ihj h0
  exact fun w j=>key M w (by omega) j
lemma KD [Finite G] (hp:p.Prime) (hG:ZB G=p^m)
    (dV:ZA (ZF X)=⊤) (jV:∀ t,X t∈lcs G (d.lv t))
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ZB G=p^(∑ t,e8 p d X t):=by
  have o5:∏ t∈(ZU:Finset (Fin d.n)),(fun t=>p^e8 p d X t) t=
      p^(∑ t,e8 p d X t):=XB _ _ _
  have sw:∀ t u,d.prec t u→
      X t *X u*(X t)⁻¹∈ZA (X '' {u | d.prec t u}):=by
    intro t u htu
    have he:X t *X u*(X t)⁻¹=⁅X t,X u⁆*X u:=by
     simp only[commutatorElement_def]
     group
    rw[he]
    refine mul_mem ?_ (ZD ⟨u,htu,rfl⟩)
    have h1:= f6 (d.lv u+1) (by omega) (bF (X t) (jV u))
    refine ZS ?_ h1
    rintro _ ⟨u',oF,rfl⟩
    refine ⟨u',?_,rfl⟩
    have aei:d.lv u+1≤d.lv u':= oF
    have aeo:d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val):=htu
    exact Y7 (by omega)
  have cO:=xd X (fun t=>p^e8 p d X t) (fun t=>XD hp.pos _) d.prec
    d.Fh d.A5 d.Gb (fun t=>oZ d X hG t) sw ZU
    (fun _ _ _ _=>Zb _)
  have Ep:=GG X (fun t=>p^e8 p d X t) d.prec d.A5 d.Gb
    (fun t k Br hk=>Qo d X hp hG t k Br hk) ZU
    (fun _ _ _ _=>Zb _)
  rw[W8,RD,dV,Yn]at cO Ep
  rw[← o5]
  exact le_antisymm cO Ep
lemma Ln [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.qN)
    (dV:ZA (ZF X)=⊤)
    (lH:∀ t,1≤d.lv t→X t=⁅X (d.df t).1,X (d.df t).2⁆)
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∃ (b:Fin d.n→Fin d.n→ℕ) (c:Fin d.n→Fin d.n→Fin d.n→ℕ),
      ({ d with a:=e8 p d X,b:=b,c:= c }:aO).Valid∧
      ({ d with a:=e8 p d X,b:=b,c:= c }:aO).Bounded p∧
      h_ p ({ d with a:=e8 p d X,b:=b,c:= c }:aO) X:=by
  have jV:= ow d hd X lH
  have hnf:=JZ d X hp hG hd jV f6
  have hb:∀ t,∃ e:Fin d.n→ℕ,(∀ u,e u≠0→d.prec t u)∧
      (∀ u,e u<p^e8 p d X u)∧X t^(p^e8 p d X t)=gN X e:=
    fun t=>hnf (d.lv t) t.val _ (oZ d X hG t)
  have hc:∀ t k,∃ e:Fin d.n→ℕ,(∀ u,e u≠0→d.lv t<d.lv u)∧
      (∀ u,e u<p^e8 p d X u)∧⁅X t,X k⁆=gN X e:=by
   intro t k
   have cI:⁅X t,X k⁆∈ZA (X '' jw d (d.lv t) 0):=by
    have h1:= f6 (d.lv t+1) (by omega) (a8 (jV t) (X k))
    refine ZS ?_ h1
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,Y7 hu,rfl⟩
   obtain ⟨e,he1,he2,he3⟩:=hnf _ _ _ cI
   refine ⟨e,fun u hu=>?_,he2,he3⟩
   have:=(dY d).mp (he1 u hu)
   omega
  choose b hb using hb
  choose c hc using hc
  refine ⟨b,c,?_,⟨fun t u=> (hb t).2.1 u,fun t k u=> (hc t k).2.1 u⟩,?_⟩
  · exact ⟨⟨hd.mono,hd.yA,hd.core,hd.wY,hd.kR,hd.oR⟩,
      fun t u h=> (hb t).1 u h,fun t k u h=> (hc t k).1 u h⟩
  · exact ⟨KD d X hp hG dV jV f6,dV,lH,fun t=> (hb t).2.2,
      fun t k _ _ _=> (hc t k).2.2,fun t k _ _=> (hc t k).2.2,fun t k _ _=> (hc t k).2.2⟩
end Layers
section Frattini
variable {G:Type u} [Group G]
def ach (A B:Subgroup G) [B.Normal] (p:ℕ)
    (hc:∀ x∈A,∀ y∈A,ZG B x*ZG B y=
      ZG B y *ZG B x):Subgroup (G⧸B) where
  carrier :={z | ∃ a∈A,z=ZG B a^p}
  mul_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    show ∃ c∈A,ZG B a^p*ZG B b^p=
      ZG B c^p
    refine ⟨a*b,A.mul_mem ha hb,?_⟩
    rw[YP,Commute.mul_pow (hc a ha b hb) p]
  one_mem':=by
    show ∃ c∈A,(1:G⧸B)=ZG B c^p
    exact ⟨1,A.one_mem,by rw[X9,one_pow]⟩
  inv_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    show ∃ c∈A,(ZG B a^p)⁻¹=ZG B c^p
    exact ⟨a⁻¹,A.inv_mem ha,by rw[Wq,inv_pow]⟩
lemma C8 [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (A B:Subgroup G) [B.Normal] (hAB:∀ x∈A,∀ y∈A,⁅x,y⁆∈B)
    (h:A≤B⊔ZA (ZF (fun g:A=> (g:G)^p))):A≤B:=by
  classical
  have:Fact p.Prime:=⟨hp⟩
  have:Finite (G⧸B):=Zy _ (YI B)
  have j3:∀ g:G,ZG B g=1↔g∈B:= fun g=>by
    rw[← Zm,YV]
  have hc:∀ x∈A,∀ y∈A,ZG B x*ZG B y=
      ZG B y *ZG B x:=by
   intro x hx y hy
   have h1:ZG B ⁅x,y⁆=1:=(j3 _).mpr (hAB x hx y hy)
   rw[YW]at h1
   exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have cO:A≤(ach A B p hc).comap (ZG B):=by
   refine h.trans (sup_le ?_ ?_)
   · intro b hb
     show ∃ a'∈A,ZG B b=ZG B a' ^p
     exact ⟨1,A.one_mem,by rw[X9,one_pow,(j3 b).mpr hb]⟩
   · rw[ZE]
     rintro _ ⟨g,rfl⟩
     show ∃ a'∈A,ZG B ((g:G)^p)=ZG B a' ^p
     exact ⟨g,g.2,by rw[map_pow]⟩
  have hAQ:∀ a∈A,∃ a'∈A,ZG B a=ZG B a' ^p:=
    fun a ha=>cO ha
  have j6:Zn (fun z:A.map (ZG B)=>
      (⟨(z:G⧸B)^p,pow_mem z.2 p⟩:A.map (ZG B))):=by
    rintro ⟨y,hy⟩
    obtain ⟨a,ha,rfl⟩:=Zj.mp hy
    obtain ⟨a',u6,he⟩:=hAQ a ha
    exact ⟨⟨ZG B a',Vi _ u6⟩,Zu he.symm⟩
  have eW:=Finite.injective_iff_surjective.mpr j6
  intro a ha
  rw[← j3]
  by_contra d8
  obtain ⟨k,hk⟩:=(YK hG).to_quotient B (ZG B a)
  have qX:∃ k,ZG B a^p^k=1:=⟨k,hk⟩
  obtain ⟨k0,nF,nU⟩:∃ k0,ZG B a^p^k0=1∧
      ∀ j<k0,ZG B a^p^j≠1:=
    ⟨Nat.find qX,Nat.find_spec qX,fun j hj=>Nat.find_min qX hj⟩
  have Br :k0≠0:=by
   rintro rfl
   rw[Y6,pow_one]at nF
   exact d8 nF
  have hz:(ZG B a^p^(k0 - 1))^p=1:=by
   rw[← X5, ← Xr,show k0 - 1+1=k0 by omega,nF]
  have hzA:ZG B a^p^(k0 - 1)∈A.map (ZG B):=
    pow_mem (Vi _ ha) _
  have heq:(⟨_,hzA⟩:A.map (ZG B))=⟨1,one_mem _⟩:=by
   apply eW
   apply Zu
   show (ZG B a^p^(k0 - 1))^p=(1:G⧸B)^p
   rw[hz,one_pow]
  exact nU (k0 - 1) (by omega) (congrArg XJ heq)
def dC (p:ℕ) (G:Type u) [Group G]:ℕ→ Subgroup G
  | 0=>cE p G
  | w+1=>lcs G (w+2)⊔ZA (ZF (fun g:lcs G (w+1)=> (g:G)^p))
lemma dD (p:ℕ):∀ w,lcs G (w+1)≤dC p G w
  | 0=>by
    show lcs G 1≤ cE p G
    rw[← eO]
    exact Z5
  | _+1=>WM
lemma oO (p:ℕ) (w:ℕ):dC p G (w+1)≤lcs G (w+1):=by
 show lcs G (w+2)⊔ZA (ZF (fun g:lcs G (w+1)=> (g:G)^p))≤
   lcs G (w+1)
 refine sup_le (bC (by omega)) ?_
 rw[ZE]
 rintro _ ⟨g,rfl⟩
 exact pow_mem g.2 p
lemma qG (p:ℕ):∀ (w:ℕ) (x:G),x∈lcs G w→x^p∈dC p G w
  | 0,x,_=>gG p x
  | w+1,x,hx =>ZL (ZD ⟨⟨x,hx⟩,rfl⟩)
lemma jU (p:ℕ) (w:ℕ) (T:Set G) (hT:T⊆lcs G w):
    (ZA T⊔dC p G w).Normal:=by
 rcases w with _ | w
 · exact qC ((dD p 0).trans Z5)
 · exact d6 (n:=w+1) ((dD p (w+1)).trans Z5)
     (sup_le ((ZE _).mpr hT) (oO p w))
lemma A8 [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) (w:ℕ)
    (T:Set G) (hT:T⊆lcs G (w+1))
    (h:lcs G (w+1)≤ZA T⊔dC p G (w+1)):
    lcs G (w+1)≤ZA T⊔lcs G (w+2):=by
 have hN:(ZA T⊔lcs G (w+2)).Normal:=
   d6 (n:=w+1) Z5
     (sup_le ((ZE _).mpr hT) (bC (by omega)))
 refine C8 hp hG (lcs G (w+1)) _ ?_ ?_
 · intro x hx y hy
   have h1:=d5 hx hy
   exact ZL
     (bC (D:=G) (show w+2≤w+1+(w+1)+1 by omega) h1)
 · rw[sup_assoc]
   exact h
lemma lC [Finite G] {p:ℕ} (hp:0<p) (M:Subgroup G) (x:ℕ→G)
    (hN:∀ j,(ZA (x '' ZH j)⊔M).Normal) (Lb:∀ j,x j^p∈M):
    ∀ j,ZB (ZA (x '' ZH j)⊔M:Subgroup G)≤p^j*ZB M:=by
 intro j
 induction j with
 | zero=>
   have cO:ZA (x '' ZH 0)⊔M≤M:=by
    refine sup_le ?_ YD
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Yw.mp hi) (Xg i)
   rw[Y6,Wn]
   exact YG cO
 | succ j ih=>
   have:=hN j
   have cO:ZA (x '' ZH (j+1))⊔M≤
       (ZA (x '' ZH j)⊔M)⊔YQ (x j):=by
    refine sup_le ?_ (Z5.trans WM)
    rw[ZE]
    rintro _ ⟨i,hi,rfl⟩
    have gJ:i<j+1:=Yw.mp hi
    by_cases hij:i<j
    · exact ZK (ZK
        (ZD ⟨i,Yw.mpr hij,rfl⟩))
    · rw[show i=j by omega]
      exact ZL (Xc (x j))
   have h1:=YG cO
   have h2:=rH (K:=ZA (x '' ZH j)⊔M) hp
     (ZL (Lb j))
   have h3:p*ZB (ZA (x '' ZH j)⊔M:Subgroup G)≤
       p*(p^j*ZB M):=Zr YD ih
   have e:p*(p^j*ZB M)=p^(j+1)*ZB M:=by
    rw[Xr]
    ring
   rw[← e]
   exact h1.trans (h2.trans h3)
end Frattini
section Greedy
variable {G:Type u} [Group G]
open Classical in
noncomputable def c9 (c:ℕ→G) (K:Subgroup G):ℕ→Finset ℕ
  | 0=> ∅
  | j +1=>if c j∈ZA (c '' (c9 c K j:Set ℕ))⊔K then c9 c K j
      else insert j (c9 c K j)
lemma qH (c:ℕ→G) (K:Subgroup G) (j:ℕ):
    (c9 c K (j+1)= c9 c K j∧
      c j∈ZA (c '' (c9 c K j:Set ℕ))⊔K)∨
    (c9 c K (j+1)=insert j (c9 c K j)∧
      c j∉ZA (c '' (c9 c K j:Set ℕ))⊔K):=by
 by_cases h:c j∈ZA (c '' (c9 c K j:Set ℕ))⊔K
 · left
   refine ⟨?_,h⟩
   simp only[c9,if_pos h]
 · right
   refine ⟨?_,h⟩
   simp only[c9,if_neg h]
lemma pD (c:ℕ→G) (K:Subgroup G):∀ j,∀ i∈c9 c K j,i<j
  | 0,i,hi=>by simp[c9]at hi
  | j +1,i,hi=>by
    rcases qH c K j with ⟨h, -⟩ | ⟨h, -⟩
    · rw[h]at hi
      exact OF (pD c K j i hi)
    · rw[h,PZ]at hi
      rcases hi with rfl | hi
      · exact XZ _
      · exact OF (pD c K j i hi)
lemma qw (c:ℕ→G) (K:Subgroup G):
    ∀ d j i,i<j→(i∈c9 c K (j+d)↔i∈c9 c K j)
  | 0,_,_,_=>U8
  | d + 1,j,i,hij=>by
    rw[← qw c K d j i hij,show j+(d+1)=j+d+1 by omega]
    rcases qH c K (j+d) with ⟨h, -⟩ | ⟨h, -⟩
    · rw[h]
    · rw [h,PZ]
      constructor
      · rintro (h' | h')
        · exact absurd h' (by omega)
        · exact h'
      · exact XQ
lemma KS (c:ℕ→G) (K:Subgroup G):
    ∀ j,∀ i<j,c i∈ZA (c '' (c9 c K j:Set ℕ))⊔K
  | 0,i,hi=>absurd hi (Xg i)
  | j + 1,i,hi=>by
    have o4:ZA (c '' (c9 c K j:Set ℕ))⊔K≤
        ZA (c '' (c9 c K (j+1):Set ℕ))⊔K:=by
     refine sup_le_sup_right (ZS (Uw ?_)) K
     intro x hx
     rcases qH c K j with ⟨h, -⟩ | ⟨h, -⟩
     · rw[h]
       exact hx
     · rw[h,Ve]
       exact Uk _ hx
    by_cases hij:i<j
    · exact o4 (KS c K j i hij)
    · have Q7:i=j:=by omega
      subst Q7
      rcases qH c K i with ⟨-,h'⟩ | ⟨h, -⟩
      · exact o4 h'
      · refine ZK (ZD ⟨i,?_,rfl⟩)
        rw[h,Ve]
        exact RA _ _
lemma Q4 (c:ℕ→G) (K:Subgroup G) {j i:ℕ} (hi:i∈c9 c K j):
    c i∉ZA (c '' (c9 c K i:Set ℕ))⊔K:=by
 have hij:=pD c K j i hi
 obtain ⟨d,rfl⟩:∃ d,j=i+1+d:=⟨j - (i+1),by omega⟩
 have h1:i∈c9 c K (i+1):=
   (qw c K d (i+1) i (XZ i)).mp hi
 rcases qH c K i with ⟨h, -⟩ | ⟨-,h'⟩
 · rw[h]at h1
   exact absurd (pD c K i i h1) (UO i)
 · exact h'
noncomputable def d9 (S:Finset ℕ) (i:ℕ):ℕ:=
  if h:i<S.card then S.orderEmbOfFin rfl ⟨i,h⟩ else 0
lemma w6 (S:Finset ℕ) {i:ℕ} (h:i<S.card):d9 S i∈S:=by
 unfold d9
 rw[dif_pos h]
 exact Finset.orderEmbOfFin_mem S rfl _
lemma Bl (S:Finset ℕ) {i j:ℕ} (hij:i<j) (hj:j<S.card):
    d9 S i<d9 S j:=by
 unfold d9
 rw[dif_pos (Uj hij hj),dif_pos hj]
 exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
lemma aa9 (S:Finset ℕ) {i j:ℕ} (hij:i≤j) (hj:j<S.card):
    d9 S i≤d9 S j:=by
 rcases XU i j with h | h
 · exact (Bl S h hj).le
 · have Q7:i=j:=by omega
   subst Q7
   exact YD
lemma aaw (S:Finset ℕ) {i j:ℕ} (hi:i<S.card) (hj:j<S.card)
    (h:d9 S i=d9 S j):i=j:=by
 rcases Vq i j with h' | h' | h'
 · exact absurd h (Bl S h' hj).ne
 · exact h'
 · exact absurd h (Bl S h' hi).ne'
lemma aak (S:Finset ℕ) {x:ℕ} (hx:x∈S):∃ i<S.card,d9 S i=x:=by
 have hr :x∈ZF (S.orderEmbOfFin rfl):=by
  rw[VL]
  exact hx
 obtain ⟨⟨i,hi⟩,rfl⟩:=hr
 refine ⟨i,hi,?_⟩
 unfold d9
 rw[dif_pos hi]
structure lB (G:Type u) where
  r :ℕ
  x:ℕ→G
  lK:ℕ→ℕ
  gC:ℕ→ℕ
noncomputable def jI (c:ℕ→G) (K:Subgroup G) (N:ℕ) (pa co:ℕ→ℕ):lB G where
  r :=(c9 c K N).card
  x:= fun i=>if i< (c9 c K N).card then c (d9 (c9 c K N) i) else 1
  lK:= fun i=>pa (d9 (c9 c K N) i)
  gC:= fun i=>co (d9 (c9 c K N) i)
variable (c:ℕ→G) (K:Subgroup G) (N:ℕ) (pa co:ℕ→ℕ)
lemma C4 {i:ℕ} (hi:i< (c9 c K N).card):
    (jI c K N pa co).x i= c (d9 (c9 c K N) i):=if_pos hi
lemma MS (i:ℕ):
    (jI c K N pa co).x i= c (d9 (c9 c K N) i)∨(jI c K N pa co).x i=1:=by
 by_cases hi:i< (c9 c K N).card
 · exact Y7 (if_pos hi)
 · exact XQ (if_neg hi)
lemma Dr {i i':ℕ} (hi:i< (c9 c K N).card) (gJ:i'< i):
    d9 (c9 c K N) i'∈c9 c K (d9 (c9 c K N) i):=by
 have h1:=Bl (c9 c K N) gJ hi
 have h2:=pD c K N _ (w6 _ hi)
 have h3:=w6 (c9 c K N) (Uj gJ hi)
 have h4:=qw c K (N - d9 (c9 c K N) i) (d9 (c9 c K N) i) _ h1
 rw[show d9 (c9 c K N) i+(N - d9 (c9 c K N) i)=N by omega]at h4
 exact h4.mp h3
lemma vF {i:ℕ} (hi:i< (jI c K N pa co).r):
    (jI c K N pa co).x i∉ZA ((jI c K N pa co).x '' ZH i)⊔K:=by
 intro cI
 have gJ:i< (c9 c K N).card:=hi
 rw[C4 c K N pa co gJ]at cI
 apply Q4 c K (w6 (c9 c K N) gJ)
 refine (sup_le_sup_right (ZS ?_) K) cI
 rintro _ ⟨i',Np,rfl⟩
 have Qu:i'< i:=Np
 refine ⟨d9 (c9 c K N) i',Dr c K N gJ Qu,?_⟩
 exact (C4 c K N pa co (Uj Qu gJ)).symm
lemma Dw {J:ℕ} (hJ:J≤N) {j:ℕ} (hj:j<J):
    c j∈ZA ((jI c K N pa co).x ''
      {i | i< (c9 c K N).card∧d9 (c9 c K N) i<J})⊔K:=by
  refine (sup_le_sup_right (ZS ?_) K) (KS c K J j hj)
  rintro _ ⟨y,hy,rfl⟩
  have hyJ:y<J:=pD c K J y hy
  have hyS:y∈c9 c K N:=by
   have h1:=qw c K (N - J) J y hyJ
   rw[show J+(N - J)=N by omega]at h1
   exact h1.mpr hy
  obtain ⟨i,hi,rfl⟩:=aak _ hyS
  exact ⟨i,⟨hi,hyJ⟩,C4 c K N pa co hi⟩
lemma LX {j:ℕ} (hj:j<N):
    c j∈ZA ((jI c K N pa co).x '' ZH (jI c K N pa co).r)⊔K:=by
 refine (sup_le_sup_right (ZS ?_) K) (Dw c K N pa co YD hj)
 rintro _ ⟨i,⟨hi, -⟩,rfl⟩
 exact ⟨i,hi,rfl⟩
end Greedy
section TheoremL
variable {G:Type u} [Group G]
def vP (s:ℕ) (u:ℕ→G):ℕ→ Set G
  | 0=> ∅
  | 1=> (fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' {ab | ab.1<ab.2∧ab.2<s}
  | w+2=> {x | ∃ y∈ZA (vP s u (w+1)),∃ b<s,x =⁅y,u b⁆}
lemma FU (s:ℕ) (u:ℕ→G):∀ w,vP s u (w+1)⊆(lcs G (w+1):Set G)
  | 0=>by
    rintro _ ⟨ab, -,rfl⟩
    exact b7 _ _
  | w+1=>by
    rintro _ ⟨y,hy,b, -,rfl⟩
    have IE:y∈lcs G (w+1):=(ZE _).mpr (FU s u w) hy
    exact a8 IE _
lemma aaT (s:ℕ) (u:ℕ→G) (H1:Set G)
    (zv:ZA H1⊔lcs G 1=⊤)
    (dG:lcs G 1≤ZA (vP s u 1)⊔lcs G 2):
    ∀ w,1≤w→lcs G w≤ZA (vP s u w)⊔lcs G (w+1):=by
 refine K7 s u H1 {ab | ab.1<ab.2∧ab.2<s} (vP s u) (fun ab hab=>hab) rfl
   ?_ zv ?_ ?_ ?_
 · intro w hw x hx
   obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
   exact hx
 · intro x _ y _
   exact dG (b7 x y)
 · intro ab hab k hk
   have lQ:k<s:=VT hk hab.2
   refine ZK (ZD ?_)
   show ⁅⁅u ab.1,u ab.2⁆,u k⁆∈vP s u (0+2)
   exact ⟨⁅u ab.1,u ab.2⁆,ZD ⟨ab,hab,rfl⟩,k,lQ,rfl⟩
 · intro w hw x hx k hk
   obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
   refine ZK (ZD ?_)
   show ⁅x,u k⁆∈vP s u (w'+2)
   exact ⟨x,ZD hx,k,hk,rfl⟩
end TheoremL
section Layers2
variable {G:Type u} [Group G]
def fO (s w j:ℕ):ℕ:=if w=0 then j % s else j/s
def fq (s w j:ℕ):ℕ:=if w=0 then j/s else j % s
def dN (s:ℕ) (u:ℕ→G) (w:ℕ) (L:lB G) (j:ℕ):G:=
  if (w=0∧¬ fO s w j<fq s w j)∨(w=1∧L.gC (fO s w j)<fq s w j) then 1
  else ⁅L.x (fO s w j),u (fq s w j)⁆
def cN (s w:ℕ) (L:lB G):ℕ:=if w=0 then s*s else L.r*s
lemma sP {s j:ℕ}:fO s 0 j=j % s:=if_pos rfl
lemma tK {s j:ℕ}:fq s 0 j=j/s:=if_pos rfl
lemma DQ {s:ℕ} {L:lB G}:cN s 0 L=s*s:=if_pos rfl
lemma Kh {s w j:ℕ} (hw:w≠0):fO s w j=j/s:=if_neg hw
lemma JX {s w j:ℕ} (hw:w≠0):fq s w j=j % s:=if_neg hw
lemma abD {s w:ℕ} {L:lB G} (hw:w≠0):cN s w L=L.r*s:=if_neg hw
lemma aaq (s:ℕ) (u:ℕ→G) (w:ℕ) (L:lB G) (j:ℕ)
    (h:¬ (w=0∧L.gC (j/s)<j % s)):
    dN s u (w+1) L j=⁅L.x (j/s),u (j % s)⁆:=by
 unfold dN
 have hn:¬ ((w+1=0∧¬ fO s (w+1) j<fq s (w+1) j)∨
     (w+1=1∧L.gC (fO s (w+1) j)<fq s (w+1) j)):=by
  rintro (h' | h')
  · exact absurd h'.1 (by omega)
  · rw[Kh (show w+1≠0 by omega),JX (show w+1≠0 by omega)]at h'
    obtain ⟨pL,jM⟩:=h'
    exact h ⟨by omega,jM⟩
 rw[if_neg hn,Kh (show w+1≠0 by omega),JX (show w+1≠0 by omega)]
lemma JK (s:ℕ) (u:ℕ→G) (L:lB G) {j:ℕ} (h:j % s<j/s):
    dN s u 0 L j=⁅L.x (j % s),u (j/s)⁆:=by
 unfold dN
 have hn:¬ (((0:ℕ)=0∧¬ fO s 0 j<fq s 0 j)∨
     ((0:ℕ)=1∧L.gC (fO s 0 j)<fq s 0 j)):=by
  rintro (h' | h')
  · exact h'.2 (by rw[sP,tK]; exact h)
  · exact Nat.zero_ne_one h'.1
 rw[if_neg hn,sP,tK]
lemma Oz {s A a b:ℕ} (ha:a<A) (hb:b<s):a*s+b<A*s:=
  lt_of_lt_of_le (VN hb _)
    (by rw[← Nat.succ_mul]; exact Za _ ha)
lemma AR {s a b:ℕ} (hb:b<s):(a*s+b)/s=a:=by
 rw[add_comm,Nat.add_mul_div_right _ _ (by omega:0<s),Nat.div_eq_of_lt hb,zero_add]
lemma A7 {s a b:ℕ} (hb:b<s):(a*s+b) % s=b:=by
 rw[add_comm,Nat.add_mul_mod_self_right,Xw hb]
lemma LD (s:ℕ) (u:ℕ→G) (hs:0<s) (w:ℕ) (L:lB G)
    (hr :w=0→s≤L.r) (K:Subgroup G) {i:ℕ}
    (hi:i< (jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).r):
    (jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).lK i<L.r∧
    (jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).gC i<s∧
    (w =0→(jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).lK i<
      (jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).gC i)∧
    (jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).x i=
      ⁅L.x ((jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).lK i),
        u ((jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).gC i)⁆:=by
 have gO:=vF (dN s u w L) K (cN s w L) (fO s w) (fq s w) hi
 have gJ:i< (c9 (dN s u w L) K (cN s w L)).card:=hi
 have hj:=pD (dN s u w L) K (cN s w L) _ (w6 _ gJ)
 have hx:=C4 (dN s u w L) K (cN s w L) (fO s w) (fq s w) gJ
 have d8:dN s u w L (d9 (c9 (dN s u w L) K (cN s w L)) i)≠1:=by
  intro h1
  apply gO
  rw[hx,h1]
  exact one_mem _
 have e1:(jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).lK i=
     fO s w (d9 (c9 (dN s u w L) K (cN s w L)) i):=rfl
 have e2:(jI (dN s u w L) K (cN s w L) (fO s w) (fq s w)).gC i=
     fq s w (d9 (c9 (dN s u w L) K (cN s w L)) i):=rfl
 rw[e1,e2,hx]
 generalize d9 (c9 (dN s u w L) K (cN s w L)) i=j at hj d8⊢
 have acq:¬ ((w=0∧¬ fO s w j<fq s w j)∨
     (w=1∧L.gC (fO s w j)<fq s w j)):=by
  intro hc
  apply d8
  unfold dN
  rw[if_pos hc]
 have hcv:¬ (w=0∧¬ fO s w j<fq s w j):= fun hc=>acq (Y7 hc)
 have ad0:dN s u w L j=⁅L.x (fO s w j),u (fq s w j)⁆:=by
  unfold dN
  rw[if_neg acq]
 refine ⟨?_,?_,?_,ad0⟩
 · by_cases hw:w=0
   · subst hw
     rw[sP]
     have h1:j % s<s:=W3 _ hs
     have h2:=hr rfl
     omega
   · rw[abD hw]at hj
     rw[Kh hw]
     exact (W2 hs).mpr hj
 · by_cases hw:w=0
   · subst hw
     rw[DQ]at hj
     rw[tK]
     exact (W2 hs).mpr hj
   · rw[JX hw]
     exact W3 _ hs
 · intro hw
   by_contra hc
   exact hcv ⟨hw,hc⟩
lemma MA (s:ℕ) (u:ℕ→G) (L:lB G) (K:Subgroup G) {i:ℕ}
    (hi:i< (jI (dN s u 1 L) K (cN s 1 L) (fO s 1) (fq s 1)).r):
    ¬ L.gC ((jI (dN s u 1 L) K (cN s 1 L) (fO s 1) (fq s 1)).lK i)<
      (jI (dN s u 1 L) K (cN s 1 L) (fO s 1) (fq s 1)).gC i:=by
 have gO:=vF (dN s u 1 L) K (cN s 1 L) (fO s 1) (fq s 1) hi
 have gJ:i< (c9 (dN s u 1 L) K (cN s 1 L)).card:=hi
 have hx:=C4 (dN s u 1 L) K (cN s 1 L) (fO s 1) (fq s 1) gJ
 intro f5
 apply gO
 rw[hx]
 have hc:((1:ℕ)=0∧¬ fO s 1 (d9 (c9 (dN s u 1 L) K (cN s 1 L)) i)<
     fq s 1 (d9 (c9 (dN s u 1 L) K (cN s 1 L)) i))∨
     ((1:ℕ)=1∧L.gC (fO s 1 (d9 (c9 (dN s u 1 L) K (cN s 1 L)) i))<
       fq s 1 (d9 (c9 (dN s u 1 L) K (cN s 1 L)) i)):=XQ ⟨rfl,f5⟩
 have h1:dN s u 1 L (d9 (c9 (dN s u 1 L) K (cN s 1 L)) i)=1:=if_pos hc
 rw[h1]
 exact one_mem _
lemma x9 (g y:G) (hg:g∈lcs G 1) (n:ℕ):
    ⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹∈lcs G 3:=by
 induction n with
 | zero=>simp
 | succ n ih=>
   have hc:⁅g,⁅g^n,y⁆⁆∈lcs G 3:=
     bC (show 3≤1+(1+1)+1 by omega)
       (d5 hg (a8 (pow_mem hg n) y))
   have e:⁅g^(n+1),y⁆*(⁅g,y⁆^(n+1))⁻¹=
       ⁅g,⁅g^n,y⁆⁆*(⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹):=by
    rw[VG g n,gX,Xr]
    group
   rw[e]
   exact Yq _ hc ih
lemma Lq (p:ℕ) (z:G) (hz:z∈dC p G 1) (g:G):⁅z,g⁆∈dC p G 2:=by
 haveI:(dC p G 2).Normal:=
   d6 (n:=2) (dD p 2) (oO p 1)
 have cO:dC p G 1≤zn (dC p G 2) g:=by
  show lcs G 2⊔ZA (ZF (fun y:lcs G 1=> (y:G)^p))≤_
  refine sup_le ?_ ?_
  · intro x hx
    exact mD.mpr (dD p 2 (bF g hx))
  · rw [ZE]
    rintro _ ⟨y,rfl⟩
    apply mD.mpr
    apply b8
    have h1:=x9 (y:G) g y.2 p
    have h2:⁅(y:G),g⁆^p∈dC p G 2:=
      qG p 2 _ (a8 y.2 g)
    have e:⁅(y:G)^p,g⁆=⁅(y:G)^p,g⁆*(⁅(y:G),g⁆^p)⁻¹*⁅(y:G),g⁆^p:=by
     group
    rw[e]
    exact Yq _ (dD p 2 h1) h2
 exact b8 (mD.mp (cO hz))
noncomputable def a7 (p s:ℕ) (u:ℕ→G) (L0:lB G):ℕ→lB G
  | 0=>L0
  | w +1=>jI (dN s u w (a7 p s u L0 w)) (dC p G (w+1)) (cN s w (a7 p s u L0 w))
      (fO s w) (fq s w)
variable (p s:ℕ) (u:ℕ→G) (L0:lB G)
lemma p8 (w:ℕ):
    a7 p s u L0 (w+1)=jI (dN s u w (a7 p s u L0 w)) (dC p G (w+1))
      (cN s w (a7 p s u L0 w)) (fO s w) (fq s w):=rfl
lemma v7:
    a7 p s u L0 1=jI (dN s u 0 L0) (dC p G 1) (cN s 0 L0) (fO s 0) (fq s 0):=rfl
lemma nT :∀ w i,(a7 p s u L0 w).x i∈lcs G w
  | 0,i=>by
    rw[lcs_zero]
    exact ZO _
  | w + 1,i=>by
    rw[p8]
    rcases MS (dN s u w (a7 p s u L0 w)) (dC p G (w+1))
        (cN s w (a7 p s u L0 w)) (fO s w) (fq s w) i with h | h
    · rw[h]
      unfold dN
      split_ifs
      · exact one_mem _
      · exact a8 (nT w _) _
    · rw[h]
      exact one_mem _
lemma GJ (w:ℕ) {i:ℕ} (hi:i< (a7 p s u L0 (w+1)).r):
    (a7 p s u L0 (w+1)).x i∉
      ZA ((a7 p s u L0 (w+1)).x '' ZH i)⊔dC p G (w+1):=by
 rw[p8]at hi⊢
 exact vF _ _ _ _ _ hi
lemma l9 (hs:0<s) (j_:s≤L0.r) (w:ℕ) {i:ℕ}
    (hi:i< (a7 p s u L0 (w+1)).r):
    (a7 p s u L0 (w+1)).lK i< (a7 p s u L0 w).r∧(a7 p s u L0 (w+1)).gC i<s∧
    (w=0→(a7 p s u L0 (w+1)).lK i< (a7 p s u L0 (w+1)).gC i)∧
    (a7 p s u L0 (w+1)).x i=⁅(a7 p s u L0 w).x ((a7 p s u L0 (w+1)).lK i),
      u ((a7 p s u L0 (w+1)).gC i)⁆:=by
 rw[p8]at hi⊢
 exact LD s u hs w (a7 p s u L0 w) (fun hw=>by subst hw; exact j_) _ hi
lemma zH (hs:0<s) (w:ℕ) {a b:ℕ} (ha:a< (a7 p s u L0 (w+1)).r)
    (hb:b<s) (hw:¬ (w=0∧(a7 p s u L0 (w+1)).gC a<b)):
    ⁅(a7 p s u L0 (w+1)).x a,u b⁆∈ZA ((a7 p s u L0 (w+1+1)).x ''
      ZH (a7 p s u L0 (w+1+1)).r)⊔dC p G (w+1+1):=by
 have hj:a*s+b<cN s (w+1) (a7 p s u L0 (w+1)):=by
  rw[abD (show w+1≠0 by omega)]
  exact Oz ha hb
 have hv:dN s u (w+1) (a7 p s u L0 (w+1)) (a*s+b)=
     ⁅(a7 p s u L0 (w+1)).x a,u b⁆:=by
  have EU:¬ (w=0∧(a7 p s u L0 (w+1)).gC ((a*s+b)/s)< (a*s+b) % s):=by
   rw[AR hb,A7 hb]
   exact hw
  rw[aaq s u w _ _ EU,AR hb,A7 hb]
 rw[← hv,p8 p s u L0 (w+1)]
 exact LX _ _ _ _ _ hj
lemma Qd {i:ℕ} (hi:i< (a7 p s u L0 2).r):
    (a7 p s u L0 2).gC i≤(a7 p s u L0 1).gC ((a7 p s u L0 2).lK i):=
  not_lt.mp (MA s u (a7 p s u L0 1) (dC p G 2) (i:=i) hi)
lemma mK (hs:0<s) (kH:∀ a<s,L0.x a=u a) {k:ℕ} (hk:k≤ s)
    {a b:ℕ} (hab:a<b) (hb:b<k):
    ⁅u a,u b⁆∈ZA ((a7 p s u L0 1).x ''
      {i | i< (a7 p s u L0 1).r∧(a7 p s u L0 1).gC i<k})⊔dC p G 1:=by
  have KZ:b<s:=lt_of_lt_of_le hb hk
  have Ox:a<s:=Uj hab KZ
  have hJ:k*s≤ cN s 0 L0:=by
   rw[DQ]
   exact Za s hk
  have hj:b*s+a<k*s:= Oz hb Ox
  have hv:dN s u 0 L0 (b*s+a)=⁅u a,u b⁆:=by
   rw [JK s u L0 (j:=b*s+a) (by rw[A7 Ox,AR Ox]; exact hab),
     A7 Ox,
     AR Ox,kH a Ox]
  rw[← hv,v7]
  refine (sup_le_sup_right (ZS ?_) _)
    (Dw (dN s u 0 L0) (dC p G 1) (cN s 0 L0) (fO s 0) (fq s 0) hJ hj)
  rintro _ ⟨i,⟨hi,hik⟩,rfl⟩
  refine ⟨i,⟨hi,?_⟩,rfl⟩
  show fq s 0 (d9 _ i)<k
  rw[tK]
  exact (W2 hs).mpr hik
lemma LW (hs:0<s) (j_:s≤L0.r) (kH:∀ a<s,L0.x a=u a):
    ∀ b,b<s→∀ a,a< (a7 p s u L0 1).r→⁅(a7 p s u L0 1).x a,u b⁆∈
      ZA ((a7 p s u L0 2).x '' ZH (a7 p s u L0 2).r)⊔dC p G 2:=by
 intro b
 induction b using V9 with
 | _ b ih =>
   intro hb a ha
   have hN:(ZA ((a7 p s u L0 2).x '' ZH (a7 p s u L0 2).r)⊔
       dC p G 2).Normal:=
     jU p 2 _ (by rintro _ ⟨i, -,rfl⟩; exact nT p s u L0 2 i)
   by_cases hab:(a7 p s u L0 1).gC a<b
   · have hg:=l9 p s u L0 hs j_ 0 ha
     have hk:(a7 p s u L0 1).gC a<s:=hg.2.1
     have hfk:(a7 p s u L0 1).lK a< (a7 p s u L0 1).gC a:=hg.2.2.1 rfl
     have hxa:(a7 p s u L0 1).x a=
         ⁅L0.x ((a7 p s u L0 1).lK a),u ((a7 p s u L0 1).gC a)⁆:=hg.2.2.2
     rw[kH ((a7 p s u L0 1).lK a) (by omega)]at hxa
     rw[hxa]
     have hKn:(ZA ((a7 p s u L0 1).x '' {i | i< (a7 p s u L0 1).r∧
         (a7 p s u L0 1).gC i<b+1})⊔dC p G 1).Normal:=
       jU p 1 _ (by rintro _ ⟨i, -,rfl⟩; exact nT p s u L0 1 i)
     have hKM:∀ c,c<b→∀ z∈ZA ((a7 p s u L0 1).x '' {i |
         i< (a7 p s u L0 1).r∧(a7 p s u L0 1).gC i<b+1})⊔dC p G 1,
         ⁅z,u c⁆∈ZA ((a7 p s u L0 2).x '' ZH (a7 p s u L0 2).r)⊔
           dC p G 2:=by
       intro c hc
       haveI:=hN
       refine kF ?_ ?_
       · rintro _ ⟨i,⟨hi, -⟩,rfl⟩
         exact ih c hc (by omega) i hi
       · intro z hz
         exact ZL (Lq p z hz (u c))
     haveI:=hN
     haveI:=hKn
     exact sW _ _ _
       (mK p s u L0 hs kH (show b+1≤ s by omega) hab (XZ b))
       (hKM _ (by omega))
       (b8 (mK p s u L0 hs kH (show b+1≤ s by omega)
         (show (a7 p s u L0 1).lK a<b by omega) (XZ b)))
       (hKM _ hab)
   · exact zH p s u L0 hs 0 ha hb (fun h=>hab h.2)
lemma MY [Finite G] {m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) (hs:0<s)
    (kH:∀ a<s,L0.x a=u a)
    (zv:ZA (L0.x '' ZH L0.r)⊔lcs G 1=⊤)
    (dG:lcs G 1≤ZA (vP s u 1)⊔lcs G 2) (j_:s≤L0.r):
    ∀ w,lcs G (w+1)≤ZA ((a7 p s u L0 (w+1)).x ''
      ZH (a7 p s u L0 (w+1)).r)⊔lcs G (w+2):=by
 have hT:=aaT s u (L0.x '' ZH L0.r) zv dG
 have jp:∀ w,(a7 p s u L0 (w+1)).x '' ZH (a7 p s u L0 (w+1)).r⊆
     (lcs G (w+1):Set G):=by
  rintro w _ ⟨i, -,rfl⟩
  exact nT p s u L0 (w+1) i
 intro w
 induction w with
 | zero=>
   apply A8 hp hG 0 _ (jp 0)
   refine (hT 1 YD).trans (sup_le ?_ ((dD p 1).trans Z5))
   rw[ZE]
   rintro _ ⟨ab,hab,rfl⟩
   have h1:=mK p s u L0 hs kH YD hab.1 hab.2
   exact (sup_le_sup_right (ZS (Uw (fun i hi=>hi.1))) _) h1
 | succ w ih =>
   apply A8 hp hG (w+1) _ (jp (w+1))
   have hN:=jU p (w+1+1)
     ((a7 p s u L0 (w+1+1)).x '' ZH (a7 p s u L0 (w+1+1)).r) (jp (w+1))
   refine (hT (w+1+1) (by omega)).trans
     (sup_le ?_ ((dD p (w+1+1)).trans Z5))
   rw[ZE]
   rintro _ ⟨y,hy,b,hb,rfl⟩
   have hy1:=ih ((ZE _).mpr (FU s u w) hy)
   have cO : ZA ((a7 p s u L0 (w+1)).x '' ZH (a7 p s u L0 (w+1)).r)⊔
       lcs G (w+2)≤zn (ZA ((a7 p s u L0 (w+1+1)).x ''
         ZH (a7 p s u L0 (w+1+1)).r)⊔dC p G (w+1+1)) (u b):=by
    refine sup_le ?_ ?_
    · rw [ZE]
      rintro _ ⟨a,ha,rfl⟩
      have qU:⁅(a7 p s u L0 (w+1)).x a,u b⁆∈ZA
          ((a7 p s u L0 (w+1+1)).x '' ZH (a7 p s u L0 (w+1+1)).r)⊔
            dC p G (w+1+1):=by
       rcases Yj w with hw | hw
       · subst hw
         exact LW p s u L0 hs j_ kH b hb a ha
       · exact zH p s u L0 hs w ha hb (fun h=>by omega)
      exact mD.mpr (b8 qU)
    · intro g hg
      exact mD.mpr (ZL
        ((dD p (w+1+1)) (bF (u b) hg)))
   exact b8 (mD.mp (cO hy1))
end Layers2
section Layer0
noncomputable def GA (G:Type u) [Group G] [Finite G] (j:ℕ):G:=
  if h:j<ZB G then (Xz G).symm ⟨j,h⟩ else 1
variable {G:Type u} [Group G] [Finite G]
lemma NW (g:G):∃ j<ZB G,GA G j=g:=by
 refine ⟨(Xz G g).val,(Xz G g).isLt,?_⟩
 unfold GA
 rw[dif_pos (Xz G g).isLt]
 simp
noncomputable abbrev vk (p s:ℕ) (u:ℕ→G):lB G:=
  jI (GA G) (ZA (u '' ZH s)⊔cE p G) (ZB G) id id
noncomputable def gd (p s:ℕ) (u:ℕ→G):lB G where
  r :=s+(vk p s u).r
  x:= fun i=>if i<s then u i else (vk p s u).x (i - s)
  lK:=id
  gC:=id
variable (p s:ℕ) (u:ℕ→G)
lemma n8 {i:ℕ} (h:i<s):(gd p s u).x i=u i:=if_pos h
lemma Dz {i:ℕ} (h:¬ i<s):(gd p s u).x i=(vk p s u).x (i - s):=if_neg h
lemma Qz (hu:∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G) {i:ℕ}
    (hi:i< (gd p s u).r):
    (gd p s u).x i∉ZA ((gd p s u).x '' ZH i)⊔cE p G:=by
 by_cases K6:i<s
 · rw[n8 p s u K6]
   intro cI
   apply hu i K6
   refine (sup_le_sup_right (ZS ?_) _) cI
   rintro _ ⟨i',gJ,rfl⟩
   have Np:i'< i:=gJ
   exact ⟨i',gJ,(n8 p s u (Uj Np K6)).symm⟩
 · rw [Dz p s u K6]
   intro cI
   have gJ:i - s< (vk p s u).r :=by
    have h1:i<s+(vk p s u).r :=hi
    omega
   apply vF _ _ _ _ _ gJ
   refine (sup_le ?_ ?_:_≤ZA ((vk p s u).x '' ZH (i - s))⊔
     (ZA (u '' ZH s)⊔cE p G)) cI
   · rw [ZE]
     rintro _ ⟨i',Np,rfl⟩
     have Qu:i'< i:=Np
     by_cases h':i'<s
     · rw [n8 p s u h']
       exact ZL
         (ZK (ZD ⟨i',h',rfl⟩))
     · rw [Dz p s u h']
       exact ZK
         (ZD ⟨i' - s,show i' - s< i - s by omega,rfl⟩)
   · exact Z5.trans Z5
lemma aaO (g:G):
    g∈ZA ((gd p s u).x '' ZH (gd p s u).r)⊔cE p G:=by
 obtain ⟨j,hj,rfl⟩:=NW g
 have h1:=Dw (GA G) (ZA (u '' ZH s)⊔cE p G) (ZB G)
   id id YD hj
 refine (sup_le ?_ ?_:_≤ZA ((gd p s u).x '' ZH (gd p s u).r)⊔
   cE p G) h1
 · rw [ZE]
   rintro _ ⟨i,⟨hi, -⟩,rfl⟩
   have gJ:i< (vk p s u).r :=hi
   refine ZK (ZD ⟨s+i,?_,?_⟩)
   · show s+i<s+(vk p s u).r
     omega
   · rw[Dz p s u (by omega),show s+i - s=i by omega]
 · refine sup_le ?_ Z5
   refine (ZS ?_).trans WM
   rintro _ ⟨k,hk,rfl⟩
   have lQ:k<s:=hk
   exact ⟨k,show k<s+(vk p s u).r by omega,n8 p s u lQ⟩
end Layer0
section Flat
variable {G:Type u} [Group G]
def aD (ℓ:ℕ→ℕ):ℕ→ℕ
  | 0=> 0
  | w+1=>aD ℓ w+ℓ w
lemma dM (ℓ:ℕ→ℕ) (w:ℕ):aD ℓ (w+1)=aD ℓ w+ℓ w:=rfl
lemma g5 (ℓ:ℕ→ℕ) {a b:ℕ} (h:a≤b):aD ℓ a≤aD ℓ b:=by
 induction b with
 | zero=>
   obtain rfl:a=0:=by omega
   exact YD
 | succ b ih=>
   rcases XU a (b+1) with h' | h'
   · rw[dM]
     exact WS (ih (by omega)) (W5 _ _)
   · obtain rfl:a=b+1:=by omega
     exact YD
def eJ (ℓ:ℕ→ℕ) (L t:ℕ):ℕ:=SO (fun w=>aD ℓ w≤t) L
lemma Cz {ℓ:ℕ→ℕ} {L t w:ℕ} (hw:w≤L) (h1:aD ℓ w≤t) (h2:t<aD ℓ (w+1)):
    eJ ℓ L t=w:=by
 unfold eJ
 have cO:=Nat.le_findGreatest (P:= fun w=>aD ℓ w≤t) hw h1
 have nF:aD ℓ (SO (fun w=>aD ℓ w≤t) L)≤t:=
   PI (P:= fun w=>aD ℓ w≤t) hw h1
 by_contra d8
 have hgt:w+1≤SO (fun w=>aD ℓ w≤t) L:=by omega
 have:=g5 ℓ hgt
 omega
lemma Bk {ℓ:ℕ→ℕ} {L t:ℕ} (ht:t<aD ℓ (L+1)):
    aD ℓ (eJ ℓ L t)≤t∧t<aD ℓ (eJ ℓ L t+1)∧eJ ℓ L t≤L:=by
 have h1:aD ℓ (eJ ℓ L t)≤t:=
   PI (P:= fun w=>aD ℓ w≤t) (Zv L) (Zv t)
 have h3:eJ ℓ L t≤L:=Nat.findGreatest_le L
 refine ⟨h1,?_,h3⟩
 by_cases hL:eJ ℓ L t=L
 · rw[hL]
   exact ht
 · have h4:=Nat.findGreatest_is_greatest (P:= fun w=>aD ℓ w≤t)
     (n:=L) (k:=eJ ℓ L t+1) (by unfold eJ; omega) (by omega)
   exact not_le.mp h4
lemma abB {ℓ:ℕ→ℕ} {L t t':ℕ} (iQ:t'<aD ℓ (L+1)) (h:t≤t'):
    eJ ℓ L t≤eJ ℓ L t':=by
 have ht:t<aD ℓ (L+1):=VT h iQ
 obtain ⟨h1, -, -⟩:=Bk ht
 obtain ⟨-,jM, -⟩:=Bk iQ
 by_contra hc
 have:=g5 ℓ (show eJ ℓ L t'+1≤eJ ℓ L t by omega)
 omega
def Kw (n k:ℕ) (dflt:Fin n):Fin n:=if h:k<n then ⟨k,h⟩ else dflt
lemma M9 {n k:ℕ} (dflt:Fin n) (h:k<n):(Kw n k dflt).val=k:=by
 unfold Kw
 rw[dif_pos h]
def bR (L:ℕ) (r :ℕ→ℕ) (w:ℕ):ℕ:=if w≤L then r w else 0
lemma k4 {L:ℕ} {r :ℕ→ℕ} {w:ℕ} (h:w≤L):bR L r w=r w:=if_pos h
lemma QY {L:ℕ} {r :ℕ→ℕ} {w:ℕ} (h:¬ w≤L):bR L r w=0:=if_neg h
lemma po (L:ℕ) (r :ℕ→ℕ):aD (bR L r) 1=r 0:=by
 show aD (bR L r) 0+bR L r 0=r 0
 rw[k4 (Zv L)]
 show 0+r 0=r 0
 omega
lemma pZ {L:ℕ} {r :ℕ→ℕ} {w i:ℕ} (hw:w≤L) (hi:i< r w):
    aD (bR L r) w+i<aD (bR L r) (L+1):=by
 have h1:aD (bR L r) (w+1)=aD (bR L r) w+r w:=by
  rw[dM,k4 hw]
 have h2:=g5 (bR L r) (show w+1≤L+1 by omega)
 omega
lemma vH {L:ℕ} {r :ℕ→ℕ} {w i:ℕ} (hw:w≤L) (hi:i< r w):
    eJ (bR L r) L (aD (bR L r) w+i)=w:=by
 apply Cz hw (W5 _ _)
 rw[dM,k4 hw]
 omega
lemma DH {L:ℕ} {r :ℕ→ℕ} {t:ℕ} (ht:t<aD (bR L r) (L+1)):
    eJ (bR L r) L t≤L∧aD (bR L r) (eJ (bR L r) L t)≤t∧
      t - aD (bR L r) (eJ (bR L r) L t)< r (eJ (bR L r) L t):=by
 obtain ⟨h1,h2,h3⟩:=Bk ht
 refine ⟨h3,h1,?_⟩
 rw[dM,k4 h3]at h2
 omega
def kJ (L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ) (t:Fin (aD (bR L r) (L+1))):
    Fin (aD (bR L r) (L+1))×Fin (aD (bR L r) (L+1)):=
  match eJ (bR L r) L t.val with
  | 0=> (t,t)
  | w +1=> (Kw _ (aD (bR L r) w+pa (w+1) (t.val - aD (bR L r) (w+1))) t,
      Kw _ (co (w+1) (t.val - aD (bR L r) (w+1))) t)
lemma M5 (L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ) (t:Fin (aD (bR L r) (L+1)))
    {w:ℕ} (h:eJ (bR L r) L t.val=w+1):
    kJ L r pa co t=(Kw _ (aD (bR L r) w+pa (w+1) (t.val - aD (bR L r) (w+1))) t,
      Kw _ (co (w+1) (t.val - aD (bR L r) (w+1))) t):=by
 unfold kJ
 rw[h]
def fX (L:ℕ) (r :ℕ→ℕ) (xs:ℕ→ℕ→G) (t:Fin (aD (bR L r) (L+1))):G:=
  xs (eJ (bR L r) L t.val) (t.val - aD (bR L r) (eJ (bR L r) L t.val))
lemma Aw (L:ℕ) (r :ℕ→ℕ) (xs:ℕ→ℕ→G) (t:Fin (aD (bR L r) (L+1))) {w:ℕ}
    (h:eJ (bR L r) L t.val=w):fX L r xs t=xs w (t.val - aD (bR L r) w):=by
 unfold fX
 rw[h]
lemma Cc {L:ℕ} {r :ℕ→ℕ} (xs:ℕ→ℕ→G) {w i:ℕ} (hw:w≤L) (hi:i< r w):
    fX L r xs ⟨aD (bR L r) w+i,pZ hw hi⟩=xs w i:=by
 rw[Aw L r xs ⟨aD (bR L r) w+i,pZ hw hi⟩ (vH hw hi)]
 show xs w (aD (bR L r) w+i - aD (bR L r) w)=xs w i
 rw[Yb]
def cZ (s L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ):aO where
  n:=aD (bR L r) (L+1)
  s:=s
  lv:= fun t=>eJ (bR L r) L t.val
  df:=kJ L r pa co
  a:= fun _=> 0
  b:= fun _ _=> 0
  c:= fun _ _ _=> 0
variable {s L:ℕ} {r :ℕ→ℕ} {xs:ℕ→ℕ→G} {pa co:ℕ→ℕ→ℕ}
lemma Jt (H0:s≤ r 0):s≤aD (bR L r) (L+1):=by
 have h1:=po L r
 have h2:=g5 (bR L r) (show 1≤L+1 by omega)
 omega
lemma pG (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (t:Fin (aD (bR L r) (L+1))) {w:ℕ} (hw:eJ (bR L r) L t.val=w+1):
    w+1≤L∧t.val - aD (bR L r) (w+1)< r (w+1)∧
    ((kJ L r pa co t).1).val=
      aD (bR L r) w+pa (w+1) (t.val - aD (bR L r) (w+1))∧
    ((kJ L r pa co t).2).val= co (w+1) (t.val - aD (bR L r) (w+1)):=by
 obtain ⟨hL, -,hi⟩:=DH (r :=r) t.isLt
 rw[hw]at hL hi
 have hp:=jq w _ hi
 have hc:=jt w _ hi
 refine ⟨hL,hi,?_,?_⟩
 · rw[M5 L r pa co t hw]
   exact M9 t (pZ (show w≤L by omega) hp)
 · rw[M5 L r pa co t hw]
   exact M9 t (lt_of_lt_of_le hc (Jt (L:=L) H0))
lemma vN (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (H1:∀ i,i< r 1→pa 1 i<co 1 i):(cZ s L r pa co).qN:=by
 refine ⟨?_,Jt H0,?_,?_,?_,?_⟩
 · intro t v htv
   exact abB v.isLt (TZ.mp htv)
 · intro t ht
   have iQ:t.val<aD (bR L r) (0+1):=by
    have h1:aD (bR L r) (0+1)=r 0:=po L r
    have h2:t.val<s:=ht
    omega
   exact Cz (Zv L) (Zv _) iQ
 · intro t ht
   obtain ⟨w,hw⟩:∃ w,eJ (bR L r) L t.val=w+1:=
     ⟨eJ (bR L r) L t.val - 1,by have:1≤eJ (bR L r) L t.val:=ht; omega⟩
   obtain ⟨hL,hi,h1, -⟩:=pG (pa:=pa) (co:= co) H0 jq jt t hw
   show eJ (bR L r) L ((kJ L r pa co t).1).val+1=eJ (bR L r) L t.val
   rw[h1,hw,vH (show w≤L by omega) (jq w _ hi)]
 · intro t ht
   obtain ⟨w,hw⟩:∃ w,eJ (bR L r) L t.val=w+1:=
     ⟨eJ (bR L r) L t.val - 1,by have:1≤eJ (bR L r) L t.val:=ht; omega⟩
   obtain ⟨-,hi, -,h2⟩:=pG (pa:=pa) (co:= co) H0 jq jt t hw
   show ((kJ L r pa co t).2).val<s
   rw[h2]
   exact jt w _ hi
 · intro t ht
   have hw:eJ (bR L r) L t.val=0+1:=ht
   obtain ⟨-,hi,h1,h2⟩:=pG (pa:=pa) (co:= co) H0 jq jt t hw
   show (kJ L r pa co t).1< (kJ L r pa co t).2
   rw[XO,h1,h2]
   have h3:pa 1 (t.val - aD (bR L r) (0+1))<co 1 (t.val - aD (bR L r) (0+1)):=
     H1 _ hi
   show 0+pa 1 (t.val - aD (bR L r) (0+1))<co 1 (t.val - aD (bR L r) (0+1))
   omega
lemma QC (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (t:Fin (aD (bR L r) (L+1))) (ht:1≤eJ (bR L r) L t.val):
    fX L r xs t=⁅fX L r xs (kJ L r pa co t).1,fX L r xs (kJ L r pa co t).2⁆:=by
 obtain ⟨w,hw⟩:∃ w,eJ (bR L r) L t.val=w+1:=⟨eJ (bR L r) L t.val - 1,by omega⟩
 obtain ⟨hL,hi,h1,h2⟩:=pG (pa:=pa) (co:= co) H0 jq jt t hw
 have hp:=jq w _ hi
 have hc:=jt w _ hi
 have e1:eJ (bR L r) L ((kJ L r pa co t).1).val=w:=by
  rw[h1]
  exact vH (show w≤L by omega) hp
 have e2:eJ (bR L r) L ((kJ L r pa co t).2).val=0:=by
  rw[h2]
  have h3:aD (bR L r) (0+1)=r 0:=po L r
  exact Cz (Zv L) (Zv _) (by omega)
 have e0:aD (bR L r) 0=0:=rfl
 rw [Aw L r xs t hw,Aw L r xs _ e1,Aw L r xs _ e2,Hx w _ hi,h1,h2,
   Yb,e0,UK]
lemma M6 (h0:ZA (xs 0 '' ZH (r 0))=⊤):
    ZA (ZF (fX L r xs))=⊤:=by
 rw[Yo, ← h0,ZE]
 rintro _ ⟨i,hi,rfl⟩
 exact ZD ⟨⟨_,pZ (Zv L) hi⟩,Cc xs (Zv L) hi⟩
lemma Az
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZH (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥) (w:ℕ):
    lcs G (w+1)≤ZA (iO (cZ s L r pa co) (fX L r xs) (w+1))⊔
      lcs G (w+2):=by
 by_cases hw:w+1≤L
 · refine (HU w hw).trans (sup_le_sup_right (ZS ?_) _)
   rintro _ ⟨i,hi,rfl⟩
   exact ⟨⟨_,pZ hw hi⟩,vH hw hi,Cc xs hw hi⟩
 · exact ((bC (D:=G) (show L+1≤w+1 by omega)).trans (WT HL)).trans
     bot_le
lemma aaD (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (h0:ZA (xs 0 '' ZH (r 0))=⊤)
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZH (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥):
    ∀ w,1≤w→lcs G w≤ZA (fX L r xs '' {v | w≤(cZ s L r pa co).lv v}):=by
  have hd:=vN (L:=L) H0 jq jt H1
  have lH:∀ t,1≤(cZ s L r pa co).lv t→ fX L r xs t=
      ⁅fX L r xs ((cZ s L r pa co).df t).1,fX L r xs ((cZ s L r pa co).df t).2⁆:=
    fun t ht=>QC H0 jq jt Hx t ht
  have jV:= ow (cZ s L r pa co) hd (fX L r xs) lH
  refine BV (cZ s L r pa co) hd (fX L r xs) (M6 h0) ⟨L+1,HL⟩ lH ?_ ?_ ?_
  · intro i k _ _
    exact Az HU HL 0 (b7 _ _)
  · intro t k ht _
    have h1:=a8 (jV t) (fX L r xs k)
    rw[ht]at h1
    exact Az HU HL 1 h1
  · intro t k _ _
    exact Az HU HL ((cZ s L r pa co).lv t) (a8 (jV t) _)
lemma aab (p:ℕ)
    (AN:∀ w i,i< r w→xs w i∉ZA (xs w '' ZH i)⊔dC p G w)
    (t:Fin (aD (bR L r) (L+1))):
    fX L r xs t∉ZA (fX L r xs '' {v | (cZ s L r pa co).lv v=
      (cZ s L r pa co).lv t∧v<t})⊔dC p G ((cZ s L r pa co).lv t):=by
  obtain ⟨-, -,hi⟩:=DH (r :=r) t.isLt
  intro cI
  apply AN _ _ hi
  rw[← Aw L r xs t rfl]
  refine (sup_le_sup_right (ZS ?_) _) cI
  rintro _ ⟨v,⟨hv1,hv2⟩,rfl⟩
  have acC:eJ (bR L r) L v.val=eJ (bR L r) L t.val:=hv1
  obtain ⟨-,hv3, -⟩:=DH (r :=r) v.isLt
  rw[acC]at hv3
  have aeX:v.val<t.val:=hv2
  refine ⟨v.val - aD (bR L r) (eJ (bR L r) L t.val),?_,(Aw L r xs v acC).symm⟩
  show v.val - aD (bR L r) (eJ (bR L r) L t.val)<
    t.val - aD (bR L r) (eJ (bR L r) L t.val)
  omega
lemma CS (u:ℕ→G) (H0:s≤ r 0) (NA:∀ i<s,xs 0 i=u i)
    (t:Fin (aD (bR L r) (L+1))) (ht:t.val<s):fX L r xs t=u t.val:=by
 have h1:aD (bR L r) (0+1)=r 0:=po L r
 have h0:eJ (bR L r) L t.val=0:=
   Cz (Zv L) (Zv _) (by omega)
 rw[Aw L r xs t h0]
 show xs 0 (t.val - 0)=u t.val
 rw[UK]
 exact NA _ ht
lemma wB (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (t:Fin (aD (bR L r) (L+1))) (ht:eJ (bR L r) L t.val=1):
    1 ≤L∧r 0≤t.val∧t.val - r 0< r 1∧
      ((kJ L r pa co t).1).val=pa 1 (t.val - r 0)∧
      ((kJ L r pa co t).2).val= co 1 (t.val - r 0):=by
 have hw:eJ (bR L r) L t.val=0+1:=ht
 obtain ⟨hL,hi,h1,h2⟩:=pG (pa:=pa) (co:= co) H0 jq jt t hw
 obtain ⟨-,h3, -⟩:=DH (r :=r) t.isLt
 rw[hw]at h3
 have e:aD (bR L r) (0+1)=r 0:=po L r
 rw[e]at hi h1 h2 h3
 refine ⟨hL,h3,hi,?_,h2⟩
 rw[h1]
 show 0+pa 1 (t.val - r 0)=pa 1 (t.val - r 0)
 omega
lemma aax (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (AY:∀ i i',i≤ i'→i'< r 1→ co 1 i≤ co 1 i')
    (t t':Fin (aD (bR L r) (L+1))) (ht:eJ (bR L r) L t.val=1)
    (iQ:eJ (bR L r) L t'.val=1) (KW:t≤t'):
    (kJ L r pa co t).2≤(kJ L r pa co t').2:=by
 obtain ⟨-,h3, -, -,h2⟩:=wB (pa:=pa) (co:= co) H0 jq jt t ht
 obtain ⟨-,h3',gJ, -,jM⟩:=wB (pa:=pa) (co:= co) H0 jq jt t' iQ
 rw[TZ,h2,jM]
 have h4:t.val≤t'.val:=TZ.mp KW
 exact AY _ _ (by omega) gJ
lemma aaU (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (F8:∀ i i',i< r 1→i'< r 1→pa 1 i=pa 1 i'→ co 1 i= co 1 i'→i=i')
    (t t':Fin (aD (bR L r) (L+1))) (ht:eJ (bR L r) L t.val=1)
    (iQ:eJ (bR L r) L t'.val=1) (h1:(kJ L r pa co t).1=(kJ L r pa co t').1)
    (h2:(kJ L r pa co t).2=(kJ L r pa co t').2):t=t':=by
 obtain ⟨-,h3,hi,e1,e2⟩:=wB (pa:=pa) (co:= co) H0 jq jt t ht
 obtain ⟨-,h3',gJ,e1',e2'⟩:=wB (pa:=pa) (co:= co) H0 jq jt t' iQ
 have hp:pa 1 (t.val - r 0)=pa 1 (t'.val - r 0):=by rw[← e1, ← e1',h1]
 have hc:co 1 (t.val - r 0)= co 1 (t'.val - r 0):=by rw[← e2, ← e2',h2]
 have h4:=F8 _ _ hi gJ hp hc
 exact YL (by omega)
lemma ab7 (p:ℕ) (u:ℕ→G) (H0:s≤ r 0)
    (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s) (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (NA:∀ i<s,xs 0 i=u i) (hL1:1≤L)
    (Mh:∀ k≤ s,∀ a b,a<b→ b<k→
      ⁅u a,u b⁆∈ZA (xs 1 '' {i | i< r 1∧co 1 i<k})⊔pN p G)
    {k:ℕ} (hk:k≤ s):
    dO (pN p G) u k=ZA (fX L r xs '' {t | (cZ s L r pa co).lv t=1∧
      ((cZ s L r pa co).df t).2.val<k})⊔pN p G:=by
  apply le_antisymm
  · refine qA (pN p G) Z5 ?_
    intro a b hab hb
    refine (sup_le_sup_right (ZS ?_) _) (Mh k hk a b hab hb)
    rintro _ ⟨i,⟨hi,hik⟩,rfl⟩
    have rV:=pZ (L:=L) hL1 hi
    have jV:=vH (L:=L) hL1 hi
    refine ⟨⟨_,rV⟩,⟨jV,?_⟩,Cc xs hL1 hi⟩
    obtain ⟨-, -, -, -,h2⟩:=wB (pa:=pa) (co:= co) H0 jq jt ⟨_,rV⟩ jV
    show ((kJ L r pa co ⟨_,rV⟩).2).val<k
    rw[h2]
    show co 1 (aD (bR L r) 1+i - r 0)<k
    have e:aD (bR L r) 1+i - r 0=i:=by
     rw[po]
     omega
    rw[e]
    exact hik
  · refine sup_le ?_ (kD _ u k)
    rw[ZE]
    rintro _ ⟨t,⟨ht1,Ml⟩,rfl⟩
    have aeQ:eJ (bR L r) L t.val=1:=ht1
    have hd:=vN (L:=L) H0 jq jt H1
    have f5:((kJ L r pa co t).1).val< ((kJ L r pa co t).2).val:=
      XO.mp (hd.oR t ht1)
    have Lh:((kJ L r pa co t).2).val<s:=
      hd.kR t (show 1≤eJ (bR L r) L t.val by omega)
    rw [QC H0 jq jt Hx t (by omega),CS u H0 NA _ (Uj f5 Lh),
      CS u H0 NA _ Lh]
    exact gI _ u f5 Ml
lemma NG (p:ℕ) (u:ℕ→G) (fo:cD (pN p G) u s)
    (hWk:∀ k≤ s,dO (pN p G) u k=ZA (fX L r xs '' {t |
      (cZ s L r pa co).lv t=1∧((cZ s L r pa co).df t).2.val<k})⊔pN p G)
    {k:ℕ} (Bw:1≤k) (BG:k<s):
    ∃ t,(cZ s L r pa co).lv t=1∧((cZ s L r pa co).df t).2.val=k:=by
  by_contra hno
  push_neg at hno
  have abx:{t:Fin (aD (bR L r) (L+1)) | (cZ s L r pa co).lv t=1∧
      ((cZ s L r pa co).df t).2.val<k}={t | (cZ s L r pa co).lv t=1∧
      ((cZ s L r pa co).df t).2.val<k+1}:=by
    ext t
    simp only[UA]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,by omega⟩
    · rintro ⟨h1,h2⟩
      have h3:=hno t h1
      exact ⟨h1,by omega⟩
  apply fo (k+1) (by omega) (by omega)
  rw[XI,hWk k (by omega),hWk (k+1) (by omega),abx]
  rfl
end Flat
section NormalForm
variable {G:Type u} [Group G]
lemma Md [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (d:aO) (hd:d.qN) (X:Fin d.n→G)
    (dV:ZA (ZF X)=⊤) (jV:∀ t,X t∈lcs G (d.lv t))
    (f6:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^e8 p d X t)∧g=gN X e:=by
  intro g
  have hnf:=JZ d X hp hG hd jV f6 0 d.n
  have cI:g∈ZA (X '' jw d 0 d.n):=by
   have cO:ZA (ZF X)≤ZA (X '' jw d 0 d.n):=by
    apply ZS
    rintro _ ⟨v,rfl⟩
    refine ⟨v,?_,rfl⟩
    rw[dY]
    rcases Yj (d.lv v) with h | h
    · exact XQ ⟨h.symm,v.isLt⟩
    · exact Y7 h
   rw[dV]at cO
   exact cO (ZO g)
  obtain ⟨e, -,he,rfl⟩:=hnf g cI
  exact ⟨e,he,rfl⟩
lemma QW [Finite G] {p:ℕ} (d:aO) (X:Fin d.n→G)
    (dS:ZB G=p^(∑ t,d.a t))
    (qX:∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^d.a t)∧g=gN X e)
    (e e':Fin d.n→ℕ) (he:∀ t,e t<p^d.a t) (he':∀ t,e' t<p^d.a t)
    (h:gN X e=gN X e'):e=e':=by
 have j6:Zn
     (fun f:(t:Fin d.n)→Fin (p^d.a t)=>gN X (fun t=> (f t:ℕ))):=by
   intro g
   obtain ⟨e0,he0,rfl⟩:=qX g
   exact ⟨fun t=> ⟨e0 t,he0 t⟩,rfl⟩
 have hc:ZB ((t:Fin d.n)→Fin (p^d.a t))=ZB G:=by
  rw[Pa,dS]
  simp only[Xk]
  exact XB _ _ _
 have eW:=(j6.bijective_of_nat_card_le (WT hc)).1
 have h2:= @eW (fun t=> ⟨e t,he t⟩) (fun t=> ⟨e' t,he' t⟩) h
 funext t
 exact congrArg (fun f:(t:Fin d.n)→Fin (p^d.a t)=> ((f t:Fin _):ℕ)) h2
end NormalForm
section SimsCore
variable {G:Type u} [Group G]
noncomputable def bD (G:Type u) [Group G]:ℕ:=
  sInf {k | ∃ u:Fin k→G,
    lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔lcs G 2}
def JM {k:ℕ} (x:Fin k→G) (i:ℕ):G:=if h:i<k then x ⟨i,h⟩ else 1
lemma Qe {k:ℕ} (x:Fin k→G) {i:ℕ} (h:i<k):JM x i=x ⟨i,h⟩:=dif_pos h
lemma IL {k:ℕ} (x:Fin k→G):ZF x =JM x '' ZH k:=by
 ext y
 constructor
 · rintro ⟨i,rfl⟩
   exact ⟨i.val,i.isLt,Qe x i.isLt⟩
 · rintro ⟨i,hi,rfl⟩
   exact ⟨⟨i,hi⟩,(Qe x hi).symm⟩
lemma abf [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {t:ℕ}
    (ht:t<bD G) (v:ℕ→G):
    ¬ lcs G 1≤⁅ZA (v '' ZH t),ZA (v '' ZH t)⁆⊔
      pN p G:=by
 intro h
 have hB:(⁅ZA (v '' ZH t),ZA (v '' ZH t)⁆⊔
     lcs G 2).Normal:=by
  refine d6 (n:=1) Z5 (sup_le ?_ (bC (by omega)))
  exact Z7.mpr (fun x _ y _=>b7 x y)
 have h2:lcs G 1≤⁅ZA (v '' ZH t),ZA (v '' ZH t)⁆⊔
     lcs G 2:=by
  refine C8 hp hG (lcs G 1) _ ?_ ?_
  · intro x hx y hy
    exact ZL
      (bC (D:=G) (show 2≤1+1+1 by omega) (d5 hx hy))
  · rw[sup_assoc]
    exact h
 have cO:bD G≤t:=by
  apply WK
  refine ⟨fun i=>v i,?_⟩
  have e:ZF (fun i:Fin t=>v i)=v '' ZH t:=by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.isLt,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  rw[e]
  exact h2
 omega
lemma DB [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s:ℕ}
    {u:ℕ→G} (hW:dO (pN p G) u s=lcs G 1):
    lcs G 1≤ZA (vP s u 1)⊔lcs G 2:=by
 apply A8 hp hG 0 (vP s u 1) (FU s u 0)
 refine (WT hW.symm).trans ?_
 refine qA (pN p G) Z5 ?_
 intro a b hab hb
 exact ZK (ZD ⟨(a,b),⟨hab,hb⟩,rfl⟩)
lemma E4 [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (wJ:lcs G 1≠⊥):
    2 ≤ bD G∧∃ u:ℕ→G,cD (pN p G) u (bD G)∧
      dO (pN p G) u (bD G)=lcs G 1∧
      (∀ k<bD G,u k∉ZA (u '' ZH k)⊔cE p G)∧
      lcs G 1≤⁅ZA (u '' ZH (bD G)),
        ZA (u '' ZH (bD G))⁆⊔lcs G 2:=by
 have:Fact p.Prime:=⟨hp⟩
 have:XN G:=(YK hG).isNilpotent
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=Yh.mp inferInstance
 let e:Fin (ZB G)→G:=(Xz G).symm
 have he:ZF e=RG:=U3 _
 have d8:{k | ∃ u:Fin k→G,
     lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
       lcs G 2}.Nonempty:=by
   refine ⟨ZB G,e,?_⟩
   rw[he,X4]
   exact WM
 obtain ⟨x,hx⟩:∃ x:Fin (bD G)→G,
     lcs G 1≤⁅ZA (ZF x),ZA (ZF x)⁆⊔lcs G 2:=
   Wr d8
 have hs:2≤bD G:=by
  by_contra f5
  have hk:bD G≤1:=by omega
  have Nj:⁅ZA (ZF x),ZA (ZF x)⁆≤⊥:=by
   refine i6 ?_
   rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
   have hij:i=j:=YL (by have:=i.isLt; have:=j.isLt; omega)
   rw[hij,commutatorElement_self]
   exact one_mem _
  have h12:lcs G 1≤lcs G 2:=WS hx (sup_le (WS Nj bot_le) YD)
  have abq:∀ n,lcs G 1≤lcs G (n+1):=by
   intro n
   induction n with
   | zero=>exact YD
   | succ n ih=>
     refine WS h12 ?_
     rw[lcs_succ 1,lcs_succ (n+1)]
     exact XE ih YD
  have rL:lcs G 1≤⊥:=by
   rw[← hN]
   exact WS (abq N) (bC (by omega))
  exact wJ (le_bot_iff.mp rL)
 have aco:lcs G 1≤⁅ZA (JM x '' ZH (bD G)),
     ZA (JM x '' ZH (bD G))⁆⊔pN p G:=by
  rw[← IL]
  exact hx.trans (SD (eo p) _)
 obtain ⟨u, -,fo,hW,gO, -, -⟩:=aav hp hG (pN p G) (cE p G)
   (eo p) (kO p) (dD p 0) (gG p)
   (fun g m hm=>b8 (u7 p hm g)) (bD G) (JM x) aco
   (fun t ht v _=>abf hp hG ht v)
 have dG:=DB hp hG hW
 have vG:ZA (vP (bD G) u 1)≤
     ⁅ZA (u '' ZH (bD G)),
       ZA (u '' ZH (bD G))⁆:=by
  rw[ZE]
  rintro _ ⟨ab,hab,rfl⟩
  exact Zo
    (ZD ⟨ab.1,Uj hab.1 hab.2,rfl⟩)
    (ZD ⟨ab.2,hab.2,rfl⟩)
 exact ⟨hs,u,fo,hW,gO,dG.trans (sup_le_sup_right vG _)⟩
end SimsCore
section aZ
variable {G:Type u} [Group G]
structure aE (p:ℕ) (u:ℕ→G) (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ):Prop where
  core:∀ t:Fin d.n,t.val<d.s→X t=u t.val
  valid:d.Valid
  bounded:d.Bounded p
  e9:h_ p d X
  a_pos:∀ t,1≤d.a t
  Fn:d.n≤∑ t,d.a t
  fD:∀ (t:Fin d.n) (w:ℕ),d.lv t=w↔aD r w≤t.val∧t.val<aD r w+r w
  kV:∀ w,p^r w*ZB (dC p G w)=ZB (lcs G w)
  E0 :∀ t,X t∉ZA (X '' {v | d.lv v=d.lv t∧v<t})⊔
    dC p G (d.lv t)
  w7:∀ w,lcs G w≤ZA (X '' {t | d.lv t=w})⊔lcs G (w+1)
  IQ:∀ t t',d.lv t=1→d.lv t'=1→t≤t'→(d.df t).2≤(d.df t').2
  KT :∀ t t',d.lv t=1→d.lv t'=1→(d.df t).1=(d.df t').1→
    (d.df t).2=(d.df t').2→t=t'
  flag:∀ k≤d.s,dO (pN p G) u k=
    ZA (X '' {t | d.lv t=1∧(d.df t).2.val<k})⊔pN p G
  F3:∀ k,1≤k→k<d.s→∃ t,d.lv t=1∧(d.df t).2.val=k
  k8:∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^d.a t)∧g=gN X e
  s7 :∀ e e':Fin d.n→ℕ,(∀ t,e t<p^d.a t)→(∀ t,e' t<p^d.a t)→
    gN X e=gN X e'→e=e'
  Kd:∀ w,1≤w→lcs G w≤ZA (X '' {t | w≤d.lv t})
  aau:∀ (w j:ℕ),∀ z∈ZA (X '' jw d w j),∃ e:Fin d.n→ℕ,
    (∀ t,e t≠0→t∈jw d w j)∧(∀ t,e t<p^d.a t)∧z=gN X e
  acv:∃ c,d.n=aD r c
  w3:∀ t,d.lv t=2→(d.df t).2.val≤(d.df (d.df t).1).2.val
lemma GI [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s L:ℕ}
    {r :ℕ→ℕ} {xs:ℕ→ℕ→G} {pa co:ℕ→ℕ→ℕ} (u:ℕ→G)
    (H0:s≤ r 0) (jq:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (jt:∀ w i,i< r (w+1)→ co (w+1) i<s) (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (NA:∀ i<s,xs 0 i=u i) (h0:ZA (xs 0 '' ZH (r 0))=⊤)
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZH (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥) (hL1:1≤L)
    (AN:∀ w i,i< r w→xs w i∉ZA (xs w '' ZH i)⊔dC p G w)
    (DY:∀ w≤L,p^r w*ZB (dC p G w)=ZB (lcs G w))
    (Mh:∀ k≤ s,∀ a b,a<b→ b<k→
      ⁅u a,u b⁆∈ZA (xs 1 '' {i | i< r 1∧co 1 i<k})⊔pN p G)
    (AY:∀ i i',i≤ i'→i'< r 1→ co 1 i≤ co 1 i')
    (F8:∀ i i',i< r 1→i'< r 1→pa 1 i=pa 1 i'→ co 1 i= co 1 i'→i=i')
    (fo:cD (pN p G) u s) (Hw3:∀ i,i< r 2→ co 2 i≤ co 1 (pa 2 i)):
    ∃ (d:aO) (X:Fin d.n→G),d.s=s∧aE p u d X (bR L r)∧
      ∀ w i,w≤L→i< r w→dE d X (aD (bR L r) w+i)=xs w i:=by
  have hd:=vN (s:=s) (L:=L) H0 jq jt H1
  have lH:∀ t,1≤(cZ s L r pa co).lv t→ fX L r xs t=
      ⁅fX L r xs ((cZ s L r pa co).df t).1,fX L r xs ((cZ s L r pa co).df t).2⁆:=
    fun t ht=>QC H0 jq jt Hx t ht
  have dV:=M6 (L:=L) h0
  have f6:=aaD (s:=s) (pa:=pa) (co:= co) H0 jq jt H1 Hx h0 HU HL
  have jV:= ow (cZ s L r pa co) hd (fX L r xs) lH
  obtain ⟨b,c,hv,hb,hr⟩:=
    Ln (cZ s L r pa co) (fX L r xs) hp hG hd dV lH f6
  have gO:=aab (s:=s) (L:=L) (pa:=pa) (co:= co) p AN
  have ha1:∀ t,1≤e8 p (cZ s L r pa co) (fX L r xs) t:=by
   intro t
   by_contra h0'
   have hz:e8 p (cZ s L r pa co) (fX L r xs) t=0:=by omega
   have cI:= oZ (cZ s L r pa co) (fX L r xs) hG t
   rw[hz,Y6,pow_one]at cI
   apply gO t
   refine (ZE _).mpr ?_ cI
   rintro _ ⟨v,K9,rfl⟩
   rcases (dY (cZ s L r pa co)).mp K9 with h | ⟨h1,h2⟩
   · exact ZL (dD p _
       (bC (D:=G) (show (cZ s L r pa co).lv t+1≤(cZ s L r pa co).lv v
         from h) (jV v)))
   · exact ZK (ZD ⟨v,⟨h1.symm,XO.mpr h2⟩,rfl⟩)
  have hWk:∀ k≤ s,dO (pN p G) u k=ZA (fX L r xs '' {t |
      (cZ s L r pa co).lv t=1∧((cZ s L r pa co).df t).2.val<k})⊔pN p G:=
    fun k hk=>ab7 p u H0 jq jt H1 Hx NA hL1 Mh hk
  have qX:=Md hp hG (cZ s L r pa co) hd (fX L r xs) dV jV f6
  have aeA:=JZ (cZ s L r pa co) (fX L r xs) hp hG hd jV f6
  have hw3:∀ t:Fin (cZ s L r pa co).n,(cZ s L r pa co).lv t=2→
      ((cZ s L r pa co).df t).2.val≤
        ((cZ s L r pa co).df ((cZ s L r pa co).df t).1).2.val:=by
   intro t ht
   have iQ:eJ (bR L r) L t.val=1+1:=ht
   obtain ⟨-,hi,h1,h2⟩:=pG (L:=L) (pa:=pa) (co:= co) H0 jq jt t iQ
   have HR:(cZ s L r pa co).lv ((cZ s L r pa co).df t).1+1=
       (cZ s L r pa co).lv t:=hd.wY t (by omega)
   have ht1:eJ (bR L r) L ((kJ L r pa co t).1).val=0+1:=by
    have e:(cZ s L r pa co).lv ((cZ s L r pa co).df t).1=1:=by omega
    exact e
   obtain ⟨-, -, -,h4⟩:=pG (L:=L) (pa:=pa) (co:= co) H0 jq jt _ ht1
   have h5:((kJ L r pa co t).1).val - aD (bR L r) (0+1)=
       pa (1+1) (t.val - aD (bR L r) (1+1)):=by
    rw[h1]
    exact Yb _ _
   show ((kJ L r pa co t).2).val≤((kJ L r pa co (kJ L r pa co t).1).2).val
   rw[h4,h2,h5]
   exact Hw3 _ hi
  refine ⟨⟨(cZ s L r pa co).n,(cZ s L r pa co).s,(cZ s L r pa co).lv,
    (cZ s L r pa co).df,e8 p (cZ s L r pa co) (fX L r xs),b,c⟩,fX L r xs,rfl,?_,
    fun w i hw hi=>?_⟩
  refine
    { core:= fun t ht=>CS u H0 NA t ht
      valid:=hv
      bounded:=hb
      e9:=hr
      a_pos:=ha1
      Fn:=?_
      fD:=?_
      kV:=?_
      E0:=gO
      w7:=?_
      IQ:= fun t t' ht iQ KW=>aax H0 jq jt AY t t' ht iQ KW
      KT:= fun t t' ht iQ h1 h2=>aaU H0 jq jt F8 t t' ht iQ h1 h2
      flag:=hWk
      F3:= fun k Bw BG=>NG p u fo hWk Bw BG
      k8:=qX
      s7:= fun e e' he he' h=>QW _ (fX L r xs) hr.card qX e e' he he' h
      Kd:= f6
      aau:= fun w j=>aeA w j
      acv:=⟨L+1,rfl⟩
      w3:=hw3 }
  · calc aD (bR L r) (L+1)=∑ _t:Fin (aD (bR L r) (L+1)),1:=by simp
      _ ≤∑ t,e8 p (cZ s L r pa co) (fX L r xs) t:=
        Z9 (fun t _=>ha1 t)
  · intro t w
    constructor
    · intro h
      have h':eJ (bR L r) L t.val=w:=h
      obtain ⟨h1,h2, -⟩:=Bk (ℓ:=bR L r) t.isLt
      rw[h']at h1 h2
      rw[dM]at h2
      exact ⟨h1,h2⟩
    · rintro ⟨h1,h2⟩
      by_cases hw:w≤L
      · exact Cz hw h1 (lt_of_lt_of_eq h2 (dM (bR L r) w).symm)
      · exfalso
        have h3:=g5 (bR L r) (show L+1≤w by omega)
        have h4:t.val<aD (bR L r) (L+1):=t.isLt
        omega
  · intro w
    by_cases hw:w≤L
    · rw[k4 hw]
      exact DY w hw
    · rw [QY hw,Y6,Wn]
      obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
      have h1:lcs G (w'+1)=⊥:=le_bot_iff.mp
        ((bC (D:=G) (show L+1≤w'+1 by omega)).trans (WT HL))
      have h2:dC p G (w'+1)=⊥:=le_bot_iff.mp ((oO p w').trans (WT h1))
      rw[h1,h2]
  · intro w
    rcases w with _ | w
    · rw [lcs_zero, ← h0]
      refine le_sup_of_le_left (ZS ?_)
      rintro _ ⟨i,hi,rfl⟩
      exact ⟨⟨_,pZ (Zv L) hi⟩,vH (Zv L) hi,
        Cc xs (Zv L) hi⟩
    · exact Az (s:=s) (pa:=pa) (co:= co) HU HL w
  · show (if h:aD (bR L r) w+i<aD (bR L r) (L+1) then
        fX L r xs ⟨aD (bR L r) w+i,h⟩ else 1)=xs w i
    rw[dif_pos (pZ hw hi)]
    exact Cc xs hw hi
noncomputable def gR [Finite G] (p s:ℕ) (u:ℕ→G) (w:ℕ):ℕ:=
  (a7 p s u (gd p s u) w).r
noncomputable def zV [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):G:=
  (a7 p s u (gd p s u) w).x i
noncomputable def Ny [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):ℕ:=
  (a7 p s u (gd p s u) w).lK i
noncomputable def zW [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):ℕ:=
  (a7 p s u (gd p s u) w).gC i
lemma qJ (p s:ℕ) (u:ℕ→G) (L0:lB G) (i:ℕ):
    (a7 p s u L0 1).gC i=d9 (c9 (dN s u 0 L0) (dC p G 1) (cN s 0 L0)) i/s:=by
 rw[v7]
 exact tK
lemma Cj (p s:ℕ) (u:ℕ→G) (L0:lB G) (i:ℕ):
    (a7 p s u L0 1).lK i=d9 (c9 (dN s u 0 L0) (dC p G 1) (cN s 0 L0)) i % s:=by
 rw[v7]
 exact sP
lemma t9 (p s:ℕ) (u:ℕ→G) (L0:lB G) {i i':ℕ} (h:i≤ i')
    (gJ:i'< (a7 p s u L0 1).r):(a7 p s u L0 1).gC i≤(a7 p s u L0 1).gC i':=by
 rw[qJ,qJ]
 have h1:i'< (c9 (dN s u 0 L0) (dC p G 1) (cN s 0 L0)).card:=gJ
 exact Nat.div_le_div_right (aa9 _ h h1)
lemma Dl (p s:ℕ) (u:ℕ→G) (L0:lB G) {i i':ℕ}
    (hi:i< (a7 p s u L0 1).r) (gJ:i'< (a7 p s u L0 1).r)
    (hp:(a7 p s u L0 1).lK i=(a7 p s u L0 1).lK i')
    (hc:(a7 p s u L0 1).gC i=(a7 p s u L0 1).gC i'):i=i':=by
 rw[Cj,Cj]at hp
 rw[qJ,qJ]at hc
 have h1:=Wa (d9 (c9 (dN s u 0 L0) (dC p G 1) (cN s 0 L0)) i) s
 have h2:=Wa (d9 (c9 (dN s u 0 L0) (dC p G 1) (cN s 0 L0)) i') s
 rw[hp,hc]at h1
 exact aaw _ hi gJ (h1.symm.trans h2)
lemma Fw [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s:ℕ}
    (hs:2≤ s) (u:ℕ→G) (fo:cD (pN p G) u s)
    (hW:dO (pN p G) u s=lcs G 1)
    (gO:∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G):
    ∃ (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ),d.s=s∧d.n≤ m∧
      r 0=ZV G∧aE p u d X r :=by
 have:Fact p.Prime:=⟨hp⟩
 have nD:IsPGroup p G:=YK hG
 have:XN G:=nD.isNilpotent
 have k6:0<s:=by omega
 have kH:∀ a<s,(gd p s u).x a=u a:= fun a ha=>n8 p s u ha
 have j_:s≤(gd p s u).r :=W5 s _
 have vh:ZA ((gd p s u).x '' ZH (gd p s u).r)=⊤:=by
  apply eD
  rw[ew nD,Yo]
  intro g _
  exact aaO p s u g
 have dG:=DB hp hG hW
 have hU:=MY p s u (gd p s u) hp hG k6 kH (by rw[vh,OQ]) dG j_
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=Yh.mp inferInstance
 have hL:lcs G (N+1+1)=⊥:=
   le_bot_iff.mp (hN▸bC (D:=G) (show N≤N+1+1 by omega))
 have AN:∀ w i,i<gR p s u w→
     zV p s u w i∉ZA (zV p s u w '' ZH i)⊔dC p G w:=by
  intro w i hi
  rcases w with _ | w
  · exact Qz p s u gO hi
  · exact GJ p s u (gd p s u) w hi
 have Heq:∀ w,ZA (zV p s u w '' ZH (gR p s u w))⊔dC p G w=
     lcs G w:=by
  intro w
  rcases w with _ | w
  · show ZA ((gd p s u).x '' ZH (gd p s u).r)⊔cE p G=lcs G 0
    rw[vh,OQ,lcs_zero]
  · apply le_antisymm
    · refine sup_le ?_ (oO p w)
      rw[ZE]
      rintro _ ⟨i, -,rfl⟩
      exact nT p s u (gd p s u) (w+1) i
    · exact (hU w).trans (SD (dD p (w+1)) _)
 have DY:∀ w,p^gR p s u w*ZB (dC p G w)=ZB (lcs G w):=by
  intro w
  have cI:∀ i,zV p s u w i∈lcs G w:= fun i=>nT p s u (gd p s u) w i
  have hN':∀ j,(ZA (zV p s u w '' ZH j)⊔dC p G w).Normal:=
    fun j=>jU p w _ (by rintro _ ⟨i, -,rfl⟩; exact cI i)
  have h1:=r6 hp hG (dC p G w) (v:=zV p s u w) (gR p s u w)
    (fun k hk=>AN w k hk)
  have h2:=lC hp.pos (dC p G w) (zV p s u w) hN'
    (fun j=>qG p w _ (cI j)) (gR p s u w)
  rw[Heq w]at h1 h2
  exact le_antisymm h1 h2
 have adq:gR p s u 0=ZV G:=by
  have h1:p^gR p s u 0*ZB (cE p G)=ZB (lcs G 0):=DY 0
  have h2:=VO (frattini G)
  rw[k5 nD,ew nD]at h2
  have h3:ZB (lcs G 0)=ZB G:=by rw[lcs_zero,Yn]
  have h4:0<ZB (cE p G):=Xi
  have h6:p^gR p s u 0*ZB (cE p G)=p^ZV G*ZB (cE p G):=by
   rw[← h2, ← h3,h1]
  exact Zd hp.two_le (Yc h4 h6)
 have jq:∀ w i,i<gR p s u (w+1)→Ny p s u (w+1) i<gR p s u w:=
   fun w i hi=> (l9 p s u (gd p s u) k6 j_ w hi).1
 have jt:∀ w i,i<gR p s u (w+1)→zW p s u (w+1) i<s:=
   fun w i hi=> (l9 p s u (gd p s u) k6 j_ w hi).2.1
 have H1:∀ i,i<gR p s u 1→Ny p s u 1 i<zW p s u 1 i:=
   fun i hi=> (l9 p s u (gd p s u) k6 j_ 0 hi).2.2.1 rfl
 have Hx:∀ w i,i<gR p s u (w+1)→zV p s u (w+1) i=
     ⁅zV p s u w (Ny p s u (w+1) i),zV p s u 0 (zW p s u (w+1) i)⁆:=by
  intro w i hi
  obtain ⟨-,hc, -,he⟩:=l9 p s u (gd p s u) k6 j_ w hi
  have e0:zV p s u 0 (zW p s u (w+1) i)=u (zW p s u (w+1) i):=n8 p s u hc
  rw[e0]
  exact he
 have Mh:∀ k≤ s,∀ a b,a<b→ b<k→⁅u a,u b⁆∈
     ZA (zV p s u 1 '' {i | i<gR p s u 1∧zW p s u 1 i<k})⊔pN p G:=
   fun k hk a b hab hb=>mK p s u (gd p s u) k6 kH hk hab hb
 have AY:∀ i i',i≤ i'→i'<gR p s u 1→zW p s u 1 i≤zW p s u 1 i':=
   fun i i' h gJ=>t9 p s u (gd p s u) h gJ
 have F8:∀ i i',i<gR p s u 1→i'<gR p s u 1→Ny p s u 1 i=Ny p s u 1 i'→
     zW p s u 1 i=zW p s u 1 i'→i=i':=
   fun i i' hi gJ Ou hc=>Dl p s u (gd p s u) hi gJ Ou hc
 have Hw3:∀ i,i<gR p s u 2→zW p s u 2 i≤zW p s u 1 (Ny p s u 2 i):=
   fun i hi=>Qd p s u (gd p s u) hi
 obtain ⟨d,X,oW,nF, -⟩:=GI (L:=N+1) (r :=gR p s u) (xs:=zV p s u)
   (pa:=Ny p s u) (co:=zW p s u) hp hG u j_ jq jt H1 Hx kH vh (fun w _=>hU w) hL
   (by omega) AN (fun w _=>DY w) Mh AY F8 fo Hw3
 refine ⟨d,X,bR (N+1) (gR p s u),oW,?_,?_,nF⟩
 · have h1:=nF.e9.card
   rw[hG]at h1
   have h2:=Zd hp.two_le h1
   rw[h2]
   exact nF.Fn
 · rw[k4 (Zv _)]
   exact adq
lemma qW [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (wJ:lcs G 1≠⊥):
    ∃ (u :ℕ→G) (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ),
      2≤bD G∧d.s=bD G∧
      lcs G 1≤⁅ZA (u '' ZH d.s),ZA (u '' ZH d.s)⁆⊔
        lcs G 2∧
      cD (pN p G) u d.s∧dO (pN p G) u d.s=lcs G 1∧
      (∀ k<d.s,u k∉ZA (u '' ZH k)⊔cE p G)∧
      d.n≤ m∧r 0=ZV G∧aE p u d X r :=by
 obtain ⟨bU,u,fo,hW,gO,dG⟩:=E4 hp hG wJ
 obtain ⟨d,X,r,oW,bZ,adl,nF⟩:=Fw hp hG bU u fo hW gO
 refine ⟨u,d,X,r,bU,oW,?_,?_,?_,?_,bZ,adl,nF⟩
 · rw[oW]
   exact dG
 · rw[oW]
   exact fo
 · rw[oW]
   exact hW
 · rw[oW]
   exact gO
end aZ
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
abbrev aR (c:ℕ) (r :Fin c→ℕ):Type:=Σ i:Fin c,Fin (r i)
abbrev kq (p c:ℕ) (r :Fin c→ℕ) (a:aR c r→ℕ):Type:=
  (k:aR c r)→(h:aR c r)→Fin (p^a h)
section PowerWordCount
variable (p:ℕ) {c:ℕ} {r :Fin c→ℕ} (a:aR c r→ℕ)
def j5 (k h:aR c r) (x:ℕ):Prop:=
  k.1<h.1∨(h.1=k.1∧h.2.val<k.2.val∧p∣x)∨x =0
def n3 (B:kq p c r a):Prop:=∀ k h,j5 p k h (B k h).val
def AO (k h:aR c r):ℕ:=
  (if k.1<h.1 then a h else 0)+(if h.1=k.1∧h.2.val<k.2.val then a h - 1 else 0)
def sL (i:Fin c):ℕ:=∑ v:Fin (r i),a ⟨i,v⟩
def nQ (i:Fin c):ℕ:=∑ u∈ZU.filter (fun u=>i<u),sL a u
def pj:ℕ:=
  ∑ i:Fin c,(r i*nQ a i+∑ v:Fin (r i),(r i - 1 - v.val)*(a ⟨i,v⟩ - 1))
def kC:ℕ:=
  ∑ i:Fin c,(r i*nQ a i+(r i - 1)*(sL a i - r i))
lemma N5 (k h:aR c r):
    ZB {x:Fin (p^a h)//j5 p k h x.val}≤p^AO a k h:=by
 unfold AO
 by_cases h1:k.1<h.1
 · have h2:¬ (h.1=k.1∧h.2.val<k.2.val):=by
     intro h'
     rw[h'.1]at h1
     exact UO _ h1
   rw[if_pos h1,if_neg h2,add_zero]
   calc ZB {x:Fin (p^a h)//j5 p k h x.val}≤ZB (Fin (p^a h)):=
         Finite.card_subtype_le _
     _=p^a h:=Xk _
 · by_cases h2:h.1=k.1∧h.2.val<k.2.val
   · rw [if_neg h1,if_pos h2,zero_add]
     have v5:∀ x:{x:Fin (p^a h)//j5 p k h x.val},p∣x.1.val:=by
      intro x
      have hx:=x.2
      unfold j5 at hx
      rcases hx with h' | ⟨_,_,hd⟩ | h0
      · exact absurd h' h1
      · exact hd
      · rw[h0]
        exact dvd_zero p
     have f5:∀ x:{x:Fin (p^a h)//j5 p k h x.val},x.1.val/p<p^(a h - 1):=by
      intro x
      have hx:x.1.val<p^a h:=x.1.isLt
      rcases Yj (a h) with ha | ha
      · have hp1:p^a h=1:=by rw[ha,Y6]
        have kH:x.1.val=0:=by omega
        have e:a h - 1=0:=by omega
        rw[e,kH,Nat.zero_div,Y6]
        exact Nat.one_pos
      · obtain ⟨n,hn⟩:∃ n,a h=n+1:=⟨a h - 1,by omega⟩
        have oQ:x.1.val<p*p^n:=by
         rw[← VG, ← hn]
         exact hx
        have e:a h - 1=n:=by omega
        rw[e]
        exact Nat.div_lt_of_lt_mul oQ
     let f:{x:Fin (p^a h)//j5 p k h x.val}→Fin (p^(a h - 1)):=
       fun x => ⟨x.1.val/p,f5 x⟩
     have hf:Z8 f:=by
      intro x y Cu
      have e:x.1.val/p=y.1.val/p:= congrArg Ty Cu
      apply Zu
      apply YL
      calc x.1.val=x.1.val/p*p:=(OC (v5 x)).symm
        _=y.1.val/p*p:=by rw[e]
        _=y.1.val:= OC (v5 y)
     calc ZB {x:Fin (p^a h)//j5 p k h x.val}≤ZB (Fin (p^(a h - 1))):=
           Yy f hf
       _=p^(a h - 1):=Xk _
   · rw [if_neg h1,if_neg h2,add_zero,Y6]
     have h0:∀ x:{x:Fin (p^a h)//j5 p k h x.val},x.1.val=0:=by
      intro x
      have hx:=x.2
      unfold j5 at hx
      rcases hx with h' | ⟨e1,e2,_⟩ | h0
      · exact absurd h' h1
      · exact (h2 ⟨e1,e2⟩).elim
      · exact h0
     have hf:Z8 (fun _:{x:Fin (p^a h)//j5 p k h x.val}=> ()):=by
       intro x y _
       apply Zu
       apply YL
       rw[h0 x,h0 y]
     calc ZB {x:Fin (p^a h)//j5 p k h x.val}≤ZB Unit:=
           Yy _ hf
       _=1:=Nat.card_unique
lemma Eh:
    ZB {B:kq p c r a//n3 p a B}≤p^(∑ k,∑ h,AO a k h):=by
 have e1:{B:kq p c r a//n3 p a B}≃
     ((k:aR c r)→{row:(h:aR c r)→Fin (p^a h)//
       ∀ h,j5 p k h (row h).val}):=
   @Equiv.subtypePiEquivPi (aR c r) (fun _=> (h:aR c r)→Fin (p^a h))
     (fun k row=> ∀ h,j5 p k h (row h).val)
 have e2:∀ k:aR c r,{row:(h:aR c r)→Fin (p^a h)//
     ∀ h,j5 p k h (row h).val}≃
     ((h:aR c r)→{x:Fin (p^a h)//j5 p k h x.val}):=
   fun k=> @Equiv.subtypePiEquivPi (aR c r) (fun h=>Fin (p^a h))
     (fun h x =>j5 p k h x.val)
 rw[YJ e1,Pa]
 calc ∏ k,ZB {row:(h:aR c r)→Fin (p^a h)//∀ h,j5 p k h (row h).val}
       = ∏ k,∏ h,ZB {x:Fin (p^a h)//j5 p k h x.val}:=by
         refine TQ rfl fun k _=>?_
         rw[YJ (e2 k),Pa]
   _ ≤ ∏ k,∏ h,p^AO a k h:=
         Ud fun k _=>Ud fun h _=>N5 p a k h
   _ = p ^(∑ k,∑ h,AO a k h):=by
         simp only[XB]
lemma aaL:∑ k,∑ h,AO a k h=pj a:=by
 unfold pj
 rw[TD]
 refine Zw rfl fun i _=>?_
 have hA:∑ h:aR c r,(if i<h.1 then a h else 0)=nQ a i:=by
   rw[TD]
   unfold nQ sL
   rw[Xd]
   refine Zw rfl fun u _=>?_
   by_cases hu:i<u
   · simp[hu]
   · simp[hu]
 have hB:∀ j:Fin (r i),
     ∑ h:aR c r,(if h.1=i∧h.2.val<j.val then a h - 1 else 0)=
       ∑ v:Fin (r i),(if v.val<j.val then a ⟨i,v⟩ - 1 else 0):=by
   intro j
   rw[TD,Fintype.sum_eq_single i]
   · simp
   · intro u hu
     simp[hu]
 have aea:∀ j:Fin (r i),∑ h,AO a ⟨i,j⟩ h=
     nQ a i+∑ v:Fin (r i),(if v.val<j.val then a ⟨i,v⟩ - 1 else 0):=by
   intro j
   rw[← hA, ← hB j, ← Xy]
   rfl
 rw [Zw rfl fun j _=>aea j,Xy,Y5,
   Y4,Zz,smul_eq_mul,OD]
 congr 1
 refine Zw rfl fun v _=>?_
 rw[← Xd,Y5,smul_eq_mul]
 congr 1
 rw[← Fin.card_Ioi (a:=v)]
 congr 1
 ext j
 simp
lemma AS (ha:∀ k,1≤a k):pj a≤kC a:=by
 unfold pj kC
 refine Z9 fun i _=>?_
 have hs:∑ v:Fin (r i),(a ⟨i,v⟩ - 1)=sL a i - r i:=by
  have h1:∑ v:Fin (r i),(a ⟨i,v⟩ - 1+1)=sL a i:=
    Zw rfl fun v _=>Vf (ha _)
  rw [Xy,Y5,Y4,Zz,
    smul_eq_mul,UH]at h1
  omega
 have h2:∑ v:Fin (r i),(r i - 1 - v.val)*(a ⟨i,v⟩ - 1)≤
     ∑ v:Fin (r i),(r i - 1)*(a ⟨i,v⟩ - 1):=
   Z9 fun v _=>Zr (S9 _ _) YD
 rw[← OH,hs]at h2
 exact TE h2 _
lemma Jr :
    ZB {B:kq p c r a//n3 p a B}≤p^pj a:=by
 rw[← aaL]
 exact Eh p a
end PowerWordCount
section PowerWordGroup
variable {p:ℕ} [hp:Fact p.Prime]
lemma wA {Q:Type u} [Group Q] [Finite Q] (hQ:IsPGroup p Q)
    {n:ℕ} (y:Fin n→Q) (dV:ZA (ZF y)=⊤)
    (Mb:∀ v,ZA (y '' {w | w≠v})≠⊤) (e:Fin n→ℕ)
    (he:(ZR fun v=>y v^e v).prod∈frattini Q) (v:Fin n):p∣e v:=by
  by_contra hv
  have j3:(dL Q).ker= frattini Q:=G8 hQ
  have o5:∏ w,(dL Q) (y w)^e w=1:=by
   have h1:(dL Q) (ZR fun v=>y v^e v).prod=1:=by
     rw[← Zm,j3]
     exact he
   rw[RO,Vv,Oc]at h1
   simp only[U9,map_pow]at h1
   exact h1
  have hM:(dL Q) (y v)^e v∈(ZA (y '' {w | w≠v})).map (dL Q):=by
    have h2:(dL Q) (y v)^e v*
        ∏ w∈ZU.erase v,(dL Q) (y w)^e w=1:=by
     rw [UC ZU (fun w=> (dL Q) (y w)^e w)
       (Zb v)]
     exact o5
    have h3:∏ w∈ZU.erase v,(dL Q) (y w)^e w∈
        (ZA (y '' {w | w≠v})).map (dL Q):=by
      refine prod_mem fun w hw=>?_
      have cI:y w∈y '' {w | w≠v}:=⟨w,Xx hw,rfl⟩
      exact pow_mem (Vi (dL Q) (ZD cI)) _
    rw[Uv h2]
    exact inv_mem h3
  have adp:(dL Q) (y v)^p=1:=by
   rw[← map_pow, ← Zm,j3,ew hQ]
   exact gG p (y v)
  have abh:Nat.Coprime (e v) p:=
    Nat.Coprime.symm ((TK hp.out).mpr hv)
  have hyM:(dL Q) (y v)∈(ZA (y '' {w | w≠v})).map (dL Q):=by
    have e1:(dL Q) (y v)=((dL Q) (y v)^(e v:ℤ))^(Nat.gcdA (e v) p)*
        ((dL Q) (y v)^(p:ℤ))^(Nat.gcdB (e v) p):=by
     rw [← TW, ← TW, ← ON, ← OE,Nat.Coprime.gcd_eq_one abh,
       Rz,zpow_one]
    rw[e1]
    refine mul_mem (OO ?_ _) (OO ?_ _)
    · rw[WO]
      exact hM
    · rw[WO,adp]
      exact one_mem _
  obtain ⟨s,hs,hsy⟩:=Zj.mp hyM
  have hyK:y v∈ZA (y '' {w | w≠v})⊔frattini Q:=by
    have hk:s⁻¹*y v∈frattini Q:=by
     rw[← j3,Zm,YP,Wq,hsy,OP]
    have qO:y v=s*(s⁻¹*y v):=by group
    rw[qO]
    exact UE hs hk
  have o9:ZA (y '' {w | w≠v})⊔frattini Q=⊤:=by
    rw[Yo, ← dV,ZE]
    rintro _ ⟨w,rfl⟩
    by_cases hw:w=v
    · rw[hw]
      exact hyK
    · have cI:y w∈y '' {w | w≠v}:=⟨w,hw,rfl⟩
      exact ZK (ZD cI)
  exact Mb v (eD o9)
lemma zU {H:Type u} [Group H] (N:Subgroup H) [N.Normal]
    [Finite (H⧸N)] (hQ:IsPGroup p (H⧸N)) {n:ℕ} (x:Fin n→H)
    (dV:ZA (ZF fun v=> (x v:H⧸N))=⊤)
    (Mb:∀ v,ZA ((fun w=> (x w:H⧸N)) '' {w | w≠v})≠⊤)
    (j:Fin n) (A:ℕ) (hA:1≤A) (b:Fin n→ℕ) (z:H) (hz:z∈N)
    (m_:x j^p^A=(ZR fun v=>x v^b v).prod*z) (v:Fin n):p∣b v:=by
  refine wA hQ (fun v=> (x v:H⧸N)) dV Mb b ?_ v
  show (ZR fun v=> (x v:H⧸N)^b v).prod∈frattini (H⧸N)
  have h1:((x j^p^A:H):H⧸N)=(((ZR fun v=>x v^b v).prod:H):H⧸N):=by
    rw[m_,QuotientGroup.mk_mul,(Yf z).mpr hz,UH]
  have h2:(((ZR fun v=>x v^b v).prod:H):H⧸N)=
      (ZR fun v=> (x v:H⧸N)^b v).prod:=by
    rw[← YY,RO,Vv]
    simp only[U9,YY,Wg]
  rw[← h2, ← h1,Wg,ew hQ]
  obtain ⟨A',rfl⟩:∃ A',A=A'+1:=⟨A - 1,by omega⟩
  rw[show p^(A'+1)=p*p^A' from VG p A',X5]
  exact pow_mem (gG p _) _
abbrev e7 (G:Type u) [Group G] (i:ℕ):Type u:=
  ↥(lcs G i)⧸(lcs G (i+1)).subgroupOf (lcs G i)
structure kN (p:ℕ) {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ}
    (a:aR c r→ℕ) (g:aR c r→G) (B:kq p c r a):Prop where
  mem:∀ k,g k∈lcs G k.1
  gen :∀ i:Fin c,ZA (ZF fun v:Fin (r i)=>
      (Z6 (⟨g ⟨i,v⟩,mem ⟨i,v⟩⟩:lcs G i):e7 G i))=⊤
  irr :∀ (i:Fin c) (v:Fin (r i)),ZA ((fun w:Fin (r i)=>
      (Z6 (⟨g ⟨i,w⟩,mem ⟨i,w⟩⟩:lcs G i):e7 G i)) '' {w | w≠v})≠⊤
  pos:∀ k,1≤a k
  supp:∀ k h,¬ k.1<h.1→¬ (h.1=k.1∧h.2.val<k.2.val)→(B k h).val=0
  pow : ∀ (i:Fin c) (j:Fin (r i)),g ⟨i,j⟩^p^a ⟨i,j⟩=
      (ZR fun v:Fin (r i)=>g ⟨i,v⟩^(B ⟨i,j⟩ ⟨i,v⟩).val).prod*
      (ZR fun u:Fin c=>if i<u then
        (ZR fun v:Fin (r u)=>g ⟨u,v⟩^(B ⟨i,j⟩ ⟨u,v⟩).val).prod else 1).prod
lemma lX {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ} (g:aR c r→G)
    (cI:∀ k,g k∈lcs G k.1) (b:aR c r→ℕ) (i:Fin c):
    (List.ofFn fun u:Fin c=>if i<u then
      (ZR fun v:Fin (r u)=>g ⟨u,v⟩^b ⟨u,v⟩).prod else 1).prod∈
        lcs G ((i:ℕ)+1):=by
  refine Wb _ fun x hx =>?_
  rw[XC]at hx
  obtain ⟨u,rfl⟩:=hx
  dsimp only
  split_ifs with hu
  · refine Wb _ fun y hy=>?_
    rw[XC]at hy
    obtain ⟨v,rfl⟩:=hy
    exact Xm _ (bC (Nat.succ_le_of_lt (hu:(i:ℕ)<u))
      (cI ⟨u,v⟩)) _
  · exact Yl _
lemma kN.KM {G:Type u} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ} {g:aR c r→G} {B:kq p c r a}
    (hd:kN p a g B) (i:Fin c) (j v:Fin (r i)):
    p∣(B ⟨i,j⟩ ⟨i,v⟩).val:=by
 have hQ:IsPGroup p (e7 G i):=(hG.to_subgroup _).to_quotient _
 have f6:=lX g hd.mem (fun h=> (B ⟨i,j⟩ h).val) i
 have L7:(ZR fun u:Fin c=>if i<u then
     (ZR fun v:Fin (r u)=>g ⟨u,v⟩^(B ⟨i,j⟩ ⟨u,v⟩).val).prod else 1).prod∈
       lcs G i:=bC (XV _) f6
 have hz:(⟨_,L7⟩:lcs G i)∈(lcs G ((i:ℕ)+1)).subgroupOf (lcs G i):=
   ZT.mpr f6
 have m_:(⟨g ⟨i,j⟩,hd.mem ⟨i,j⟩⟩:lcs G i)^p^a ⟨i,j⟩=
     (ZR fun w:Fin (r i)=>
       (⟨g ⟨i,w⟩,hd.mem ⟨i,w⟩⟩:lcs G i)^(B ⟨i,j⟩ ⟨i,w⟩).val).prod*⟨_,L7⟩:=by
   apply (lcs G i).subtype_injective
   rw[YP,map_pow,RO,Vv]
   simp only[U9,map_pow,UF]
   exact hd.pow i j
 exact zU ((lcs G ((i:ℕ)+1)).subgroupOf (lcs G i)) hQ
   (fun w=> (⟨g ⟨i,w⟩,hd.mem ⟨i,w⟩⟩:lcs G i)) (hd.gen i) (hd.irr i) j (a ⟨i,j⟩)
   (hd.pos _) (fun w=> (B ⟨i,j⟩ ⟨i,w⟩).val) _ hz m_ v
lemma kN.abV {G:Type u} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ} {g:aR c r→G} {B:kq p c r a}
    (hd:kN p a g B):n3 p a B:=by
 rintro ⟨i,j⟩ ⟨u,v⟩
 by_cases h1:i<u
 · exact Y7 h1
 by_cases h2:u=i∧v.val<j.val
 · obtain ⟨hu,hv⟩:=h2
   subst hu
   exact XQ (Y7 ⟨rfl,hv,hd.KM hG _ _ _⟩)
 · exact XQ (XQ (hd.supp ⟨i,j⟩ ⟨u,v⟩ h1 h2))
def kZ (p c:ℕ) (r :Fin c→ℕ) (a:aR c r→ℕ):Set (kq p c r a):=
  {B | ∃ (G:Type) (_:Group G) (_:Finite G) (g:aR c r→G),
    IsPGroup p G∧kN p a g B}
lemma zL (c:ℕ) (r :Fin c→ℕ) (a:aR c r→ℕ):
    (kZ p c r a).ncard≤p^pj a:=by
 have jp:kZ p c r a⊆{B | n3 p a B}:=by
   rintro B ⟨G,_,_,g,hG,hd⟩
   exact hd.abV hG
 calc (kZ p c r a).ncard≤{B | n3 p a B}.ncard:=
       Yk jp (Zl _)
   _=ZB {B:kq p c r a//n3 p a B}:=(Xt _).symm
   _≤p^pj a:=Jr p a
lemma KJ (c:ℕ) (r :Fin c→ℕ) (a:aR c r→ℕ) (ha:∀ k,1≤a k):
    (kZ p c r a).ncard≤p^kC a:=
  (zL c r a).trans
    (Zk hp.out.pos (AS a ha))
lemma yD {Q:Type u} [Group Q] {n:ℕ} (y:Fin n→Q)
    (nU:∀ (m:ℕ) (z:Fin m→Q),ZA (ZF z)=⊤→n≤ m)
    (v:Fin n):ZA (y '' {w | w≠v})≠⊤:=by
  intro o9
  obtain ⟨m,rfl⟩:∃ m,n=m+1:=⟨n - 1,by have:=v.isLt; omega⟩
  have hr :ZF (y∘v.succAbove)=y '' {w | w≠v}:=by
    rw[WJ,Fin.range_succAbove]
    ext w
    simp
  have h:=nU m (y∘v.succAbove) (by rw[hr]; exact o9)
  omega
lemma j7 {M:Type*} [Monoid M] (n:ℕ):∀ (f:Fin n→M) (i:Fin n),
    (∀ u,u< i→ f u=1)→
    (ZR f).prod= f i*(ZR fun u=>if i<u then f u else 1).prod:=by
  induction n with
  | zero=>intro f i; exact i.elim0
  | succ n ih=>
    intro f i hf
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i',rfl⟩
    · simp[Ut,Fin.succ_pos]
    · have hf0:f 0=1:=hf 0 (Fin.succ_pos i')
      have hrec:=ih (fun u=>f u.succ) i'
        (fun u hu=>hf u.succ (Uz.mpr hu))
      rw[Ut,S5,hf0,Wn,hrec]
      conv_rhs=>rw[Ut,S5]
      simp[Uz,Oa]
section Bridge
variable {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ}
def cW (g:aR c r→G) (e:aR c r→ℕ) (u:Fin c):G:=
  (ZR fun v:Fin (r u)=>g ⟨u,v⟩^e ⟨u,v⟩).prod
def ju (g:aR c r→G) (e:aR c r→ℕ):G:=
  (ZR fun u:Fin c=>cW g e u).prod
def z8 (g:aR c r→G) (i:Fin c) (j:ℕ):Subgroup G:=
  ZA {x | ∃ v:Fin (r i),v.val<j∧g ⟨i,v⟩=x}⊔lcs G ((i:ℕ)+1)
def EY (i:Fin c) (j:ℕ) (e:aR c r→ℕ):Prop:=
  ∀ h:aR c r,(h.1< i∨(h.1=i∧j≤h.2.val))→e h=0
structure ov (p:ℕ) (a:aR c r→ℕ) (g:aR c r→G) where
  coord:G→(h:aR c r)→Fin (p^a h)
  uniq:∀ e:(h:aR c r)→Fin (p^a h),coord (ju g fun h=> (e h).val)=e
  sub :∀ (i:Fin c) (j:ℕ) (x:G),x∈z8 g i j→
    ∃ e:(h:aR c r)→Fin (p^a h),
      EY i j (fun h=> (e h).val)∧ju g (fun h=> (e h).val)=x
lemma ov.q5 {p:ℕ} {a:aR c r→ℕ} {g:aR c r→G}
    (nf:ov p a g) (i:Fin c) (j:ℕ) (x:G) (hx:x∈z8 g i j):
    EY i j (fun h=> (nf.coord x h).val)∧
      ju g (fun h=> (nf.coord x h).val)=x:=by
  obtain ⟨e,he,o5⟩:=nf.sub i j x hx
  have hc:nf.coord x =e:=by
   rw[← o5]
   exact nf.uniq e
  rw[hc]
  exact ⟨he,o5⟩
structure aZ (p:ℕ) (a:aR c r→ℕ) (g:aR c r→G) where
  mem:∀ k,g k∈lcs G k.1
  gen :∀ i:Fin c,ZA (ZF fun v:Fin (r i)=>
      (Z6 (⟨g ⟨i,v⟩,mem ⟨i,v⟩⟩:lcs G i):e7 G i))=⊤
  minimum:∀ (i:Fin c) (n:ℕ) (y:Fin n→e7 G i),
    ZA (ZF y)=⊤→ r i≤n
  pos:∀ k,1≤a k
  rel:∀ (i:Fin c) (j:Fin (r i)),g ⟨i,j⟩^p^a ⟨i,j⟩∈z8 g i j.val
  nf:ov p a g
def aZ.c_ {p:ℕ} {a:aR c r→ℕ} {g:aR c r→G}
    (S:aZ p a g):kq p c r a:=
  fun k=>S.nf.coord (g k^p^a k)
lemma aZ.CH {p:ℕ} {a:aR c r→ℕ} {g:aR c r→G}
    (S:aZ p a g):kN p a g S.c_ where
  mem:=S.mem
  gen:=S.gen
  irr := fun i v=>yD _ (S.minimum i) v
  pos:=S.pos
  supp :=by
    rintro ⟨i,j⟩ ⟨u,v⟩ h1 h2
    have hs:=(S.nf.q5 i j.val _ (S.rel i j)).1
    refine hs ⟨u,v⟩ ?_
    have pL:u≤ i:=not_lt.mp h1
    rcases lt_or_eq_of_le pL with hu | hu
    · exact Y7 hu
    · subst hu
      exact XQ ⟨rfl,not_lt.mp fun hv=>h2 ⟨rfl,hv⟩⟩
  pow := by
    intro i j
    obtain ⟨hs,o5⟩:=S.nf.q5 i j.val _ (S.rel i j)
    show g ⟨i,j⟩^p^a ⟨i,j⟩=
      (ZR fun v:Fin (r i)=>
        g ⟨i,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨i,v⟩).val).prod*
      (List.ofFn fun u:Fin c=>if i<u then
        (ZR fun v:Fin (r u)=>
          g ⟨u,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val).prod else 1).prod
    have hf:∀ u,u< i→
        cW g (fun h=> (S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) h).val) u=1:=by
      intro u hu
      unfold cW
      refine Xv fun x hx =>?_
      rw[XC]at hx
      obtain ⟨v,rfl⟩:=hx
      have h0:(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val=0:=
        hs ⟨u,v⟩ (Y7 hu)
      show g ⟨u,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val=1
      rw[h0,Y6]
    have qO:=j7 _
      (fun u=>cW g (fun h=> (S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) h).val) u) i hf
    conv_lhs=>rw[← o5]
    exact qO
end Bridge
lemma aZ.JY {G:Type} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ} {g:aR c r→G}
    (S:aZ p a g):S.c_∈kZ p c r a:=
  ⟨G,inferInstance,inferInstance,g,hG,S.CH⟩
end PowerWordGroup
end OMA.SimsLite
namespace OMA.SimsLite
section DataCount
abbrev nV (k n:ℕ):Type:=
  {a:Fin k→Fin (n+1)//(∀ i,0< (a i).val)∧∑ i,(a i).val=n}
def nV.toComp {k n:ℕ} (a:nV k n):Composition n where
  blocks:=ZR (fun i=> (a.1 i).val)
  blocks_pos:=by
    intro x hx
    rw[List.mem_ofFn]at hx
    obtain ⟨i,rfl⟩:=hx
    exact a.2.1 i
  blocks_sum:=by
    rw[List.sum_ofFn]
    exact a.2.2
lemma nV.pH (k n:ℕ):Z8 (@nV.toComp k n):=by
 intro a b h
 have h2:ZR (fun i=> (a.1 i).val)=ZR (fun i=> (b.1 i).val):=
   congrArg RH h
 have h3:=Pd h2
 apply Zu
 funext i
 exact YL (congrFun h3 i)
lemma zG (k n:ℕ):Zq (nV k n)≤2^(n - 1):=
  (Tz _ (nV.pH k n)).trans_eq (composition_card n)
abbrev fG (m c:ℕ):Type:=
  {r :Fin c→Fin (m+1)//(∀ i,0< (r i).val)∧∑ i,(r i).val≤ m}
def fG.toComp {m c:ℕ} (r :fG m c):Composition (m+1) where
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
lemma fG.pH (m c:ℕ):Z8 (@fG.toComp m c):=by
 intro a b h
 have h2:ZR (fun i=> (a.1 i).val) ++[m+1 - ∑ i,(a.1 i).val]
     =ZR (fun i=> (b.1 i).val) ++[m+1 - ∑ i,(b.1 i).val]:=
   congrArg RH h
 have h3:ZR (fun i=> (a.1 i).val)=ZR (fun i=> (b.1 i).val):=
   List.append_inj_left' h2 (by simp)
 have h4:=Pd h3
 apply Zu
 funext i
 exact YL (congrFun h4 i)
lemma Jv (m c:ℕ):Zq (fG m c)≤2^m:=by
 have h:=Tz _ (fG.pH m c)
 rw[composition_card,XI]at h
 exact h
def fG.tot {m c:ℕ} (r :fG m c):ℕ:=∑ i,(r.1 i).val
def fG.r2 {m c:ℕ} (r :fG m c):ℕ:=
  ∑ i∈ZU.filter (fun i:Fin c=>i.val=1),(r.1 i).val
def fG.r3 {m c:ℕ} (r :fG m c):ℕ:=
  ∑ i∈ZU.filter (fun i:Fin c=>2≤ i.val),(r.1 i).val
lemma fG.Nb {m c:ℕ} (r :fG m c):r.r2+r.r3≤ m:=by
 have Gz:Disjoint (ZU.filter (fun i:Fin c=>i.val=1))
     (ZU.filter (fun i:Fin c=>2≤ i.val)):=by
   rw[Finset.disjoint_filter]
   intro i _ h1 h2
   omega
 unfold fG.r2 fG.r3
 rw[← Finset.sum_union Gz]
 exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans r.2.2
lemma qP {ι:Type*} [Fintype ι] (f:ι→ℕ) (A B:ℕ)
    (hA:Zq ι≤A) (hB:∀ i,f i≤B):∑ i,f i≤A*B:=by
 calc ∑ i,f i≤∑ _i:ι,B:=Z9 (fun i _=>hB i)
   _=Zq ι*B:=by simp
   _≤A*B:=Zr hA YD
abbrev JN (m s r₂ R₃:ℕ):Type:=(Fin r₂→Fin (s - 1))×(Fin R₃→Fin m×Fin m)
lemma Me (m s r₂ R₃:ℕ):
    Zq (JN m s r₂ R₃)=(s - 1)^r₂*(m*m)^R₃:=by
 simp only[TI,Fintype.card_fun,Zz]
lemma IZ (m s r₂ R₃:ℕ) (hs:s≤ m+1) (hr :r₂+R₃≤ m):
    Zq (JN m s r₂ R₃)≤ m^(2*m):=by
 rw[Me]
 rcases Yj m with rfl | hm
 · have h1:r₂=0:=by omega
   have h2:R₃=0:=by omega
   subst h1
   subst h2
   simp
 · calc (s - 1)^r₂*(m*m)^R₃≤ m^r₂*(m*m)^R₃:=
         Zr (XR (by omega) _) YD
     _=m^(r₂+2*R₃):=by ring
     _≤ m^(2*m):=Zk hm (by omega)
lemma FH (R m:ℕ):Zq (nV R m)≤2^(m - 1):=
  zG R m
abbrev a9 (m:ℕ):Type:=
  Σ c:Fin (m+1),Σ s:Fin (m+1),Σ r :fG m c.val,
    nV (s.val - 1) r.r2×JN m s.val r.r2 r.r3×nV r.tot m
lemma JE (m:ℕ):
    Zq (a9 m)≤
      (m+1)*((m+1)*(2^m*(2^(m - 1)*(m^(2*m)*2^(m - 1))))):=by
 rw[U4]
 refine qP _ _ _ (by simp) (fun c=>?_)
 rw[U4]
 refine qP _ _ _ (by simp) (fun s=>?_)
 rw[U4]
 refine qP _ _ _ (Jv m c.val) (fun r=>?_)
 have hr :=r.Nb
 rw[TI,TI]
 refine Zr ?_ (Zr ?_ ?_)
 · exact (zG _ _).trans (Zk (by norm_num) (by omega))
 · exact IZ m s.val r.r2 r.r3 (by omega) hr
 · exact FH r.tot m
lemma B4 (m:ℕ) (hm:1≤ m):
    Zq (a9 m)≤(m+1)^(5*m+2):=by
 refine (JE m).trans ?_
 have h1:2^(m - 1)≤2^m:=Zk (by norm_num) (S9 m 1)
 have h2:m^(2*m)≤(m+1)^(2*m):=XR (XV m) _
 have h8:(8:ℕ)≤(m+1)^3:=by
  calc (8:ℕ)=2^3:=by norm_num
    _≤(m+1)^3:=XR (by omega) 3
 have h3:2^m*2^m*2^m≤(m+1)^(3*m):=by
  calc 2^m*2^m*2^m=(2*2*2)^m:=by rw[mul_pow,mul_pow]
    _=8^m:=by norm_num
    _≤((m+1)^3)^m:=XR h8 m
    _=(m+1)^(3*m):=by rw[← X5]
 calc (m +1)*((m+1)*(2^m*(2^(m - 1)*(m^(2*m)*2^(m - 1)))))
     ≤ (m +1)*((m+1)*(2^m*(2^m*((m+1)^(2*m)*2^m)))):=
       Zr YD (Zr YD
         (Zr YD (Zr h1 (Zr h2 h1))))
   _=(m+1)^2*(2^m*2^m*2^m)*(m+1)^(2*m):=by ring
   _ ≤ (m+1)^2*(m+1)^(3*m)*(m+1)^(2*m):=
       Zr (Zr YD h3) YD
   _=(m+1)^(5*m+2):=by ring
end DataCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section ListProd
lemma tq {D:Type u} [Group D]:∀ (n:ℕ) (f:Fin n→D),
    sprod n f=(ZR f).prod
  | 0,f=>by
    show (1:D)=(ZR f).prod
    rw[S6,List.prod_nil]
  | n+1,f=>by
    show f 0*sprod n (fun i=>f i.succ)=_
    rw[tq n,Ut,S5]
lemma KE {D:Type u} {n n':ℕ} (h:n=n') (F:ℕ→D):
    ZR (fun t:Fin n=>F t.val)=ZR (fun t:Fin n'=>F t.val):=by
  subst h
  rfl
lemma Ac {D:Type u} [Monoid D] (r :ℕ→ℕ) (F:ℕ→D):∀ c:ℕ,
    (List.ofFn fun t:Fin (aD r c)=>F t.val).prod=
      (ZR fun i:Fin c=>
        (ZR fun v:Fin (r i.val)=>F (aD r i.val+v.val)).prod).prod
  | 0 => by
    show (ZR fun t:Fin 0=>F t.val).prod=
      (ZR fun i:Fin 0=>
        (ZR fun v:Fin (r i.val)=>F (aD r i.val+v.val)).prod).prod
    rw[S6,S6]
  | c + 1 =>by
    have hL:(ZR fun t:Fin (aD r c+r c)=>F t.val)=
        (ZR fun t:Fin (aD r c)=>F t.val) ++
          (ZR fun v:Fin (r c)=>F (aD r c+v.val)):=by
      rw[List.ofFn_add]<;>rfl
    have hR:(ZR fun i:Fin (c+1)=>
        (ZR fun v:Fin (r i.val)=>F (aD r i.val+v.val)).prod)=
        (ZR fun i:Fin c=>
          (ZR fun v:Fin (r i.val)=>F (aD r i.val+v.val)).prod) ++
          [(ZR fun v:Fin (r c)=>F (aD r c+v.val)).prod]:=by
      rw[List.ofFn_add]<;>rfl
    show (ZR fun t:Fin (aD r c+r c)=>F t.val).prod=_
    rw[hL,hR,OI,OI,Ac r F c,List.prod_singleton]
def sD {D:Type u} [One D] {n:ℕ} (f:Fin n→D) (k:ℕ):D:=
  if h:k<n then f ⟨k,h⟩ else 1
lemma CJ {D:Type u} [One D] {n:ℕ} (f:Fin n→D) (t:Fin n):
    sD f t.val= f t:=by
 unfold sD
 exact dif_pos t.isLt
end ListProd
section LayerQuot
variable {G:Type u} [Group G]
lemma zY (i:ℕ) {N:ℕ} (x:Fin N→G) (hx:∀ v,x v∈lcs G i)
    (h:lcs G i≤ZA (ZF x)⊔lcs G (i+1)):
    ZA (ZF fun v=>
      (Z6 (⟨x v,hx v⟩:lcs G i):e7 G i))=⊤:=by
  set Y:=ZA (ZF fun v=>
      (Z6 (⟨x v,hx v⟩:lcs G i):e7 G i)) with hY
  have hK:lcs G i≤(Y.comap (ZG ((lcs G (i+1)).subgroupOf (lcs G i)))).map
      (lcs G i).subtype:=by
   refine h.trans (sup_le ?_ ?_)
   · rw[ZE]
     rintro _ ⟨v,rfl⟩
     exact ⟨⟨x v,hx v⟩,ZD ⟨v,rfl⟩,rfl⟩
   · intro z hz
     have La:z∈lcs G i:=bC (XV i) hz
     refine ⟨⟨z,La⟩,?_,rfl⟩
     show ZG ((lcs G (i+1)).subgroupOf (lcs G i)) ⟨z,La⟩∈Y
     have h1:ZG ((lcs G (i+1)).subgroupOf (lcs G i)) ⟨z,La⟩=1:=
       (Yf _).mpr (ZT.mpr hz)
     rw[h1]
     exact Y.one_mem
  rw[Yo]
  rintro q -
  obtain ⟨z,rfl⟩:=Z3 q
  obtain ⟨z',La,hzz⟩:=hK z.2
  have hz2:z'=z:=Zu hzz
  rw[hz2]at La
  exact La
lemma t7 (i:ℕ) {N:ℕ} (x:Fin N→lcs G i)
    (h:ZA (ZF fun v=> (Z6 (x v):e7 G i))=⊤):
    lcs G i≤ZA (ZF fun v=> (x v:G))⊔lcs G (i+1):=by
  intro z hz
  set M:=ZA (ZF fun v=> (x v:G))⊔lcs G (i+1) with hM
  have cO:ZA (ZF fun v=> (Z6 (x v):e7 G i))≤
      (M.subgroupOf (lcs G i)).map
        (ZG ((lcs G (i+1)).subgroupOf (lcs G i))):=by
    rw[ZE]
    rintro _ ⟨v,rfl⟩
    exact ⟨x v,ZT.mpr
      (ZK (ZD ⟨v,rfl⟩)),rfl⟩
  rw[h]at cO
  obtain ⟨z',La,hzz⟩:=
    cO (ZO (Z6 (⟨z,hz⟩:lcs G i):e7 G i))
  have aew:(Z6 z':e7 G i)=Z6 ⟨z,hz⟩:=hzz
  have h2:z'⁻¹*⟨z,hz⟩∈(lcs G (i+1)).subgroupOf (lcs G i):=WX.mp aew
  have jM:((z'⁻¹*⟨z,hz⟩:lcs G i):G)∈lcs G (i+1):=ZT.mp h2
  have adR:(z':G)∈M:=ZT.mp La
  have h3:z=(z':G)*((z'⁻¹*⟨z,hz⟩:lcs G i):G):=by simp
  rw[h3]
  exact M.mul_mem adR (ZL jM)
lemma LQ [Finite G] {p:ℕ} (hp:p.Prime) (i R:ℕ)
    (dS:p^R*ZB (dC p G i)=ZB (lcs G i))
    (N:ℕ) (y:Fin N→e7 G i) (hy:ZA (ZF y)=⊤):R≤N:=by
 choose x hx using fun v=>Z3 (y v)
 have IE:ZA (ZF fun v=> (Z6 (x v):e7 G i))=⊤:=by
   have e:(fun v=> (Z6 (x v):e7 G i))=y:= funext hx
   rw[e]
   exact hy
 have h1:=t7 i x IE
 have hxN:∀ j,sD (fun v=> (x v:G)) j∈lcs G i:=by
   intro j
   unfold sD
   split_ifs
   · exact (x _).2
   · exact one_mem _
 have wc:ZF (fun v=> (x v:G))⊆sD (fun v=> (x v:G)) '' ZH N:=by
   rintro _ ⟨v,rfl⟩
   exact ⟨v.val,v.isLt,CJ _ v⟩
 have h2:lcs G i≤ZA (sD (fun v=> (x v:G)) '' ZH N)⊔dC p G i:=
   h1.trans (sup_le_sup (ZS wc) (dD p i))
 have hN:∀ j,(ZA (sD (fun v=> (x v:G)) '' ZH j)⊔
     dC p G i).Normal:= fun j=>
   jU p i _ (by rintro _ ⟨k, -,rfl⟩; exact hxN k)
 have h3:=lC hp.pos (dC p G i) (sD (fun v=> (x v:G))) hN
   (fun j=>qG p i _ (hxN j)) N
 have h4:ZB (lcs G i)≤p^N*ZB (dC p G i):=
   (YG h2).trans h3
 have h5:0<ZB (dC p G i):=Xi
 rw[← dS]at h4
 have h6:p^R≤p^N:=Nat.le_of_mul_le_mul_right h4 h5
 by_contra hRN
 have e3:p^(N+1)≤p^R:=Zk hp.pos (by omega)
 have e1:p^(N+1)=p^N*p:=Xr p N
 have e2:p^N*2≤p^N*p:=VR _ hp.two_le
 have e4:0<p^N:=XD hp.pos N
 rw[e1]at e3
 linarith
end LayerQuot
section Reindex
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
abbrev mL (r :ℕ→ℕ) (c:ℕ):Fin c→ℕ:= fun i=>r i.val
lemma Mo {n:ℕ} (r :ℕ→ℕ) {c:ℕ} (hn:n=aD r c) (i:Fin c)
    (v:Fin (r i.val)):aD r i.val+v.val<n:=by
 have h1:=g5 r (show i.val+1≤ c from i.isLt)
 rw[dM]at h1
 have h2:=v.isLt
 omega
def A4 {n:ℕ} (r :ℕ→ℕ) {c:ℕ} (hn:n=aD r c) (k:aR c (mL r c)):Fin n:=
  ⟨aD r k.1.val+k.2.val,Mo r hn k.1 k.2⟩
lemma aE.FZ (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k:aR c (mL r c)):d.lv (A4 r hn k)=k.1.val:=
  (hS.fD (A4 r hn k) k.1.val).mpr
    ⟨W5 _ _,VN k.2.isLt _⟩
lemma aE.GK (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c) (t:Fin d.n):
    d.lv t<c:=by
 by_contra h
 have h1:=g5 r (not_lt.mp h)
 have h2:=((hS.fD t (d.lv t)).mp rfl).1
 have h3:=t.isLt
 omega
lemma aE.aay (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c):
    Z8 (A4 r hn):=by
 rintro ⟨i,v⟩ ⟨i',v'⟩ h
 have e1:d.lv (A4 r hn ⟨i,v⟩)=i.val:=hS.FZ hn ⟨i,v⟩
 have e2:d.lv (A4 r hn ⟨i',v'⟩)=i'.val:=hS.FZ hn ⟨i',v'⟩
 rw[h]at e1
 have h1:i=i':=YL (e1.symm.trans e2)
 subst h1
 have h3:aD r i.val+v.val=aD r i.val+v'.val:= congrArg Ty h
 have h2:v=v':=YL (by omega)
 subst h2
 rfl
lemma aE.Q3 (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c):
    Zn (A4 r hn):=by
 intro t
 obtain ⟨h1,h2⟩:=(hS.fD t (d.lv t)).mp rfl
 refine ⟨⟨⟨d.lv t,hS.GK hn t⟩,⟨t.val - aD r (d.lv t),
   show t.val - aD r (d.lv t)< r (d.lv t) by omega⟩⟩,?_⟩
 apply YL
 show aD r (d.lv t)+(t.val - aD r (d.lv t))=t.val
 omega
noncomputable def aE.aV (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c):
    aR c (mL r c)≃Fin d.n:=
  Pq (A4 r hn) ⟨hS.aay hn,hS.Q3 hn⟩
lemma aE.j4 (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k:aR c (mL r c)):d.lv (hS.aV hn k)=k.1.val:=
  hS.FZ hn k
lemma aE.o3 (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k:aR c (mL r c)):(hS.aV hn k).val=aD r k.1.val+k.2.val:=rfl
lemma aE.Kz (hS:aE p u d X r) (t:Fin d.n):X t∈lcs G (d.lv t):=
  ow d hS.valid.toqN X hS.e9.Fk t
lemma aE.acH (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k:aR c (mL r c)):X (hS.aV hn k)∈lcs G k.1:=by
 have h:=hS.Kz (hS.aV hn k)
 rwa[hS.j4 hn k]at h
lemma aE.xB (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (e:aR c (mL r c)→ℕ):
    ju (fun k=>X (hS.aV hn k)) e=gN X (fun t=>e ((hS.aV hn).symm t)):=by
  have h1:gN X (fun t=>e ((hS.aV hn).symm t))=
      (ZR fun t:Fin d.n=>
        sD (fun t=>X t^e ((hS.aV hn).symm t)) t.val).prod:=by
    unfold gN
    rw[tq]
    simp only[CJ]
  have key:∀ (i:Fin c) (v:Fin (r i.val)),
      sD (fun t=>X t^e ((hS.aV hn).symm t)) (aD r i.val+v.val)=
        X (hS.aV hn ⟨i,v⟩)^e ⟨i,v⟩:=by
    intro i v
    have h:=CJ (fun t=>X t^e ((hS.aV hn).symm t)) (hS.aV hn ⟨i,v⟩)
    refine h.trans ?_
    show X (hS.aV hn ⟨i,v⟩)^e ((hS.aV hn).symm (hS.aV hn ⟨i,v⟩))=_
    rw[UB]
  rw[h1,KE hn,Ac r _ c]
  unfold ju cW
  simp only[key]
lemma aE.Jj (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (i:Fin c) (j:ℕ):
    ZA (X '' jw d i.val (aD r i.val+j))≤
      z8 (fun k=>X (hS.aV hn k)) i j:=by
  rw[ZE]
  rintro _ ⟨t,ht,rfl⟩
  rcases (dY d).mp ht with h | ⟨h1,h2⟩
  · exact ZL
      (bC (show i.val+1≤d.lv t by omega) (hS.Kz t))
  · apply ZK
    apply ZD
    obtain ⟨⟨i',v'⟩,rfl⟩:=(hS.aV hn).surjective t
    have hk:d.lv (hS.aV hn ⟨i',v'⟩)=i'.val:=hS.j4 hn _
    have hii:i'=i:=YL (by omega)
    subst hii
    have h3:aD r i'.val+v'.val<aD r i'.val+j:=h2
    exact ⟨v',by omega,rfl⟩
lemma aE.aaG (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (i:Fin c) (j:ℕ):
    z8 (fun k=>X (hS.aV hn k)) i j≤
      ZA (X '' jw d i.val (aD r i.val+j)):=by
  refine sup_le ?_ ?_
  · rw[ZE]
    rintro _ ⟨v,hv,rfl⟩
    apply ZD
    refine ⟨hS.aV hn ⟨i,v⟩,?_,rfl⟩
    refine (dY d).mpr (XQ ⟨(hS.j4 hn ⟨i,v⟩).symm,?_⟩)
    show aD r i.val+v.val<aD r i.val+j
    omega
  · refine (hS.Kd (i.val+1) (by omega)).trans (ZS ?_)
    rintro _ ⟨t,ht,rfl⟩
    have iQ:i.val+1≤d.lv t:=ht
    exact ⟨t,(dY d).mpr (Y7 (by omega)),rfl⟩
noncomputable def aE.toNF (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c):
    ov p (fun k=>d.a (hS.aV hn k)) (fun k=>X (hS.aV hn k)) where
  coord x h:=⟨XP (hS.k8 x) (hS.aV hn h),
    (Ym (hS.k8 x)).1 _⟩
  uniq e:=by
    funext h
    apply YL
    obtain ⟨hb,hx⟩:=Ym
      (hS.k8 (ju (fun k=>X (hS.aV hn k)) fun h=> (e h).val))
    have Io:∀ t,(e ((hS.aV hn).symm t)).val<p^d.a t:=by
     intro t
     have h0:=(e ((hS.aV hn).symm t)).isLt
     simpa only[Rb] using h0
    have h2:=hS.s7 _ (fun t=> (e ((hS.aV hn).symm t)).val) hb Io
      (hx.symm.trans (hS.xB hn _))
    show XP (hS.k8 (ju (fun k=>X (hS.aV hn k))
      fun h=> (e h).val)) (hS.aV hn h)=(e h).val
    rw[h2]
    show (e ((hS.aV hn).symm (hS.aV hn h))).val=(e h).val
    rw[UB]
  sub := by
    intro i j x hx
    obtain ⟨e0,L9,hbd,kH⟩:=
      hS.aau i.val (aD r i.val+j) x (hS.aaG hn i j hx)
    refine ⟨fun h=> ⟨e0 (hS.aV hn h),hbd (hS.aV hn h)⟩,?_,?_⟩
    · rintro ⟨i',v'⟩ hh
      show e0 (hS.aV hn ⟨i',v'⟩)=0
      by_contra d8
      have hm:=(dY d).mp (L9 _ d8)
      have hk:d.lv (hS.aV hn ⟨i',v'⟩)=i'.val:=hS.j4 hn _
      have hv:(hS.aV hn ⟨i',v'⟩).val=aD r i'.val+v'.val:=rfl
      rcases hh with h1 | ⟨h1,h2⟩
      · have pL:i'.val< i.val:=h1
        omega
      · have pL:i'=i:=h1
        subst pL
        have jM:j≤v'.val:=h2
        omega
    · rw[hS.xB hn,kH]
      refine congrArg (gN X) (funext fun t=>?_)
      show e0 (hS.aV hn ((hS.aV hn).symm t))=e0 t
      rw[Rb]
noncomputable def aE.toaZ [Finite G] (hp:p.Prime) (hS:aE p u d X r)
    {c:ℕ} (hn:d.n=aD r c):
    aZ p (fun k=>d.a (hS.aV hn k)) (fun k=>X (hS.aV hn k)) where
  mem:=hS.acH hn
  gen :=by
    intro i
    refine zY i.val (fun v=>X (hS.aV hn ⟨i,v⟩))
      (fun v=>hS.acH hn ⟨i,v⟩) ?_
    refine (hS.w7 i.val).trans (sup_le_sup_right (ZS ?_) _)
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨⟨i',v'⟩,rfl⟩:=(hS.aV hn).surjective t
    have hk:d.lv (hS.aV hn ⟨i',v'⟩)=i'.val:=hS.j4 hn _
    have iQ:d.lv (hS.aV hn ⟨i',v'⟩)=i.val:=ht
    have hii:i'=i:=YL (by omega)
    subst hii
    exact ⟨v',rfl⟩
  minimum:= fun i N y hy=>LQ hp i.val (r i.val) (hS.kV i.val) N y hy
  pos:= fun k=>hS.a_pos _
  rel:=by
    intro i j
    show X (hS.aV hn ⟨i,j⟩)^p^d.a (hS.aV hn ⟨i,j⟩)∈_
    rw[hS.e9.pow (hS.aV hn ⟨i,j⟩)]
    refine hS.Jj hn i j.val (vI X _ _ fun t ht=>?_)
    have hpr :=hS.valid.GZ _ t ht
    have hk:d.lv (hS.aV hn ⟨i,j⟩)=i.val:=hS.j4 hn _
    have hv:(hS.aV hn ⟨i,j⟩).val=aD r i.val+j.val:=rfl
    unfold aO.prec at hpr
    refine (dY d).mpr ?_
    omega
  nf:=hS.toNF hn
end Reindex
section NatLemmas
lemma Ov (r :ℕ→ℕ):∀ c,(∀ w<c,1≤ r w)→ c≤aD r c
  | 0,_=>Zv _
  | c+1,h=>by
    have h1:= Ov r c (fun w hw=>h w (by omega))
    have h2:=h c (by omega)
    rw[dM]
    omega
lemma k9 {r r':ℕ→ℕ} {c:ℕ} (h:∀ w<c,r w=r' w):
    ∀ w≤ c,aD r w=aD r' w
  | 0,_=>rfl
  | w+1,hw=>by
    rw[dM,dM,k9 h w (by omega),h w (by omega)]
lemma nC (r :ℕ→ℕ):∀ c,∑ i:Fin c,r i.val=aD r c
  | 0=>by
    rw[OJ]
    rfl
  | c+1=>by
    rw[PL]
    simp only[OW,Fin.val_last]
    rw[nC r c,dM]
lemma x5 (r :ℕ→ℕ) (k:ℕ):∀ c,k≤ c→
    ∑ i:Fin c,(if k≤ i.val then r i.val else 0)=aD r c - aD r k
  | 0,hk=>by
    rw[OJ]
    have Br :k=0:=by omega
    subst Br
    rfl
  | c + 1,hk=>by
    rcases XU k (c+1) with f5 | Ep
    · rw[PL]
      simp only[OW,Fin.val_last]
      rw[x5 r k c (by omega),if_pos (show k≤ c by omega),dM]
      have:=g5 r (show k≤ c by omega)
      omega
    · have lQ:k= c+1:=by omega
      subst lQ
      have hz:∀ i:Fin (c+1),(if c+1≤ i.val then r i.val else 0)=0:=
        fun i=>if_neg (by have:=i.isLt; omega)
      rw[Finset.sum_eq_zero (fun i _=>hz i),Nat.sub_self]
lemma jQ (f:ℕ→ℕ) (R:ℕ) (hf:∀ i j,i≤j→j<R→ f i≤f j)
    (k j:ℕ) (hj:j<R):
    f j<k↔j< ((ZM R).filter (fun i=>f i<k)).card:=by
  constructor
  · intro h
    have jp:ZM (j+1)⊆(ZM R).filter (fun i=>f i<k):=by
      intro i hi
      rw[Zt]at hi
      rw[ZI,Zt]
      exact ⟨by omega,VT (hf i j (by omega) hj) h⟩
    have h1:=VB jp
    rw[Xf]at h1
    omega
  · intro h
    by_contra hk
    have lQ:k≤f j:=not_lt.mp hk
    have jp:(ZM R).filter (fun i=>f i<k)⊆ZM j:=by
      intro i hi
      rw[ZI,Zt]at hi
      rw[Zt]
      by_contra hij
      have h2:=hf j i (by omega) hi.1
      omega
    have h1:=VB jp
    rw[Xf]at h1
    omega
lemma p7 (f:ℕ→ℕ) (R k:ℕ):
    ((ZM R).filter (fun i=>f i<k)).card=
      ∑ b∈ZM k,((ZM R).filter (fun i=>f i=b)).card:=by
  have oc:∀ i∈(ZM R).filter (fun i=>f i<k),f i∈ZM k:=by
    intro i hi
    rw[ZI]at hi
    exact Zt.mpr hi.2
  rw[Wd oc]
  refine Zw rfl fun b hb=>?_
  rw[Finset.filter_filter]
  congr 1
  apply R6
  intro i _
  rw[Zt]at hb
  constructor
  · rintro ⟨-,h⟩
    exact h
  · intro h
    exact ⟨by omega,h⟩
lemma vY (f g:ℕ→ℕ) (R:ℕ) (hf:∀ i j,i≤j→j<R→ f i≤f j)
    (hg:∀ i j,i≤j→j<R→ g i≤g j)
    (pC:∀ k,((ZM R).filter (fun i=>f i=k)).card=
      ((ZM R).filter (fun i=>g i=k)).card)
    (j:ℕ) (hj:j<R):f j=g j:=by
  have hA:∀ k,((ZM R).filter (fun i=>f i<k)).card=
      ((ZM R).filter (fun i=>g i<k)).card:=by
    intro k
    rw[p7,p7]
    exact Zw rfl fun b _=>pC b
  have h1:=(jQ f R hf (f j+1) j hj).mp (XZ _)
  rw[hA]at h1
  have pL:=(jQ g R hg (f j+1) j hj).mpr h1
  have h2:=(jQ g R hg (g j+1) j hj).mp (XZ _)
  rw[← hA]at h2
  have jM:=(jQ f R hf (g j+1) j hj).mpr h2
  omega
end NatLemmas
section DataBridge
instance Nv (d:aO) (t k:Fin d.n):Decidable (d.q8 t k):=by
 unfold aO.q8
 infer_instance
def aO.normalize (d:aO):aO where
  n:=d.n
  s:=d.s
  lv:=d.lv
  df:= fun t=>if 1≤d.lv t then d.df t else (t,t)
  a:=d.a
  b:=d.b
  c:= fun t k v=>if d.q8 t k then d.c t k v else 0
lemma aO.Gi {d:aO} (hd:d.Valid) (t k v:Fin d.n)
    (h:(if d.q8 t k then d.c t k v else 0)≠0):d.lv t<d.lv v:=by
  split_ifs at h with hr
  · exact hd.Aa t k v h
  · exact absurd rfl h
lemma aO.JJ {d:aO} (hd:d.Valid):d.normalize.Valid where
  mono:=hd.mono
  yA:=hd.yA
  core:=hd.core
  wY := fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact hd.wY t ht
  kR := fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact hd.kR t ht
  oR := fun t ht=>by
    have iQ:d.lv t=1:=ht
    have e:d.normalize.df t=d.df t:=if_pos (show 1≤d.lv t by omega)
    rw[e]
    exact hd.oR t ht
  GZ:=hd.GZ
  Aa:= fun t k v h=>aO.Gi hd t k v h
lemma aO.s5 {G:Type u} [Group G] {p:ℕ} {d:aO}
    {X:Fin d.n→G} (h:h_ p d X):h_ p d.normalize X where
  card:=h.card
  gen:=h.gen
  Fk := fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact h.Fk t ht
  pow:=h.pow
  DZ := fun t k ht hk Ml=>by
    have hrec:d.q8 t k:=Y7 ⟨ht,hk,Ml⟩
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.DZ t k ht hk Ml
  Iq := fun t k ht hk=>by
    have iQ:d.lv t=1:=ht
    have e:d.normalize.df t=d.df t:=if_pos (show 1≤d.lv t by omega)
    rw[e]at hk
    have hrec:d.q8 t k:=XQ (Y7 ⟨ht,hk⟩)
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.Iq t k ht hk
  IG := fun t k ht hk=>by
    have hrec:d.q8 t k:=XQ (XQ ⟨ht,hk⟩)
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.IG t k ht hk
lemma aO.normalize_eq {d1 d2:aO} (hn:d1.n=d2.n) (hs:d1.s=d2.s)
    (jV:∀ i (h1:i<d1.n) (h2:i<d2.n),d1.lv ⟨i,h1⟩=d2.lv ⟨i,h2⟩)
    (lH :∀ i (h1:i<d1.n) (h2:i<d2.n),1≤d1.lv ⟨i,h1⟩→
      (d1.df ⟨i,h1⟩).1.val=(d2.df ⟨i,h2⟩).1.val∧
        (d1.df ⟨i,h1⟩).2.val=(d2.df ⟨i,h2⟩).2.val)
    (ha:∀ i (h1:i<d1.n) (h2:i<d2.n),d1.a ⟨i,h1⟩=d2.a ⟨i,h2⟩)
    (hb:∀ i j (h1:i<d1.n) (pL:j<d1.n) (h2:i<d2.n) (jM:j<d2.n),
      d1.b ⟨i,h1⟩ ⟨j,pL⟩=d2.b ⟨i,h2⟩ ⟨j,jM⟩)
    (hc :∀ i j k (h1:i<d1.n) (pL:j<d1.n) (aaZ:k<d1.n) (h2:i<d2.n)
      (jM:j<d2.n) (abu:k<d2.n),
      (if d1.q8 ⟨i,h1⟩ ⟨j,pL⟩ then d1.c ⟨i,h1⟩ ⟨j,pL⟩ ⟨k,aaZ⟩ else 0)=
        (if d2.q8 ⟨i,h2⟩ ⟨j,jM⟩ then d2.c ⟨i,h2⟩ ⟨j,jM⟩ ⟨k,abu⟩ else 0)):
    d1.normalize=d2.normalize:=by
  obtain ⟨n1,s1,lv1,df1,a1,b1,c1⟩:=d1
  obtain ⟨n2,s2,lv2,df2,a2,b2,c2⟩:=d2
  have hn':n1=n2:=hn
  subst hn'
  have hs':s1=s2:=hs
  subst hs'
  have elv:lv1=lv2:= funext fun t=>jV t.val t.isLt t.isLt
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
      have h':=lH t.val t.isLt t.isLt h
      exact V7 (YL h'.1) (YL h'.2)
    · rw[if_neg h,if_neg h]
  have ec:(fun t k v=>if aO.q8 ⟨n1,s1,lv1,df1,a1,b1,c1⟩ t k then c1 t k v
      else 0)=(fun t k v=>if aO.q8 ⟨n1,s1,lv1,df2,a1,b1,c2⟩ t k then c2 t k v
      else 0):=by
    funext t k v
    exact hc t.val k.val v.val t.isLt k.isLt v.isLt t.isLt k.isLt v.isLt
  show aO.mk n1 s1 lv1 (fun t=>if 1≤lv1 t then df1 t else (t,t)) a1 b1
      (fun t k v=>if aO.q8 ⟨n1,s1,lv1,df1,a1,b1,c1⟩ t k then c1 t k v else 0)=
    aO.mk n1 s1 lv1 (fun t=>if 1≤lv1 t then df2 t else (t,t)) a1 b1
      (fun t k v=>if aO.q8 ⟨n1,s1,lv1,df2,a1,b1,c2⟩ t k then c2 t k v else 0)
  rw[edf,ec]
lemma N6 {G H:Type u} [Group G] [Group H] [Finite G] [Finite H] {p:ℕ}
    (hp:p.Prime) (D1 D2:aO) (e:D1=D2) (hv:D1.Valid) (Y1:Fin D1.n→G)
    (Y2:Fin D2.n→H) (k1:h_ p D1 Y1) (k2:h_ p D2 Y2):
    Nonempty (G≃*H):=by
 subst e
 exact LI hp D1 hv Y1 Y2 k1 k2
def b9 (d:aO) (r :ℕ→ℕ) (j:ℕ):ℕ:=
  if h:aD r 1+j<d.n then (d.df ⟨aD r 1+j,h⟩).2.val else 0
def t5 (d:aO) (r :ℕ→ℕ) (j:ℕ):ℕ:=
  if h:aD r 1+j<d.n then (d.df ⟨aD r 1+j,h⟩).1.val else 0
def rW (d:aO) (r :ℕ→ℕ) (j:ℕ):ℕ×ℕ:=
  if h:aD r 2+j<d.n then ((d.df ⟨aD r 2+j,h⟩).1.val,(d.df ⟨aD r 2+j,h⟩).2.val)
  else (0,0)
def lL (d:aO) (j:ℕ):ℕ:=if h:j<d.n then d.a ⟨j,h⟩ else 0
def tB (d:aO) (i j:ℕ):ℕ:=
  if h:i<d.n∧j<d.n then d.b ⟨i,h.1⟩ ⟨j,h.2⟩ else 0
def jd (d:aO) (i j k:ℕ):ℕ:=
  if h:i<d.n∧j<d.n∧k<d.n then
    (if d.q8 ⟨i,h.1⟩ ⟨j,h.2.1⟩ then d.c ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩ else 0)
  else 0
def og (d:aO) (r :ℕ→ℕ) (k:ℕ):ℕ:=
  ((ZM (r 1)).filter (fun j=>b9 d r j=k+1)).card
lemma kQ (d:aO) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:aD r 1+j=t.val):
    b9 d r j=(d.df t).2.val:=by
 have h:aD r 1+j<d.n:=by have:=t.isLt; omega
 unfold b9
 rw[dif_pos h]
 have e:(⟨aD r 1+j,h⟩:Fin d.n)=t:=YL hj
 rw[e]
lemma r5 (d:aO) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:aD r 1+j=t.val):
    t5 d r j=(d.df t).1.val:=by
 have h:aD r 1+j<d.n:=by have:=t.isLt; omega
 unfold t5
 rw[dif_pos h]
 have e:(⟨aD r 1+j,h⟩:Fin d.n)=t:=YL hj
 rw[e]
lemma Qj (d:aO) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:aD r 2+j=t.val):
    rW d r j=((d.df t).1.val,(d.df t).2.val):=by
 have h:aD r 2+j<d.n:=by have:=t.isLt; omega
 unfold rW
 rw[dif_pos h]
 have e:(⟨aD r 2+j,h⟩:Fin d.n)=t:=YL hj
 rw[e]
lemma yP {d:aO} {m:ℕ} (hsum:∑ t,d.a t=m) (t:Fin d.n):d.a t≤ m:=by
 rw[← hsum]
 exact Finset.single_le_sum (f:=d.a) (fun t _=>Zv _) (Zb t)
lemma acu {d:aO} {m:ℕ} (hsum:∑ t,d.a t=m) (j:ℕ):lL d j≤ m:=by
 unfold lL
 split_ifs with h
 · exact yP hsum _
 · exact Zv _
lemma acS {d:aO} {p m:ℕ} (hp:0<p) (hb:d.Bounded p) (hsum:∑ t,d.a t=m)
    (i j:ℕ):tB d i j<p^m:=by
 unfold tB
 split_ifs with h
 · exact lt_of_lt_of_le (hb.1 _ _) (Zk hp (yP hsum _))
 · exact XD hp m
lemma ab6 {d:aO} {p m:ℕ} (hp:0<p) (hb:d.Bounded p) (hsum:∑ t,d.a t=m)
    (i j k:ℕ):jd d i j k<p^m:=by
 unfold jd
 split_ifs
 · exact lt_of_lt_of_le (hb.2 _ _ _) (Zk hp (yP hsum _))
 · exact XD hp m
 · exact XD hp m
lemma O1 (d:aO) (r :ℕ→ℕ) {m:ℕ} (bZ:d.n≤ m) (hm:0< m) (j:ℕ):
    (rW d r j).1< m∧(rW d r j).2< m:=by
 unfold rW
 split_ifs with h
 · exact ⟨lt_of_lt_of_le (d.df ⟨aD r 2+j,h⟩).1.isLt bZ,
     lt_of_lt_of_le (d.df ⟨aD r 2+j,h⟩).2.isLt bZ⟩
 · exact ⟨hm,hm⟩
abbrev cQ (p m:ℕ):Type:=
  Σ D:a9 m,(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))×
    (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
def rdC {p m:ℕ} (D:cQ p m):ℕ:=D.1.1.val
def rdS {p m:ℕ} (D:cQ p m):ℕ:=D.1.2.1.val
def rdR {p m:ℕ} (D:cQ p m) (i:ℕ):ℕ:=
  if h:i<D.1.1.val then (D.1.2.2.1.1 ⟨i,h⟩).val else 0
def QO {p m:ℕ} (D:cQ p m) (k:ℕ):ℕ:=
  if h:k<D.1.2.1.val - 1 then (D.1.2.2.2.1.1 ⟨k,h⟩).val else 0
def rdF {p m:ℕ} (D:cQ p m) (j:ℕ):ℕ:=
  if h:j<D.1.2.2.1.r2 then (D.1.2.2.2.2.1.1 ⟨j,h⟩).val else 0
def rdP {p m:ℕ} (D:cQ p m) (j:ℕ):ℕ×ℕ:=
  if h:j<D.1.2.2.1.r3 then
    ((D.1.2.2.2.2.1.2 ⟨j,h⟩).1.val,(D.1.2.2.2.2.1.2 ⟨j,h⟩).2.val)
  else (0,0)
def rdA {p m:ℕ} (D:cQ p m) (j:ℕ):ℕ:=
  if h:j<D.1.2.2.1.tot then (D.1.2.2.2.2.2.1 ⟨j,h⟩).val else 0
def rdB {p m:ℕ} (D:cQ p m) (i j:ℕ):ℕ:=
  if h:i<D.1.2.2.1.tot∧j<D.1.2.2.1.tot then (D.2.1 ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
def QF {p m:ℕ} (D:cQ p m) (i j k:ℕ):ℕ:=
  if h:i<D.1.2.2.1.tot∧j<D.1.2.2.1.tot∧k<D.1.2.2.1.tot then
    (D.2.2 ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩).val
  else 0
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.QS (hS:aE p u d X r):∃ c,aD r c=d.n:=by
 obtain ⟨c,hc⟩:=hS.acv
 exact ⟨c,hc.symm⟩
noncomputable def aE.nL (hS:aE p u d X r):ℕ:=Nat.find hS.QS
lemma aE.g6 (hS:aE p u d X r):aD r hS.nL=d.n:=Nat.find_spec hS.QS
lemma aE.acr (hS:aE p u d X r) {w:ℕ} (hw:w<hS.nL):aD r w≠d.n:=
  Nat.find_min hS.QS hw
lemma aE.Nq [Finite G] (hp:p.Prime) (hS:aE p u d X r):
    ∀ w<hS.nL,0< r w:=by
 intro w hw
 by_contra h0
 have j_:r w=0:=by omega
 have f5:aD r w<d.n:=by
  have h1:=g5 r hw.le
  have h2:=hS.acr hw
  rw[hS.g6]at h1
  omega
 have h4:(⟨aD r w,f5⟩:Fin d.n).val=aD r w:=rfl
 have hw0:w<d.lv ⟨aD r w,f5⟩:=by
  obtain ⟨h1,h2⟩:=(hS.fD ⟨aD r w,f5⟩ (d.lv ⟨aD r w,f5⟩)).mp rfl
  by_contra cO
  have ad7:d.lv ⟨aD r w,f5⟩≤w:=not_lt.mp cO
  rcases lt_or_eq_of_le ad7 with hl | he
  · have h3:=g5 r (show d.lv ⟨aD r w,f5⟩+1≤w by omega)
    rw[dM]at h3
    omega
  · rw[he,j_]at h2
    omega
 have jp:lcs G w≤lcs G (w+1):=by
  refine (hS.w7 w).trans (sup_le ?_ YD)
  rw[ZE]
  rintro _ ⟨t,ht,rfl⟩
  exfalso
  have:=(hS.fD t w).mp ht
  omega
 have ada:∀ k,lcs G (w+k)=lcs G w:=by
  intro k
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw[show w+(k+1)=(w+k)+1 from rfl,lcs_succ,ih, ← lcs_succ]
    exact le_antisymm (bC (XV w)) jp
 have:Fact p.Prime:=⟨hp⟩
 have nD:IsPGroup p G:=YK hS.e9.card
 have:XN G:=nD.isNilpotent
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=
   Yh.mp inferInstance
 have rL:lcs G w=⊥:=by
  rw[← ada N]
  exact le_bot_iff.mp ((bC (Nat.le_add_left N w)).trans (WT hN))
 have hX:X ⟨aD r w,f5⟩=1:=by
  have h:=bC hw0.le (hS.Kz ⟨aD r w,f5⟩)
  rw[rL]at h
  exact WB.mp h
 apply hS.E0 ⟨aD r w,f5⟩
 rw[hX]
 exact one_mem _
lemma aE.acW (hS:aE p u d X r) (w:ℕ) (hw:w<hS.nL):r w≤d.n:=by
 have h1:=g5 r (show w+1≤hS.nL from hw)
 rw[dM,hS.g6]at h1
 omega
lemma aE.abW [Finite G] (hp:p.Prime) (hS:aE p u d X r):hS.nL≤d.n:=by
 have h:= Ov r hS.nL (fun w hw=>hS.Nq hp w hw)
 rw[hS.g6]at h
 exact h
lemma aE.tA (hS:aE p u d X r) (bU:2≤d.s):1<hS.nL:=by
 obtain ⟨t,ht, -⟩:=hS.F3 1 YD (by omega)
 have:=hS.GK hS.g6.symm t
 omega
lemma aE.EI (hS:aE p u d X r) (bU:2≤d.s):aD r 2≤d.n:=by
 have h:=g5 r (show 2≤hS.nL from hS.tA bU)
 rw[hS.g6]at h
 exact h
lemma aE.pO (hS:aE p u d X r) (bU:2≤d.s) (j:ℕ) (hj:j< r 1):
    ∃ h:aD r 1+j<d.n,d.lv ⟨aD r 1+j,h⟩=1:=by
 have h2:=hS.EI bU
 have e:aD r 2=aD r 1+r 1:=dM r 1
 exact ⟨by omega,(hS.fD _ 1).mpr ⟨W5 _ _,VN hj _⟩⟩
lemma aE.jC (hS:aE p u d X r) (bU:2≤d.s) (j:ℕ) (hj:j< r 1):
    1≤b9 d r j∧b9 d r j<d.s:=by
 obtain ⟨h,hl⟩:=hS.pO bU j hj
 rw[kQ d r ⟨aD r 1+j,h⟩ j rfl]
 have h1:(d.df ⟨aD r 1+j,h⟩).1.val< (d.df ⟨aD r 1+j,h⟩).2.val:=
   hS.valid.oR _ hl
 exact ⟨by omega,hS.valid.kR _ (by omega)⟩
lemma aE.DN (hS:aE p u d X r) (bU:2≤d.s) (j:ℕ) (hj:j< r 1):
    t5 d r j<d.s - 1:=by
 obtain ⟨h,hl⟩:=hS.pO bU j hj
 rw[r5 d r ⟨aD r 1+j,h⟩ j rfl]
 have h1:(d.df ⟨aD r 1+j,h⟩).1.val< (d.df ⟨aD r 1+j,h⟩).2.val:=
   hS.valid.oR _ hl
 have h2:=hS.valid.kR ⟨aD r 1+j,h⟩ (by omega)
 omega
lemma aE.w_ (hS:aE p u d X r) (bU:2≤d.s) (i j:ℕ) (hij:i≤j)
    (hj:j< r 1):b9 d r i≤b9 d r j:=by
 obtain ⟨h1,HR⟩:=hS.pO bU i (by omega)
 obtain ⟨h2,hl2⟩:=hS.pO bU j hj
 rw[kQ d r ⟨aD r 1+i,h1⟩ i rfl,kQ d r ⟨aD r 1+j,h2⟩ j rfl]
 exact hS.IQ _ _ HR hl2 (show aD r 1+i≤aD r 1+j by omega)
lemma aE.aas (hS:aE p u d X r) (k:ℕ) (hk:k<d.s - 1):
    0<og d r k:=by
 obtain ⟨t,ht,EK⟩:=hS.F3 (k+1) (by omega) (by omega)
 obtain ⟨a1,a2⟩:=(hS.fD t 1).mp ht
 apply SF.mpr
 refine ⟨t.val - aD r 1,ZI.mpr ⟨Zt.mpr (by omega),?_⟩⟩
 rw[kQ d r t (t.val - aD r 1) (by omega)]
 exact EK
lemma aa_ (d:aO) (r :ℕ→ℕ) (k:ℕ):og d r k≤ r 1:=
  (Rd _ _).trans (Xf _).le
lemma aE.aaz (hS:aE p u d X r) (bU:2≤d.s):
    ∑ k∈ZM (d.s - 1),og d r k=r 1:=by
 have oc:∀ j∈ZM (r 1),b9 d r j - 1∈ZM (d.s - 1):=by
  intro j hj
  rw[Zt]at hj⊢
  have:=hS.jC bU j hj
  omega
 have h:=Wd oc
 rw[Xf]at h
 rw[h]
 refine Zw rfl fun k _=>?_
 unfold og
 congr 1
 apply R6
 intro j hj
 have:=hS.jC bU j (Zt.mp hj)
 constructor
 · intro e
   omega
 · intro e
   omega
noncomputable def aE.f7 [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m):fG m hS.nL:=
  ⟨fun i=> ⟨r i.val,by have:=hS.acW i.val i.isLt; omega⟩,
    fun i=>hS.Nq hp i.val i.isLt,by
      show ∑ i:Fin hS.nL,r i.val≤ m
      rw[nC,hS.g6]
      exact bZ⟩
lemma aE.m4 [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m):(hS.f7 hp bZ).tot=d.n:=by
 unfold fG.tot
 show ∑ i:Fin hS.nL,r i.val=d.n
 rw[nC,hS.g6]
lemma aE.oa [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s):(hS.f7 hp bZ).r2=r 1:=by
 unfold fG.r2
 show ∑ i∈ZU.filter (fun i:Fin hS.nL=>i.val=1),r i.val=r 1
 have cI:(⟨1,hS.tA bU⟩:Fin hS.nL)∈
     ZU.filter (fun i:Fin hS.nL=>i.val=1):=
   ZI.mpr ⟨Zb _,rfl⟩
 exact Finset.sum_eq_single_of_mem _ cI
   (fun b hb d8=>absurd (YL (ZI.mp hb).2) d8)
lemma aE.Q2 [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s):(hS.f7 hp bZ).r3=d.n - aD r 2:=by
 unfold fG.r3
 show ∑ i∈ZU.filter (fun i:Fin hS.nL=>2≤ i.val),r i.val=d.n - aD r 2
 rw[Xd,x5 r 2 hS.nL (hS.tA bU),hS.g6]
noncomputable def aE.ab1 [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s):nV (d.s - 1) (hS.f7 hp bZ).r2:=
  ⟨fun k=> ⟨og d r k.val,by
      rw[hS.oa hp bZ bU]
      exact Ws (aa_ d r k.val)⟩,
    fun k=>hS.aas k.val k.isLt,by
      show ∑ k:Fin (d.s - 1),og d r k.val=_
      rw[hS.oa hp bZ bU,XF (fun k=>og d r k) (d.s - 1)]
      exact hS.aaz bU⟩
noncomputable def aE.adU [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s):Fin (hS.f7 hp bZ).r2→Fin (d.s - 1):=
  fun j=> ⟨t5 d r j.val,hS.DN bU j.val
    (lt_of_lt_of_eq j.isLt (hS.oa hp bZ bU))⟩
noncomputable def aE.aeD [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s):Fin (hS.f7 hp bZ).r3→Fin m×Fin m:=
  fun j=> (⟨(rW d r j.val).1,(O1 d r bZ (by have:=hS.valid.yA; omega) j.val).1⟩,
    ⟨(rW d r j.val).2,(O1 d r bZ (by have:=hS.valid.yA; omega) j.val).2⟩)
noncomputable def aE.adT [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (hsum:∑ t,d.a t=m):nV (hS.f7 hp bZ).tot m:=
  ⟨fun j => ⟨lL d j.val,Ws (acu hsum j.val)⟩,fun j=>by
      have hj:j.val<d.n:=lt_of_lt_of_eq j.isLt (hS.m4 hp bZ)
      show 0<lL d j.val
      unfold lL
      rw[dif_pos hj]
      exact hS.a_pos _,by
      show ∑ j:Fin (hS.f7 hp bZ).tot,lL d j.val=m
      rw [XF (fun j=>lL d j),hS.m4 hp bZ,
        ← XF (fun j=>lL d j)]
      have e:∀ t:Fin d.n,lL d t.val=d.a t:= fun t=>by
        unfold lL
        exact dif_pos t.isLt
      simp only[e]
      exact hsum⟩
noncomputable def aE.k_ [Finite G] (hp:p.Prime) (hS:aE p u d X r) (m:ℕ) (bZ:d.n≤ m)
    (bU:2≤d.s) (hsum:∑ t,d.a t=m):cQ p m:=
  ⟨⟨⟨hS.nL,by have:=hS.abW hp; omega⟩,⟨d.s,by have:=hS.valid.yA; omega⟩,
      hS.f7 hp bZ,hS.ab1 hp bZ bU,(hS.adU hp bZ bU,hS.aeD hp bZ bU),
      hS.adT hp bZ hsum⟩,
    (fun i j=> ⟨tB d i.val j.val,acS hp.pos hS.bounded hsum _ _⟩,
      fun i j k=> ⟨jd d i.val j.val k.val,ab6 hp.pos hS.bounded hsum _ _ _⟩)⟩
section Readback
variable [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ} (bZ:d.n≤ m)
  (bU:2≤d.s) (hsum:∑ t,d.a t=m)
lemma aE.JP:rdC (hS.k_ hp m bZ bU hsum)=hS.nL:=rfl
lemma aE.Ka:rdS (hS.k_ hp m bZ bU hsum)=d.s:=rfl
lemma aE.DU (i:ℕ):
    rdR (hS.k_ hp m bZ bU hsum) i=dite (i<hS.nL) (fun _=>r i) (fun _=> 0):=rfl
lemma aE.Cn (k:ℕ):
    QO (hS.k_ hp m bZ bU hsum) k=
      dite (k<d.s - 1) (fun _=>og d r k) (fun _=> 0):=rfl
lemma aE.J4 (j:ℕ):
    rdF (hS.k_ hp m bZ bU hsum) j=
      dite (j< (hS.f7 hp bZ).r2) (fun _=>t5 d r j) (fun _=> 0):=rfl
lemma aE.Qc (j:ℕ):rdP (hS.k_ hp m bZ bU hsum) j=rW d r j:=by
 have e:rdP (hS.k_ hp m bZ bU hsum) j=dite (j< (hS.f7 hp bZ).r3)
     (fun _=> ((rW d r j).1,(rW d r j).2)) (fun _=> (0,0)):=rfl
 rw[e,hS.Q2 hp bZ bU]
 have h2:=hS.EI bU
 split_ifs with h
 · rfl
 · have h':¬ (aD r 2+j<d.n):=by omega
   unfold rW
   rw[dif_neg h']
lemma aE.DS (j:ℕ):rdA (hS.k_ hp m bZ bU hsum) j=lL d j:=by
 have e:rdA (hS.k_ hp m bZ bU hsum) j=
     dite (j< (hS.f7 hp bZ).tot) (fun _=>lL d j) (fun _=> 0):=rfl
 rw[e,hS.m4 hp bZ]
 split_ifs with h
 · rfl
 · unfold lL
   rw[dif_neg h]
lemma aE.DM (i j:ℕ):rdB (hS.k_ hp m bZ bU hsum) i j=tB d i j:=by
 have e :rdB (hS.k_ hp m bZ bU hsum) i j=
     dite (i< (hS.f7 hp bZ).tot∧j< (hS.f7 hp bZ).tot)
       (fun _=>tB d i j) (fun _=> 0):=rfl
 rw[e,hS.m4 hp bZ]
 split_ifs with h
 · rfl
 · unfold tB
   rw[dif_neg h]
lemma aE.Fp (i j k:ℕ):
    QF (hS.k_ hp m bZ bU hsum) i j k=jd d i j k:=by
 have e :QF (hS.k_ hp m bZ bU hsum) i j k=
     dite (i< (hS.f7 hp bZ).tot∧j< (hS.f7 hp bZ).tot∧
       k< (hS.f7 hp bZ).tot) (fun _=>jd d i j k) (fun _=> 0):=rfl
 rw[e,hS.m4 hp bZ]
 split_ifs with h
 · rfl
 · unfold jd
   rw[dif_neg h]
end Readback
lemma aE.B6 {G₁ G₂:Type u} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] {p m:ℕ} (hp:p.Prime) {u₁:ℕ→G₁} {d₁:aO} {X₁:Fin d₁.n→G₁}
    {r₁:ℕ→ℕ} {u₂:ℕ→G₂} {d₂:aO} {X₂:Fin d₂.n→G₂} {r₂:ℕ→ℕ}
    (jE:aE p u₁ d₁ X₁ r₁) (lM:aE p u₂ d₂ X₂ r₂)
    (nP:d₁.n≤ m) (oE:2≤d₁.s) (l_:∑ t,d₁.a t=m)
    (n7:d₂.n≤ m) (oL:2≤d₂.s) (l7:∑ t,d₂.a t=m)
    (heq:jE.k_ hp m nP oE l_=lM.k_ hp m n7 oL l7):
    d₁.normalize=d₂.normalize:=by
 have hc:jE.nL=lM.nL:=by
  have h:= congrArg rdC heq
  rwa[jE.JP hp nP oE l_,lM.JP hp n7 oL l7]at h
 have hs:d₁.s=d₂.s:=by
  have h:= congrArg rdS heq
  rwa[jE.Ka hp nP oE l_,lM.Ka hp n7 oL l7]at h
 have hr :∀ i<jE.nL,r₁ i=r₂ i:=by
  intro i hi
  have hi2:i<lM.nL:=by rw[← hc]; exact hi
  have h:= congrFun (congrArg rdR heq) i
  rw [jE.DU hp nP oE l_,lM.DU hp n7 oL l7,dif_pos hi,
    dif_pos hi2]at h
  exact h
 have xO:∀ w≤jE.nL,aD r₁ w=aD r₂ w:=k9 hr
 have hn:d₁.n=d₂.n:=by
  rw[← jE.g6, ← lM.g6, ← hc]
  exact xO _ YD
 have h1c:1<jE.nL:=jE.tA oE
 have jB:r₁ 1=r₂ 1:=hr 1 h1c
 have hf1:aD r₁ 1=aD r₂ 1:=xO 1 h1c.le
 have hf2:aD r₁ 2=aD r₂ 2:=xO 2 h1c
 have jV:∀ i (h1:i<d₁.n) (h2:i<d₂.n),d₁.lv ⟨i,h1⟩=d₂.lv ⟨i,h2⟩:=by
  intro i h1 h2
  have hw:=jE.GK jE.g6.symm ⟨i,h1⟩
  obtain ⟨e1,e2⟩:=(jE.fD ⟨i,h1⟩ (d₁.lv ⟨i,h1⟩)).mp rfl
  rw[xO _ hw.le,hr _ hw]at e2
  rw[xO _ hw.le]at e1
  exact ((lM.fD ⟨i,h2⟩ (d₁.lv ⟨i,h1⟩)).mpr ⟨e1,e2⟩).symm
 have hA:lL d₁=lL d₂:=by
  funext j
  have h:= congrFun (congrArg rdA heq) j
  rwa[jE.DS hp nP oE l_,lM.DS hp n7 oL l7]at h
 have hB:tB d₁=tB d₂:=by
  funext i j
  have h:= congrFun (congrFun (congrArg rdB heq) i) j
  rwa[jE.DM hp nP oE l_,lM.DM hp n7 oL l7]at h
 have hCm:jd d₁=jd d₂:=by
  funext i j k
  have h:= congrFun (congrFun (congrFun (congrArg QF heq) i) j) k
  rwa[jE.Fp hp nP oE l_,lM.Fp hp n7 oL l7]at h
 have hP:rW d₁ r₁=rW d₂ r₂:=by
  funext j
  have h:= congrFun (congrArg rdP heq) j
  rwa[jE.Qc hp nP oE l_,lM.Qc hp n7 oL l7]at h
 have hPa:∀ j< r₁ 1,t5 d₁ r₁ j=t5 d₂ r₂ j:=by
  intro j hj
  have tM:j< (jE.f7 hp nP).r2:=by rw[jE.oa hp nP oE]; exact hj
  have zB:j< (lM.f7 hp n7).r2:=by rw[lM.oa hp n7 oL, ← jB]; exact hj
  have h:= congrFun (congrArg rdF heq) j
  rw [jE.J4 hp nP oE l_,lM.J4 hp n7 oL l7,dif_pos tM,
    dif_pos zB]at h
  exact h
 have pC :∀ k,((ZM (r₁ 1)).filter (fun j=>b9 d₁ r₁ j=k)).card=
     ((ZM (r₁ 1)).filter (fun j=>b9 d₂ r₂ j=k)).card:=by
   intro k
   by_cases hk:1≤k∧k<d₁.s
   · have Bw:k - 1<d₁.s - 1:=by omega
     have Oy:k - 1<d₂.s - 1:=by omega
     have h:= congrFun (congrArg QO heq) (k - 1)
     rw [jE.Cn hp nP oE l_,lM.Cn hp n7 oL l7,dif_pos Bw,
       dif_pos Oy]at h
     unfold og at h
     rw[← jB,show k - 1+1=k by omega]at h
     exact h
   · have e1:(ZM (r₁ 1)).filter (fun j=>b9 d₁ r₁ j=k)= ∅ :=
       WC.mpr fun j hj=>by
         have:=jE.jC oE j (Zt.mp hj)
         omega
     have e2:(ZM (r₁ 1)).filter (fun j=>b9 d₂ r₂ j=k)= ∅ :=
       WC.mpr fun j hj=>by
         have mC:j< r₂ 1:=by rw[← jB]; exact Zt.mp hj
         have:=lM.jC oL j mC
         omega
     rw[e1,e2]
 have acD:∀ i j,i≤j→j< r₁ 1→ b9 d₂ r₂ i≤b9 d₂ r₂ j:=
   fun i j hij hj=>lM.w_ oL i j hij (by rw[← jB]; exact hj)
 have EK:∀ j< r₁ 1,b9 d₁ r₁ j=b9 d₂ r₂ j:= fun j hj=>
   vY _ _ _ (fun i j hij hj=>jE.w_ oE i j hij hj) acD pC j hj
 have lH:∀ i (h1:i<d₁.n) (h2:i<d₂.n),1≤d₁.lv ⟨i,h1⟩→
     (d₁.df ⟨i,h1⟩).1.val=(d₂.df ⟨i,h2⟩).1.val∧
       (d₁.df ⟨i,h1⟩).2.val=(d₂.df ⟨i,h2⟩).2.val:=by
  intro i h1 h2 hl
  by_cases hw:d₁.lv ⟨i,h1⟩=1
  · obtain ⟨a1,a2⟩:=(jE.fD ⟨i,h1⟩ 1).mp hw
    have a1':aD r₁ 1≤ i:=a1
    have a2':i<aD r₁ 1+r₁ 1:=a2
    have ej1:aD r₁ 1+(i - aD r₁ 1)=(⟨i,h1⟩:Fin d₁.n).val:=by
     show aD r₁ 1+(i - aD r₁ 1)=i
     omega
    have ej2:aD r₂ 1+(i - aD r₁ 1)=(⟨i,h2⟩:Fin d₂.n).val:=by
     show aD r₂ 1+(i - aD r₁ 1)=i
     omega
    have hj:i - aD r₁ 1< r₁ 1:=by omega
    constructor
    · rw[← r5 d₁ r₁ ⟨i,h1⟩ _ ej1, ← r5 d₂ r₂ ⟨i,h2⟩ _ ej2]
      exact hPa _ hj
    · rw[← kQ d₁ r₁ ⟨i,h1⟩ _ ej1, ← kQ d₂ r₂ ⟨i,h2⟩ _ ej2]
      exact EK _ hj
  · have Ep:2≤d₁.lv ⟨i,h1⟩:=by omega
    have a1:=((jE.fD ⟨i,h1⟩ (d₁.lv ⟨i,h1⟩)).mp rfl).1
    have a1':aD r₁ (d₁.lv ⟨i,h1⟩)≤ i:=a1
    have a3:=g5 r₁ Ep
    have ej1:aD r₁ 2+(i - aD r₁ 2)=(⟨i,h1⟩:Fin d₁.n).val:=by
     show aD r₁ 2+(i - aD r₁ 2)=i
     omega
    have ej2:aD r₂ 2+(i - aD r₁ 2)=(⟨i,h2⟩:Fin d₂.n).val:=by
     show aD r₂ 2+(i - aD r₁ 2)=i
     omega
    have e:= congrFun hP (i - aD r₁ 2)
    rw[Qj d₁ r₁ ⟨i,h1⟩ _ ej1,Qj d₂ r₂ ⟨i,h2⟩ _ ej2]at e
    exact Tn.inj e
 refine aO.normalize_eq hn hs jV lH ?_ ?_ ?_
 · intro i h1 h2
   have e:= congrFun hA i
   unfold lL at e
   rwa[dif_pos h1,dif_pos h2]at e
 · intro i j h1 pL h2 jM
   have e:= congrFun (congrFun hB i) j
   unfold tB at e
   rwa[dif_pos (TA h1 pL),dif_pos (TA h2 jM)]at e
 · intro i j k h1 pL aaZ h2 jM abu
   have e:= congrFun (congrFun (congrFun hCm i) j) k
   unfold jd at e
   rwa[dif_pos (TA h1 (TA pL aaZ)),
     dif_pos (TA h2 (TA jM abu))]at e
def dW {p:ℕ} (hp:p.Prime) (m:ℕ) (G:Type u) [Group G] [Finite G]
    (D:cQ p m):Prop:=
  ∃ (u:ℕ→G) (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ) (hS:aE p u d X r)
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m),hS.k_ hp m bZ bU hsum=D
lemma HW {G:Type u} [Group G] [Finite G] {p m:ℕ} (hp:p.Prime)
    (hG:ZB G=p^m) (wJ:lcs G 1≠⊥):∃ D:cQ p m,dW hp m G D:=by
 obtain ⟨u,d,X,r,bU,oW, -, -, -, -,bZ, -,hS⟩:=qW hp hG wJ
 have hsum:∑ t,d.a t=m:=by
  have h1:=hS.e9.card
  rw[hG]at h1
  exact (Zd hp.two_le h1).symm
 have C5:2≤d.s:=by rw[oW]; exact bU
 exact ⟨_,u,d,X,r,hS,bZ,C5,hsum,rfl⟩
lemma zF {G H:Type u} [Group G] [Finite G] [Group H] [Finite H] {p m:ℕ}
    (hp:p.Prime) {D:cQ p m} (hG:dW hp m G D) (hH:dW hp m H D):
    Nonempty (G≃*H):=by
 obtain ⟨u₁,d₁,X₁,r₁,jE,nP,oE,l_,e₁⟩:=hG
 obtain ⟨u₂,d₂,X₂,r₂,lM,n7,oL,l7,e₂⟩:=hH
 exact N6 hp d₁.normalize d₂.normalize
   (aE.B6 hp jE lM nP oE l_ n7 oL l7 (e₁.trans e₂.symm))
   (aO.JJ jE.valid) X₁ X₂ (aO.s5 jE.e9)
   (aO.s5 lM.e9)
end DataBridge
section FiberCount
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.sI (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k:aR c (mL r c)):lL d (aD r k.1.val+k.2.val)=d.a (hS.aV hn k):=by
 unfold lL
 exact dif_pos (hS.aV hn k).isLt
lemma aE.Ez (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (k k':aR c (mL r c)):
    tB d (aD r k.1.val+k.2.val) (aD r k'.1.val+k'.2.val)=
      d.b (hS.aV hn k) (hS.aV hn k'):=by
 unfold tB
 exact dif_pos ⟨(hS.aV hn k).isLt,(hS.aV hn k').isLt⟩
lemma aE.oC [Finite G] (hp:p.Prime) (hS:aE p u d X r)
    {c:ℕ} (hn:d.n=aD r c) (k k':aR c (mL r c)):
    ((hS.toaZ hp hn).c_ k k').val=d.b (hS.aV hn k) (hS.aV hn k'):=by
 have hx:=Ym
   (hS.k8 (X (hS.aV hn k)^p^d.a (hS.aV hn k)))
 have h2:=hS.s7 _ (d.b (hS.aV hn k)) hx.1 (fun t=>hS.bounded.1 _ t)
   (hx.2.symm.trans (hS.e9.pow _))
 show XP (hS.k8 (X (hS.aV hn k)^p^d.a (hS.aV hn k)))
   (hS.aV hn k')=_
 rw[h2]
lemma aE.uZ [Finite G] (hp:p.Prime) (hS:aE p u d X r)
    {c:ℕ} (hn:d.n=aD r c) (k k':aR c (mL r c)):
    tB d (hS.aV hn k).val (hS.aV hn k').val=
      ((hS.toaZ hp hn).c_ k k').val:=by
 rw[hS.oC hp hn]
 exact hS.Ez hn k k'
lemma tZ (r :ℕ→ℕ):∀ c i,i<aD r c→∃ w<c,∃ v< r w,i=aD r w+v
  | 0,i,h=>absurd h (by show ¬ i<0; omega)
  | c +1,i,h=>by
    by_cases hi:i<aD r c
    · obtain ⟨w,hw,v,hv,e⟩:=tZ r c i hi
      exact ⟨w,by omega,v,hv,e⟩
    · rw[dM]at h
      exact ⟨c,by omega,i - aD r c,by omega,by omega⟩
def o6 {n q:ℕ} (B:Fin n→Fin n→Fin q) (i j:ℕ):ℕ:=
  if h:i<n∧j<n then (B ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
lemma K4 {n q:ℕ} (B:Fin n→Fin n→Fin q) (i j:Fin n):
    o6 B i.val j.val=(B i j).val:=by
 unfold o6
 rw[dif_pos ⟨i.isLt,j.isLt⟩]
def aW {m:ℕ} (D:a9 m) (i:ℕ):ℕ:=
  if h:i<D.1.val then (D.2.2.1.1 ⟨i,h⟩).val else 0
def qQ {m:ℕ} (D:a9 m) (j:ℕ):ℕ:=
  if h:j<D.2.2.1.tot then (D.2.2.2.2.2.1 ⟨j,h⟩).val else 0
abbrev aF {m:ℕ} (D:a9 m):Fin D.1.val→ℕ:=mL (aW D) D.1.val
def bT {m:ℕ} (D:a9 m):aR D.1.val (aF D)→ℕ:=
  fun k=>qQ D (aD (aW D) k.1.val+k.2.val)
lemma M4 {m:ℕ} (D:a9 m):D.2.2.1.tot=aD (aW D) D.1.val:=by
 unfold fG.tot
 rw[← nC]
 refine Zw rfl fun i _=>?_
 unfold aW
 rw[dif_pos i.isLt]
lemma K8 {m:ℕ} (D:a9 m) (k:aR D.1.val (aF D)):
    aD (aW D) k.1.val+k.2.val<D.2.2.1.tot:=
  Mo (aW D) (M4 D) k.1 k.2
lemma CX {m:ℕ} (D:a9 m) (k:aR D.1.val (aF D)):1≤bT D k:=by
 show 1≤qQ D (aD (aW D) k.1.val+k.2.val)
 unfold qQ
 rw[dif_pos (K8 D k)]
 exact D.2.2.2.2.2.2.1 _
def tD {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:a9 m):
    Set (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):=
  {B | ∃ G∈T,∃ C,dW hp m G (⟨D,(B,C)⟩:cQ p m)}
lemma J5 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (hT:∀ G∈T,ZB G=p^m∧lcs G 1≠⊥):
    (Yd (YF FiniteGrp.{0}) '' T).Finite:=by
 have jp:∀ D:cQ p m,Set.Subsingleton {s | ∃ G∈T,
     Yd (YF FiniteGrp.{0}) G=s∧
       dW hp m G D}:=by
   intro D
   rintro s₁ ⟨G₁,hG₁,rfl,h₁⟩ s₂ ⟨G₂,hG₂,rfl,h₂⟩
   obtain ⟨e⟩:=zF hp h₁ h₂
   exact Pt ⟨Wj (R7 e)⟩
 refine Set.Finite.subset (Set.finite_iUnion fun D:cQ p m=> (jp D).finite) ?_
 rintro s ⟨G,hG,rfl⟩
 obtain ⟨D,hD⟩:=HW hp (hT G hG).1 (hT G hG).2
 exact Set.mem_iUnion.mpr ⟨D,G,hG,rfl,hD⟩
lemma Jp {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H] {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:dW hp m H (⟨D,(B,C)⟩:cQ p m)):
    ∃ (u :ℕ→H) (d:aO) (X:Fin d.n→H) (r :ℕ→ℕ) (hS:aE p u d X r),
      D.1.val=hS.nL∧(∀ i<hS.nL,aW D i=r i)∧(∀ j,qQ D j=lL d j)∧
        D.2.2.1.tot=d.n∧(∀ i j,o6 B i j=tB d i j):=by
 obtain ⟨u,d,X,r,hS,bZ,bU,hsum,e⟩:=hc
 refine ⟨u,d,X,r,hS,(congrArg rdC e).symm,?_,?_,?_,?_⟩
 · intro i hi
   have h:= congrFun (congrArg rdR e) i
   rw[hS.DU hp bZ bU hsum,dif_pos hi]at h
   exact h.symm
 · intro j
   have h:= congrFun (congrArg rdA e) j
   rw[hS.DS hp bZ bU hsum]at h
   exact h.symm
 · have h:(hS.f7 hp bZ).tot=D.2.2.1.tot:=
     congrArg (fun E:cQ p m=>E.1.2.2.1.tot) e
   exact h.symm.trans (hS.m4 hp bZ)
 · intro i j
   have h:= congrFun (congrFun (congrArg rdB e) i) j
   rw[hS.DM hp bZ bU hsum]at h
   exact h.symm
lemma Fy {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:a9 m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:dW hp m H (⟨D,(B,C)⟩:cQ p m)) (i j:ℕ) (hj:j<D.2.2.1.tot):
    o6 B i j<p^qQ D j:=by
 obtain ⟨u,d,X,r,hS, -, -,hA,aeE,hB⟩:=Jp hp hc
 rw[hB,hA]
 rw[aeE]at hj
 unfold tB lL
 rw[dif_pos hj]
 split_ifs with h
 · exact hS.bounded.1 _ _
 · exact XD hp.pos _
def aaa {m:ℕ} (n5:0<p) (D:a9 m)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    kq p D.1.val (aF D) (bT D):=
  fun k h=>if f5:o6 B (aD (aW D) k.1.val+k.2.val)
      (aD (aW D) h.1.val+h.2.val)<p^bT D h then ⟨_,f5⟩
    else ⟨0,XD n5 _⟩
lemma oH {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:a9 m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:dW hp m H (⟨D,(B,C)⟩:cQ p m)) (k h:aR D.1.val (aF D)):
    (aaa hp.pos D B k h).val=
      o6 B (aD (aW D) k.1.val+k.2.val) (aD (aW D) h.1.val+h.2.val):=by
 have f5:o6 B (aD (aW D) k.1.val+k.2.val) (aD (aW D) h.1.val+h.2.val)<
     p^bT D h:=Fy hp hc _ _ (K8 D h)
 simp only[aaa,dif_pos f5]
lemma FI {c c':ℕ} {r :Fin c→ℕ} {r':Fin c'→ℕ} {a:aR c r→ℕ}
    {a':aR c' r'→ℕ} {B:kq p c r a} {B':kq p c' r' a'} (hc:c= c')
    (hr :∀ i:Fin c,r i=r' (U5 hc i))
    (ha:∀ (i:Fin c) (v:Fin (r i)),a ⟨i,v⟩=a' ⟨U5 hc i,U5 (hr i) v⟩)
    (hB :∀ (i:Fin c) (v:Fin (r i)) (i':Fin c) (v':Fin (r i')),
      (B ⟨i,v⟩ ⟨i',v'⟩).val=
        (B' ⟨U5 hc i,U5 (hr i) v⟩ ⟨U5 hc i',U5 (hr i') v'⟩).val)
    (h:B∈kZ p c r a):B'∈kZ p c' r' a':=by
 subst hc
 have er :r=r':= funext hr
 subst er
 have ea:a=a':= funext fun k=>ha k.1 k.2
 subst ea
 have eB:B=B':= funext fun k=>funext fun k'=>YL (hB k.1 k.2 k'.1 k'.2)
 subst eB
 exact h
lemma CZ {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:a9 m):
    (tD hp T D).ncard≤(kZ p D.1.val (aF D) (bT D)).ncard:=by
 have:Fact p.Prime:=⟨hp⟩
 refine YM (aaa hp.pos D) ?_ ?_ (Zl _)
 · rintro B ⟨G, -,C,hc⟩
   obtain ⟨u,d,X,r,hS,lT,hR,hA, -,hBf⟩:=Jp hp hc
   have hn:d.n=aD r hS.nL:=hS.g6.symm
   have hG:IsPGroup p G:=YK hS.e9.card
   have cI:=(hS.toaZ hp hn).JY hG
   refine FI lT.symm ?_ ?_ ?_ cI
   · intro i
     exact (hR i.val i.isLt).symm
   · intro i v
     show d.a (hS.aV hn ⟨i,v⟩)=qQ D (aD (aW D) i.val+v.val)
     rw[hA,k9 hR i.val i.isLt.le]
     exact (hS.sI hn ⟨i,v⟩).symm
   · intro i v i' v'
     rw[hS.oC hp hn,oH hp hc]
     show _= o6 B (aD (aW D) i.val+v.val) (aD (aW D) i'.val+v'.val)
     rw[hBf,k9 hR i.val i.isLt.le,k9 hR i'.val i'.isLt.le]
     exact (hS.Ez hn ⟨i,v⟩ ⟨i',v'⟩).symm
 · rintro B₁ ⟨G₁, -,C₁,hc₁⟩ B₂ ⟨G₂, -,C₂,hc₂⟩ heq
   have abq:∀ k k':aR D.1.val (aF D),
       o6 B₁ (aD (aW D) k.1.val+k.2.val) (aD (aW D) k'.1.val+k'.2.val)=
         o6 B₂ (aD (aW D) k.1.val+k.2.val) (aD (aW D) k'.1.val+k'.2.val):=by
    intro k k'
    have h:= congrArg Ty (congrFun (congrFun heq k) k')
    rw[oH hp hc₁,oH hp hc₂]at h
    exact h
   funext i j
   apply YL
   obtain ⟨w,hw,v,hv,ei⟩:=
     tZ (aW D) D.1.val i.val (lt_of_lt_of_eq i.isLt (M4 D))
   obtain ⟨w',EU,v',K9,ej⟩:=
     tZ (aW D) D.1.val j.val (lt_of_lt_of_eq j.isLt (M4 D))
   have h2:o6 B₁ (aD (aW D) w+v) (aD (aW D) w'+v')=
       o6 B₂ (aD (aW D) w+v) (aD (aW D) w'+v'):=
     abq ⟨⟨w,hw⟩,⟨v,hv⟩⟩ ⟨⟨w',EU⟩,⟨v',K9⟩⟩
   rw[← ei, ← ej,K4,K4]at h2
   exact h2
end FiberCount
end OMA.SimsLite
namespace OMA.SimsLite.Alt2
open Module Matrix
section Defs
variable {F:Type*} [Field F] {R M:ℕ}
def kG (A:Matrix (Fin R) (Fin R) F):Prop:=
  (∀ i,A i i=0)∧∀ i j,A j i= -A i j
variable (R) in
abbrev tj:Type:={p:Fin R×Fin R//p.1<p.2}
lemma NX (R:ℕ):Zq (tj R)=R.choose 2:=by
 have h1:Zq (tj R)=
     ∑ j:Fin R,∑ i:Fin R,if i<j then 1 else 0:=by
   rw[Rg,PN,Fintype.sum_prod_type,OD]
 have h2:∀ j:Fin R,(∑ i:Fin R,if i<j then 1 else 0)=(j:ℕ):=by
   intro j
   rw[← PN,Finset.filter_gt_eq_Iio,Fin.card_Iio]
 have h3:∑ j:Fin R,(j:ℕ)=∑ i∈ZM R,i:=
   XF (fun i=>i) R
 rw [h1,Zw rfl (fun j _=>h2 j),h3,Nat.choose_two_right,
   ← Finset.sum_range_id_mul_two,Nat.mul_div_cancel _ (by norm_num)]
def Ho (x y:Fin R→F):Matrix (Fin R) (Fin R) F→ₗ[F] F where
  toFun A:=x ⬝ᵥ (A*ᵥ y)
  map_add' A B:=by rw[Matrix.add_mulVec,dotProduct_add]
  map_smul' c A:=by rw[Matrix.smul_mulVec,dotProduct_smul,Pe]
lemma lw (x y:Fin R→F) (A:Matrix (Fin R) (Fin R) F):
    Ho x y A=x ⬝ᵥ (A*ᵥ y):=rfl
lemma aad (A:Matrix (Fin R) (Fin R) F) (i j:Fin R):
    Ho (Yz i 1) (Yz j 1) A=A i j:=by
 simp[Ho,dotProduct,Matrix.mulVec,Um]
lemma lY {A:Matrix (Fin R) (Fin R) F} (hA:kG A) (x:Fin R→F):
    Ho x x A=0:=by
 rw[lw,Matrix.dot_mulVec_eq_sum_sum]
 have e:∑ j,∑ i,x i*A i j*x j=∑ p:Fin R×Fin R,x p.2*A p.2 p.1*x p.1:=
   (Fintype.sum_prod_type' (fun j i=>x i*A i j*x j)).symm
 rw[e]
 apply Finset.sum_ninvolution (fun p=> (p.2,p.1))
 · rintro ⟨j,i⟩
   show x i*A i j*x j+x j*A j i*x i=0
   rw[hA.2 i j]
   ring
 · rintro ⟨j,i⟩ d8 heq
   have hij:i=j:= congrArg W9 heq
   apply d8
   show x i*A i j*x j=0
   rw[hij,hA.1 j]
   ring
 · intro p
   exact Zb _
 · intro p
   rfl
def QP (β:Fin M→Matrix (Fin R) (Fin R) F) (U:Submodule F (Fin R→F)):
    Set (Fin M→F):=
  {w | ∃ x∈U,∃ y∈U,w= fun k=>Ho x y (β k)}
def gQ (β:Fin M→Matrix (Fin R) (Fin R) F) (U:Submodule F (Fin R→F)):Prop:=
  ZQ F (QP β U)=⊤
noncomputable def kA (β:Fin M→Matrix (Fin R) (Fin R) F):ℕ:=
  sInf {d | ∃ U:Submodule F (Fin R→F),finrank F U=d∧gQ β U}
end Defs
section Duality
variable {F:Type*} [Field F] {R M:ℕ}
lemma wN (β:Fin M→Matrix (Fin R) (Fin R) F) {U:Submodule F (Fin R→F)} {d:ℕ}
    (hU:finrank F U=d) (hg:gQ β U):kA β≤d:=
  WK ⟨U,hU,hg⟩
lemma N9 (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:gQ β ⊤):kA β≤R:=
  wN β (by rw[SY,Wh]) hg
lemma z5 (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:gQ β ⊤):
    ∃ U:Submodule F (Fin R→F),finrank F U=kA β∧gQ β U:=
  Wr (s:={d | ∃ U:Submodule F (Fin R→F),finrank F U=d∧gQ β U})
    ⟨R,⊤,by rw[SY,Wh],hg⟩
end Duality
section N2
open Classical in
noncomputable def N2 (r1 r2 s:ℕ):ℕ:=
  (ZU.filter (fun β:Fin r2→Matrix (Fin r1) (Fin r1) (ZMod 2)=>
    (∀ k,kG (β k))∧gQ β ⊤∧kA β=s)).card
end N2
section Lemma27
variable {F:Type*} [Field F]
lemma Dk (n k:ℕ):
    {U :Submodule F (Fin n→F) | finrank F U=k}⊆
      ZF (fun v:Fin k→(Fin n→F)=>ZQ F (ZF v)):=by
  intro U hU
  let B:=WD F U hU
  refine ⟨fun i=> (B i:Fin n→F),?_⟩
  have h:= congrArg (Pw U.subtype) B.span_eq
  rw[Rh,SG, ← WJ]at h
  exact h
end Lemma27
section Grass
variable {F:Type*} [Field F] {n:ℕ}
lemma BK (U:Submodule F (Fin n→F)):
    ∃ S:Finset (Fin n),S.card= finrank F U∧
      (∀ v∈U,(∀ i∈S,v i=0)→v=0)∧
      (∀ w:S→F,∃ v∈U,∀ i:S,v i=w i):=by
 classical
 let P:Finset (Fin n)→Prop:= fun S=> ∀ v∈U,(∀ i∈S,v i=0)→v=0
 have d8:(ZU.filter P).Nonempty:=
   ⟨ZU,ZI.2 ⟨Zb _,
     fun v _ hv=>funext fun i=>hv i (Zb i)⟩⟩
 obtain ⟨S,hS,nU⟩:=RB (ZU.filter P) Finset.card d8
 have hPS:P S:=(ZI.1 hS).2
 let L:U→ₗ[F] (S→F):=(LinearMap.funLeft F F (fun i:S=> (i:Fin n))).comp U.subtype
 have eW:Z8 L:=by
  rw[← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro v hv
  apply Zu
  exact hPS v v.2 (fun i hi=>congrFun hv ⟨i,hi⟩)
 have j6:Zn L:=by
  rw[← LinearMap.range_eq_top]
  by_contra Mm
  obtain ⟨φ,hφ0,hφ⟩:=Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 Mm)
  obtain ⟨c,key⟩:∃ c:S→F,∀ w,φ w=∑ i,c i*w i:=
    ⟨fun i=>φ (fun j=>if i=j then 1 else 0),fun w=>by
      rw[LinearMap.pi_apply_eq_sum_univ φ w]
      exact Zw rfl (fun i _=>by rw[smul_eq_mul,mul_comm])⟩
  have hc:c≠0:=by
   intro h0
   apply hφ0
   exact LinearMap.ext fun w=>by rw[key w,h0]; simp
  obtain ⟨i0,hi0⟩:∃ i0,c i0≠0:=by
   by_contra h
   push_neg at h
   exact hc (funext h)
  have m_:∀ v∈U,∑ i:S,c i*v i=0:=by
   intro v hv
   have:=Ro.1 (hφ (LinearMap.mem_range_self L ⟨v,hv⟩))
   rw[key]at this
   exact this
  have hP':P (S.erase (i0:Fin n)):=by
   intro v hv hz
   apply hPS v hv
   have hv0:v i0=0:=by
    have h1:=m_ v hv
    rw[Ue i0]at h1
    · exact (mul_eq_zero.1 h1).resolve_left hi0
    · intro b _ hb
      rw[hz b (WI.2 ⟨fun h=>hb (Zu h),b.2⟩),mul_zero]
    · intro h
      exact absurd (Zb _) h
   intro i hi
   by_cases h:i=(i0:Fin n)
   · rw[h]
     exact hv0
   · exact hz i (WI.2 ⟨h,hi⟩)
  have h1:=nU (S.erase (i0:Fin n)) (ZI.2 ⟨Zb _,hP'⟩)
  have h2:=Finset.card_erase_lt_of_mem i0.2
  omega
 refine ⟨S,?_,hPS,fun w=>?_⟩
 · have e:=(LinearEquiv.ofBijective L ⟨eW,j6⟩).finrank_eq
   rw[Module.finrank_fintype_fun_eq_card,WG]at e
   exact e.symm
 · obtain ⟨v,hv⟩:=j6 w
   exact ⟨v,v.2,fun i=>congrFun hv i⟩
lemma A9 [Finite F] (k:ℕ):
    {U :Submodule F (Fin n→F) | finrank F U=k}.ncard≤
      2^n*ZB F^(k*(n - k)):=by
  classical
  have ads:∀ U:{U:Submodule F (Fin n→F)//finrank F U=k},
      ∃ S:Finset (Fin n),∃ _:S.card=k,∃ u:Fin n→(Fin n→F),
        (∀ i,u i∈U.1)∧(∀ i∈S,∀ j∈S,u i j=if j=i then 1 else 0)∧
        (∀ v∈U.1,(∀ i∈S,v i=0)→v=0):=by
    intro U
    obtain ⟨S,hS,eW,j6⟩:=BK U.1
    choose u' aeq oF using fun i:S=>j6 (Yz i 1)
    refine ⟨S,hS.trans U.2,fun i=>if h:i∈S then u' ⟨i,h⟩ else 0,?_,?_,eW⟩
    · intro i
      by_cases h:i∈S
      · dsimp only
        rw[dif_pos h]
        exact aeq _
      · dsimp only
        rw[dif_neg h]
        exact U.1.zero_mem
    · intro i hi j hj
      dsimp only
      rw[dif_pos hi,oF ⟨i,hi⟩ ⟨j,hj⟩]
      simp[Um]
  choose S hS u hu abm eW using ads
  have hc:∀ U,((S U)ᶜ).card=n - k:= fun U=>by
    rw[Finset.card_compl,Zz,hS U]
  let code:{U:Submodule F (Fin n→F)//finrank F U=k}→
      Finset (Fin n)×(Fin k→Fin (n - k)→F):= fun U=>
    (S U,fun a b=>u U ((S U).orderEmbOfFin (hS U) a) (((S U)ᶜ).orderEmbOfFin (hc U) b))
  have acN:∀ (T T':Finset (Fin n)) {m:ℕ} (h:T.card=m) (h':T'.card=m),T=T'→
      ∀ a,T.orderEmbOfFin h a=T'.orderEmbOfFin h' a:=by
   rintro T _ m h h' rfl a
   rfl
  have cO:∀ U U',code U= code U'→U.1≤U'.1:=by
   intro U U' h
   have hSS:S U=S U':= congrArg W9 h
   have h2:= congrArg PO h
   have huu:∀ i∈S U,u U i=u U' i:=by
    intro i hi
    funext j
    by_cases hj:j∈S U
    · rw[abm U i hi j hj,abm U' i (hSS▸hi) j (hSS▸hj)]
    · have hjc:j∈(S U)ᶜ:=Finset.mem_compl.2 hj
      obtain ⟨b,hb⟩:j∈ZF ((S U)ᶜ.orderEmbOfFin (hc U)):=by
       rw[VL]
       exact hjc
      obtain ⟨a,ha⟩:i∈ZF ((S U).orderEmbOfFin (hS U)):=by
       rw[VL]
       exact hi
      have h3:= congrFun (congrFun h2 a) b
      simp only[code]at h3
      rw [← acN _ _ (hS U) (hS U') hSS a, ← acN _ _ (hc U) (hc U') (by rw[hSS]) b,ha,
        hb]at h3
      exact h3
   intro v hv
   have hw:v - ∑ i∈S U,v i•u U i=0:=by
    apply eW U _ (sub_mem hv (sum_mem (fun i _=>VE _ _ (hu U i))))
    intro j hj
    have hsum:∑ i∈S U,v i*u U i j=∑ i∈S U,if j=i then v i else 0:=
      Zw rfl (fun i hi=>by rw[abm U i hi j hj]; split_ifs<;>simp)
    simp only[SH,Py,Te,smul_eq_mul]
    rw[hsum,Finset.sum_ite_eq,if_pos hj,sub_self]
   have K9:v=∑ i∈S U,v i•u U i:=sub_eq_zero.1 hw
   rw[K9]
   exact sum_mem (fun i hi=>by rw[huu i hi]; exact VE _ _ (hu U' i))
  have ac9:Z8 code:=by
   intro U U' h
   exact Zu (le_antisymm (cO U U' h) (cO U' U h.symm))
  rw[← Xt]
  calc Nat.card {U:Submodule F (Fin n→F) | finrank F U=k}
      =ZB {U:Submodule F (Fin n→F)//finrank F U=k}:=rfl
    _ ≤ ZB (Finset (Fin n)×(Fin k→Fin (n - k)→F)):=
        Yy code ac9
    _ = 2 ^n*ZB F^(k*(n - k)):=by
        rw [W7,Xl,Xl,Xk,Xk,
          YA (α:=Finset (Fin n)),Fintype.card_finset,Zz,
          ← X5,mul_comm (n - k) k]
end Grass
section Lemma27ii
variable {F:Type*} [Field F] {R:ℕ}
lemma aa6 {A:Matrix (Fin R) (Fin R) F} (hA:kG A) (x y:Fin R→F):
    Ho x y A= -Ho y x A:=by
 have h:=lY hA (x+y)
 have hx:=lY hA x
 have hy:=lY hA y
 rw[lw,Ph,dotProduct_add,OT,OT]at h
 rw[lw]at hx hy
 rw[lw,lw]
 linear_combination h - hx - hy
end Lemma27ii
section Lemma81
variable {F:Type*} [Field F] {R:ℕ}
end Lemma81
section SimsBounds
variable {F:Type*} [Field F] {R M:ℕ}
def jo (β:Fin M→Matrix (Fin R) (Fin R) F):
    (Fin R→F)→ₗ[F] (Fin R→F)→ₗ[F] (Fin M→F):=
  Pz F (fun x y k=>Ho x y (β k))
    (fun x x' y=>by funext k; simp[lw,OT])
    (fun c x y=>by funext k; simp[lw,smul_dotProduct])
    (fun x y y'=>by funext k; simp[lw,Ph,dotProduct_add])
    (fun c x y=>by funext k; simp[lw,Matrix.mulVec_smul,dotProduct_smul])
lemma QD (β:Fin M→Matrix (Fin R) (Fin R) F) (x y:Fin R→F):
    jo β x y= fun k=>Ho x y (β k):=rfl
lemma LR (β:Fin M→Matrix (Fin R) (Fin R) F) {U:Submodule F (Fin R→F)}
    {x y:Fin R→F} (hx:x∈U) (hy:y∈U):jo β x y∈QP β U:=
  ⟨x,hx,y,hy,rfl⟩
lemma aaA (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,kG (β k))
    (x:Fin R→F):jo β x x =0:=by
 funext k
 exact lY (hA k) x
lemma aaQ (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,kG (β k))
    (x y:Fin R→F):jo β y x = -jo β x y:=by
 funext k
 exact aa6 (hA k) y x
lemma yJ (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,kG (β k))
    {s:ℕ} (v:Fin s→(Fin R→F)):
    QP β (ZQ F (ZF v))⊆
      ZQ F (ZF (fun q:tj s=>jo β (v q.1.1) (v q.1.2))):=by
  set S:=ZQ F (ZF (fun q:tj s=>jo β (v q.1.1) (v q.1.2)))
  have h1:∀ i j,jo β (v i) (v j)∈S:=by
   intro i j
   rcases Vq i j with h | h | h
   · exact Z1 ⟨⟨(i,j),h⟩,rfl⟩
   · rw[h,aaA β hA]
     exact S.zero_mem
   · rw[aaQ β hA]
     exact S.neg_mem (Z1 ⟨⟨(j,i),h⟩,rfl⟩)
  have h2:∀ j,∀ x∈ZQ F (ZF v),jo β x (v j)∈S:=by
   intro j x hx
   have cO:ZQ F (ZF v)≤S.comap ((jo β).flip (v j)):=by
    rw[YU]
    rintro _ ⟨i,rfl⟩
    exact h1 i j
   exact cO hx
  rintro w ⟨x,hx,y,hy,rfl⟩
  have cO:ZQ F (ZF v)≤S.comap (jo β x):=by
   rw[YU]
   rintro _ ⟨j,rfl⟩
   exact h2 j x hx
  exact cO hy
lemma zX (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,kG (β k))
    (hg:gQ β ⊤):M≤(kA β).choose 2:=by
 obtain ⟨U,hU,hgU⟩:=z5 β hg
 obtain ⟨v,hv⟩:=Dk (F:=F) R (kA β) hU
 have K9:ZQ F (ZF v)=U:=hv
 have jp:=yJ β hA v
 rw[K9]at jp
 have o9:ZQ F
     (ZF (fun q:tj (kA β)=>jo β (v q.1.1) (v q.1.2)))=⊤:=by
   apply top_unique
   unfold gQ at hgU
   rw[← hgU]
   exact YU.2 jp
 have h1:finrank F (ZQ F
     (ZF (fun q:tj (kA β)=>jo β (v q.1.1) (v q.1.2))))≤
     Zq (tj (kA β)):=
   finrank_range_le_card (fun q:tj (kA β)=>jo β (v q.1.1) (v q.1.2))
 rw[o9,SY,Wh,NX]at h1
 exact h1
def d7 (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) (k:ℕ):
    Submodule F (Fin M→F):=
  ZQ F {w | ∃ a b,a<b∧b<k∧w=jo β (u a) (u b)}
def kd (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) (t:ℕ):
    Prop:=
  ∀ k,1≤k→k<t→d7 β u k≠d7 β u (k+1)
lemma kW (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) {a b k:ℕ}
    (hab:a<b) (oN:b<k):jo β (u a) (u b)∈d7 β u k:=
  Z1 ⟨a,b,hab,oN,rfl⟩
lemma EW (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) {k l:ℕ}
    (hkl:k≤l):d7 β u k≤d7 β u l:=by
 apply Submodule.span_mono
 rintro _ ⟨a,b,hab,oN,rfl⟩
 exact ⟨a,b,hab,by omega,rfl⟩
lemma pU (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {k:ℕ}
    {S:Submodule F (Fin M→F)} (h:∀ a b,a<b→ b<k→jo β (u a) (u b)∈S):
    d7 β u k≤S:=by
 rw[d7,YU]
 rintro _ ⟨a,b,hab,oN,rfl⟩
 exact h a b hab oN
lemma Ds (β:Fin M→Matrix (Fin R) (Fin R) F) {u u':ℕ→(Fin R→F)} {k:ℕ}
    (h:∀ i<k,u i=u' i):d7 β u k=d7 β u' k:=by
 apply le_antisymm
 · refine pU β fun a b hab oN=>?_
   rw[h a (by omega),h b oN]
   exact kW β u' hab oN
 · refine pU β fun a b hab oN=>?_
   rw[← h a (by omega), ← h b oN]
   exact kW β u hab oN
lemma Qy (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)):
    d7 β u 1=⊥:=by
 refine le_antisymm ?_ bot_le
 refine pU β fun a b hab hb=>?_
 exact absurd hab (by omega)
lemma Ak (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)}
    {s:ℕ} (h:d7 β u s≠d7 β u (s+1)):
    ∃ a<s,jo β (u a) (u s)∉d7 β u s:=by
 by_contra hc
 push_neg at hc
 apply h
 apply le_antisymm (EW β u (XV s))
 refine pU β fun a b hab hb=>?_
 by_cases KZ:b<s
 · exact kW β u hab KZ
 · rw[show b=s by omega]
   exact hc a (by omega)
lemma Ek (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (hu:kd β u t):∀ k,1≤k→k≤t→k - 1≤finrank F (d7 β u k):=by
 intro k
 induction k with
 | zero=>intro h; exact absurd h (by norm_num)
 | succ k ih=>
   intro _ qB
   rcases Yj k with hk | hk
   · subst hk
     simp
   · have h1:=ih hk (by omega)
     have f5:d7 β u k<d7 β u (k+1):=
       lt_of_le_of_ne (EW β u (XV k)) (hu k hk (by omega))
     have h2:=Submodule.finrank_lt_finrank_of_lt f5
     omega
lemma vO (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (hu:kd β u t) (ht:1≤t):t≤M+1:=by
 have h1:=Ek β hu t ht YD
 have h2:=RI (d7 β u t)
 rw[Wh]at h2
 omega
lemma Kb (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (ht:2≤t) (hu:kd β u t) {x y:Fin R→F}
    (Cu:jo β x y∉d7 β u t):∃ u':ℕ→(Fin R→F),kd β u' (t+1):=by
 by_cases hc:∃ a<t,∃ v,jo β (u a) v∉d7 β u t
 · obtain ⟨a,ha,v,hv⟩:=hc
   set u':ℕ→(Fin R→F):= fun i=>if i<t then u i else v with oF
   have hW:∀ k≤t,d7 β u' k=d7 β u k:= fun k hk=>
     Ds β fun i hi=> (if_pos (show i<t by omega):u' i=u i)
   refine ⟨u',fun k Bw qB=>?_⟩
   rcases XU k t with hk | hk
   · rw[hW k hk.le,hW (k+1) (by omega)]
     exact hu k Bw hk
   · rw[show k=t by omega,hW t YD]
     intro heq
     apply hv
     have hm:=kW β u' ha (show t<t+1 by omega)
     have e1:u' a=u a:=if_pos ha
     have e2:u' t=v:=if_neg (UO t)
     rw[e1,e2, ← heq]at hm
     exact hm
 · have hc':∀ a<t,∀ v,jo β (u a) v∈d7 β u t:= fun a ha v=>by
     by_contra hn
     exact hc ⟨a,ha,v,hn⟩
   obtain ⟨s,rfl⟩:∃ s,t=s+1:=⟨t - 1,by omega⟩
   obtain ⟨a0,ML,abp⟩:=Ak β (hu s (by omega) (by omega))
   have hw :∃ w,(∃ a<s,jo β (u a) w∉d7 β u s)∧
       jo β w y∉d7 β u (s+1):=by
    by_cases oQ:∃ a<s,jo β (u a) x∉d7 β u s
    · exact ⟨x,oQ,Cu⟩
    · push_neg at oQ
      refine ⟨u s+x,⟨a0,ML,?_⟩,?_⟩
      · rw[map_add,Submodule.add_mem_iff_left _ (oQ a0 ML)]
        exact abp
      · rw [map_add,WH,
          Submodule.add_mem_iff_right _ (hc' s (by omega) y)]
        exact Cu
   obtain ⟨w,Fd,H_⟩:=hw
   set u':ℕ→(Fin R→F):= fun i=>if i<s then u i else if i=s then w else y with oF
   have e1:∀ i<s,u' i=u i:= fun i hi=>if_pos hi
   have e2:u' s=w:=by
    show (if s<s then u s else if s=s then w else y)=w
    rw[if_neg (UO s),if_pos rfl]
   have e3:u' (s+1)=y:=by
    show (if s+1<s then u (s+1) else if s+1=s then w else y)=y
    rw[if_neg (show ¬ (s+1<s) by omega),if_neg (show ¬ (s+1=s) by omega)]
   have hW:∀ k≤ s,d7 β u' k=d7 β u k:= fun k hk=>
     Ds β fun i hi=>e1 i (by omega)
   have cO:d7 β u' (s+1)≤d7 β u (s+1):=by
    refine pU β fun a b hab hb=>?_
    by_cases KZ:b<s
    · rw[e1 a (by omega),e1 b KZ]
      exact kW β u hab (by omega)
    · rw[show b=s by omega,e1 a (by omega),e2]
      exact hc' a (by omega) w
   refine ⟨u',fun k Bw qB=>?_⟩
   by_cases BG:k<s
   · rw[hW k (by omega),hW (k+1) (by omega)]
     exact hu k Bw (by omega)
   · by_cases lQ:k=s
     · rw[lQ,hW s YD]
       obtain ⟨a,ha,wJ⟩:=Fd
       intro heq
       apply wJ
       have hm:=kW β u' ha (show s<s+1 by omega)
       rw[e1 a ha,e2, ← heq]at hm
       exact hm
     · rw[show k=s+1 by omega]
       intro heq
       apply H_
       have hm:=kW β u' (show s<s+1 by omega) (show s+1<s+1+1 by omega)
       rw[e2,e3, ← heq]at hm
       exact cO hm
lemma sO (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:gQ β ⊤)
    {S:Submodule F (Fin M→F)} (hS:S≠⊤):∃ x y,jo β x y∉S:=by
 by_contra hc
 push_neg at hc
 apply hS
 apply top_unique
 unfold gQ at hg
 rw[← hg,YU]
 rintro _ ⟨x, -,y, -,rfl⟩
 exact hc x y
lemma D6 (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:gQ β ⊤)
    (hM:1≤M):∃ u:ℕ→(Fin R→F),∃ t,kd β u t∧2≤t∧
      d7 β u t=⊤:=by
 have d8:(⊥:Submodule F (Fin M→F))≠⊤:=by
  intro h
  have cI:(Yz (⟨0,hM⟩:Fin M) (1:F):Fin M→F)∈
      (⊥:Submodule F (Fin M→F)):=by
   rw[h]
   exact XK
  rw[VS]at cI
  have:= congrFun cI ⟨0,hM⟩
  simp at this
 obtain ⟨x0,y0,h0⟩:=sO β hg d8
 have step:∀ j,∃ u:ℕ→(Fin R→F),∃ t,kd β u t∧2≤t∧
     (d7 β u t=⊤∨j+2≤t):=by
  intro j
  induction j with
  | zero=>
    set u:ℕ→(Fin R→F):= fun i=>if i=0 then x0 else y0 with hu
    refine ⟨u,2,fun k Bw Oy=>?_,YD,XQ (by norm_num)⟩
    rw[show k=1 by omega,Qy]
    intro heq
    apply h0
    have hm:=kW β u (show 0<1 by norm_num) (show 1<1+1 by norm_num)
    have e0:u 0=x0:=if_pos rfl
    have e1:u 1=y0:=if_neg (by norm_num)
    rw[e0,e1, ← heq]at hm
    exact hm
  | succ j ih=>
    obtain ⟨u,t,hu,ht,hor⟩:=ih
    by_cases o9:d7 β u t=⊤
    · exact ⟨u,t,hu,ht,Y7 o9⟩
    · have hj:j+2≤t:=hor.resolve_left o9
      obtain ⟨x,y,Cu⟩:=sO β hg o9
      obtain ⟨u',oF⟩:=Kb β ht hu Cu
      exact ⟨u',t+1,oF,by omega,XQ (by omega)⟩
 obtain ⟨u,t,hu,ht,hor⟩:=step M
 rcases hor with h | h
 · exact ⟨u,t,hu,ht,h⟩
 · have:=vO β hu (by omega)
   omega
lemma JT (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:gQ β ⊤):
    kA β≤M+1:=by
 rcases Yj M with hM | hM
 · subst hM
   have rL:gQ β ⊥:=by
    unfold gQ
    apply Yo.2
    intro w _
    rw[Subsingleton.elim w 0]
    exact VA _
   have:=wN β (U:=⊥) (d:=0) (by simp) rL
   omega
 · obtain ⟨u,t,hu,ht,o9⟩:=D6 β hg hM
   set U:Submodule F (Fin R→F):=ZQ F (ZF (fun i:Fin t=>u i))
   have abR:∀ i<t,u i∈U:= fun i hi=>
     Z1 ⟨⟨i,hi⟩,rfl⟩
   have hgU:gQ β U:=by
    unfold gQ
    apply top_unique
    rw[← o9]
    refine pU β fun a b hab hb=>?_
    exact Z1 (LR β (abR a (by omega)) (abR b hb))
   have h1:=wN β rfl hgU
   have h2:finrank F U≤Zq (Fin t):=
     finrank_range_le_card (fun i:Fin t=>u i)
   have h3:=vO β hu (by omega)
   rw[Zz]at h2
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
def jg (B:V→ₗ[F] V→ₗ[F] W) (U:Submodule F V):Prop:=
  ZQ F {w | ∃ x∈U,∃ y∈U,w=B x y}=⊤
noncomputable def x8 (B:V→ₗ[F] V→ₗ[F] W):ℕ:=
  sInf {d | ∃ U:Submodule F V,finrank F U=d∧jg B U}
noncomputable def gW (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V) (bW:Basis (Fin r2) F W):
    Fin r2→Matrix (Fin r1) (Fin r1) F:=
  fun k i j=>bW.repr (B (bV i) (bV j)) k
lemma equivFun_symm_single (b:Basis (Fin r1) F V) (i:Fin r1):
    b.equivFun.symm (Yz i 1)=b i:=by
 rw[Basis.equivFun_symm_apply]
 simp[Um]
lemma BU (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (x y:Fin r1→F):
    jo (gW B bV bW) x y=
      bW.equivFun (B (bV.equivFun.symm x) (bV.equivFun.symm y)):=by
 have h :jo (gW B bV bW)=
     (B.compl₁₂ bV.equivFun.symm.toLinearMap bV.equivFun.symm.toLinearMap).compr₂
       bW.equivFun.toLinearMap:=by
  refine LinearMap.ext_basis (Vz F (Fin r1)) (Vz F (Fin r1)) fun i j=>?_
  show jo (gW B bV bW) (Vz F (Fin r1) i) (Vz F (Fin r1) j)=
    bW.equivFun (B (bV.equivFun.symm (Vz F (Fin r1) i))
      (bV.equivFun.symm (Vz F (Fin r1) j)))
  rw [OX,OX,equivFun_symm_single,equivFun_symm_single,
    QD]
  funext k
  rw[aad,Basis.equivFun_apply]
  rfl
 rw[h]
 rfl
lemma Kt (B:V→ₗ[F] V→ₗ[F] W) (hB:∀ x,B x x =0) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (k:Fin r2):kG (gW B bV bW k):=by
 refine ⟨fun i=>?_,fun i j=>?_⟩
 · show bW.repr (B (bV i) (bV i)) k=0
   rw[hB,map_zero,Finsupp.zero_apply]
 · have h2:B (bV j) (bV i)= -B (bV i) (bV j):=by
     have:=hB (bV i+bV j)
     simp only[map_add,WH,hB,zero_add,add_zero]at this
     rw[eq_neg_iff_add_eq_zero]
     first
       | exact this
       | exact (add_comm _ _).trans this
   show bW.repr (B (bV j) (bV i)) k= -bW.repr (B (bV i) (bV j)) k
   rw[h2,map_neg,Finsupp.neg_apply]
lemma F9 (bV:Basis (Fin r1) F V) (U:Submodule F V):
    (U.map bV.equivFun.toLinearMap).map bV.equivFun.symm.toLinearMap=U:=by
 rw[← Submodule.map_comp]
 convert Submodule.map_id U
 ext v
 simp
lemma m7 (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (U:Submodule F (Fin r1→F)):
    gQ (gW B bV bW) U↔jg B (U.map bV.equivFun.symm.toLinearMap):=by
 set U':=U.map bV.equivFun.symm.toLinearMap with MZ
 set S:Set W:={w | ∃ x∈U',∃ y∈U',w=B x y} with hS
 have hv:QP (gW B bV bW) U=bW.equivFun.toLinearMap '' S:=by
  ext w
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    refine ⟨B (bV.equivFun.symm x) (bV.equivFun.symm y),
      ⟨_,VY hx,_,VY hy,rfl⟩,?_⟩
    exact (BU B bV bW x y).symm
  · rintro ⟨_,⟨x',oQ,y',IE,rfl⟩,rfl⟩
    obtain ⟨x,hx,rfl⟩:=WZ.1 oQ
    obtain ⟨y,hy,rfl⟩:=WZ.1 IE
    exact ⟨x,hx,y,hy,(BU B bV bW x y).symm⟩
 unfold gQ jg
 rw[hv,Submodule.span_image]
 first
   | exact SP
   | rw[SP (RV _),LinearEquiv.ker,sup_bot_eq]
lemma IU (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W):kA (gW B bV bW)=x8 B:=by
 unfold kA x8
 congr 1
 ext d
 constructor
 · rintro ⟨U,hU,hg⟩
   exact ⟨U.map bV.equivFun.symm.toLinearMap,by rw[W6,hU],
     (m7 B bV bW U).1 hg⟩
 · rintro ⟨U',MZ,hg⟩
   refine ⟨U'.map bV.equivFun.toLinearMap,by rw[W6,MZ],?_⟩
   rw[m7,F9]
   exact hg
lemma wP (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W):gQ (gW B bV bW) ⊤↔jg B ⊤:=by
 rw[m7,Submodule.map_top,RV]
end Transport
end OMA.SimsLite.Alt2
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section jD
variable {p:ℕ} {H:Type u} [Group H]
abbrev DG (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):Subgroup (Abelianization H):=
  K.map ZJ⊔(powMonoidHom p:Abelianization H→*Abelianization H).range
abbrev jD (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):Type u:=
  Abelianization H⧸DG p H K
def zR (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):H→*jD p H K:=
  (ZG (DG p H K)).comp ZJ
lemma jZ (K:Subgroup H):Zn (zR p H K):=by
 intro x
 obtain ⟨a,rfl⟩:=Z3 x
 obtain ⟨g,hg⟩:=Z3 (a:H⧸commutator H)
 refine ⟨g,?_⟩
 rw[← hg]
 rfl
lemma aaE (K:Subgroup H) (x:jD p H K):x^p=1:=by
 obtain ⟨a,rfl⟩:=Z3 x
 rw[← Wg,Yf]
 exact ZL (RW.mpr ⟨a,rfl⟩)
lemma Bm {K:Subgroup H} (h1:commutator H≤K) (h2:∀ g:H,g^p∈K):
    (zR p H K).ker=K:=by
 have cO:(powMonoidHom p:Abelianization H→*Abelianization H).range≤
     K.map ZJ:=by
  rintro _ ⟨a,rfl⟩
  obtain ⟨g,hg⟩:=Z3 (a:H⧸commutator H)
  refine Zj.mpr ⟨g^p,h2 g,?_⟩
  rw[map_pow]
  rw[← hg]
  rfl
 have hK:DG p H K=K.map ZJ:=sup_eq_left.mpr cO
 rw [zR, ← RQ,YV,hK,V8,
   WV,sup_eq_left.mpr h1]
lemma H7 {K:Subgroup H} (h1:commutator H≤K) (h2:∀ g:H,g^p∈K):
    ZB (jD p H K)=K.index:=by
 have e:=YJ
   (Xj (zR p H K) (jZ K)).toEquiv
 rw[Bm h1 h2]at e
 exact e.symm
variable [hp:Fact p.Prime]
lemma N7 (K:Subgroup H) (x:Additive (jD p H K)):p•x =0:=by
 show ZC (ZW x^p)=ZC 1
 rw[aaE]
instance acl (K:Subgroup H):Module (ZMod p) (Additive (jD p H K)):=
  letI:NeZero p:=⟨hp.out.ne_zero⟩
  VK (N7 K)
lemma jr (K:Subgroup H) (c:ZMod p) (x:Additive (jD p H K)):
    c•x = c.val•x:=by
 have:NeZero p:=⟨hp.out.ne_zero⟩
 conv_lhs=>rw[← R4 c]
 exact UJ (ZMod p) c.val x
lemma i8 [Finite H] (K:Subgroup H):
    ZB (jD p H K)=p^WA (ZMod p) (Additive (jD p H K)):=by
 have:Finite (jD p H K):=Zy _ (jZ K)
 have:Finite (Additive (jD p H K)):=inferInstance
 have:Module.Free (ZMod p) (Additive (jD p H K)):=
   TN (ZMod p) (Additive (jD p H K))
 have:Yx (ZMod p) (Additive (jD p H K)):=inferInstance
 have h:=W0 (K:=ZMod p) (V:=Additive (jD p H K))
 rw[TP]at h
 exact h
end jD
section Frame0
variable (p:ℕ) (G:Type u) [Group G]
abbrev VQ:Type u:=jD p G (cE p G)
abbrev WQ:Type u:=jD p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))
def dH:G→*VQ p G:=zR p G (cE p G)
def jL:lcs G 1→*WQ p G:=zR p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))
def cw {G:Type u} [Group G] (g h:G):lcs G 1:=⟨⁅g,h⁆,b7 g h⟩
variable {p G}
lemma cV:Zn (dH p G):=jZ _
lemma lP:Zn (jL p G):=jZ _
lemma s9:commutator G≤ cE p G:=Z5
lemma lO:
    commutator (lcs G 1)≤(pN p G).subgroupOf (lcs G 1):=by
 rw[WE,Z7]
 intro a _ b _
 rw[ZT]
 show ⁅(a:G),(b:G)⁆∈pN p G
 exact eo p (a8 (n:=1) a.2 (b:G))
lemma lJ (g:lcs G 1):g^p∈(pN p G).subgroupOf (lcs G 1):=by
 rw[ZT]
 have e:((g^p:lcs G 1):G)=(g:G)^p:=map_pow (lcs G 1).subtype g p
 rw[e]
 exact ZL (ZD ⟨g,rfl⟩)
lemma Ky:(dH p G).ker= cE p G:=
  Bm s9 (gG p)
lemma JO:(jL p G).ker=(pN p G).subgroupOf (lcs G 1):=
  Bm lO lJ
lemma Bb {g g':G}:dH p G g=dH p G g'↔g*g'⁻¹∈cE p G:=by
 rw[← mul_inv_eq_one, ← Wq, ← YP, ← Zm,Ky]
lemma C7 {a b:lcs G 1} (h:(a:G)*(b:G)⁻¹∈pN p G):
    jL p G a=jL p G b:=by
 have hk:a*b⁻¹∈(jL p G).ker :=by
  rw[JO,ZT]
  exact h
 rw[Zm,YP,Wq,mul_inv_eq_one]at hk
 exact hk
lemma t6 {a:lcs G 1} (h:(a:G)∈pN p G):jL p G a=1:=by
 rw[← Zm,JO,ZT]
 exact h
lemma wX:ZB (VQ p G)=(cE p G).index:=
  H7 s9 (gG p)
lemma xW:ZB (WQ p G)=((pN p G).subgroupOf (lcs G 1)).index:=
  H7 lO lJ
noncomputable def oq (v:VQ p G):G:=Function.surjInv cV v
lemma xZ (v:VQ p G):dH p G (oq v)=v:=Function.surjInv_eq cV v
noncomputable def lA (v w:VQ p G):WQ p G:=jL p G (cw (oq v) (oq w))
lemma oz (g h:G):lA (dH p G g) (dH p G h)=jL p G (cw g h):=by
 show jL p G (cw (oq (dH p G g)) (oq (dH p G h)))=jL p G (cw g h)
 apply C7
 have hg:oq (dH p G g)*g⁻¹∈cE p G:=Bb.mp (xZ _)
 have hh:oq (dH p G h)*h⁻¹∈cE p G:=Bb.mp (xZ _)
 have e1:=vX p g (oq (dH p G g)) (oq (dH p G h)) hg
 have e2:=D4 p g h (oq (dH p G h)) hh
 have e3:=Yq _ e1 e2
 rw[UQ,inv_mul_cancel_left]at e3
 exact e3
lemma Lx (v v' w:VQ p G):lA (v*v') w=lA v w*lA v' w:=by
 obtain ⟨g,rfl⟩:= cV v
 obtain ⟨g',rfl⟩:= cV v'
 obtain ⟨h,rfl⟩:= cV w
 have e:dH p G g*dH p G g'=dH p G (g*g'):=(YP _ _ _).symm
 rw[e,oz,oz,oz, ← YP]
 apply C7
 exact D9 p g g' h
lemma J_ (v w w':VQ p G):lA v (w*w')=lA v w*lA v w':=by
 obtain ⟨g,rfl⟩:= cV v
 obtain ⟨h,rfl⟩:= cV w
 obtain ⟨h',rfl⟩:= cV w'
 have e:dH p G h*dH p G h'=dH p G (h*h'):=(YP _ _ _).symm
 rw[e,oz,oz,oz, ← YP]
 apply C7
 exact Dt p g h h'
lemma aat (v:VQ p G):lA v v=1:=by
 obtain ⟨g,rfl⟩:= cV v
 have e:cw g g=1:=Zu (commutatorElement_self g)
 rw[oz,e,X9]
lemma Mj:
    ZA (ZF (fun vw:VQ p G×VQ p G=>lA vw.1 vw.2))=⊤:=by
  have h1:ZA (ZF (fun xy:G×G=> ⁅xy.1,xy.2⁆))≤
      ((ZA (ZF (fun vw:VQ p G×VQ p G=>lA vw.1 vw.2))).comap
        (jL p G)).map (lcs G 1).subtype:=by
    rw[ZE]
    rintro _ ⟨⟨x,y⟩,rfl⟩
    refine Zj.mpr ⟨cw x y,?_,rfl⟩
    rw[Zp, ← oz]
    exact ZD ⟨(dH p G x,dH p G y),rfl⟩
  have h2:pN p G≤
      ((ZA (ZF (fun vw:VQ p G×VQ p G=>lA vw.1 vw.2))).comap
        (jL p G)).map (lcs G 1).subtype:=by
    intro n hn
    refine Zj.mpr ⟨⟨n,kO p hn⟩,?_,rfl⟩
    rw[Zp,t6 (a:=⟨n,kO p hn⟩) hn]
    exact Yl _
  have h3:=(LO (G:=G) p).trans (sup_le h1 h2)
  rw[Yo]
  intro w _
  obtain ⟨a,rfl⟩:=lP w
  obtain ⟨b,hb,hba⟩:=Zj.mp (h3 a.2)
  have e:b=a:=Zu hba
  rw[← e]
  exact hb
section Lin
variable [hp:Fact p.Prime]
noncomputable def lG (v w:Additive (VQ p G)):Additive (WQ p G):=
  ZC (lA (ZW v) (ZW w))
lemma xg (v v' w:Additive (VQ p G)):
    lG (v+v') w=lG v w+lG v' w:=by
 show ZC (lA (ZW v*ZW v') (ZW w))=
   ZC (lA (ZW v) (ZW w)*
     lA (ZW v') (ZW w))
 rw[Lx]
lemma wI (v w w':Additive (VQ p G)):
    lG v (w+w')=lG v w+lG v w':=by
 show ZC (lA (ZW v) (ZW w*ZW w'))=
   ZC (lA (ZW v) (ZW w)*
     lA (ZW v) (ZW w'))
 rw[J_]
lemma FL (c:ZMod p) (v w:Additive (VQ p G)):
    lG (c•v) w= c•lG v w:=by
 rw[jr,jr]
 exact map_nsmul (RY (fun v=>lG v w) (fun a b=>xg a b w))
   c.val v
lemma Eb (c:ZMod p) (v w:Additive (VQ p G)):
    lG v (c•w)= c•lG v w:=by
 rw[jr,jr]
 exact map_nsmul (RY (fun w=>lG v w) (fun a b=>wI v a b))
   c.val w
noncomputable def cP:
    Additive (VQ p G)→ₗ[ZMod p] Additive (VQ p G)→ₗ[ZMod p] Additive (WQ p G):=
  Pz (ZMod p) lG xg FL wI
    Eb
lemma Dj (v w:Additive (VQ p G)):
    cP v w=ZC (lA (ZW v) (ZW w)):=rfl
lemma CY (g h:G):
    cP (ZC (dH p G g)) (ZC (dH p G h))=
      ZC (jL p G (cw g h)):=by
 rw[Dj]
 exact congrArg ZC (oz g h)
lemma EH (v:Additive (VQ p G)):cP v v=0:=by
 rw[Dj,aat]
 rfl
lemma N8:
    ZQ (ZMod p)
      (ZF (fun vw:Additive (VQ p G)×Additive (VQ p G)=>cP vw.1 vw.2))=⊤:=by
  let T:Submodule (ZMod p) (Additive (WQ p G)):=ZQ (ZMod p)
    (ZF (fun vw:Additive (VQ p G)×Additive (VQ p G)=>cP vw.1 vw.2))
  let K :Subgroup (WQ p G):=
    { carrier :={w | ZC w∈T}
      mul_mem':= fun {a b} ha hb=>by
        have u6:ZC a∈T:=ha
        have Io:ZC b∈T:=hb
        exact Rj T u6 Io
      one_mem':=by
        have h0:(0:Additive (WQ p G))∈T:=VA T
        exact h0
      inv_mem':= fun {a} ha=>by
        have u6:ZC a∈T:=ha
        have h1: - ZC a∈T:=Rk T u6
        exact h1 }
  have cO:ZA (ZF (fun vw:VQ p G×VQ p G=>lA vw.1 vw.2))≤K:=by
    rw[ZE]
    rintro _ ⟨⟨v,w⟩,rfl⟩
    show ZC (lA v w)∈ZQ (ZMod p)
      (ZF (fun vw:Additive (VQ p G)×Additive (VQ p G)=>cP vw.1 vw.2))
    exact Z1 ⟨(ZC v,ZC w),rfl⟩
  rw[Yo]
  intro x _
  have hx:ZW x∈K:= cO (by rw[Mj]; exact ZO _)
  exact hx
noncomputable def r2 (p:ℕ) [Fact p.Prime] (G:Type u) [Group G]:ℕ:=
  WA (ZMod p) (Additive (WQ p G))
end Lin
end Frame0
section Frame
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G] [Finite G]
lemma lD {a b:ℕ} (hp2:2≤p) (h:p^a≤p^b):a≤b:=by
 by_contra hc
 push_neg at hc
 have h1:p^(b+1)≤p^a:=Zk (by omega) hc
 have h2:0<p^b:=X7 (SZ _ (by omega))
 rw[Xr]at h1
 nlinarith
lemma My (hG:IsPGroup p G):ZB (VQ p G)=p^ZV G:=by
 rw[wX]
 exact oA hG
lemma Lc (hG:IsPGroup p G):
    WA (ZMod p) (Additive (VQ p G))=ZV G:=by
 have h1:=i8 (p:=p) (cE p G)
 rw[My hG]at h1
 exact (Zd hp.out.two_le h1).symm
lemma aaN:ZB (WQ p G)=p^r2 p G:=
  i8 _
lemma xT:ZB (lcs G 1)=ZB (pN p G)*p^r2 p G:=by
 have h1:=Z4 ((pN p G).subgroupOf (lcs G 1))
 have h2:=YJ (XM (kO (G:=G) p)).toEquiv
 have h3:((pN p G).subgroupOf (lcs G 1)).index =p^r2 p G:=by
  rw[← aaN (p:=p) (G:=G)]
  exact xW.symm
 rw[h3,h2]at h1
 exact h1.symm
lemma B8:
    (cE p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).comap
      (ZG ((lcs G 2).subgroupOf (lcs G 1)))=(pN p G).subgroupOf (lcs G 1):=by
 have hKN:(lcs G 2).subgroupOf (lcs G 1)≤(pN p G).subgroupOf (lcs G 1):=by
  intro a ha
  rw[ZT]at ha⊢
  exact eo p ha
 apply le_antisymm
 · have h1:cE p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))≤
       ((pN p G).subgroupOf (lcs G 1)).map
         (ZG ((lcs G 2).subgroupOf (lcs G 1))):=by
     refine sup_le ?_ ?_
     · rw[ZE]
       rintro _ ⟨q,rfl⟩
       obtain ⟨a,rfl⟩:=YI ((lcs G 2).subgroupOf (lcs G 1)) q
       exact Zj.mpr ⟨a^p,lJ a,map_pow _ a p⟩
     · rw [WE,Z7]
       intro q1 _ q2 _
       obtain ⟨a,rfl⟩:=YI ((lcs G 2).subgroupOf (lcs G 1)) q1
       obtain ⟨b,rfl⟩:=YI ((lcs G 2).subgroupOf (lcs G 1)) q2
       refine Zj.mpr ⟨⁅a,b⁆,?_,YW _ a b⟩
       exact lO
         (Zo (ZO a) (ZO b))
   refine (Subgroup.comap_mono h1).trans ?_
   rw[V8,YV]
   exact sup_le YD hKN
 · intro a ha
   rw[ZT]at ha
   have h2:pN p G≤((cE p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).comap
       (ZG ((lcs G 2).subgroupOf (lcs G 1)))).map (lcs G 1).subtype:=by
    refine sup_le ?_ ?_
    · intro n hn
      have hn1:n∈lcs G 1:=bC (by norm_num) hn
      refine Zj.mpr ⟨⟨n,hn1⟩,?_,rfl⟩
      rw[Zp]
      have e:ZG ((lcs G 2).subgroupOf (lcs G 1)) ⟨n,hn1⟩=1:=by
       rw[YY,Yf,ZT]
       exact hn
      rw[e]
      exact Yl _
    · rw[ZE]
      rintro _ ⟨g,rfl⟩
      refine Zj.mpr ⟨g^p,?_,map_pow (lcs G 1).subtype g p⟩
      rw[Zp,map_pow]
      exact gG p _
   obtain ⟨b,hb,hba⟩:=Zj.mp (h2 ha)
   have e:b=a:=Zu hba
   rw[← e]
   exact hb
lemma m8 (hG:IsPGroup p G):
    ZV (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))=r2 p G:=by
 have hQ:IsPGroup p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)):=
   (hG.to_subgroup (lcs G 1)).to_quotient _
 have h1:(cE p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).index =
     p^ZV (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)):= oA hQ
 have h2:((pN p G).subgroupOf (lcs G 1)).index =p^r2 p G:=by
  rw[← xW,aaN]
 rw [← B8,Subgroup.index_comap_of_surjective _
   (YI _),h1]at h2
 exact Zd hp.out.two_le h2
lemma aaB (hG:IsPGroup p G):lcs G 1≤frattini G:=by
 rw[ew hG, ← eO (G:=G)]
 exact Z5
lemma Mw (hG:IsPGroup p G) (H:Subgroup G):
    lcs G 1≤⁅H,H⁆⊔pN p G↔⁅H,H⁆⊔lcs G 2=lcs G 1:=by
 have Nj:⁅H,H⁆≤lcs G 1:=XE le_top le_top
 have h21:lcs G 2≤lcs G 1:=bC (by norm_num)
 constructor
 · intro h
   refine le_antisymm (sup_le Nj h21) ?_
   have hP:IsPGroup p (lcs G 1):=hG.to_subgroup (lcs G 1)
   have hS:lcs G 1≤((⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)⊔
       frattini (lcs G 1)).map (lcs G 1).subtype:=by
    rw[ew hP]
    refine h.trans (sup_le ?_ (sup_le ?_ ?_))
    · intro x hx
      refine Zj.mpr ⟨⟨x,Nj hx⟩,ZK ?_,rfl⟩
      rw[ZT]
      exact ZK hx
    · intro x hx
      refine Zj.mpr ⟨⟨x,h21 hx⟩,ZK ?_,rfl⟩
      rw[ZT]
      exact ZL hx
    · rw [ZE]
      rintro _ ⟨g,rfl⟩
      exact Zj.mpr ⟨g^p,ZL (gG p g),
        map_pow (lcs G 1).subtype g p⟩
   have hL:(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)⊔frattini (lcs G 1)=⊤:=by
    rw[Yo]
    intro a _
    obtain ⟨b,hb,hba⟩:=Zj.mp (hS a.2)
    have e:b=a:=Zu hba
    rw[← e]
    exact hb
   have hLt:(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)=⊤:=by
    have h3:=eD
      (s :=(((⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1):Subgroup (lcs G 1)):
        Set (lcs G 1))) (by rw[UR]; exact hL)
    rwa[UR]at h3
   intro x hx
   have cI:(⟨x,hx⟩:lcs G 1)∈(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1):=by
    rw[hLt]
    exact ZO _
   exact ZT.mp cI
 · intro h
   calc lcs G 1=⁅H,H⁆⊔lcs G 2:=h.symm
     _≤⁅H,H⁆⊔pN p G:=SD (eo p) _
lemma Dx (T:Finset G):∃ x:ℕ→G,x '' ZH T.card=(T:Set G):=by
 refine ⟨fun i=>if h:i<T.card then ((T.equivFin.symm ⟨i,h⟩:T):G) else 1,?_⟩
 ext y
 constructor
 · rintro ⟨i,hi,rfl⟩
   have gJ:i<T.card:=hi
   dsimp only
   rw[dif_pos gJ]
   exact (T.equivFin.symm ⟨i,gJ⟩).2
 · intro hy
   have hj:=(T.equivFin ⟨y,hy⟩).2
   refine ⟨(T.equivFin ⟨y,hy⟩:ℕ),hj,?_⟩
   dsimp only
   rw[dif_pos hj,Fin.eta,UB]
lemma BX (H:Subgroup G):
    ∃ x:ℕ→G,ZA (x '' ZH (ZV H))=H:=by
 classical
 obtain ⟨T,Ij,hTg⟩:=SN H
 have dS:(T.image XJ).card=ZV H:=by
  rw[XG T Subtype.val_injective,Ij]
 obtain ⟨x,hx⟩:=Dx (T.image XJ)
 refine ⟨x,?_⟩
 rw[← dS,hx]
 apply le_antisymm
 · rw[ZE]
   intro y hy
   obtain ⟨z, -,rfl⟩:=Xp.mp hy
   exact z.2
 · intro h hh
   have h1:ZA (T:Set H)≤
       (ZA ((T.image XJ:Finset G):Set G)).comap H.subtype:=by
    rw[ZE]
    intro z hz
    exact ZD (Y9.mpr (Vr XJ hz))
   have h2:(⟨h,hh⟩:H)∈ZA (T:Set H):=by
    rw[hTg]
    exact ZO _
   exact h1 h2
lemma vE (v:ℕ→G) (t:ℕ):
    ZV (ZA (v '' ZH t))≤t:=by
 classical
 have e:v '' ZH t=(((ZM t).image v:Finset G):Set G):=by
  rw[Tu,Finset.coe_range]
 rw[Ri (congrArg ZA e)]
 exact (Subgroup.rank_closure_finset_le_card _).trans
   (UZ.trans (Xf t).le)
noncomputable def s1 (p:ℕ) (G:Type u) [Group G]:ℕ:=YZ p (lcs G 1).index
noncomputable def j9 (p:ℕ) (G:Type u) [Group G] [Finite G]:ℕ:=
  s1 p G - ZV G
lemma oD (hG:IsPGroup p G):(lcs G 1).index =p^s1 p G:=by
 obtain ⟨n,hn⟩:=IsPGroup.iff_card.mp hG
 have hd:(lcs G 1).index∣p^n:=by
  rw[← hn]
  exact Subgroup.index_dvd_card (lcs G 1)
 obtain ⟨k, -,hk⟩:=(Yp hp.out).mp hd
 rw[s1,hk,Nat.log_pow hp.out.one_lt]
lemma QN (hG:IsPGroup p G):ZV G≤ s1 p G:=by
 have hd:(frattini G).index∣(lcs G 1).index:=Subgroup.index_dvd_of_le (aaB hG)
 have hi:(frattini G).index =p^ZV G:=k5 hG
 rw[hi,oD hG]at hd
 exact lD hp.out.two_le
   (Nat.le_of_dvd (X7 (SZ _ hp.out.ne_zero)) hd)
lemma o_ (hG:IsPGroup p G):
    (lcs G 1).index =p^(ZV G+j9 p G):=by
 rw[oD hG,j9,Wt (QN hG)]
end Frame
end OMA.SimsLite
namespace OMA.SimsLite.Alt2
open Module
universe u
section Bridge
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G]
def Nw (H:Subgroup G):AddSubgroup (Additive (VQ p G)) where
  carrier :={x | ∃ h∈H,ZC (dH p G h)=x}
  add_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a*b,H.mul_mem ha hb,by rw[YP]; rfl⟩
  zero_mem':=⟨1,H.one_mem,by rw[X9]; rfl⟩
  neg_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹,H.inv_mem ha,by rw[Wq]; rfl⟩
def aaR (K:Subgroup G):AddSubgroup (Additive (WQ p G)) where
  carrier :={w | ∃ a:lcs G 1,(a:G)∈K∧ZC (jL p G a)=w}
  add_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a*b,K.mul_mem ha hb,by rw[YP]; rfl⟩
  zero_mem':=⟨1,K.one_mem,by rw[X9]; rfl⟩
  neg_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹,K.inv_mem ha,by rw[Wq]; rfl⟩
def acR (U:Submodule (ZMod p) (Additive (VQ p G))):Subgroup G where
  carrier :={g | ZC (dH p G g)∈U}
  mul_mem':=by
    intro a b ha hb
    show ZC (dH p G (a*b))∈U
    rw[YP]
    exact U.add_mem ha hb
  one_mem':=by
    show ZC (dH p G 1)∈U
    rw[X9]
    exact U.zero_mem
  inv_mem':=by
    intro a ha
    show ZC (dH p G a⁻¹)∈U
    rw[Wq]
    exact U.neg_mem ha
def aeb (S:Submodule (ZMod p) (Additive (WQ p G))):Subgroup G where
  carrier :={g | ∃ hg:g∈lcs G 1,ZC (jL p G ⟨g,hg⟩)∈S}
  mul_mem':=by
    rintro a b ⟨ha,hSa⟩ ⟨hb,hSb⟩
    refine ⟨(lcs G 1).mul_mem ha hb,?_⟩
    show ZC (jL p G (⟨a,ha⟩*⟨b,hb⟩))∈S
    rw[YP]
    exact S.add_mem hSa hSb
  one_mem':=by
    refine ⟨(lcs G 1).one_mem,?_⟩
    show ZC (jL p G 1)∈S
    rw[X9]
    exact S.zero_mem
  inv_mem':=by
    rintro a ⟨ha,hSa⟩
    refine ⟨(lcs G 1).inv_mem ha,?_⟩
    show ZC (jL p G (⟨a,ha⟩⁻¹))∈S
    rw[Wq]
    exact S.neg_mem hSa
lemma x7 {k:ℕ} (u:Fin k→G)
    (dG:lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
      lcs G 2):
    jg (cP (p:=p) (G:=G))
      (ZQ (ZMod p) (ZF (fun i=>ZC (dH p G (u i))))):=by
  set U:=ZQ (ZMod p) (ZF (fun i=>ZC (dH p G (u i))))
  set S:=ZQ (ZMod p) {w | ∃ x∈U,∃ y∈U,w= cP (p:=p) (G:=G) x y}
  have hHU:ZA (ZF u)≤acR U:=by
   rw[ZE]
   rintro _ ⟨i,rfl⟩
   exact Z1 ⟨i,rfl⟩
  have cO:⁅ZA (ZF u),ZA (ZF u)⁆⊔lcs G 2≤
      aeb S:=by
   refine sup_le ?_ ?_
   · rw [Z7]
     intro g hg h hh
     refine ⟨b7 g h,?_⟩
     show ZC (jL p G (cw g h))∈S
     rw[← CY]
     exact Z1 ⟨ZC (dH p G g),hHU hg,
       ZC (dH p G h),hHU hh,rfl⟩
   · intro g hg
     have hg1:g∈lcs G 1:=(eo p).trans (kO p) hg
     refine ⟨hg1,?_⟩
     rw[t6 (a:=⟨g,hg1⟩) (eo p hg)]
     exact S.zero_mem
  show S=⊤
  rw[Yo]
  intro w _
  obtain ⟨a,ha⟩:=lP (p:=p) (G:=G) (ZW w)
  obtain ⟨h,hS⟩:= cO (dG a.2)
  have e:w=ZC (jL p G a):=by
   rw[ha]
   rfl
  rw[e]
  exact hS
lemma y5 [Finite G] (hG:IsPGroup p G) {d:ℕ}
    (v:Fin d→ Additive (VQ p G))
    (hU:jg (cP (p:=p) (G:=G)) (ZQ (ZMod p) (ZF v))):
    bD G≤d:=by
 set U:=ZQ (ZMod p) (ZF v)
 set x:Fin d→G:= fun i=>oq (ZW (v i))
 set H:=ZA (ZF x)
 set K:=⁅H,H⁆⊔pN p G
 have hUP:U≤TU p (Nw (p:=p) H):=by
  rw[YU]
  rintro _ ⟨i,rfl⟩
  refine ⟨x i,ZD ⟨i,rfl⟩,?_⟩
  show ZC (dH p G (oq (ZW (v i))))=v i
  rw[xZ]
  rfl
 have hT:(⊤:Submodule (ZMod p) (Additive (WQ p G)))≤
     TU p (aaR (p:=p) K):=by
  unfold jg at hU
  rw[← hU,YU]
  rintro _ ⟨a,ha,b,hb,rfl⟩
  have u6:a∈Nw (p:=p) H:=hUP ha
  have Io:b∈Nw (p:=p) H:=hUP hb
  obtain ⟨g,hg,rfl⟩:=u6
  obtain ⟨h,hh,rfl⟩:=Io
  exact ⟨cw g h,ZK (Zo hg hh),
    (CY g h).symm⟩
 have dG:lcs G 1≤K:=by
  intro g hg
  have hw:ZC (jL p G ⟨g,hg⟩)∈aaR (p:=p) K:=
    hT XK
  obtain ⟨a,haK,heq⟩:=hw
  have adY:jL p G a=jL p G ⟨g,hg⟩:= congrArg ZW heq
  have hk:(⟨g,hg⟩*a⁻¹:lcs G 1)∈(jL p G).ker :=by
   rw[Zm,YP,Wq, ← adY,mul_inv_cancel]
  rw[JO,ZT]at hk
  have lQ:g*(a:G)⁻¹∈pN p G:=hk
  have e:g=g*(a:G)⁻¹*a:=by group
  rw[e]
  exact K.mul_mem (ZL lQ) haK
 apply WK
 exact ⟨x,((Mw hG H).1 dG).ge⟩
lemma tJ:jg (cP (p:=p) (G:=G)) ⊤:=by
 have e :ZF (fun vw:Additive (VQ p G)×Additive (VQ p G)=>cP vw.1 vw.2)=
     {w | ∃ x∈(⊤:Submodule (ZMod p) (Additive (VQ p G))),
       ∃ y∈(⊤:Submodule (ZMod p) (Additive (VQ p G))),w= cP (p:=p) (G:=G) x y}:=by
   ext w
   constructor
   · rintro ⟨⟨x,y⟩,rfl⟩
     exact ⟨x,XK,y,XK,rfl⟩
   · rintro ⟨x, -,y, -,rfl⟩
     exact ⟨(x,y),rfl⟩
 have h:=N8 (p:=p) (G:=G)
 rw[e]at h
 exact h
lemma JQ [Finite G] (U:Submodule (ZMod p) (Additive (VQ p G))):
    ∃ v:Fin (finrank (ZMod p) U)→ Additive (VQ p G),ZQ (ZMod p) (ZF v)=U:=by
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Finite U:=inferInstance
 have:Yx (ZMod p) U:=inferInstance
 let B:=WD (ZMod p) U rfl
 refine ⟨fun i=> (B i:Additive (VQ p G)),?_⟩
 have h:= congrArg (Pw U.subtype) B.span_eq
 rw[Rh,SG, ← WJ]at h
 exact h
lemma wM [Finite G] (hG:IsPGroup p G):
    x8 (cP (p:=p) (G:=G))=bD G:=by
 apply le_antisymm
 · have d8:{k | ∃ u:Fin k→G,
       lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
         lcs G 2}.Nonempty:=by
     let e:Fin (ZB G)→G:=(Xz G).symm
     have he:ZF e=RG:=U3 _
     refine ⟨ZB G,e,?_⟩
     rw[he,X4]
     exact WM
   obtain ⟨u,hu⟩:=Wr d8
   have hg:=x7 (p:=p) u hu
   have h1:x8 (cP (p:=p) (G:=G))≤finrank (ZMod p)
       (ZQ (ZMod p) (ZF (fun i=>ZC (dH p G (u i))))):=
     WK ⟨_,rfl,hg⟩
   have h2:finrank (ZMod p)
       (ZQ (ZMod p) (ZF (fun i=>ZC (dH p G (u i)))))≤
       Zq (Fin (bD G)):=
     finrank_range_le_card (fun i=>ZC (dH p G (u i)))
   rw[Zz]at h2
   exact h1.trans h2
 · have o9:jg (cP (p:=p) (G:=G)) ⊤:=tJ
   have d8:{d | ∃ U:Submodule (ZMod p) (Additive (VQ p G)),finrank (ZMod p) U=d∧
       jg (cP (p:=p) (G:=G)) U}.Nonempty:=⟨_,⊤,rfl,o9⟩
   obtain ⟨U,hU,hg⟩:=Wr d8
   obtain ⟨v,hv⟩:=JQ (p:=p) U
   rw[← hv]at hg
   have:=y5 hG v hg
   exact this.trans hU.le
lemma rF [Finite G] (hG:IsPGroup p G) {r1 r2:ℕ}
    (bV:Basis (Fin r1) (ZMod p) (Additive (VQ p G)))
    (bW:Basis (Fin r2) (ZMod p) (Additive (WQ p G))):
    (∀ k,kG (gW (cP (p:=p) (G:=G)) bV bW k))∧
      gQ (gW (cP (p:=p) (G:=G)) bV bW) ⊤∧
      kA (gW (cP (p:=p) (G:=G)) bV bW)=bD G:=by
 refine ⟨Kt _ (fun x =>EH (p:=p) (G:=G) x) bV bW,?_,?_⟩
 · rw[wP]
   exact tJ
 · rw[IU,wM hG]
lemma zQ [Finite G] (hG:IsPGroup p G):
    ∃ β:Fin (r2 p G)→Matrix (Fin (ZV G)) (Fin (ZV G)) (ZMod p),
      (∀ k,kG (β k))∧gQ β ⊤∧kA β=bD G:=by
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
 have:Finite (WQ p G):=Zy _ lP
 have:Finite (Additive (WQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (WQ p G)):=inferInstance
 let bV:=WD (ZMod p) (Additive (VQ p G)) (Lc (p:=p) (G:=G) hG)
 let bW:=WD (ZMod p) (Additive (WQ p G)) (rfl:finrank (ZMod p)
   (Additive (WQ p G))=r2 p G)
 exact ⟨_,rF hG bV bW⟩
lemma Ih [Finite G] (hG:IsPGroup p G):
    bD G≤ r2 p G+1∧r2 p G≤(bD G).choose 2∧bD G≤ZV G:=by
 obtain ⟨β,hA,hg,hs⟩:=zQ hG
 refine ⟨?_,?_,?_⟩
 · rw[← hs]
   exact JT β hg
 · rw[← hs]
   exact zX β hA hg
 · rw[← hs]
   exact N9 β hg
end Bridge
end OMA.SimsLite.Alt2
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section BrCount
lemma I8 {α β:Type*} [Finite β] (S:Set α) (f:α→β) (M:ℕ)
    (hM:∀ b,(S∩f ⁻¹' {b}).ncard≤M):S.ncard≤ZB β *M:=by
 classical
 have:=Tf β
 rcases S.finite_or_infinite with hS | hS
 · rw [Set.ncard_eq_toFinset_card S hS,
     Wd (f:= f) (t:=ZU) (by intro x _; simp)]
   calc ∑ b : β,(hS.toFinset.filter (fun a=>f a=b)).card≤∑ _b:β,M:=by
         refine Z9 fun b _=>?_
         have h1:((hS.toFinset.filter (fun a=>f a=b):Finset α):Set α)=
             S∩f ⁻¹' {b}:=by
           ext a
           simp
         rw[← VF,h1]
         exact hM b
     _=ZB β *M:=by simp
 · rw[hS.ncard]
   exact Zv _
lemma jO {α β:Type*} (S:Set α) (f:α→β) (M:ℕ)
    (hM:∀ b,(S∩f ⁻¹' {b}).ncard≤M):S.ncard≤(f '' S).ncard*M:=by
 classical
 rcases S.finite_or_infinite with hS | hS
 · rw [Set.ncard_eq_toFinset_card S hS,Finset.card_eq_sum_card_image f hS.toFinset]
   have qv:(f '' S).ncard=(hS.toFinset.image f).card:=by
    rw[← VF,Tu,Set.Finite.coe_toFinset]
   rw[qv]
   calc ∑ b ∈ hS.toFinset.image f,(hS.toFinset.filter (fun a=>f a=b)).card
       ≤ ∑ _b ∈hS.toFinset.image f,M:=by
         refine Z9 fun b _=>?_
         have h1:((hS.toFinset.filter (fun a=>f a=b):Finset α):Set α)=
             S∩f ⁻¹' {b}:=by
           ext a
           simp
         rw[← VF,h1]
         exact hM b
     _=(hS.toFinset.image f).card*M:=by simp
 · rw[hS.ncard]
   exact Zv _
lemma i7 {α β:Type*} [Finite β] (S:Set α) (f:α→β)
    (hf:WP f S):S.ncard≤ZB β:=by
 have h:=YM (t:=(RG:Set β)) f
   (fun _ _=>Set.mem_univ _) hf
 rwa[Set.ncard_univ]at h
lemma iE {p a b:ℕ} (hp:1<p) (h:p^a≤p^b):a≤b:=by
 by_contra hc
 push_neg at hc
 have h1:p^(b+1)≤p^a:=Zk (by omega) hc
 have h2:0<p^b:=X7 (SZ _ (by omega))
 rw[Xr]at h1
 nlinarith
lemma uq {p n a c:ℕ} (hp:p.Prime) (ha:a∣p^n) (hc:c∣p^n)
    (hac:a∣c) (d8:a≠c):p*a≤ c:=by
 obtain ⟨i, -,rfl⟩:=(Yp hp).1 ha
 obtain ⟨j, -,rfl⟩:=(Yp hp).1 hc
 have hij:i≤j:=(X8 hp.one_lt).1 hac
 have Q7:i≠j:= fun h=>d8 (by rw[h])
 rw[← VG]
 exact Zk hp.pos (by omega)
lemma J8 {M N:Type*} [Group M] [Group N] [Finite M] {p s b:ℕ} (hp:p.Prime)
    (f:M→*N) (hM:ZB M=p^s) (hb:p^b≤ZB f.range):
    ZB f.ker≤p^(s - b):=by
 have h1:ZB f.ker*ZB f.range=p^s:=by
  have e:=YJ (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw[← e, ← hM]
  exact Z4 f.ker
 obtain ⟨k, -,hk⟩:=(Yp hp).1 (⟨_,h1.symm⟩:ZB f.ker∣p^s)
 obtain ⟨j, -,hj⟩:=(Yp hp).1
   (⟨ZB f.ker,by rw[mul_comm]; exact h1.symm⟩:ZB f.range∣p^s)
 rw[hk,hj, ← Xh]at h1
 have hkj:k+j=s:=Zd hp.two_le h1
 rw[hj]at hb
 have hbj:b≤j:=iE hp.one_lt hb
 rw[hk]
 exact Zk hp.pos (by omega)
end BrCount
section BrSub
variable {L:Type*} [CommGroup L]
lemma rT [Finite L] (H K:Subgroup L):
    ZB ↥(H⊔K)≤ZB H*ZB K:=by
 rw[← W7]
 refine YO
   (fun q:H×K=> (⟨(q.1:L)*q.2,UE q.1.2 q.2.2⟩:↥(H⊔K))) ?_
 rintro ⟨x,hx⟩
 obtain ⟨y,hy,z,hz,rfl⟩:=PS.mp hx
 exact ⟨(⟨y,hy⟩,⟨z,hz⟩),rfl⟩
end BrSub
section BrSubCount
lemma oY {L:Type*} [Group L] [Finite L]:
    {H:Subgroup L | ZB H=1}.ncard≤1:=by
  have jp:{H:Subgroup L | ZB H=1}⊆{⊥}:=by
    intro H hH
    exact Subgroup.eq_bot_of_card_eq H hH
  calc _≤({⊥}:Set (Subgroup L)).ncard:=Yk jp (Set.finite_singleton _)
    _=1:=P5 _
lemma oK {L:Type*} [Group L] [Finite L] {p e b:ℕ} (hp:p.Prime)
    (hL:ZB L=p^e) (hb:e<b):{H:Subgroup L | ZB H=p^b}.ncard=0:=by
  have he:{H:Subgroup L | ZB H=p^b}= ∅ :=by
    ext H
    simp only[UA,Rm,iff_false]
    intro hH
    have h:=YC H
    rw[hH,hL]at h
    have:=(X8 hp.one_lt).1 h
    omega
  rw[he,Y3]
lemma A3 {p:ℕ} (hp:p.Prime) (e:ℕ):
    ∀ (L:Type u) [CommGroup L] [Finite L],ZB L=p^e→∀ b:ℕ,
      {H:Subgroup L | ZB H=p^b}.ncard≤p^(b*(e+1 - b)):=by
  haveI:=Fact.mk hp
  induction e with
  | zero=>
    intro L _ _ hL b
    rcases Yj b with rfl | hb
    · simpa using oY (L:=L)
    · rw[oK hp hL hb]
      exact Zv _
  | succ e ih=>
    intro L _ _ hL b
    rcases Yj b with rfl | Fj
    · simpa using oY (L:=L)
    rcases XU (e+1) b with hbe | hbe
    · rw[oK hp hL hbe]
      exact Zv _
    obtain ⟨c,rfl⟩:∃ c,b= c+1:=⟨b - 1,by omega⟩
    obtain ⟨d,rfl⟩:∃ d,e= c+d:=⟨e - c,by omega⟩
    classical
    haveI:Finite (Subgroup L):=
      YH (fun H:Subgroup L=> (H:Set L)) X6
    obtain ⟨M,hM⟩:=Sylow.exists_subgroup_card_pow_prime p
      (show p^(c+d)∣ZB L by rw[hL]; exact pow_dvd_pow p (XV _))
    haveI:Finite (Subgroup M):=
      YH (fun H:Subgroup M=> (H:Set M)) X6
    have hMi:M.index =p:=by
     have h:=Z4 M
     rw[hM,hL,Xr]at h
     exact WR (XD hp.pos _) h
    have adb:M≠⊤:=by
     intro h
     rw[h,Subgroup.index_top]at hMi
     exact hp.one_lt.ne hMi
    obtain ⟨t,htM⟩:∃ t,t∉M:=by
     by_contra d8
     push_neg at d8
     exact adb (Yo.2 fun x _=>d8 x)
    set S1:={H:Subgroup L | ZB H=p^(c+1)∧H≤M} with MQ
    set S2:={H:Subgroup L | ZB H=p^(c+1)∧¬ H≤M} with Mz
    have qO:{H:Subgroup L | ZB H=p^(c+1)}=S1∪S2:=by
      ext H
      simp only[MQ,Mz,Set.mem_union,UA]
      tauto
    have h1:S1.ncard≤p^((c+1)*(c+d+1 - (c+1))):=by
     refine WS ?_ (ih M hM (c+1))
     refine YM (fun H=>H.subgroupOf M) ?_ ?_ (Zl _)
     · rintro H ⟨hH,Nk⟩
       show ZB (H.subgroupOf M)=p^(c+1)
       rw[← hH]
       exact YJ (XM Nk).toEquiv
     · rintro H ⟨-,Nk⟩ H' ⟨-,adP⟩ he
       have:=Sb.1 he
       rwa[inf_of_le_left Nk,inf_of_le_left adP]at this
    have O8:∀ H∈S2,ZB ↥(M⊓H)=p^c:=by
     rintro H ⟨hH,Nk⟩
     have v5:M.relIndex H∣p:=hMi▸Subgroup.relIndex_dvd_index_of_normal (H:=M) (K:=H)
     have d8:M.relIndex H≠1:= fun h1=>Nk (Subgroup.relIndex_eq_one.1 h1)
     have m_:M.relIndex H=p:=((Nat.dvd_prime hp).1 v5).resolve_left d8
     have lT:=Z4 (M⊓H)
     have uL:=T7 (inf_le_right:M⊓H≤H)
     rw[Subgroup.inf_relIndex_right (H:=M) (K:=H),m_]at uL
     have hc3:=Z4 H
     rw[hH]at hc3
     rw[← uL,hL]at lT
     have hi:H.index≠0:=Subgroup.index_ne_zero_of_finite
     have e1:(ZB ↥(M⊓H)*p)*H.index =(p^c*p)*H.index:=by
      rw[← Xr,hc3,hL, ← lT]
      ring
     have e2:=Yc (X7 hi) e1
     exact Yc hp.pos e2
    have qX:∀ H∈S2,∃ y,y∈H∧t⁻¹*y∈M:=by
     rintro H ⟨hH,Nk⟩
     have cO:M≤H⊔M:=Z5
     have d8:M≠H⊔M:= fun h=>Nk (WM.trans h.symm.le)
     have ad5:ZB M≠ZB ↥(H⊔M):= fun h=>
       d8 (YS cO h.symm.le)
     have hp1:=uq hp (n:= c+d+1)
       (by rw[← hL]; exact YC _)
       (by rw[← hL]; exact YC _) (WU cO) ad5
     have o9:H⊔M=⊤:=by
      refine YS le_top ?_
      rw[Yn,hL,Xr, ← hM,mul_comm]
      exact hp1
     have ht:t∈H⊔M:=by
      rw[o9]
      exact ZO t
     obtain ⟨y,hy,z,hz,hyz⟩:=PS.1 ht
     refine ⟨y,hy,?_⟩
     have e:t⁻¹*y=z⁻¹:=by
      rw[← hyz]
      group
     rw[e]
     exact inv_mem hz
    let ch:Subgroup L→ L:= fun H=>Rq (fun y=>y∈H∧t⁻¹*y∈M)
    have hch:∀ H∈S2,ch H∈H∧t⁻¹*ch H∈M:= fun H hH=>
      Sd (qX H hH)
    let f:Subgroup L→ Subgroup M:= fun H=> (M⊓H).subgroupOf M
    have pC :∀ a:Subgroup M,(S2∩f ⁻¹' {a}).ncard≤p^d:=by
     intro a
     rcases (S2∩f ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨H0,hH0,adJ⟩
     · rw[he,Y3]
       exact Zv _
     obtain ⟨K,hK⟩:∃ K:Subgroup L,K=M⊓H0:=⟨_,rfl⟩
     have hKc:ZB K=p^c:=by
      rw[hK]
      exact O8 H0 hH0
     have hKM:K≤M:=by
      rw[hK]
      exact inf_le_left
     have hfK:∀ H∈S2∩f ⁻¹' {a},M⊓H=K:=by
      rintro H ⟨-,hHa⟩
      have e:f H= f H0:=(show f H=a from hHa).trans (show f H0=a from adJ).symm
      have e2:=Sb.1 e
      rw[inf_of_le_left inf_le_left,inf_of_le_left inf_le_left]at e2
      rw[hK]
      exact e2
     have Nm:ZB ↥(M.map (ZG K))=p^d:=by
      have e:=Subgroup.relIndex_ker (K:=M) (f:=ZG K)
      rw[YV]at e
      have uL:=T7 hKM
      rw[e,hMi]at uL
      have lT:=Z4 K
      rw[hKc, ← uL,hL]at lT
      have h3:p^c*(ZB ↥(M.map (ZG K))*p)=p^c*(p^d*p):=by
       rw[lT]
       ring
      exact Yc hp.pos (WR (XD hp.pos c) h3)
     let Φ:Subgroup L→ L⧸K:= fun H=> ((t⁻¹*ch H:L):L⧸K)
     have oc:∀ H∈S2∩f ⁻¹' {a},
         Φ H∈((M.map (ZG K):Subgroup (L⧸K)):Set (L⧸K)):=by
      intro H hH
      exact Zj.2 ⟨t⁻¹*ch H,(hch H hH.1).2,rfl⟩
     have eW:WP Φ (S2∩f ⁻¹' {a}):=by
      intro H hH H' hH' hΦ
      obtain ⟨hy1, -⟩:=hch H hH.1
      obtain ⟨ad1,adw⟩:=hch H' hH'.1
      have acT:ZB H=p^(c+1):=hH.1.1
      have O5:ZB H'=p^(c+1):=hH'.1.1
      have hKH:K≤H:=by
       rw[← hfK H hH]
       exact inf_le_right
      have adS:K≤H':=by
       rw[← hfK H' hH']
       exact inf_le_right
      have hq:(ch H)⁻¹*ch H'∈K:=by
       have h0:=WX.1 hΦ
       have e:(t⁻¹*ch H)⁻¹*(t⁻¹*ch H')=(ch H)⁻¹*ch H':=by group
       rwa[e]at h0
      have hcH:ch H'∈H:=by
       have e:ch H'= ch H*((ch H)⁻¹*ch H'):=by group
       rw[e]
       exact mul_mem hy1 (hKH hq)
      have acX:ch H'∉K:=by
       intro hc
       have hcM:ch H'∈M:=hKM hc
       apply htM
       have e:t= ch H'*(t⁻¹*ch H')⁻¹:=by group
       rw[e]
       exact mul_mem hcM (inv_mem adw)
      obtain ⟨J,hJ⟩:∃ J:Subgroup L,J=K⊔YQ (ch H'):=⟨_,rfl⟩
      have hJH:J≤H:=by
       rw[hJ]
       exact sup_le hKH (UU.2 hcH)
      have aeg:J≤H':=by
       rw[hJ]
       exact sup_le adS (UU.2 ad1)
      have hKJ:K≤J:=by
       rw[hJ]
       exact WM
      have adI:ZB K≠ZB J:=by
       intro h
       have h':=YS hKJ h.symm.le
       apply acX
       rw[h',hJ]
       exact ZL (Xc _)
      have hpJ:=uq hp (n:= c+d+1)
        (by rw[← hL]; exact YC _)
        (by rw[← hL]; exact YC _) (WU hKJ) adI
      have aes:J=H':=by
       refine YS aeg ?_
       rw[O5,Xr, ← hKc,mul_comm]
       exact hpJ
      have ady:H'≤H:=by
       rw[← aes]
       exact hJH
      exact (YS ady (by rw[acT,O5])).symm
     calc (S2∩f ⁻¹' {a}).ncard
         ≤ ((M.map (ZG K):Subgroup (L⧸K)):Set (L⧸K)).ncard:=
           YM Φ oc eW (Zl _)
       _=p^d:=by rw[← Xt]; exact Nm
    have qv:(f '' S2).ncard≤p^(c*(c+d+1 - c)):=by
     refine WS (Yk ?_ (Zl _)) (ih M hM c)
     rintro _ ⟨H,hH,rfl⟩
     show ZB ((M⊓H).subgroupOf M)=p^c
     rw[← O8 H hH]
     exact YJ (XM inf_le_left).toEquiv
    have h2:S2.ncard≤(f '' S2).ncard*p^d:=jO S2 f _ pC
    have e1:c+d+1 - (c+1)=d:=by omega
    have e2:c+d+1 - c=d+1:=by omega
    have e3:c+d+1+1 - (c+1)=d+1:=by omega
    rw[e1]at h1
    rw[e2]at qv
    rw[e3,qO]
    calc (S1 ∪S2).ncard≤S1.ncard+S2.ncard:=Tj _ _
      _ ≤ p^((c+1)*d)+p^(c*(d+1))*p^d:=
          Nat.add_le_add h1 (h2.trans (Za _ qv))
      _ ≤ p ^(c*d+ c+d)+p^(c*d+ c+d):=by
          refine Nat.add_le_add (Zk hp.pos ?_) (WT ?_)
          · rw[add_mul,Wn]
            omega
          · rw[← Xh]
            congr 1<;>ring
      _=2*p^(c*d+ c+d):=by ring
      _≤p*p^(c*d+ c+d):=Za _ hp.two_le
      _ = p^((c+1)*(d+1)):=by
          rw[← VG]
          congr 1
          ring
end BrSubCount
section BrProp42
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
lemma C6 {X:Type*} [Finite X] (T:Set X) (x0:X) (kH:x0∈T) (s:ℕ):
    {κ:Fin s→X | ∀ k,κ k∈T}.ncard≤T.ncard^s:=by
  classical
  let F:(Fin s→X)→(Fin s→T):= fun κ k=>if h:κ k∈T then ⟨κ k,h⟩ else ⟨x0,kH⟩
  have eW:WP F {κ:Fin s→X | ∀ k,κ k∈T}:=by
    intro κ hκ κ' hκ' he
    funext k
    have Bw:κ k∈T:=hκ k
    have Oy:κ' k∈T:=hκ' k
    have e:= congrArg XJ (congrFun he k)
    have e1:((F κ k:T):X)=κ k:=by
     show ((if h:κ k∈T then (⟨κ k,h⟩:T) else ⟨x0,kH⟩:T):X)=κ k
     rw[dif_pos Bw]
    have e2:((F κ' k:T):X)=κ' k:=by
     show ((if h:κ' k∈T then (⟨κ' k,h⟩:T) else ⟨x0,kH⟩:T):X)=κ' k
     rw[dif_pos Oy]
    rw[← e1, ← e2]
    exact e
  calc _≤ZB (Fin s→T):=i7 _ F eW
    _=T.ncard^s:=by rw[Xl,Xk,Xt]
lemma zS [Finite L2] [Finite L3] {p s3 n b:ℕ} (hp:p.Prime)
    (jG:ZB L3=p^s3) (hb:b≤ s3) (y:Fin n→ L2)
    (hy:ZA (ZF y)=⊤):
    {φ:L2→*L3 | ZB φ.range≤p^b}.ncard≤p^(b*(n+s3+1 - b)):=by
  classical
  haveI:=Fact.mk hp
  haveI:Finite (Subgroup L3):=
    YH (fun H:Subgroup L3=> (H:Set L3)) X6
  set S:={φ:L2→*L3 | ZB φ.range≤p^b} with DK
  have hext:∀ φ∈S,∃ K:Subgroup L3,ZB K=p^b∧φ.range≤K:=by
   intro φ hφ
   have hφ':ZB φ.range≤p^b:=hφ
   obtain ⟨k, -,hk⟩:=(Yp hp).1
     (show ZB φ.range∣p^s3 by rw[← jG]; exact YC _)
   rw[hk]at hφ'
   have hkb:k≤b:=iE hp.one_lt hφ'
   exact Sylow.exists_subgroup_card_pow_prime_le p
     (show p^b∣ZB L3 by rw[jG]; exact pow_dvd_pow p hb) φ.range hk hkb
  let f:(L2→*L3)→ Subgroup L3:= fun φ=>
    Rq (fun K:Subgroup L3=>ZB K=p^b∧φ.range≤K)
  have hf:∀ φ∈S,ZB (f φ)=p^b∧φ.range≤f φ:= fun φ hφ=>
    Sd (hext φ hφ)
  have hM:∀ K:Subgroup L3,(S∩f ⁻¹' {K}).ncard≤(p^b)^n:=by
   intro K
   rcases (S∩f ⁻¹' {K}).eq_empty_or_nonempty with he | ⟨φ0,hφ0S,hφ0K⟩
   · rw[he,Y3]
     exact Zv _
   · have hK:ZB K=p^b:=by
       have h0:=(hf φ0 hφ0S).1
       rwa[show f φ0=K from hφ0K]at h0
     have cI:∀ φ∈S∩f ⁻¹' {K},∀ i,φ (y i)∈K:=by
      rintro φ ⟨hφS,hφK⟩ i
      have hφK':f φ=K:=hφK
      rw[← hφK']
      exact (hf φ hφS).2 ⟨y i,rfl⟩
     let F:(L2→*L3)→(Fin n→K):= fun φ i=>
       if h:φ (y i)∈K then ⟨φ (y i),h⟩ else 1
     have eW:WP F (S∩f ⁻¹' {K}):=by
      intro φ hφ ψ hψ aec
      apply XS hy
      rintro _ ⟨i,rfl⟩
      have h1:= congrFun aec i
      have h2:((F φ i:K):L3)=φ (y i):=by
       show ((if h:φ (y i)∈K then (⟨φ (y i),h⟩:K) else 1:K):L3)=φ (y i)
       rw[dif_pos (cI φ hφ i)]
      have h3:((F ψ i:K):L3)=ψ (y i):=by
       show ((if h:ψ (y i)∈K then (⟨ψ (y i),h⟩:K) else 1:K):L3)=ψ (y i)
       rw[dif_pos (cI ψ hψ i)]
      rw[← h2, ← h3,h1]
     calc (S∩f ⁻¹' {K}).ncard≤ZB (Fin n→K):=i7 _ F eW
       _=ZB K^n:=by rw[Xl,Xk]
       _=(p^b)^n:=by rw[hK]
  have qv:(f '' S).ncard≤p^(b*(s3+1 - b)):=by
   refine WS (Yk ?_ (Zl _)) (A3 hp s3 L3 jG b)
   rintro _ ⟨φ,hφ,rfl⟩
   exact (hf φ hφ).1
  calc S.ncard≤(f '' S).ncard*(p^b)^n:=jO S f _ hM
    _≤p^(b*(s3+1 - b))*(p^b)^n:=Za _ qv
    _ =p^(b*(n+s3+1 - b)):=by
      rw[← X5, ← Xh]
      congr 1
      obtain ⟨d,rfl⟩:∃ d,s3=b+d:=⟨s3 - b,by omega⟩
      rw[show b+d+1 - b=d+1 by omega,show n+(b+d)+1 - b=n+d+1 by omega]
      ring
lemma aaF [Finite L2] [Finite L3] {p s3 n b:ℕ} (hp:p.Prime)
    (jG:ZB L3=p^s3) (hb:b≤ s3) (y:Fin n→ L2)
    (hy:ZA (ZF y)=⊤) (s:ℕ):
    {κ :Fin s→(L2→*L3) | ∀ k,ZB (κ k).range≤p^b}.ncard≤
      p^(s*(b*(n+s3+1 - b))):=by
  haveI:Finite (L2→*L3):=
    YH (fun f:L2→*L3=> (f:L2→ L3)) Yr
  have h1:(1:L2→*L3)∈{φ:L2→*L3 | ZB φ.range≤p^b}:=by
    show ZB (1:L2→*L3).range≤p^b
    rw[MonoidHom.range_one,Wf]
    exact Nat.one_le_pow _ _ hp.pos
  calc _ ≤{φ:L2→*L3 | ZB φ.range≤p^b}.ncard^s:=
        C6 {φ:L2→*L3 | ZB φ.range≤p^b} 1 h1 s
    _ ≤ (p^(b*(n+s3+1 - b)))^s:=
        XR (zS hp jG hb y hy) s
    _=p^(s*(b*(n+s3+1 - b))):=by rw[← X5,mul_comm]
end BrProp42
section BrBracket
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
abbrev g4 (β:L1→*L1→*L2):Prop:=∀ x,β x x =1
abbrev f4 (β1:L1→*L1→*L2) (β2:L2→*L1→*L3):Prop:=
  ∀ x y z,β2 (β1 x y) z*β2 (β1 y z) x*β2 (β1 z x) y=1
lemma g9 {β:L1→*L1→*L2} (hA:g4 β) (x y:L1):β y x =(β x y)⁻¹:=by
 have h:=hA (x*y)
 simp only[YP,Y8,hA x,hA y,Wn,UH]at h
 exact Uv h
lemma nJ (β:L1→*L1→*L2) (x y:L1) (n:ℕ):
    β (x^n) y=(β x y)^n:=by
 have h:=map_pow (β.flip y) x n
 simpa[YB] using h
lemma Jx (C:Subgroup L1) {β1 β1':L1→*L1→*L2} {β2 β2':L2→*L1→*L3}
    (hA:g4 β1) (BT:g4 β1') (hJ:f4 β1 β2) (hJ':f4 β1' β2')
    (dV:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}=⊤)
    (h1:∀ x,∀ u∈C,β1 x u=β1' x u) (h2:∀ z,∀ u∈C,β2 z u=β2' z u):
    β2=β2':=by
  have key:∀ w∈{w | ∃ u∈C,∃ v∈C,β1 u v=w},β2 w=β2' w:=by
    rintro _ ⟨u,hu,v,hv,rfl⟩
    ext x
    have e1:=hJ u v x
    have e2:=hJ' u v x
    have a1:β1 v x =β1' v x:=by
     rw[g9 hA x v,g9 BT x v,h1 x v hv]
    have a2:β2 (β1 v x) u=β2' (β1' v x) u:=by rw[a1,h2 _ u hu]
    have a3:β2 (β1 x u) v=β2' (β1' x u) v:=by rw[h1 x u hu,h2 _ v hv]
    have a4:β1' u v=β1 u v:=(h1 u v hv).symm
    rw[a2,a3]at e1
    rw[a4]at e2
    exact Vm (Vm (e1.trans e2.symm))
  exact XS dV key
lemma FK (C:Subgroup L1) {κ:L2→*L1→*L3} {β β0:L1→*L1→*L2}
    {β2 β20:L2→*L1→*L3} (hA:g4 β) (BJ:g4 β0) (hJ:f4 β β2)
    (hJ0:f4 β0 β20) (dV:ZA {w | ∃ u∈C,∃ v∈C,β u v=w}=⊤)
    (hκ:∀ z,∀ u∈C,β2 z u=κ z u) (hκ0:∀ z,∀ u∈C,β20 z u=κ z u)
    (MJ:∀ x,∀ u∈C,β x u=β0 x u) {h:L1} (hh:h∈C) (x y:L1):
    κ (β x y) h=κ (β0 x y) h:=by
  have h22:β2=β20:=Jx C hA BJ hJ hJ0 dV MJ
    (fun z u hu=> (hκ z u hu).trans (hκ0 z u hu).symm)
  have e1:=hJ x y h
  have e2:=hJ0 x y h
  have b1:β y h=β0 y h:=MJ y h hh
  have b2:β h x =β0 h x:=by
   rw[g9 hA x h,g9 BJ x h,MJ x h hh]
  rw[b1,b2,h22]at e1
  rw[← hκ _ h hh, ← hκ0 _ h hh,h22]
  exact Vm (Vm (e1.trans e2.symm))
lemma LJ {ι:Type*} {g:ι→ L1} (hg:ZA (ZF g)=⊤)
    {Cidx:Set ι} {β β':L1→*L1→*L2} (hA:g4 β) (BT:g4 β')
    (Pc:Finset (ι×ι)) (Gp:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (hP:∀ q∈Pc,β (g q.1) (g q.2)=β' (g q.1) (g q.2)):
    ∀ x,∀ u∈ZA (g '' Cidx),β x u=β' x u:=by
 have dV:∀ j∈Cidx,β.flip (g j)=β'.flip (g j):=by
  intro j hj
  apply XS hg
  rintro _ ⟨i,rfl⟩
  simp only[YB]
  rcases Gp i j hj with rfl | h | h
  · exact (hA _).trans (BT _).symm
  · exact hP _ h
  · rw[g9 hA (g j) (g i),g9 BT (g j) (g i),hP _ h]
 intro x u hu
 have cO:ZA (g '' Cidx)≤(β x).eqLocus (β' x):=by
  rw[ZE]
  rintro _ ⟨j,hj,rfl⟩
  show β x (g j)=β' x (g j)
  have:= congrArg (fun φ:L1→*L2=>φ x) (dV j hj)
  simpa[YB] using this
 exact cO hu
lemma Jq {ι:Type*} {g:ι→ L1} (hg:ZA (ZF g)=⊤)
    {Cidx:Set ι} {β β':L1→*L1→*L2} (hA:g4 β) (BT:g4 β')
    (Po:Finset (ι×ι))
    (Bh:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (hC:∀ x,∀ u∈ZA (g '' Cidx),β x u=β' x u)
    (Eo:∀ q∈Po,β (g q.1) (g q.2)=β' (g q.1) (g q.2)):β=β':=by
 have hgi:∀ i,β (g i)=β' (g i):=by
  intro i
  apply XS hg
  rintro _ ⟨j,rfl⟩
  by_cases hj:j∈Cidx
  · exact hC _ _ (ZD ⟨j,hj,rfl⟩)
  · by_cases hi:i∈Cidx
    · rw [g9 hA (g j) (g i),g9 BT (g j) (g i),
        hC _ _ (ZD ⟨i,hi,rfl⟩)]
    · rcases Bh i j hi hj with rfl | h | h
      · exact (hA _).trans (BT _).symm
      · exact Eo _ h
      · rw[g9 hA (g j) (g i),g9 BT (g j) (g i),Eo _ h]
 apply XS hg
 rintro _ ⟨i,rfl⟩
 exact hgi i
lemma NU {L:Type*} [Group L] {K:Subgroup L} {x:L} [Decidable (x∈K)]
    (h:x∈K):((if hp:x∈K then (⟨x,hp⟩:K) else 1:K):L)=x:=by
  rw[dif_pos h]
lemma LG [Finite L2] {ι:Type*} [DecidableEq ι] (g:ι→ L1)
    (hg:ZA (ZF g)=⊤) (Cidx:Set ι) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' Cidx)) (Pc Po D:Finset (ι×ι))
    (Gp:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (Bh:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (v:ι×ι→ L2):
    {β1 : L1→*L1→*L2 | g4 β1∧
        ZA {w | ∃ u∈ZA (g '' Cidx),
          ∃ u'∈ZA (g '' Cidx),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈ZA (g '' Cidx),β2 z u=κ z u)∧
          f4 β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      ZB L2^(Pc \ D).card*ZB (κ.flip h).ker^Po.card:=by
  classical
  set C:=ZA (g '' Cidx) with abH
  set S :={β1:L1→*L1→*L2 | g4 β1∧
        ZA {w | ∃ u∈C,∃ u'∈C,β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈C,β2 z u=κ z u)∧f4 β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q} with DK
  let fc:(L1→*L1→*L2)→(↥(Pc \ D)→ L2):= fun β q=>β (g q.1.1) (g q.1.2)
  have pC : ∀ a,(S∩fc ⁻¹' {a}).ncard≤ZB (κ.flip h).ker^Po.card:=by
   intro a
   rcases (S∩fc ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0S,hβ0a⟩
   · rw[he,Y3]
     exact Zv _
   · obtain ⟨BJ, -,⟨β20,hκ0,hJ0⟩,hD0⟩:=hβ0S
     have hβ0a':fc β0=a:=hβ0a
     have GQ:∀ β∈S∩fc ⁻¹' {a},∀ x,∀ u∈C,β x u=β0 x u:=by
      rintro β ⟨⟨hA, -, -,hD⟩,hβa⟩
      have hβa':fc β=a:=hβa
      apply LJ hg hA BJ Pc Gp
      intro q hq
      by_cases hqD:q∈D
      · rw[hD q hqD,hD0 q hqD]
      · have hq':q∈Pc \ D:=Xq.2 ⟨hq,hqD⟩
        exact congrFun (hβa'.trans hβ0a'.symm) ⟨q,hq'⟩
     have j3:∀ β∈S∩fc ⁻¹' {a},∀ x y,
         β x y/β0 x y∈(κ.flip h).ker :=by
      intro β hβ x y
      obtain ⟨⟨hA,dV,⟨β2,hκ,hJ⟩, -⟩, -⟩:=id hβ
      rw [Zm,map_div,YB,YB,
        FK C hA BJ hJ hJ0 dV hκ hκ0 (GQ β hβ) hh x y,div_self']
     let F:(L1→*L1→*L2)→(↥Po→(κ.flip h).ker):= fun β q=>
       if hq:β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2)∈(κ.flip h).ker then
         ⟨_,hq⟩ else 1
     have hv:∀ β∈S∩fc ⁻¹' {a},∀ q:↥Po,((F β q:(κ.flip h).ker):L2)=
         β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2):=by
      intro β hβ q
      exact NU (j3 β hβ _ _)
     have eW:WP F (S∩fc ⁻¹' {a}):=by
      intro β hβ β' hβ' hF
      have hpo:∀ q∈Po,β (g q.1) (g q.2)=β' (g q.1) (g q.2):=by
       intro q hq
       have e:= congrArg XJ (congrFun hF ⟨q,hq⟩)
       rw[hv β hβ ⟨q,hq⟩,hv β' hβ' ⟨q,hq⟩]at e
       exact div_left_inj.mp e
      obtain ⟨⟨hA, -⟩, -⟩:=id hβ
      obtain ⟨⟨BT, -⟩, -⟩:=id hβ'
      exact Jq hg hA BT Po Bh
        (fun x u hu=> (GQ β hβ x u hu).trans (GQ β' hβ' x u hu).symm) hpo
     calc (S∩fc ⁻¹' {a}).ncard≤ZB (↥Po→(κ.flip h).ker):=
           i7 _ F eW
       _ = ZB (κ.flip h).ker^Po.card:=by
           rw[Xl,YA (α:=↥Po),WG]
  calc S.ncard≤ZB (↥(Pc \ D)→ L2)*ZB (κ.flip h).ker^Po.card:=
        I8 S fc _ pC
    _ = ZB L2^(Pc \ D).card*ZB (κ.flip h).ker^Po.card:=by
        rw[Xl,YA (α:=↥(Pc \ D)),WG]
lemma aan [Finite L2] {ι:Type*} [DecidableEq ι] {p s2 b:ℕ} (hp:p.Prime)
    (lU:ZB L2=p^s2) (g:ι→ L1)
    (hg:ZA (ZF g)=⊤) (Cidx:Set ι) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' Cidx)) (hb:p^b≤ZB (κ.flip h).range)
    (Pc Po D:Finset (ι×ι))
    (Gp:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (Bh:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (v:ι×ι→ L2):
    {β1 : L1→*L1→*L2 | g4 β1∧
        ZA {w | ∃ u∈ZA (g '' Cidx),
          ∃ u'∈ZA (g '' Cidx),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈ZA (g '' Cidx),β2 z u=κ z u)∧
          f4 β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      p^(s2*(Pc \ D).card+(s2 - b)*Po.card):=by
  refine WS (LG g hg Cidx κ hh Pc Po D Gp Bh v) ?_
  rw[lU,Xh,X5,X5]
  exact VR _ (XR (J8 hp _ lU hb) _)
lemma uO (s:ℕ):∀ r :ℕ,
    ((ZM r×ˢ ZM r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)).card=
      (r - s).choose 2
  | 0=>by simp
  | r + 1 =>by
    classical
    have qO:(ZM (r+1)×ˢ ZM (r+1)).filter
          (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)=
        (ZM r×ˢ ZM r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)∪
          (PV s r).image (fun i=> (i,r)):=by
      ext ⟨i,j⟩
      simp only[ZI,XH,Zt,Finset.mem_union,
        Xp,OL,Tn.injEq]
      constructor
      · rintro ⟨⟨hi,hj⟩,hij,O6⟩
        by_cases jW:j< r
        · exact Y7 ⟨⟨by omega,jW⟩,hij,O6⟩
        · exact XQ ⟨i,⟨O6,by omega⟩,rfl,by omega⟩
      · rintro (⟨⟨hi,hj⟩,hij,O6⟩ | ⟨a,⟨Ow,har⟩,rfl,rfl⟩)
        · exact ⟨⟨by omega,by omega⟩,hij,O6⟩
        · exact ⟨⟨by omega,by omega⟩,har,Ow⟩
    have Gz:Disjoint ((ZM r×ˢ ZM r).filter
        (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)) ((PV s r).image (fun i=> (i,r))):=by
      rw[Rr]
      rintro ⟨i,j⟩ h1 h2
      simp only[ZI,XH,Zt,Xp,
        OL,Tn.injEq]at h1 h2
      obtain ⟨a, -, -,hj⟩:=h2
      omega
    have eW:Z8 (fun i:ℕ=> (i,r)):= fun a b h=> (Tn.inj h).1
    have hu:=Finset.card_union_add_card_inter
      ((ZM r×ˢ ZM r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1))
      ((PV s r).image (fun i=> (i,r)))
    rw[Finset.disjoint_iff_inter_eq_empty.1 Gz,Pk,add_zero]at hu
    rw[qO,hu,uO s r,XG _ eW,Nat.card_Ico]
    rcases XU r s with h | h
    · rw[show r - s=0 by omega,show r+1 - s=0 by omega,T8]
    · rw [show r+1 - s=(r - s)+1 by omega,Uq,U6,
        Nat.add_comm]
lemma jY (r s:ℕ):
    ((ZU:Finset (Fin r×Fin r)).filter
      (fun q=>q.1<q.2∧¬ (q.1:ℕ)<s)).card=(r - s).choose 2:=by
  classical
  rw[← uO s r]
  have eW:Z8 (fun q:Fin r×Fin r=> ((q.1:ℕ),(q.2:ℕ))):=by
    intro q1 q2 h
    simp only[Tn.injEq]at h
    exact V7 (YL h.1) (YL h.2)
  rw[← XG _ eW]
  congr 1
  ext ⟨i,j⟩
  simp only[Xp,ZI,Zb,true_and,XH,
    Zt,Tn.injEq]
  constructor
  · rintro ⟨q,⟨h1,h2⟩,rfl,rfl⟩
    exact ⟨⟨q.1.2,q.2.2⟩,h1,not_lt.1 h2⟩
  · rintro ⟨⟨hi,hj⟩,hij,O6⟩
    exact ⟨(⟨i,hi⟩,⟨j,hj⟩),⟨hij,not_lt.2 O6⟩,rfl,rfl⟩
lemma Lm [Finite L2] {p r s s2 b:ℕ} (hp:p.Prime)
    (lU:ZB L2=p^s2) (g:Fin r→ L1)
    (hg:ZA (ZF g)=⊤) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' {j | (j:ℕ)<s}))
    (hb:p^b≤ZB (κ.flip h).range) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β1 : L1→*L1→*L2 | g4 β1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,
          (∀ z,∀ u∈ZA (g '' {j | (j:ℕ)<s}),β2 z u=κ z u)∧
          f4 β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  set T:=(ZU:Finset (Fin r×Fin r)).filter (fun q=>q.1<q.2) with qM
  set Pc:=T.filter (fun q=> (q.1:ℕ)<s) with Dd
  set Po:=T.filter (fun q=> ¬ (q.1:ℕ)<s) with Ip
  have Gp:∀ i,∀ j∈{j:Fin r | (j:ℕ)<s},i=j∨(i,j)∈Pc∨(j,i)∈Pc:=by
    intro i j hj
    have mC:(j:ℕ)<s:=hj
    rcases Vq i j with hij | hij | hij
    · refine XQ (Y7 ?_)
      rw[Dd,qM,ZI,ZI]
      exact ⟨⟨Zb _,hij⟩,Nat.lt_trans (show (i:ℕ)<j from hij) mC⟩
    · exact Y7 hij
    · refine XQ (XQ ?_)
      rw[Dd,qM,ZI,ZI]
      exact ⟨⟨Zb _,hij⟩,mC⟩
  have Bh:∀ i j,i∉{j:Fin r | (j:ℕ)<s}→j∉{j:Fin r | (j:ℕ)<s}→
      i=j∨(i,j)∈Po∨(j,i)∈Po:=by
    intro i j hi hj
    have gJ:¬ (i:ℕ)<s:=hi
    have mC:¬ (j:ℕ)<s:=hj
    rcases Vq i j with hij | hij | hij
    · refine XQ (Y7 ?_)
      rw[Ip,qM,ZI,ZI]
      exact ⟨⟨Zb _,hij⟩,gJ⟩
    · exact Y7 hij
    · refine XQ (XQ ?_)
      rw[Ip,qM,ZI,ZI]
      exact ⟨⟨Zb _,hij⟩,mC⟩
  have main:=aan hp lU g hg {j:Fin r | (j:ℕ)<s} κ hh hb Pc Po D Gp Bh v
  refine WS main (Zk hp.pos ?_)
  have Ij:T.card=r.choose 2:=by
   have h0:=jY r 0
   rw[UK]at h0
   rw[← h0,qM]
   congr 1
   ext q
   simp
  have hT:Pc.card+Po.card=r.choose 2:=by
   rw[Dd,Ip,Uh,Ij]
  have Eo:Po.card=(r - s).choose 2:=by
   rw[← jY r s,Ip,qM]
   congr 1
   ext q
   simp
  have QX:D⊆Pc:=by
   intro q hq
   rw[Dd,qM,ZI,ZI]
   exact ⟨⟨Zb _,(hD q hq).1⟩,(hD q hq).2⟩
  have hsd:(Pc \ D).card+D.card=Pc.card:=XX QX
  have wc:ZB (κ.flip h).range≤ZB L2:=
    YO _ (κ.flip h).rangeRestrict_surjective
  have KZ:b≤ s2:=iE hp.one_lt (hb.trans (wc.trans lU.le))
  have key:∀ a o b c:ℕ,(b+ c)*a+ c* o≤(a+ o)*(b+ c) - o*b:=by
   intro a o b c
   have e:(a+ o)*(b+ c)= o*b+((b+ c)*a+ c* o):=by ring
   rw[e,Yb]
  have e1:r.choose 2 - D.card=(Pc \ D).card+Po.card:=by omega
  rw[e1, ← Eo]
  obtain ⟨c,hc⟩:∃ c,s2=b+ c:=⟨s2 - b,by omega⟩
  rw[hc,Yb]
  exact key _ _ _ _
lemma ab3 [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n b:ℕ} (hp:p.Prime)
    (kB:s≤ r) (lU:ZB L2=p^s2) (jG:ZB L3=p^s3) (y:Fin n→ L2)
    (hy:ZA (ZF y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZF g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | g4 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        (∀ j:Fin r,(j:ℕ)<s→ZB (β.2.flip (g j)).range≤p^b)∧
        (∃ h∈ZA (g '' {j | (j:ℕ)<s}),p^b≤ZB (β.2.flip h).range)∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      p ^(s*(b*(n+s3+1 - b)))*
        p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  haveI:Finite (L2→*L3):=
    YH (fun f:L2→*L3=> (f:L2→ L3)) Yr
  haveI:Finite (L1→*L2):=
    YH (fun f:L1→*L2=> (f:L1→ L2)) Yr
  haveI:Finite (L1→*L1→*L2):=
    YH (fun f:L1→*L1→*L2=> (f:L1→(L1→*L2))) Yr
  set C:=ZA (g '' {j | (j:ℕ)<s}) with abH
  let c:Fin s→ L1:= fun k=>g (RJ kB k)
  set BR :={β:(L1→*L1→*L2)×(L2→*L1→*L3) | g4 β.1∧
        ZA {w | ∃ u∈C,∃ u'∈C,β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        (∀ j:Fin r,(j:ℕ)<s→ZB (β.2.flip (g j)).range≤p^b)∧
        (∃ h∈C,p^b≤ZB (β.2.flip h).range)∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q} with hBR
  rcases BR.eq_empty_or_nonempty with hBe | ⟨β1,hβ1⟩
  · rw[hBe,Y3]
    exact Zv _
  have aex:b≤ s3:=by
   obtain ⟨-, -, -, -,⟨h1, -,s8⟩, -⟩:=id hβ1
   have hr :ZB (β1.2.flip h1).range≤ZB L3:=
     T9 (H:=(β1.2.flip h1).range)
   exact iE hp.one_lt (s8.trans (hr.trans jG.le))
  let ρ:(L1→*L1→*L2)×(L2→*L1→*L3)→(Fin s→(L2→*L3)):=
    fun β k=>β.2.flip (c k)
  have qv:(ρ '' BR).ncard≤p^(s*(b*(n+s3+1 - b))):=by
   refine WS (Yk ?_ (Zl _))
     (aaF hp jG aex y hy s (b:=b))
   rintro _ ⟨β,hβ,rfl⟩ k
   obtain ⟨-, -, -,adX, -⟩:=id hβ
   exact adX (RJ kB k) (by simp)
  have pC : ∀ a,(BR∩ρ ⁻¹' {a}).ncard≤
      p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
   intro a
   rcases (BR∩ρ ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0,hβ0a⟩
   · rw[he,Y3]
     exact Zv _
   · obtain ⟨-, -, -, -,⟨h0,hh0,Fj⟩, -⟩:=id hβ0
     have hβ0a':ρ β0=a:=hβ0a
     have hsl:∀ β∈BR∩ρ ⁻¹' {a},∀ z,∀ u∈C,β.2 z u=β0.2 z u:=by
      rintro β ⟨-,hβa⟩ z u hu
      have hβa':ρ β=a:=hβa
      have dV:∀ j:Fin r,(j:ℕ)<s→β.2.flip (g j)=β0.2.flip (g j):=by
       intro j hj
       have e:= congrFun (hβa'.trans hβ0a'.symm) ⟨(j:ℕ),hj⟩
       change β.2.flip (c ⟨(j:ℕ),hj⟩)=β0.2.flip (c ⟨(j:ℕ),hj⟩) at e
       have e2:c ⟨(j:ℕ),hj⟩=g j:= congrArg g (YL rfl)
       rw[e2]at e
       exact e
      have cO:C≤(β.2 z).eqLocus (β0.2 z):=by
       rw[abH,ZE]
       rintro _ ⟨j,hj,rfl⟩
       show β.2 z (g j)=β0.2 z (g j)
       have:= congrArg (fun φ:L2→*L3=>φ z) (dV j hj)
       simpa[YB] using this
      exact cO hu
     let S43:Set (L1→*L1→*L2):={β1 | g4 β1∧
       ZA {w | ∃ u∈C,∃ u'∈C,β1 u u'=w}=⊤∧
       (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈C,β2 z u=β0.2 z u)∧f4 β1 β2)∧
       ∀ q∈D,β1 (g q.1) (g q.2)=v q}
     have oc:∀ β∈BR∩ρ ⁻¹' {a},W9 β∈S43:=by
      intro β hβ
      obtain ⟨⟨hA,dV,hJ, -, -,hDv⟩, -⟩:=id hβ
      exact ⟨hA,dV,⟨β.2,hsl β hβ,hJ⟩,hDv⟩
     have eW:WP W9 (BR∩ρ ⁻¹' {a}):=by
      intro β hβ β' hβ' h1
      obtain ⟨⟨hA,dV,hJ, -⟩, -⟩:=id hβ
      obtain ⟨⟨BT, -,hJ', -⟩, -⟩:=id hβ'
      have pL:β.1=β'.1:=h1
      have h2:β.2=β'.2:=Jx C hA BT hJ hJ' dV (fun x u _=>by rw[pL])
        (fun z u hu=> (hsl β hβ z u hu).trans (hsl β' hβ' z u hu).symm)
      exact V7 pL h2
     calc (BR∩ρ ⁻¹' {a}).ncard≤S43.ncard:=
           YM W9 oc eW (Zl _)
       _≤_:=Lm hp lU g hg β0.2 hh0 Fj D hD v
  calc BR.ncard≤(ρ '' BR).ncard*p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=
        jO BR ρ _ pC
    _ ≤ p ^(s*(b*(n+s3+1 - b)))*
          p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=
        Za _ qv
end BrBracket
section BrBreadth
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
noncomputable def jh (p:ℕ) (κ:L2→*L1→*L3) (C:Subgroup L1):ℕ:=
  sSup {k | ∃ u∈C,p^k≤ZB (κ.flip u).range}
lemma tw [Finite L3] (p:ℕ) (κ:L2→*L1→*L3) (C:Subgroup L1):
    {k | ∃ u∈C,p^k≤ZB (κ.flip u).range}.Nonempty:=
  ⟨0,show ∃ u∈C,p^0≤ZB (κ.flip u).range from
    ⟨1,C.one_mem,by rw[Y6]; exact Xi⟩⟩
lemma t8 [Finite L3] {p s3:ℕ} (hp:p.Prime) (jG:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):
    ∀ k∈{k | ∃ u∈C,p^k≤ZB (κ.flip u).range},k≤ s3:=by
  rintro k ⟨u, -,hk⟩
  exact iE hp.one_lt
    (hk.trans ((T9 (H:=(κ.flip u).range)).trans jG.le))
lemma zD [Finite L3] {p s3:ℕ} (hp:p.Prime) (jG:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):
    ∃ h∈C,p^jh p κ C≤ZB (κ.flip h).range:=
  Nat.sSup_mem (tw p κ C) ⟨s3,t8 hp jG κ C⟩
lemma GD [Finite L3] {p s3:ℕ} (hp:p.Prime) (jG:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):jh p κ C≤ s3:=
  csSup_le (tw p κ C) (t8 hp jG κ C)
lemma nY [Finite L3] {p s3:ℕ} (hp:p.Prime)
    (jG:ZB L3=p^s3) (κ:L2→*L1→*L3) (C:Subgroup L1) {u:L1} (hu:u∈C):
    ZB (κ.flip u).range≤p^jh p κ C:=by
 obtain ⟨k, -,hk⟩:=(Yp hp).1
   (show ZB (κ.flip u).range∣p^s3 by
     rw[← jG]; exact YC _)
 rw[hk]
 exact Zk hp.pos
   (le_csSup ⟨s3,t8 hp jG κ C⟩
     (show ∃ v∈C,p^k≤ZB (κ.flip v).range from ⟨u,hu,hk.ge⟩))
lemma G9 [Finite L2] [Finite L3] {p s2 s3:ℕ} (hp:p.Prime)
    (lU:ZB L2=p^s2) (jG:ZB L3=p^s3) (κ:L2→*L1→*L3)
    (C:Subgroup L1):jh p κ C≤ s2:=by
 obtain ⟨h, -,hh⟩:=zD hp jG κ C
 have hr :ZB (κ.flip h).range≤ZB L2:=
   YO _ (κ.flip h).rangeRestrict_surjective
 exact iE hp.one_lt (hh.trans (hr.trans lU.le))
lemma z9 {L:Type*} [CommGroup L] [Finite L] {ι:Type*}
    (H:ι→ Subgroup L) (M:ℕ):
    ∀ I:Finset ι,(∀ i∈I,ZB (H i)≤M)→ZB ↥(I.sup H)≤M^I.card:=by
 classical
 intro I
 refine Xn I ?_ ?_
 · intro _
   rw[Finset.sup_empty,Wf,Pk,Y6]
 · intro a I ha ih hM
   rw[Finset.sup_insert,Se,if_neg ha,Xr,mul_comm]
   exact (rT _ _).trans (Zr (hM a (Finset.mem_insert_self a I))
     (ih fun i hi=>hM i (Finset.mem_insert_of_mem hi)))
lemma Gd [Finite L3] {p r s s3:ℕ} (hp:p.Prime) (kB:s≤ r)
    (jG:ZB L3=p^s3) (κ:L2→*L1→*L3) (g:Fin r→ L1)
    (Bc:ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),κ z u=w}=⊤):
    s3≤ s*jh p κ (ZA (g '' {j | (j:ℕ)<s})):=by
  classical
  let c:Fin s→ L1:= fun k=>g (RJ kB k)
  have hc:∀ j:Fin r,∀ hj:(j:ℕ)<s,c ⟨(j:ℕ),hj⟩=g j:= fun j hj=>
    congrArg g (YL rfl)
  have aa3:(⊤:Subgroup L3)≤ZU.sup (fun k=> (κ.flip (c k)).range):=by
    rw[← Bc,ZE]
    rintro _ ⟨z,u,hu,rfl⟩
    have cO:ZA (g '' {j | (j:ℕ)<s})≤
        (ZU.sup (fun k=> (κ.flip (c k)).range)).comap (κ z):=by
      rw[ZE]
      rintro _ ⟨j,hj,rfl⟩
      rw[Xb,Zp]
      have mC:(j:ℕ)<s:=hj
      have cI:κ z (g j)∈(κ.flip (c ⟨(j:ℕ),mC⟩)).range:=by
       rw[hc j mC]
       exact ⟨z,YB _ _ _⟩
      exact OV (f:= fun k=> (κ.flip (c k)).range) (b:=⟨(j:ℕ),mC⟩)
        (Zb _) cI
    exact cO hu
  have dS:ZB L3≤
      (p^jh p κ (ZA (g '' {j | (j:ℕ)<s})))^s:=by
    have h1:=z9 (fun k=> (κ.flip (c k)).range)
      (p^jh p κ (ZA (g '' {j | (j:ℕ)<s}))) ZU
      (fun k _=>nY hp jG κ _
        (ZD ⟨RJ kB k,by simp,rfl⟩))
    rw[Y4,Zz]at h1
    rw[← Yn (G:=L3)]
    exact (YG aa3).trans h1
  rw[jG, ← X5]at dS
  have h2:=iE hp.one_lt dS
  rw[mul_comm]at h2
  exact h2
lemma F6 [Finite L2] [Finite L3] {p r s s2 s3:ℕ} (hp:p.Prime) (kB:s≤ r)
    (lU:ZB L2=p^s2) (jG:ZB L3=p^s3) (κ:L2→*L1→*L3)
    (g:Fin r→ L1)
    (Bc:ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),κ z u=w}=⊤):
    s3 ≤ s*jh p κ (ZA (g '' {j | (j:ℕ)<s}))∧
      jh p κ (ZA (g '' {j | (j:ℕ)<s}))≤ min s2 s3:=
  ⟨Gd hp kB jG κ g Bc,
    le_min (G9 hp lU jG κ _) (GD hp jG κ _)⟩
lemma qu [Finite L1] [Finite L2] [Finite L3]:
    Finite ((L1→*L1→*L2)×(L2→*L1→*L3)):=by
 haveI:Finite (L1→*L2):=
   YH (fun f:L1→*L2=> (f:L1→ L2)) Yr
 haveI:Finite (L1→*L3):=
   YH (fun f:L1→*L3=> (f:L1→ L3)) Yr
 haveI:Finite (L1→*L1→*L2):=
   YH (fun f:L1→*L1→*L2=> (f:L1→(L1→*L2))) Yr
 haveI:Finite (L2→*L1→*L3):=
   YH (fun f:L2→*L1→*L3=> (f:L2→(L1→*L3))) Yr
 infer_instance
lemma GO [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n b:ℕ}
    (hp:p.Prime) (kB:s≤ r) (lU:ZB L2=p^s2) (jG:ZB L3=p^s3)
    (y:Fin n→ L2) (hy:ZA (ZF y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZF g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | g4 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        jh p β.2 (ZA (g '' {j | (j:ℕ)<s}))=b∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      p ^(s*(b*(n+s3+1 - b)))*
        p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  have:=qu (L1:=L1) (L2:=L2) (L3:=L3)
  refine WS (Yk ?_ (Zl _))
    (ab3 hp kB lU jG y hy g hg D hD v)
  rintro β ⟨hA,dV,hJ,hb,hDv⟩
  refine ⟨hA,dV,hJ,?_,?_,hDv⟩
  · intro j hj
    rw[← hb]
    exact nY hp jG β.2 _ (ZD ⟨j,hj,rfl⟩)
  · rw[← hb]
    exact zD hp jG β.2 _
lemma rD {ι α:Type*} [DecidableEq ι] (I:Finset ι) (T:ι→ Set α):
    (⋃ i∈I,T i).ncard≤∑ i∈I,(T i).ncard:=by
 refine Xn I ?_ ?_
 · simp
 · intro a J ha ih
   rw[Sh,TV ha]
   exact (Tj _ _).trans (TE ih _)
lemma NY [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n:ℕ}
    (hp:p.Prime) (kB:s≤ r) (lU:ZB L2=p^s2) (jG:ZB L3=p^s3)
    (y:Fin n→ L2) (hy:ZA (ZF y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZF g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | g4 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        ZA
          {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      ∑ b ∈(ZM (min s2 s3+1)).filter (fun b=>s3≤ s*b),
        p ^(s*(b*(n+s3+1 - b)))*
          p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  have:=qu (L1:=L1) (L2:=L2) (L3:=L3)
  set I:=(ZM (min s2 s3+1)).filter (fun b=>s3≤ s*b) with hI
  obtain ⟨T,hT⟩:∃ T:ℕ→ Set ((L1→*L1→*L2)×(L2→*L1→*L3)),T= fun b=>
    {β | g4 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        jh p β.2 (ZA (g '' {j | (j:ℕ)<s}))=b∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}:=⟨_,rfl⟩
  have jp :{β:(L1→*L1→*L2)×(L2→*L1→*L3) | g4 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        f4 β.1 β.2∧
        ZA
          {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}⊆ ⋃ b∈I,T b:=by
    rintro β ⟨hA,dV,hJ,Bc,hDv⟩
    obtain ⟨h51,nU⟩:=F6 hp kB lU jG β.2 g Bc
    refine VJ.2 ⟨jh p β.2 (ZA (g '' {j | (j:ℕ)<s})),?_,?_⟩
    · rw[hI,ZI,Zt]
      exact ⟨Ws nU,h51⟩
    · rw[hT]
      exact ⟨hA,dV,hJ,rfl,hDv⟩
  calc _≤(⋃ b∈I,T b).ncard:=Yk jp (Zl _)
    _≤∑ b∈I,(T b).ncard:=rD I T
    _ ≤_:=Z9 fun b _=>by
      rw[hT]
      exact GO hp kB lU jG y hy g hg D hD v
lemma Jh {Γ:Type*} [Finite Γ] {ι:Type*} [DecidableEq ι] {p m3:ℕ}
    (hΓ:ZB Γ=p^m3) (P D:Finset (ι×ι)) (hDP:D⊆P) (c0:ι×ι→Γ):
    {c:ι×ι→Γ | ∀ q,q∉P \ D→ c q= c0 q}.ncard≤p^((P.card - D.card)*m3):=by
  classical
  let F:(ι×ι→Γ)→(↥(P \ D)→Γ):= fun c q=>c q.1
  have eW:WP F {c:ι×ι→Γ | ∀ q,q∉P \ D→ c q= c0 q}:=by
    intro c hc c' hc' he
    funext q
    by_cases hq:q∈P \ D
    · exact congrFun he ⟨q,hq⟩
    · rw[hc q hq,hc' q hq]
  have hk:(P \ D).card=P.card - D.card:=by
   have:=XX hDP
   omega
  calc _ ≤ZB (↥(P \ D)→Γ):=i7 _ F eW
    _ = p^((P.card - D.card)*m3):=by
      rw [Xl,YA (α:=↥(P \ D)),WG,hk,hΓ,
        ← X5]
      ring
lemma rG {Γ:Type*} [Finite Γ] {p r m3:ℕ} (hΓ:ZB Γ=p^m3)
    (D:Finset (Fin r×Fin r)) (hD:∀ q∈D,q.1<q.2) (c0:Fin r×Fin r→Γ):
    {c :Fin r×Fin r→Γ | ∀ q,q∉(ZU.filter (fun q:Fin r×Fin r=>q.1<q.2)) \ D→
      c q= c0 q}.ncard≤p^((r.choose 2 - D.card)*m3):=by
  classical
  have Ij:(ZU.filter (fun q:Fin r×Fin r=>q.1<q.2)).card=r.choose 2:=by
    have h0:=jY r 0
    rw[UK]at h0
    rw[← h0]
    congr 1
    ext q
    simp
  have hDP:D⊆ZU.filter (fun q:Fin r×Fin r=>q.1<q.2):=by
    intro q hq
    rw[ZI]
    exact ⟨Zb _,hD q hq⟩
  have h:=Jh hΓ _ D hDP c0
  rwa[Ij]at h
end BrBreadth
section BrLemma61
variable {L1 L2:Type*} [CommGroup L1] [CommGroup L2]
def yF {A B:Type*} [CommGroup A] [CommGroup B] (γ:A→*A→*B) (S:Subgroup A):
    Subgroup B:=
  ZA {w | ∃ a∈S,∃ b∈S,γ a b=w}
lemma BW {A B:Type*} [CommGroup A] [CommGroup B] [Finite A] [Finite B]
    {p k:ℕ} (hp:p.Prime) (γ:A→*A→*B) (hA:g4 γ) (hk:ZB A=p^k):
    ZB (ZA {w | ∃ a b:A,γ a b=w})≤p^k.choose 2:=by
  classical
  haveI:=Tf A
  have main : ∀ T:Finset A,∀ j,ZB (ZA (T:Set A))=p^j→
      ZB (yF γ (ZA (T:Set A)))≤p^j.choose 2:=by
   intro T
   refine Xn T ?_ ?_
   · intro j _
     have rL:yF γ (ZA ((∅ :Finset A):Set A))=⊥:=by
      rw[eq_bot_iff,yF,ZE]
      rintro _ ⟨a,ha,b, -,rfl⟩
      simp only[Finset.coe_empty,Sz,WB]at ha
      rw[ha,X9,UL]
      exact Yl _
     rw[rL,Wf]
     exact Nat.one_le_pow _ _ hp.pos
   · intro x T _ ih j hj
     set S':=ZA (T:Set A) with aeK
     set S:=ZA ((insert x T:Finset A):Set A) with DK
     have hS:S=ZA {x}⊔S':=by
      rw[DK,Ve,Set.insert_eq,S7]
     have aem:ZB S'∣p^k:=by
      rw[← hk]
      exact YC S'
     obtain ⟨j', -,mC⟩:=(Yp hp).1 aem
     have IH:=ih j' mC
     have cO:S'≤S:=by rw[hS]; exact Z5
     by_cases heq:S'=S
     · rw[← heq,mC]at hj
       have Er :j'=j:=Zd hp.two_le hj
       rw[← heq, ← Er]
       exact IH
     · have d8:ZB S'≠ZB S:= fun h'=>
         heq (YS cO h'.symm.le)
       have v5:=WU cO
       rw[mC,hj]at v5
       rw[mC,hj]at d8
       have h1:j'≤j:=(X8 hp.one_lt).1 v5
       have h2:j'≠j:= fun h'=>d8 (by rw[h'])
       have f5:j'+1≤j:=by omega
       let R:=S'.map (γ.flip x)
       set Qs:=yF γ S'⊔R with hQs
       have f1:∀ b∈S,γ x b∈Qs:=by
        have hc:S≤Qs.comap (γ x):=by
         rw[hS]
         refine sup_le ?_ ?_
         · rw[ZE,V0]
           show γ x x∈Qs
           rw[hA x]
           exact Yl _
         · intro b' Io
           show γ x b'∈Qs
           rw[g9 hA b' x]
           exact ZL (PH _
             (Zj.2 ⟨b',Io,YB _ _ _⟩))
        exact fun b hb=>hc hb
       have f2:∀ a'∈S',∀ b∈S,γ a' b∈Qs:=by
        intro a' u6
        have hc:S≤Qs.comap (γ a'):=by
         rw[hS]
         refine sup_le ?_ ?_
         · rw [ZE,V0]
           show γ a' x∈Qs
           exact ZL
             (Zj.2 ⟨a',u6,YB _ _ _⟩)
         · intro b' Io
           show γ a' b'∈Qs
           exact ZK (ZD ⟨a',u6,b',Io,rfl⟩)
        exact fun b hb=>hc hb
       have f3:∀ b∈S,S≤Qs.comap (γ.flip b):=by
        intro b hb
        rw[hS]
        refine sup_le ?_ ?_
        · rw[ZE,V0]
          show γ.flip b x∈Qs
          rw[YB]
          exact f1 b hb
        · intro a' u6
          show γ.flip b a'∈Qs
          rw[YB]
          exact f2 a' u6 b hb
       have jp:yF γ S≤Qs:=by
        rw[yF,ZE]
        rintro _ ⟨a,ha,b,hb,rfl⟩
        have:= f3 b hb ha
        rw[Zp,YB]at this
        exact this
       have hR:ZB R≤ZB S':=
         YO _ (MonoidHom.subgroupMap_surjective (γ.flip x) S')
       calc ZB (yF γ S)≤ZB ↥Qs:=YG jp
         _≤ZB (yF γ S')*ZB R:=rT _ _
         _≤p^j'.choose 2*p^j':=Zr IH (hR.trans mC.le)
         _ = p^(j'+1).choose 2:=by
             rw[Uq,U6,Xh,mul_comm]
         _≤p^j.choose 2:=Zk hp.pos (Nat.choose_le_choose 2 f5)
  have key:=main ZU k (by rw[W8,X4,
    Yn,hk])
  have e:yF γ (ZA ((ZU:Finset A):Set A))=
      ZA {w | ∃ a b:A,γ a b=w}:=by
    rw[W8,X4,yF]
    congr 1
    ext w
    simp
  rw[← e]
  exact key
lemma Qt [Finite L1] [Finite L2] {p δ:ℕ} (hp:p.Prime) (β:L1→*L1→*L2)
    (hA:g4 β) (dV:ZA (ZF (fun q:L1×L1=>β q.1 q.2))=⊤)
    (hd:ZB (powMonoidHom p:L1→*L1).range=p^δ):
    ZB (powMonoidHom p:L2→*L2).range≤p^δ.choose 2:=by
  classical
  set P:=(powMonoidHom p:L1→*L1).range with hP
  have QK:∀ a:P,∃ x:L1,x^p=(a:L1):= fun a=>by
    obtain ⟨x,hx⟩:=RW.1 a.2
    exact ⟨x,hx⟩
  let r :P→ L1:= fun a=>XP (QK a)
  have hr :∀ a,r a^p=(a:L1):= fun a=>Ym (QK a)
  have aef:∀ k:L1,k^p=1→∀ b:P,β k (b:L1)=1:=by
   intro k hk b
   obtain ⟨y,hy⟩:=QK b
   rw[← hy,map_pow, ← nJ,hk,X9,UL]
  let γ:P→*P→*L2:=WL (fun a=> (β (r a)).comp P.subtype) (by
    intro a a'
    ext b
    simp only[Y0,UF,Y8]
    have hk:(r (a*a')*(r a*r a')⁻¹)^p=1:=by
     rw[mul_pow,inv_pow,mul_pow,hr,hr,hr]
     simp
    have h0:=aef _ hk b
    simp only[YP,Wq,Y8,MonoidHom.inv_apply]at h0
    exact mul_inv_eq_one.mp h0)
  have hγ:∀ a b:P,γ a b=β (r a) (b:L1):= fun a b=>rfl
  have hAγ:g4 γ:=by
   intro a
   rw[hγ]
   conv_lhs=>rw[← hr a]
   rw[map_pow,hA (r a),one_pow]
  have hQ:(powMonoidHom p:L2→*L2).range≤ZA {w | ∃ a b:P,γ a b=w}:=by
    have h1:ZA (ZF (fun q:L1×L1=>β q.1 q.2))≤
        (ZA {w | ∃ a b:P,γ a b=w}).comap (powMonoidHom p):=by
      rw[ZE]
      rintro _ ⟨⟨x,y⟩,rfl⟩
      show powMonoidHom p (β x y)∈ZA {w | ∃ a b:P,γ a b=w}
      rw[powMonoidHom_apply]
      apply ZD
      let ax:P:=⟨x^p,x,rfl⟩
      let ay:P:=⟨y^p,y,rfl⟩
      refine ⟨ax,ay,?_⟩
      have e1:r ax^p=x^p:=hr ax
      calc γ ax ay=β (r ax) (y^p):=rfl
        _=(β (r ax) y)^p:=map_pow _ _ _
        _=β (r ax^p) y:=(nJ β _ y p).symm
        _=β (x^p) y:=by rw[e1]
        _=(β x y)^p:=nJ β x y p
    rw[dV]at h1
    rintro _ ⟨z,rfl⟩
    exact h1 (ZO z)
  calc ZB (powMonoidHom p:L2→*L2).range
      ≤ZB (ZA {w | ∃ a b:P,γ a b=w}):=YG hQ
    _≤p^δ.choose 2:=BW hp γ hAγ hd
lemma D8 {L:Type*} [CommGroup L] [Finite L] {n:ℕ} (hn:0<n)
    (adz:∀ z:L,z^n=1) (T:Finset L) (hT:ZA (T:Set L)=⊤):
    ZB L≤n^T.card:=by
 classical
 have main:∀ T:Finset L,ZB (ZA (T:Set L))≤n^T.card:=by
  intro T
  refine Xn T ?_ ?_
  · simp
  · intro x T hx ih
    rw [Ve,Set.insert_eq,S7,Se,
      if_neg hx,Xr,mul_comm]
    refine WS (rT _ _) (Zr ?_ ih)
    rw[← Subgroup.zpowers_eq_closure,OU]
    exact orderOf_le_of_pow_eq_one hn (adz x)
 have h:=main T
 rwa[hT,Yn]at h
lemma abC [Finite L1] [Finite L2] {p δ:ℕ} (hp:p.Prime) (β:L1→*L1→*L2)
    (dV:ZA (ZF (fun q:L1×L1=>β q.1 q.2))=⊤)
    (hd:ZB (powMonoidHom p:L1→*L1).range=p^δ) (T:Finset L2)
    (hT:ZA (T:Set L2)=⊤):
    ZB L2≤p^((δ+1)*T.card):=by
  have hx:∀ x:L1,x^(p^(δ+1))=1:=by
   intro x
   have h1:(⟨x^p,x,rfl⟩:(powMonoidHom p:L1→*L1).range)^
       ZB (powMonoidHom p:L1→*L1).range=1:=TY
   rw[hd]at h1
   have h2:= congrArg XJ h1
   simp only[Vg,S8]at h2
   rw[VG,X5]
   exact h2
  have hz:∀ z:L2,z^(p^(δ+1))=1:=by
   have cO:ZA (ZF (fun q:L1×L1=>β q.1 q.2))≤
       (powMonoidHom (p^(δ+1)):L2→*L2).ker :=by
     rw[ZE]
     rintro _ ⟨⟨x,y⟩,rfl⟩
     show (β x y)^(p^(δ+1))=1
     rw[← nJ,hx,X9,UL]
   rw[dV]at cO
   intro z
   exact (Zm).1 (cO (ZO z))
  have h:=D8 (X7 (SZ _ hp.ne_zero)) hz T hT
  rwa[← X5]at h
end BrLemma61
section BrGroup
variable {G:Type u} [Group G]
lemma xG {H:Type*} [Group H] (N:Subgroup H) [N.Normal] {x y:H}
    (h:x*y⁻¹∈N):ZG N x =ZG N y:=by
 have h1:ZG N (x*y⁻¹)=1:=by
  rw[← Zm,YV]
  exact h
 rw[YP,Wq]at h1
 exact mul_inv_eq_one.mp h1
lemma CQ {A B:Subgroup G} [(B.subgroupOf A).Normal]
    (h:∀ x∈A,∀ y∈A,⁅x,y⁆∈B) (a b:A⧸B.subgroupOf A):a*b=b*a:=by
 obtain ⟨x,rfl⟩:=YI (B.subgroupOf A) a
 obtain ⟨y,rfl⟩:=YI (B.subgroupOf A) b
 rw[← YP, ← YP]
 apply xG
 rw[ZT]
 show (x:G)*(y:G)*((y:G)*(x:G))⁻¹∈B
 have e:(x:G)*(y:G)*((y:G)*(x:G))⁻¹=⁅(x:G),(y:G)⁆:=by
  simp only[commutatorElement_def]
  group
 rw[e]
 exact h _ x.2 _ y.2
variable (G) in
def gY:Type u:=lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)
variable (G) in
def oI:Type u:=lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2)
noncomputable instance gY.instCommGroup:CommGroup (gY G):=
  { (inferInstance:Group (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))) with
    mul_comm:=CQ (A:=lcs G 1) (B:=lcs G 2) (fun x hx y hy=>
      bC (by norm_num) (d5 hx hy)) }
noncomputable instance oI.instCommGroup:CommGroup (oI G):=
  { (inferInstance:Group (lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2))) with
    mul_comm:=CQ (A:=lcs G 2) (B:=lcs G 3) (fun x hx y hy=>
      bC (by norm_num) (d5 hx hy)) }
instance gY.instFinite [Finite G]:Finite (gY G):=
  inferInstanceAs (Finite (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)))
instance oI.instFinite [Finite G]:Finite (oI G):=
  inferInstanceAs (Finite (lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2)))
variable (G) in
noncomputable def f9:lcs G 1→*gY G:=ZG ((lcs G 2).subgroupOf (lcs G 1))
variable (G) in
noncomputable def jK:lcs G 2→* oI G:=ZG ((lcs G 3).subgroupOf (lcs G 2))
lemma nI:Zn (f9 G):=
  YI ((lcs G 2).subgroupOf (lcs G 1))
lemma jT (w:lcs G 1):f9 G w=1↔(w:G)∈lcs G 2:=by
 have hk:(f9 G).ker=(lcs G 2).subgroupOf (lcs G 1):=
   YV ((lcs G 2).subgroupOf (lcs G 1))
 rw[← Zm,hk,ZT]
lemma jP (w:lcs G 2):jK G w=1↔(w:G)∈lcs G 3:=by
 have hk:(jK G).ker=(lcs G 3).subgroupOf (lcs G 2):=
   YV ((lcs G 3).subgroupOf (lcs G 2))
 rw[← Zm,hk,ZT]
lemma GC {a b:lcs G 1} (h:(a:G)*(b:G)⁻¹∈lcs G 2):
    f9 G a= f9 G b:=by
 have h1:f9 G (a*b⁻¹)=1:=(jT _).2 h
 rw[YP,Wq]at h1
 exact mul_inv_eq_one.mp h1
lemma GR {a b:lcs G 2} (h:(a:G)*(b:G)⁻¹∈lcs G 3):
    jK G a=jK G b:=by
 have h1:jK G (a*b⁻¹)=1:=(jP _).2 h
 rw[YP,Wq]at h1
 exact mul_inv_eq_one.mp h1
def uu (w:lcs G 1) (y:G):lcs G 2:=⟨⁅(w:G),y⁆,a8 w.2 y⟩
lemma Ee (x y z:G):
    f9 G (cw x (y *z))= f9 G (cw x y)*f9 G (cw x z):=by
 rw[← YP]
 apply GC
 show ⁅x,y *z⁆*(⁅x,y⁆*⁅x,z⁆)⁻¹∈lcs G 2
 rw[jF]
 have hc:⁅y,⁅x,z⁆⁆∈lcs G 2:=
   bF y (bF (n:=0) x (ZO z))
 have e:⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,z⁆*(⁅x,y⁆*⁅x,z⁆)⁻¹=
     ⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,y⁆⁻¹:=by group
 rw[e]
 exact TJ inferInstance _ hc _
lemma Fz (x x' y:G):
    f9 G (cw (x*x') y)= f9 G (cw x y)*f9 G (cw x' y):=by
 rw[mul_comm (f9 G (cw x y)), ← YP]
 apply GC
 show ⁅x*x',y⁆*(⁅x',y⁆*⁅x,y⁆)⁻¹∈lcs G 2
 rw[gX]
 have e:⁅x,⁅x',y⁆⁆*⁅x',y⁆*⁅x,y⁆*(⁅x',y⁆*⁅x,y⁆)⁻¹=⁅x,⁅x',y⁆⁆:=by group
 rw[e]
 exact bF x (bF (n:=0) x' (ZO y))
lemma Da (w:lcs G 1) (y z:G):
    jK G (uu w (y *z))=jK G (uu w y)*jK G (uu w z):=by
 rw[← YP]
 apply GR
 show ⁅(w:G),y *z⁆*(⁅(w:G),y⁆*⁅(w:G),z⁆)⁻¹∈lcs G 3
 rw[jF]
 have hc:⁅y,⁅(w:G),z⁆⁆∈lcs G 3:=
   bF y (a8 w.2 z)
 have e:⁅(w:G),y⁆*⁅y,⁅(w:G),z⁆⁆*⁅(w:G),z⁆*(⁅(w:G),y⁆*⁅(w:G),z⁆)⁻¹=
     ⁅(w:G),y⁆*⁅y,⁅(w:G),z⁆⁆*⁅(w:G),y⁆⁻¹:=by group
 rw[e]
 exact TJ inferInstance _ hc _
lemma Ed (w w':lcs G 1) (y:G):
    jK G (uu (w*w') y)=jK G (uu w y)*jK G (uu w' y):=by
 rw[mul_comm (jK G (uu w y)), ← YP]
 apply GR
 show ⁅(w:G)*(w':G),y⁆*(⁅(w':G),y⁆*⁅(w:G),y⁆)⁻¹∈lcs G 3
 rw[gX]
 have e:⁅(w:G),⁅(w':G),y⁆⁆*⁅(w':G),y⁆*⁅(w:G),y⁆*
     (⁅(w':G),y⁆*⁅(w:G),y⁆)⁻¹=⁅(w:G),⁅(w':G),y⁆⁆:=by group
 rw[e]
 exact bF (w:G) (a8 w'.2 y)
noncomputable def wn (x:G):G→*gY G:=
  WL (fun y=>f9 G (cw x y)) (fun y z=>Ee x y z)
noncomputable def wC (w:lcs G 1):G→* oI G:=
  WL (fun y=>jK G (uu w y)) (fun y z=>Da w y z)
lemma Q5 (x x':G):wn (x*x')=wn x*wn x':=by
 ext y
 rw[Y8]
 exact Fz x x' y
lemma Qr (w w':lcs G 1):wC (w*w')=wC w*wC w':=by
 ext y
 rw[Y8]
 exact Ed w w' y
lemma E3 {A:Type*} [CommGroup A] (f f':G→*A):
    YN (f*f')=YN f*YN f':=by
 apply Tv
 ext y
 simp only[Y0,Y8,Abelianization.lift_apply_of]
variable (G) in
noncomputable def AH:Abelianization G→*Abelianization G→*gY G:=
  Abelianization.lift (WL (fun x =>YN (wn x))
    (fun x x'=>by
      show YN (wn (x*x'))=
        YN (wn x)*YN (wn x')
      rw[Q5,E3]))
variable (G) in
noncomputable def FO:gY G→*Abelianization G→* oI G:=
  QuotientGroup.lift ((lcs G 2).subgroupOf (lcs G 1))
    (MonoidHom.mk' (fun w=>YN (wC w))
      (fun w w'=>by
        show YN (wC (w*w'))=
          YN (wC w)*YN (wC w')
        rw[Qr,E3]))
    (by
      intro w hw
      rw[Zm]
      apply Tv
      ext y
      show jK G (uu w y)=1
      rw[jP]
      rw[ZT]at hw
      exact a8 hw y)
lemma z4 (x y:G):
    AH G (ZJ x) (ZJ y)= f9 G (cw x y):=rfl
lemma qI (w:lcs G 1) (z:G):
    FO G (f9 G w) (ZJ z)=jK G (uu w z):=rfl
lemma jv:Zn (ZJ:G→*Abelianization G):=
  fun a=>QuotientGroup.induction_on a fun x => ⟨x,rfl⟩
instance ab2 [Finite G]:Finite (Abelianization G):=
  Zy _ jv
lemma Mx:g4 (AH G):=by
 intro a
 obtain ⟨x,rfl⟩:=jv a
 rw[z4,jT]
 show ⁅x,x⁆∈lcs G 2
 rw[commutatorElement_self]
 exact Yl _
lemma Db:
    ZA (ZF (fun q:Abelianization G×Abelianization G=>
      AH G q.1 q.2))=⊤:=by
  set K:=ZA (ZF (fun q:Abelianization G×Abelianization G=>
      AH G q.1 q.2)) with hK
  have hcw:∀ a b:G,cw a b∈K.comap (f9 G):=by
   intro a b
   rw[Zp]
   exact ZD ⟨(ZJ a,ZJ b),rfl⟩
  have cO:commutator G≤(K.comap (f9 G)).map (lcs G 1).subtype:=by
   rw[commutator_eq_closure,ZE]
   rintro _ ⟨a,b,rfl⟩
   exact Zj.2 ⟨cw a b,hcw a b,rfl⟩
  rw[Yo]
  intro q _
  obtain ⟨w,rfl⟩:=nI q
  have hw:(w:G)∈commutator G:=by
   rw[eO]
   exact w.2
  obtain ⟨w',EU,hww⟩:=Zj.1 (cO hw)
  have:w'=w:=Zu hww
  rw[← this]
  exact EU
lemma Nc (a b c:G):
    ⁅⁅a,b⁆,b*c*b⁻¹⁆*⁅⁅b,c⁆,c*a*c⁻¹⁆*⁅⁅c,a⁆,a*b*a⁻¹⁆=1:=by
 simp only[commutatorElement_def]
 group
lemma o8 {w:G} (hw:w∈lcs G 1) (y z:G):
    ⁅w,z⁆*⁅w,y *z*y⁻¹⁆⁻¹∈lcs G 3:=by
 have e:y *z*y⁻¹=⁅y,z⁆*z:=by
  simp only[commutatorElement_def]
  group
 rw[e,jF]
 have h1:⁅w,⁅y,z⁆⁆∈lcs G 3:=
   d5 (a:=1) (b:=1) hw (b7 y z)
 have h2:⁅⁅y,z⁆,⁅w,z⁆⁆∈lcs G 3:=
   bC (show 3≤1+2+1 by norm_num) (d5 (a:=1) (b:=2)
     (b7 y z) (a8 hw z))
 have e2:⁅w,z⁆*(⁅w,⁅y,z⁆⁆*⁅⁅y,z⁆,⁅w,z⁆⁆*⁅w,z⁆)⁻¹=
     ⁅⁅y,z⁆,⁅w,z⁆⁆⁻¹*⁅w,⁅y,z⁆⁆⁻¹:=by group
 rw[e2]
 exact mul_mem (inv_mem h2) (inv_mem h1)
lemma QH:f4 (AH G) (FO G):=by
 intro a b c
 obtain ⟨x,rfl⟩:=jv a
 obtain ⟨y,rfl⟩:=jv b
 obtain ⟨z,rfl⟩:=jv c
 rw [z4,z4,z4,qI,qI,qI, ← YP, ← YP,
   jP]
 show ⁅⁅x,y⁆,z⁆*⁅⁅y,z⁆,x⁆*⁅⁅z,x⁆,y⁆∈lcs G 3
 have h1:= o8 (b7 x y) y z
 have h2:= o8 (b7 y z) z x
 have h3:= o8 (b7 z x) x y
 have key:ZG (lcs G 3) (⁅⁅x,y⁆,z⁆*⁅⁅y,z⁆,x⁆*⁅⁅z,x⁆,y⁆)=1:=by
  rw [YP,YP,xG _ h1,xG _ h2,xG _ h3, ← YP, ← YP,
    Nc,X9]
 rwa[← Zm,YV]at key
variable {p:ℕ} [hp:Fact p.Prime] [Finite G]
lemma x6:ZB (lcs G 1)=ZB (lcs G 2)*ZB (gY G):=by
 have h1:=Z4 ((lcs G 2).subgroupOf (lcs G 1))
 have h2:=YJ (XM
   (bC (D:=G) (show 1≤2 by norm_num))).toEquiv
 rw[h2]at h1
 exact h1.symm
lemma aah (hG:IsPGroup p G):
    ZB (powMonoidHom p:gY G→*gY G).range *p^r2 p G=ZB (gY G):=by
 have hQ:IsPGroup p (gY G):=(hG.to_subgroup (lcs G 1)).to_quotient _
 have h1:(cE p (gY G)).index =p^ZV (gY G):= oA hQ
 have h2:ZV (gY G)=r2 p G:=m8 hG
 have h3:cE p (gY G)=(powMonoidHom p:gY G→*gY G).range:=by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw[ZE]
      rintro _ ⟨g,rfl⟩
      exact ⟨g,rfl⟩
    · rw[WE,Z7]
      intro g1 _ g2 _
      rw[commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm g1 g2)]
      exact Yl _
  · rintro _ ⟨g,rfl⟩
    exact ZK (ZD ⟨g,rfl⟩)
 rw[h3,h2]at h1
 rw[← h1]
 exact Z4 _
lemma Et (hG:IsPGroup p G):
    ZB (powMonoidHom p:Abelianization G→*Abelianization G).range=
      p^j9 p G:=by
 have hK:DG p G (cE p G)=(powMonoidHom p:Abelianization G→*Abelianization G).range:=by
  apply le_antisymm _ Z5
  refine sup_le ?_ YD
  rw[Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw[XT,ZE]
    rintro _ ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨ZJ g,(map_pow ZJ g p).symm⟩
  · rw[Subgroup.map_le_iff_le_comap]
    intro x hx
    rw[Zp]
    have h1:ZJ x =1:=by
     rw[← Zm,WV]
     exact hx
    rw[h1]
    exact Yl _
 have hV:(DG p G (cE p G)).index =p^ZV G:=My hG
 have hAb:ZB (Abelianization G)=p^(ZV G+j9 p G):=by
  rw[← o_ hG, ← eO]
  rfl
 have h1:=Z4 (DG p G (cE p G))
 rw[hV,hAb,hK,Xh,mul_comm (p^ZV G)]at h1
 exact Yc (X7 (SZ _ hp.out.ne_zero)) h1
lemma Gm (hG:IsPGroup p G):
    ZB (lcs G 1)≤ZB (lcs G 2)*p^(r2 p G+(j9 p G).choose 2):=by
 have h61:=Qt hp.out (AH G) Mx Db (Et hG)
 rw[x6, ← aah hG,Xh,mul_comm (p^r2 p G)]
 exact VR _ (Za _ h61)
lemma KG (hG:IsPGroup p G):
    ZB (lcs G 1)≤ZB (lcs G 2)*p^(r2 p G*(j9 p G+1)):=by
 obtain ⟨T,Ij,hT⟩:=SN (gY G)
 have h:=abC hp.out (AH G) Db (Et hG) T hT
 have hr :ZV (gY G)=r2 p G:=m8 hG
 rw[Ij,hr,mul_comm]at h
 rw[x6]
 exact VR _ h
end BrGroup
section BrTransport
variable {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
noncomputable def qz (e1:Abelianization G≃*L1) (e2:gY G≃*L2):L1→*L1→*L2:=
  MonoidHom.mk' (fun x => (e2.toMonoidHom.comp (AH G (e1.symm x))).comp e1.symm.toMonoidHom)
    (fun x x'=>by
      ext z
      simp[Y0,Y8,YP])
noncomputable def tQ (e1:Abelianization G≃*L1) (e2:gY G≃*L2) (e3:oI G≃*L3):
    L2→*L1→*L3:=
  MonoidHom.mk' (fun x => (e3.toMonoidHom.comp (FO G (e2.symm x))).comp e1.symm.toMonoidHom)
    (fun x x'=>by
      ext z
      simp[Y0,Y8,YP])
variable (e1:Abelianization G≃*L1) (e2:gY G≃*L2) (e3:oI G≃*L3)
lemma qV (x y:L1):qz e1 e2 x y=e2 (AH G (e1.symm x) (e1.symm y)):=rfl
lemma qd (z:L2) (x:L1):tQ e1 e2 e3 z x =e3 (FO G (e2.symm z) (e1.symm x)):=
  rfl
lemma DE (a b:G):
    qz e1 e2 (e1 (ZJ a)) (e1 (ZJ b))=e2 (f9 G (cw a b)):=by
 rw[qV,Yv,Yv,z4]
lemma Qa (w:lcs G 1) (c:G):
    tQ e1 e2 e3 (e2 (f9 G w)) (e1 (ZJ c))=e3 (jK G (uu w c)):=by
 rw[qd,Yv,Yv,qI]
lemma aaX:g4 (qz e1 e2):=by
 intro x
 rw[qV,Mx,X9]
lemma Iz:f4 (qz e1 e2) (tQ e1 e2 e3):=by
 intro x y z
 rw [qV,qV,qV,qd,qd,qd,
   Yv,Yv,Yv,
   ← YP e3, ← YP e3,QH (G:=G) (e1.symm x) (e1.symm y) (e1.symm z),X9]
lemma LZ {G':Type u} [Group G'] (e1':Abelianization G'≃*L1)
    (e2':gY G'≃*L2) (hT:qz e1 e2=qz e1' e2') {ι:Type*} (a:ι→G) (a':ι→G')
    (ha:∀ i,e1 (ZJ (a i))=e1' (ZJ (a' i))) (j k:ι):
    e2 (f9 G (cw (a j) (a k)))=e2' (f9 G' (cw (a' j) (a' k))):=by
 rw[← DE e1 e2, ← DE e1' e2',hT,ha j,ha k]
lemma LV {G':Type u} [Group G'] (e1':Abelianization G'≃*L1)
    (e2':gY G'≃*L2) (e3':oI G'≃*L3) (hT:tQ e1 e2 e3=tQ e1' e2' e3')
    (w:lcs G 1) (w':lcs G' 1) (hw:e2 (f9 G w)=e2' (f9 G' w')) (c:G) (c':G')
    (hc:e1 (ZJ c)=e1' (ZJ c')):
    e3 (jK G (uu w c))=e3' (jK G' (uu w' c')):=by
 rw[← Qa e1 e2 e3, ← Qa e1' e2' e3',hT,hw,hc]
end BrTransport
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CNT3Defs
def fF (m r1 r2 s lam m2 m3 r3:ℕ):Set FiniteGrp.{0}:=
  {G | ZB G=2^m∧
    (⊤:Subgroup G).lowerCentralSeries 2≠⊥∧
    (⊤:Subgroup G).lowerCentralSeries 3=⊥∧
    ZV G=r1∧
    Group.rank ((⊤:Subgroup G).lowerCentralSeries 1⧸
      ((⊤:Subgroup G).lowerCentralSeries 2).subgroupOf
        ((⊤:Subgroup G).lowerCentralSeries 1))=r2∧
    sInf {k | ∃ H:Subgroup G,(⊤:Subgroup G).lowerCentralSeries 1=
      ⁅H,H⁆⊔(⊤:Subgroup G).lowerCentralSeries 2∧ZV H=k}=s∧
    ((⊤:Subgroup G).lowerCentralSeries 1).index =2^(r1+lam)∧
    ZB ((⊤:Subgroup G).lowerCentralSeries 1)=2^m2∧
    ZB ((⊤:Subgroup G).lowerCentralSeries 2)=2^m3∧
    ZV ((⊤:Subgroup G).lowerCentralSeries 2)=r3}
def f8 (m r1 r2 s lam m2 m3 r3:ℕ):
    Set (Quotient (YF FiniteGrp.{0})):=
  Yd (YF FiniteGrp.{0}) '' fF m r1 r2 s lam m2 m3 r3
def kv (r1 r2 r3 lam m2 m3:ℕ):ℕ:=
  (r1*m2+(r1 - 1)*lam)+(r2*m3+(r2 - 1)*(m2 - m3 - r2))+(r3 - 1)*(m3 - r3)
noncomputable def oB (r1 r2 s m2 m3 b2:ℕ):ℝ:=
  ((r1.choose 2:ℝ) - r2)*m2+
    (b2:ℝ)*((s:ℝ)*((r2:ℝ)+m3 - b2+1) - ((r1 - s).choose 2:ℝ))
def w9 (r1 r2 s lam m2 m3:ℕ):Prop:=
  2 ≤ s∧s≤ r1∧s - 1≤ r2∧r2≤ s.choose 2∧m2 - m3 - r2≤lam.choose 2∧
    m2 - m3≤ r2*(lam+1)
def Lk:Prop:=
  ∀ m r1 r2 s lam m2 m3 r3:ℕ,¬ w9 r1 r2 s lam m2 m3→
    f8 m r1 r2 s lam m2 m3 r3= ∅
end CNT3Defs
section CNT3Bridge
variable (G:Type u) [Group G] [Finite G]
noncomputable def y3:ℕ:=
  sInf {k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧ZV H=k}
lemma Gh (H:Subgroup G):⁅H,H⁆⊔lcs G 2≤lcs G 1:=by
 refine sup_le ?_ (bC (by norm_num))
 rw[← eO,WE]
 exact XE le_top le_top
lemma z6:y3 G=bD G:=by
 apply le_antisymm
 · have d8:{k | ∃ u:Fin k→G,
       lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
         lcs G 2}.Nonempty:=by
     let e:Fin (ZB G)→G:=(Xz G).symm
     have he:ZF e=RG:=U3 _
     refine ⟨ZB G,e,?_⟩
     rw[he,X4]
     exact WM
   obtain ⟨u,hu⟩:=Wr d8
   have cI:ZV (ZA (ZF u))∈
       {k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧ZV H=k}:=
     ⟨_,le_antisymm hu (Gh G _),rfl⟩
   have h1:=WK cI
   have h2:=(Ri (congrArg ZA (IL u))).le.trans
     (vE (JM u) _)
   unfold y3 bD
   exact h1.trans h2
 · have adQ:{k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧ZV H=k}.Nonempty:=
     ⟨_,⊤,(sup_eq_left.mpr (bC (by norm_num):lcs G 2≤lcs G 1)).symm,rfl⟩
   obtain ⟨H,hH,hk⟩:=Wr adQ
   obtain ⟨x,hx⟩:=BX H
   unfold y3 bD
   apply WK
   refine ⟨fun i=>x i.val,?_⟩
   have e:ZF (fun i:Fin (sInf {k | ∃ H:Subgroup G,
       lcs G 1=⁅H,H⁆⊔lcs G 2∧ZV H=k})=>x i.val)=
       x '' ZH (ZV H):=by
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
lemma zC [Fact (Vd 2)] (hG:IsPGroup 2 G):
    ZV (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))=r2 2 G:=
  m8 hG
lemma vW [Fact (Vd 2)] (hG:IsPGroup 2 G) (lam:ℕ):
    (lcs G 1).index =2^(ZV G+lam)↔j9 2 G=lam:=by
 constructor
 · intro h
   have h':=(o_ hG).symm.trans h
   have:=Zd (Tw 2) h'
   omega
 · rintro rfl
   exact o_ hG
end CNT3Bridge
section CNT3Mem
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma jc [Fact (Vd 2)] (G:FiniteGrp.{0}):
    G ∈ fF m r1 r2 s lam m2 m3 r3↔
      ZB G=2^m∧lcs G 2≠⊥∧lcs G 3=⊥∧ZV G=r1∧OMA.SimsLite.r2 2 G=r2∧
        bD G=s∧j9 2 G=lam∧ZB (lcs G 1)=2^m2∧
        ZB (lcs G 2)=2^m3∧ZV (lcs G 2)=r3:=by
 unfold fF
 constructor
 · rintro ⟨hc,h3,h4,jB,q7,hs,aa7,w8,ED,hr3⟩
   have hp:IsPGroup 2 G:=YK hc
   refine ⟨hc,h3,h4,jB,(zC hp).symm.trans q7,
     (z6 G).symm.trans hs,?_,w8,ED,hr3⟩
   have h:(lcs G 1).index =2^(ZV G+lam):=by
    rw[jB]
    exact aa7
   exact (vW hp lam).mp h
 · rintro ⟨hc,h3,h4,jB,q7,hs,hl,w8,ED,hr3⟩
   have hp:IsPGroup 2 G:=YK hc
   refine ⟨hc,h3,h4,jB,(zC hp).trans q7,(z6 G).trans hs,?_,
     w8,ED,hr3⟩
   have h:=(vW hp lam).mpr hl
   rw[jB]at h
   exact h
lemma Ci {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3):
    m=r1+lam+m2:=by
 obtain ⟨hc, -, -, -, -, -,aa7,w8, -, -⟩:=hG
 have h:=Z4 ((⊤:Subgroup G).lowerCentralSeries 1)
 rw[aa7,w8,hc, ← Xh]at h
 have:=Zd (Tw 2) h
 omega
lemma tL:(f8 m r1 r2 s lam m2 m3 r3).Finite:=by
 unfold f8
 refine J5 (m:=m) Ze _ ?_
 intro G hG
 refine ⟨hG.1,?_⟩
 intro h
 apply hG.2.1
 rw[eq_bot_iff, ← h]
 exact bC (by norm_num)
end CNT3Mem
section Lk
lemma yI [Fact (Vd 2)] {G:Type u} [Group G] [Finite G] {m:ℕ}
    (dS:ZB G=2^m) (h3:lcs G 2≠⊥):
    2 ≤bD G∧bD G≤ZV G∧bD G - 1≤ r2 2 G∧
      r2 2 G≤(bD G).choose 2∧
      ZB (lcs G 1)≤ZB (lcs G 2)*2^(r2 2 G+(j9 2 G).choose 2)∧
      ZB (lcs G 1)≤ZB (lcs G 2)*2^(r2 2 G*(j9 2 G+1)):=by
 have hG:IsPGroup 2 G:=YK dS
 have wJ:lcs G 1≠⊥:=by
  intro h
  apply h3
  rw[eq_bot_iff, ← h]
  exact bC (by norm_num)
 obtain ⟨u,d,X,r,bU, -⟩:=qW Ze dS wJ
 obtain ⟨h1,h2,h3'⟩:=Alt2.Ih (p:=2) hG
 exact ⟨bU,h3',by omega,h2,Gm hG,KG hG⟩
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma wT {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3):
    w9 r1 r2 s lam m2 m3:=by
 have:Fact (Vd 2):=⟨Ze⟩
 have hG':=(jc G).mp hG
 obtain ⟨hc,h3, -,jB,q7,hs,hl,w8,ED, -⟩:=hG'
 obtain ⟨c1,c2,c3,c4,c5,c6⟩:=yI hc h3
 rw[hs]at c1 c2 c3 c4
 rw[jB]at c2
 rw[q7]at c3 c4 c5 c6
 rw[hl]at c5 c6
 rw[w8,ED, ← Xh]at c5 c6
 have e5:= OMA.SimsLite.lD (p:=2) (Tw 2) c5
 have e6:= OMA.SimsLite.lD (p:=2) (Tw 2) c6
 refine ⟨c1,c2,c3,c4,?_,?_⟩<;>omega
end Lk
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section Mult3Defs
end Mult3Defs
section Mult3Bridge
variable {m r1 r2 s lam m2 m3 r3 z k:ℕ}
end Mult3Bridge
namespace Mult3
open Module
section CoreCent
variable {F V W:Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
def gz (B:V→ₗ[F] V→ₗ[F] W) (U:Submodule F V):Submodule F V where
  carrier :={v | ∀ u∈U,B v u=0}
  add_mem':=by
    intro a b ha hb u hu
    rw[map_add,WH,ha u hu,hb u hu,add_zero]
  zero_mem':=by
    intro u _
    rw[map_zero,LinearMap.zero_apply]
  smul_mem':=by
    intro c a ha u hu
    rw[map_smul,RK,ha u hu,smul_zero]
lemma v9 {B:V→ₗ[F] V→ₗ[F] W} {U:Submodule F V} {v:V}:
    v∈gz B U↔∀ u∈U,B v u=0:=U8
lemma yW (B:V→ₗ[F] V→ₗ[F] W) (hB:∀ x,B x x =0) (x y:V):
    B x y= - B y x:=by
 have h:=hB (x+y)
 simp only[map_add,WH,hB,zero_add,add_zero]at h
 exact eq_neg_of_add_eq_zero_right h
lemma B3 [FiniteDimensional F V] (B:V→ₗ[F] V→ₗ[F] W)
    (hB:∀ x,B x x =0) (U:Submodule F V) (hU:Alt2.jg B U)
    (nU:∀ U':Submodule F V,Alt2.jg B U'→ finrank F U≤finrank F U'):
    gz B U⊓U=⊥:=by
 rw[eq_bot_iff]
 intro v hv
 rw[VS]
 by_contra hv0
 obtain ⟨hvK,hvU⟩:=U7.mp hv
 have acQ:=v9.mp hvK
 have aek:(⟨v,hvU⟩:U)≠0:=by
  intro h
  apply hv0
  have:= congrArg XJ h
  exact this
 obtain ⟨C,hC⟩:=SU (F ∙ (⟨v,hvU⟩:U))
 have F5:finrank F (F ∙ (⟨v,hvU⟩:U))+finrank F C= finrank F U:=
   Submodule.finrank_add_eq_of_isCompl hC
 rw[finrank_span_singleton aek]at F5
 have MZ:finrank F (C.map U.subtype)= finrank F C:=Submodule.finrank_map_subtype_eq U C
 have abQ:∀ c∈C.map U.subtype,c∈U:=by
  intro c hc
  obtain ⟨c', -,rfl⟩:=WZ.mp hc
  exact c'.2
 have acU:∀ x∈U,∃ a:F,∃ c∈C.map U.subtype,x =a•v+ c:=by
  intro x hx
  have cI:(⟨x,hx⟩:U)∈(F ∙ (⟨v,hvU⟩:U))⊔C:=by
   rw[hC.sup_eq_top]
   exact XK
  obtain ⟨y,hy,c,hc,hyc⟩:=Ru.mp cI
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hy
  refine ⟨a,(c:V),VY hc,?_⟩
  have:= congrArg XJ hyc
  rw[Submodule.coe_add,Submodule.coe_smul]at this
  exact this.symm
 have hsk:∀ y∈U,B y v=0:=by
  intro y hy
  rw[yW B hB y v,acQ y hy,neg_zero]
 have hG':Alt2.jg B (C.map U.subtype):=by
  unfold Alt2.jg at hU⊢
  rw[Yo, ← hU,YU]
  rintro w ⟨x,hx,y,hy,rfl⟩
  obtain ⟨a,c1,lT,rfl⟩:=acU x hx
  obtain ⟨b,c2,uL,rfl⟩:=acU y hy
  have e:B (a•v+ c1) (b•v+ c2)=B c1 c2:=by
   simp only[map_add,map_smul,WH,RK,hB v,
     acQ c2 (abQ c2 uL),hsk c1 (abQ c1 lT),smul_zero,zero_add,add_zero]
  rw[e]
  exact Z1 ⟨c1,lT,c2,uL,rfl⟩
 have:=nU _ hG'
 omega
end CoreCent
section Prop131
variable {F V W:Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
def zj (B:V→ₗ[F] V→ₗ[F] W) {s z:ℕ} (u:Fin s→V) (x:Fin z→V):
    Fin z→Fin s→ W:=
  fun l j=>B (u j) (x l)
lemma yZ (B:V→ₗ[F] V→ₗ[F] W) (hB:∀ x,B x x =0) {s z:ℕ}
    (u:Fin s→V) {x y:Fin z→V} (h:zj B u x =zj B u y) (l:Fin z):
    x l - y l∈gz B (ZQ F (ZF u)):=by
 rw[v9]
 have cO:ZQ F (ZF u)≤LinearMap.ker (B (x l - y l)):=by
  rw[YU]
  rintro _ ⟨j,rfl⟩
  have hj:B (u j) (x l)=B (u j) (y l):= congrFun (congrFun h l) j
  show B (x l - y l) (u j)=0
  rw[yW B hB (x l - y l) (u j),map_sub,hj,sub_self,neg_zero]
 intro w hw
 exact Ro.mp (cO hw)
lemma y6 {α β:Type*} [Finite α] (f:α→β) (M:ℕ)
    (h:∀ a:α,ZB {a':α//f a'= f a}≤M):
    ZB α≤ZB (ZF f)*M:=by
 classical
 have:=Tf α
 have h1:=Finset.card_le_mul_card_image (f:= f) (ZU:Finset α) M (by
  intro b hb
  obtain ⟨a, -,rfl⟩:=Xp.mp hb
  have e:(ZU.filter fun x =>f x = f a).card=ZB {a':α//f a'= f a}:=by
    rw[YA,Rg]
  rw[e]
  exact h a)
 have e2:ZB (ZF f)=(ZU.image f).card:=by
  rw [show ZF f=((ZU.image f:Finset β):Set β) by
    rw[Tu,W8,RD],Xt,
    VF]
 rw[Y4, ← YA]at h1
 rw[e2,mul_comm]
 exact h1
lemma J7 {q:ℕ} (hq:2≤q) (z:ℕ):
    q^(z*(z - 1))≤∏ i:Fin z,(q^z - q^(i:ℕ)):=by
 have key:∀ A B X:ℕ,2*X≤A→B≤X→X≤A - B:=by
  intro A B X h1 h2
  omega
 have hi:∀ i∈(ZU:Finset (Fin z)),q^(z - 1)≤q^z - q^(i:ℕ):=by
  intro i _
  have h1:q^(i:ℕ)≤q^(z - 1):=Zk (by omega) (by omega)
  have h2:q^z=q*q^(z - 1):=by
   rw[← VG]
   congr 1
   have:=i.2
   omega
  have h3:2*q^(z - 1)≤q*q^(z - 1):=Za _ hq
  exact key _ _ _ (h2▸h3) h1
 calc q ^(z*(z - 1))=∏ _i:Fin z,q^(z - 1):=by
       rw[Finset.prod_const,Y4,Zz, ← X5,mul_comm]
   _≤∏ i:Fin z,(q^z - q^(i:ℕ)):=Ud hi
lemma LH [Fintype F] [Finite V] (Z:Submodule F V):
    ZB F^(finrank F Z*(finrank F Z - 1))≤
      ZB {x:Fin (finrank F Z)→Z//LinearIndependent F x}:=by
 rw [card_linearIndependent (K:=F) (V:=Z) (k:= finrank F Z) YD,
   YA]
 exact J7 (Fintype.one_lt_card) _
lemma Jm [Fintype F] [Finite V] [FiniteDimensional F V]
    (B:V→ₗ[F] V→ₗ[F] W) (hB:∀ x,B x x =0) {s:ℕ} (u:Fin s→V)
    (Z:Submodule F V):
    Nat.card F^(finrank F Z*(finrank F Z - 1))≤
      ZB (ZF (fun x:{x:Fin (finrank F Z)→Z//LinearIndependent F x}=>
        zj B u (fun l=> (x.1 l:V))))*
        ZB F^(finrank F Z*finrank F (gz B (ZQ F (ZF u)))):=by
  set K:=gz B (ZQ F (ZF u))
  set f:= fun x:{x:Fin (finrank F Z)→Z//LinearIndependent F x}=>
    zj B u (fun l=> (x.1 l:V))
  have pC : ∀ a,ZB {a'//f a'= f a}≤ZB F^(finrank F Z*finrank F K):=by
   intro a
   let g:{a'//f a'= f a}→(Fin (finrank F Z)→K):= fun y l=>
     ⟨(y.1.1 l:V) - (a.1 l:V),yZ B hB u y.2 l⟩
   have hg:Z8 g:=by
    intro y y' hyy
    apply Zu
    apply Zu
    funext l
    have h1:= congrArg XJ (congrFun hyy l)
    have h2:(y.1.1 l:V)=(y'.1.1 l:V):=sub_left_injective h1
    exact Zu h2
   calc Nat.card {a'//f a'= f a}≤ZB (Fin (finrank F Z)→K):=
         Yy g hg
     _ = ZB F^(finrank F Z*finrank F K):=by
         rw [Xl,Xk,W0 (K:=F) (V:=K),
           ← X5,mul_comm]
  exact (LH Z).trans (y6 f _ pC)
end Prop131
section Rem64
variable {F X Y:Type*} [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
end Rem64
section Cor141
end Cor141
end Mult3
namespace Mult3
open Module
section GroupCore
variable {p:ℕ} [Fact p.Prime] {G:Type u} [Group G]
def cT {k:ℕ} (u:Fin k→G):Submodule (ZMod p) (Additive (VQ p G)):=
  ZQ (ZMod p) (ZF (fun i=>ZC (dH p G (u i))))
lemma Bd (x:Additive (VQ p G)):cP (p:=p) (G:=G) x x =0:=EH x
lemma j8 [Finite G] (hG:IsPGroup p G) {k:ℕ} (u:Fin k→G)
    (dG:lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
      lcs G 2) (hk:k=bD G):
    gz (cP (p:=p) (G:=G)) (cT (p:=p) u)⊓cT (p:=p) u=⊥∧
      finrank (ZMod p) (cT (p:=p) u)=k:=by
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
 have dV:Alt2.jg (cP (p:=p) (G:=G)) (cT (p:=p) u):=
   Alt2.x7 (p:=p) u dG
 have acn:∀ U':Submodule (ZMod p) (Additive (VQ p G)),
     Alt2.jg (cP (p:=p) (G:=G)) U'→k≤finrank (ZMod p) U':=by
  intro U' MZ
  rw[hk, ← Alt2.wM (p:=p) hG]
  exact WK ⟨U',rfl,MZ⟩
 have O4:finrank (ZMod p) (cT (p:=p) u)≤k:=by
  have h2:finrank (ZMod p) (cT (p:=p) u)≤Zq (Fin k):=
    finrank_range_le_card (fun i=>ZC (dH p G (u i)))
  rw[Zz]at h2
  exact h2
 have heq:finrank (ZMod p) (cT (p:=p) u)=k:=le_antisymm O4 (acn _ dV)
 refine ⟨B3 _ Bd _ dV ?_,heq⟩
 intro U' MZ
 rw[heq]
 exact acn U' MZ
lemma vq [Finite G] (hG:IsPGroup p G) {k:ℕ} (u:Fin k→G)
    (dG:lcs G 1≤⁅ZA (ZF u),ZA (ZF u)⁆⊔
      lcs G 2) (hk:k=bD G):
    finrank (ZMod p) (gz (cP (p:=p) (G:=G)) (cT (p:=p) u))+bD G≤
      ZV G:=by
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
 obtain ⟨rL,F5⟩:=j8 hG u dG hk
 have h:=V5
   (gz (cP (p:=p) (G:=G)) (cT (p:=p) u)) (cT (p:=p) u)
 rw[rL,finrank_bot,F5]at h
 have h2:=RI
   (gz (cP (p:=p) (G:=G)) (cT (p:=p) u)⊔cT (p:=p) u)
 rw[Lc hG]at h2
 omega
end GroupCore
section Mult3Group
variable {m r1 r2 s lam m2 m3 r3 z k:ℕ}
end Mult3Group
section Summand
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G]
abbrev omQ (p:ℕ) (G:Type u) [Group G]:Subgroup (Abelianization G):=
  (powMonoidHom p:Abelianization G→*Abelianization G).ker
lemma ab0 (x:omQ p G):(x:Abelianization G)^p=1:=Zm.mp x.2
lemma aam (x:Additive (omQ p G)):p•x =0:=by
 show ZC (ZW x^p)=ZC 1
 have h:ZW x^p=1:=Zu (by
  rw[Vg,S8]
  exact ab0 _)
 rw[h]
instance acY:Module (ZMod p) (Additive (omQ p G)):=
  letI:NeZero p:=⟨hp.out.ne_zero⟩
  VK aam
def C9 (K:Subgroup G):Submodule (ZMod p) (Additive (VQ p G)) where
  carrier :={x | ∃ b∈K,ZC (dH p G b)=x}
  add_mem':=by
    rintro _ _ ⟨b1,h1,rfl⟩ ⟨b2,h2,rfl⟩
    exact ⟨b1*b2,K.mul_mem h1 h2,by rw[YP,ofMul_mul]⟩
  zero_mem':=⟨1,K.one_mem,by rw[X9,ofMul_one]⟩
  smul_mem':=by
    rintro c _ ⟨b,hb,rfl⟩
    refine ⟨b^c.val,K.pow_mem hb _,?_⟩
    rw[jr,map_pow,ofMul_pow]
lemma Ao {K:Subgroup G} {x:Additive (VQ p G)}:
    x∈C9 (p:=p) K↔∃ b∈K,ZC (dH p G b)=x:=U8
end Summand
section Mult3Cover
variable {m r1 r2 s lam m2 m3 r3 z k:ℕ}
end Mult3Cover
end Mult3
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section NSer
variable {G:Type u} [Group G]
structure aeI (F:ℕ→ Subgroup G):Prop where
  normal:∀ i,(F i).Normal
  succ_le:∀ i,F (i+1)≤F i
  aeH:∀ a b,⁅F a,F b⁆≤F (a+b+1)
variable {F:ℕ→ Subgroup G}
lemma Nu (g:G):g∈lcs G 0:=by
 rw[lcs_zero]
 exact ZO g
abbrev grK (F:ℕ→ Subgroup G) (i:ℕ):Subgroup (F i):=(F (i+1)).subgroupOf (F i)
abbrev GrL (F:ℕ→ Subgroup G) (i:ℕ):Type u:=Additive (jD 0 (F i) (grK F i))
instance adn [Finite G] (F:ℕ→ Subgroup G) (i:ℕ):Finite (GrL F i):=by
 have:Finite (jD 0 (F i) (grK F i)):=
   Zy _ (jZ (p:=0) (grK F i))
 exact inferInstanceAs (Finite (Additive (jD 0 (F i) (grK F i))))
section Remark26
variable {p:ℕ}
end Remark26
lemma aZ.q6 {p c:ℕ} {r :Fin c→ℕ}
    {a:aR c r→ℕ} {g:aR c r→G} (S:aZ p a g) (i:Fin c)
    (j v:Fin (r i)) (h:j.val≤v.val):(S.c_ ⟨i,j⟩ ⟨i,v⟩).val=0:=
  S.CH.supp ⟨i,j⟩ ⟨i,v⟩ (UO _) (fun h'=> (not_lt.mpr h) h'.2)
lemma r4 {i n:ℕ} (X:Fin n→G) (hX:∀ v,X v∈lcs G i)
    (dV:ZA (ZF fun v=>
      (Z6 (⟨X v,hX v⟩:lcs G i):e7 G i))=⊤):
    lcs G i≤ZA (ZF X)⊔lcs G (i+1):=by
  intro x hx
  have Nm:(ZA (ZF fun v=> (⟨X v,hX v⟩:lcs G i))).map
      (ZG ((lcs G (i+1)).subgroupOf (lcs G i)))=⊤:=by
    rw[XT, ← WJ]
    exact dV
  have cI:ZG ((lcs G (i+1)).subgroupOf (lcs G i)) (⟨x,hx⟩:lcs G i)∈
      (ZA (ZF fun v=> (⟨X v,hX v⟩:lcs G i))).map
        (ZG ((lcs G (i+1)).subgroupOf (lcs G i))):=by
    rw[Nm]
    exact ZO _
  obtain ⟨y,hy,Qg⟩:=Zj.mp cI
  rw [YY,YY,WX,
    ZT]at Qg
  have cO:(ZA (ZF fun v=> (⟨X v,hX v⟩:lcs G i))).map
      (lcs G i).subtype≤ZA (ZF X):=by
    rw[XT,ZE]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    exact ZD ⟨v,rfl⟩
  have hyc:(y:G)∈ZA (ZF X):= cO ⟨y,hy,rfl⟩
  have e:x =(y:G)*((y⁻¹*⟨x,hx⟩:lcs G i):G):=by simp
  rw[e]
  exact UE hyc Qg
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
lemma aaj {β1:L1→*L1→*L2} {β2:L2→*L1→*L3} (hJ:f4 β1 β2)
    (C:Subgroup L1) (ac5:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}=⊤)
    (Bc:ZA {w | ∃ z x,β2 z x =w}=⊤):
    ZA {w | ∃ z,∃ u∈C,β2 z u=w}=⊤:=by
  set K:=ZA {w | ∃ z,∃ u∈C,β2 z u=w} with hK
  have hx:∀ x:L1,∀ z:L2,β2 z x∈K:=by
   intro x
   have cO:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}≤K.comap (β2.flip x):=by
     rw[ZE]
     rintro _ ⟨u,hu,v,hv,rfl⟩
     rw[Xb,Zp,YB]
     have e:=hJ u v x
     have hA:β2 (β1 v x) u∈K:=ZD ⟨_,u,hu,rfl⟩
     have hB:β2 (β1 x u) v∈K:=ZD ⟨_,v,hv,rfl⟩
     have e':β2 (β1 u v) x =(β2 (β1 v x) u*β2 (β1 x u) v)⁻¹:=by
      rw[UQ]at e
      exact Uv e
     rw[e']
     exact K.inv_mem (K.mul_mem hA hB)
   rw[ac5]at cO
   intro z
   have h:= cO (ZO z)
   rwa[Zp,YB]at h
  rw[Yo, ← Bc,ZE]
  rintro _ ⟨z,x,rfl⟩
  exact hx x z
lemma nZ (G:Type u) [Group G]:Zn (jK G):=
  YI ((lcs G 3).subgroupOf (lcs G 2))
lemma Jy (G:Type u) [Group G]:
    ZA {w | ∃ z x,FO G z x =w}=⊤:=by
  set K:=ZA {w | ∃ z x,FO G z x =w} with hK
  have cO:⁅lcs G 1,(⊤:Subgroup G)⁆≤(K.comap (jK G)).map (lcs G 2).subtype:=by
   rw[Subgroup.commutator_def,ZE]
   rintro _ ⟨w,hw,y, -,rfl⟩
   refine Zj.2 ⟨uu ⟨w,hw⟩ y,?_,rfl⟩
   rw[Zp, ← qI]
   exact ZD ⟨_,_,rfl⟩
  rw[Yo]
  intro q _
  obtain ⟨w,rfl⟩:=nZ G q
  obtain ⟨w',EU,hww⟩:=Zj.1 (cO w.2)
  have:w'=w:=Zu hww
  rw[← this]
  exact EU
end LfCore
section LfTransport
lemma EZ {G:Type u} [Group G] {L1:Type*} [CommGroup L1]
    (e1:Abelianization G≃*L1) {r s:ℕ} (X:Fin r→G) {a:G}
    (ha:a∈ZA (X '' {j | (j:ℕ)<s})):
    e1 (ZJ a)∈
      ZA ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}):=by
  have cO:ZA (X '' {j | (j:ℕ)<s})≤
      (ZA ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s})).comap
        (e1.toMonoidHom.comp ZJ):=by
    rw[ZE]
    rintro _ ⟨j,hj,rfl⟩
    rw[Xb,Zp]
    exact ZD ⟨j,hj,rfl⟩
  exact Zp.mp (cO ha)
lemma DA {G:Type u} [Group G] {L1 L2:Type*} [CommGroup L1] [CommGroup L2]
    (e1:Abelianization G≃*L1) (e2:gY G≃*L2) {r s:ℕ} (X:Fin r→G)
    (dG:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2):
    Subgroup.closure {w | ∃ u∈ZA
        ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}),
        qz e1 e2 u u'=w}=⊤:=by
  set K :=ZA {w | ∃ u∈ZA
        ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}),
        qz e1 e2 u u'=w} with hK
  have hM :lcs G 1≤(K.comap (e2.toMonoidHom.comp (f9 G))).map (lcs G 1).subtype:=by
   refine dG.trans (sup_le ?_ ?_)
   · rw [Z7]
     intro a ha b hb
     refine Zj.2 ⟨cw a b,?_,rfl⟩
     rw[Zp,Y0]
     have e:e2.toMonoidHom (f9 G (cw a b))=
         qz e1 e2 (e1 (ZJ a)) (e1 (ZJ b)):=
       (DE e1 e2 a b).symm
     rw[e]
     exact ZD ⟨_,EZ e1 X ha,_,EZ e1 X hb,rfl⟩
   · intro x hx
     have Lg:x∈lcs G 1:=bC (by norm_num) hx
     refine Zj.2 ⟨⟨x,Lg⟩,?_,rfl⟩
     rw[Zp,Y0]
     have h1:f9 G ⟨x,Lg⟩=1:=(jT _).2 hx
     rw[h1,X9]
     exact K.one_mem
  rw[Yo]
  intro q _
  obtain ⟨w,hw⟩:=nI (e2.symm q)
  obtain ⟨w',EU,hww⟩:=Zj.1 (hM w.2)
  have ad8:w'=w:=Zu hww
  rw[ad8,Zp,Y0,hw]at EU
  simpa using EU
lemma Nl {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:gY G≃*L2) (e3:oI G≃*L3):
    ZA {w | ∃ z x,tQ e1 e2 e3 z x =w}=⊤:=by
  have cO:ZA {w | ∃ z x,FO G z x =w}≤
      (ZA {w | ∃ z x,tQ e1 e2 e3 z x =w}).comap e3.toMonoidHom:=by
    rw[ZE]
    rintro _ ⟨z,x,rfl⟩
    rw[Xb,Zp]
    refine ZD ⟨e2 z,e1 x,?_⟩
    simp[qd]
  rw[Jy G]at cO
  rw[Yo]
  intro q _
  have h:= cO (ZO (e3.symm q))
  rw[Zp]at h
  simpa using h
lemma Ni {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:gY G≃*L2) (e3:oI G≃*L3)
    {r s:ℕ} (X:Fin r→G)
    (dG:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2):
    Subgroup.closure {w | ∃ z,∃ u∈ZA
        ((fun j=>e1 (ZJ (X j))) '' {j | (j:ℕ)<s}),
      tQ e1 e2 e3 z u=w}=⊤:=
  aaj (Iz e1 e2 e3) _ (DA e1 e2 X dG) (Nl e1 e2 e3)
def DJ {L1 L2:Type*} [CommGroup L1] [CommGroup L2] (L3:Type*) [CommGroup L3] {r :ℕ}
    (s:ℕ) (g:Fin r→ L1) (D:Finset (Fin r×Fin r)) (v:Fin r×Fin r→ L2):
    Set ((L1→*L1→*L2)×(L2→*L1→*L3)):=
  {β | g4 β.1∧
    ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
    f4 β.1 β.2∧
    ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
    ∀ q∈D,β.1 (g q.1) (g q.2)=v q}
lemma aac {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:gY G≃*L2) (e3:oI G≃*L3)
    {r s:ℕ} (X:Fin r→G) (g:Fin r→ L1) (hg:∀ j,e1 (ZJ (X j))=g j)
    (dG:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2)
    (D:Finset (Fin r×Fin r)) (v:Fin r×Fin r→ L2)
    (hv:∀ q∈D,e2 (f9 G (cw (X q.1) (X q.2)))=v q):
    (qz e1 e2,tQ e1 e2 e3)∈DJ L3 s g D v:=by
  have hgX:g= fun j=>e1 (ZJ (X j)):= funext fun j=> (hg j).symm
  subst hgX
  rw[DJ,UA]
  refine ⟨aaX e1 e2,DA e1 e2 X dG,Iz e1 e2 e3,
    Ni e1 e2 e3 X dG,fun q hq=>?_⟩
  show qz e1 e2 (e1 (ZJ (X q.1))) (e1 (ZJ (X q.2)))=v q
  rw[DE]
  exact hv q hq
end LfTransport
section LfPresent
def k7 {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):Fin n→ℤ:=
  fun i=>if i=j then (p:ℤ)^a j else if i<j then -(b j i:ℤ) else 0
def iz {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):AddSubgroup (Fin n→ℤ):=
  AddSubgroup.closure (ZF (k7 p a b))
lemma QV {n p:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):
    k7 p a b j j=(p:ℤ)^a j:=by
 unfold k7
 rw[if_pos rfl]
lemma Oo {n p:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) {i j:Fin n} (h:j< i):
    k7 p a b j i=0:=by
 unfold k7
 rw[if_neg h.ne',if_neg (not_lt.mpr h.le)]
lemma aaC {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (x :Fin n→ℤ):∃ w:Fin n→ℤ,(∀ j,0≤w j∧w j< (p:ℤ)^a j)∧
      x - w∈iz p a b:=by
 have key : ∀ k:ℕ,∃ w:Fin n→ℤ,
     (∀ j:Fin n,n≤(j:ℕ)+k→0≤w j∧w j< (p:ℤ)^a j)∧
       x - w∈iz p a b:=by
  intro k
  induction k with
  | zero=>
    refine ⟨x,fun j hj=>absurd hj (by have:=j.isLt; omega),?_⟩
    rw[sub_self]
    exact (iz p a b).zero_mem
  | succ k ih=>
    obtain ⟨w,hw,hx⟩:=ih
    by_cases hk:k<n
    · obtain ⟨jk,adt⟩:∃ jk:Fin n,(jk:ℕ)=n - 1 - k:=⟨⟨n - 1 - k,by omega⟩,rfl⟩
      have abS:(0:ℤ)< (p:ℤ)^a jk:=XD (by exact_mod_cast hp) _
      obtain ⟨q,hq⟩:∃ q:ℤ,q=w jk/(p:ℤ)^a jk:=⟨_,rfl⟩
      refine ⟨w - q•k7 p a b jk,fun j hj=>?_,?_⟩
      · by_cases Er :j=jk
        · rw[Er]
          have e:(w - q•k7 p a b jk) jk=w jk % (p:ℤ)^a jk:=by
           rw[SH,Te,QV,smul_eq_mul,hq]
           have h:=Int.mul_ediv_add_emod (w jk) ((p:ℤ)^a jk)
           linear_combination -h
          rw[e]
          exact ⟨OZ _ abS.ne',P8 _ abS⟩
        · have d8:(j:ℕ)≠n - 1 - k:= fun h=>Er (YL (h.trans adt.symm))
          have f5:jk<j:=XO.mpr (by omega)
          have h0:(w - q•k7 p a b jk) j=w j:=by
           rw[SH,Te,Oo a b f5,smul_zero,sub_zero]
          rw[h0]
          exact hw j (by omega)
      · have e:x - (w - q•k7 p a b jk)=(x - w)+q•k7 p a b jk:=by abel
        rw[e]
        have cI:k7 p a b jk∈iz p a b:=AddSubgroup.subset_closure ⟨jk,rfl⟩
        exact (iz p a b).add_mem hx (zsmul_mem cI q)
    · exact ⟨w,fun j hj=>hw j (by omega),hx⟩
 obtain ⟨w,hw,hx⟩:=key n
 exact ⟨w,fun j=>hw j (by omega),hx⟩
lemma E5 {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    Zn (fun e:(j:Fin n)→Fin (p^a j)=>
      (ZP (fun j=> ((e j:ℕ):ℤ)):(Fin n→ℤ)⧸iz p a b)):=by
    intro q
    obtain ⟨x,rfl⟩:=UG q
    obtain ⟨w,hw,hxw⟩:=aaC hp a b x
    have aae:∀ j,((w j).toNat:ℤ)=w j:= fun j=>Int.toNat_of_nonneg (hw j).1
    have f5:∀ j,(w j).toNat<p^a j:=by
     intro j
     have h1:((w j).toNat:ℤ)< ((p^a j:ℕ):ℤ):=by
      rw[aae j,Nat.cast_pow]
      exact (hw j).2
     exact_mod_cast h1
    refine ⟨fun j=> ⟨(w j).toNat,f5 j⟩,?_⟩
    have aa2:(fun j=> (((w j).toNat:ℕ):ℤ))=w:= funext aae
    show ZP (fun j=> (((w j).toNat:ℕ):ℤ))=ZP x
    rw[aa2,Od]
    have e: -w+x =x - w:=by abel
    rw[e]
    exact hxw
lemma m6 {n p:ℕ} (a:Fin n→ℕ):
    ZB ((j:Fin n)→Fin (p^a j))=p^∑ j,a j:=by
 rw[YA,P6]
 simp only[Zz]
 rw[XB]
lemma nO {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    Finite ((Fin n→ℤ)⧸iz p a b)∧
      ZB ((Fin n→ℤ)⧸iz p a b)≤p^∑ j,a j:=by
 have j6:=E5 hp a b
 refine ⟨Zy _ j6,?_⟩
 rw[← m6 (p:=p) a]
 exact YO _ j6
variable {L:Type*} [CommGroup L]
def jS {n:ℕ} (y:Fin n→ L):(Fin n→ℤ)→+Additive L where
  toFun x:=∑ j,x j•ZC (y j)
  map_zero':=by simp
  map_add' x x':=by simp only[Vc,add_smul,Xy]
lemma y9 {n:ℕ} (y:Fin n→ L) (x:Fin n→ℤ):
    jS y x =∑ j,x j•ZC (y j):=rfl
lemma qo {n:ℕ} (y:Fin n→ L) (j:Fin n):
    jS y (Yz j 1)=ZC (y j):=by
 rw[y9,Ue j]
 · simp
 · intro i _ hi
   simp[hi]
 · intro h
   exact absurd (Zb j) h
lemma aaH {n p:ℕ} (y:Fin n→ L) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):
    jS y (k7 p a b j)=((p:ℤ)^a j)•ZC (y j) -
      ∑ i∈ZU.filter (fun i=>i<j),(b j i:ℤ)•ZC (y i):=by
  have hpt:∀ i,k7 p a b j i•ZC (y i)=
      (if i=j then ((p:ℤ)^a i)•ZC (y i) else 0) -
        (if i<j then (b j i:ℤ)•ZC (y i) else 0):=by
    intro i
    unfold k7
    by_cases h1:i=j
    · subst h1
      simp
    · by_cases h2:i<j
      · simp[h1,h2]
      · simp[h1,h2]
  rw [y9,Zw rfl (fun i _=>hpt i),RZ,
    Finset.sum_ite_eq',if_pos (Zb j),Xd]
lemma Ej {n p:ℕ} (y:Fin n→ L) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (j :Fin n) (m_:(p^a j)•ZC (y j)=
      ∑ i∈ZU.filter (fun i=>i<j),b j i•ZC (y i)):
    jS y (k7 p a b j)=0:=by
  rw[aaH, ← Nat.cast_pow,natCast_zsmul]
  simp only[natCast_zsmul]
  rw[m_,sub_self]
lemma Ls [Finite L] {n p:ℕ} (hp:0<p) (a:Fin n→ℕ)
    (b:Fin n→Fin n→ℕ) (y:Fin n→ L) (hy:ZA (ZF y)=⊤)
    (hL:ZB L=p^∑ j,a j) (m_:∀ j,jS y (k7 p a b j)=0):
    ∃ φ :((Fin n→ℤ)⧸iz p a b)≃+Additive L,
      (∀ j,φ (ZP (Yz j 1))=ZC (y j))∧
        ∀ x,φ (ZP x)=jS y x:=by
 have cO:iz p a b≤(jS y).ker :=by
  rw[iz,AddSubgroup.closure_le]
  rintro _ ⟨j,rfl⟩
  exact AddMonoidHom.mem_ker.2 (m_ j)
 let φ:= Oe (iz p a b) (jS y) cO
 have hs :∀ z:L,∃ x,jS y x =ZC z:=by
  let T :Subgroup L:=
    { carrier :={z | ∃ x,jS y x =ZC z}
      mul_mem':=by
        rintro z z' ⟨x,hx⟩ ⟨x',oQ⟩
        exact ⟨x+x',by rw[map_add,hx,oQ,ofMul_mul]⟩
      one_mem':=⟨0,by rw[map_zero,ofMul_one]⟩
      inv_mem':=by
        rintro z ⟨x,hx⟩
        exact ⟨-x,by rw[map_neg,hx,ofMul_inv]⟩ }
  have hT:ZA (ZF y)≤T:=by
   rw[ZE]
   rintro _ ⟨j,rfl⟩
   exact ⟨Yz j 1,qo y j⟩
  rw[hy]at hT
  intro z
  obtain ⟨x,hx⟩:=hT (ZO z)
  exact ⟨x,hx⟩
 have j6:Zn φ:=by
  intro z
  obtain ⟨x,hx⟩:=hs (ZW z)
  exact ⟨ZP x,hx⟩
 obtain ⟨A6,dS⟩:=nO hp a b
 have hLA:ZB L=ZB (Additive L):=YJ ZC
 have aaS:Ur φ:=by
  refine (TB φ).2 ⟨j6,le_antisymm ?_ ?_⟩
  · rw[← hLA,hL]
    exact dS
  · exact YO φ j6
 refine ⟨AddEquiv.ofBijective φ aaS,fun j=>?_,fun x =>rfl⟩
 have h1:φ (ZP (Yz j 1))=jS y (Yz j 1):=rfl
 show φ (ZP (Yz j 1))=ZC (y j)
 rw[h1,qo]
lemma Jg {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (φ:((Fin n→ℤ)⧸iz p a b)≃+Additive L) (hL:ZB L=p^∑ j,a j)
    (e e':Fin n→ℕ) (he:∀ j,e j<p^a j) (he':∀ j,e' j<p^a j)
    (h :(ZP (fun j=> (e j:ℤ)):(Fin n→ℤ)⧸iz p a b)=
      ZP (fun j=> (e' j:ℤ))):e=e':=by
  have dS:ZB ((j:Fin n)→Fin (p^a j))=
      ZB ((Fin n→ℤ)⧸iz p a b):=by
   rw[m6, ← hL]
   exact (YJ (ZC:L≃ Additive L)).trans
     (YJ φ.toEquiv).symm
  have aaS:=(TB _).2 ⟨E5 hp a b,dS⟩
  have key:(fun j=> (⟨e j,he j⟩:Fin (p^a j)))= fun j=> ⟨e' j,he' j⟩:=aaS.1 h
  funext j
  exact congrArg Ty (congrFun key j)
end LfPresent
section LfSimsLift
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G}
lemma aZ.tP (S:aZ p a g) (i:Fin c) {x:G}
    (hx:x∈lcs G i):x∈z8 g i (r i):=by
 have h:=r4 (fun v:Fin (r i)=>g ⟨i,v⟩)
   (fun v=>S.mem ⟨i,v⟩) (S.gen i) hx
 have o4:ZA (ZF fun v:Fin (r i)=>g ⟨i,v⟩)≤
     ZA {x | ∃ v:Fin (r i),v.val< r i∧g ⟨i,v⟩=x}:=by
   apply ZS
   rintro _ ⟨v,rfl⟩
   exact ⟨v,v.isLt,rfl⟩
 exact sup_le_sup_right o4 (lcs G ((i:ℕ)+1)) h
lemma aZ.nS (S:aZ p a g) (i:Fin c) {x:G}
    (hx:x∈lcs G i):
    x = cW g (fun h=> (S.nf.coord x h).val) i*
      (ZR fun u:Fin c=>
        if i<u then cW g (fun h=> (S.nf.coord x h).val) u else 1).prod:=by
  obtain ⟨L9,o5⟩:=S.nf.q5 i (r i) x (S.tP i hx)
  refine o5.symm.trans
    (j7 c (cW g fun h=> (S.nf.coord x h).val) i fun u hu=>?_)
  unfold cW
  refine Xv fun z hz=>?_
  rw[XC]at hz
  obtain ⟨v,rfl⟩:=hz
  have h0:(S.nf.coord x ⟨u,v⟩).val=0:=L9 ⟨u,v⟩ (Y7 hu)
  show g ⟨u,v⟩^(S.nf.coord x ⟨u,v⟩).val=1
  rw[h0,Y6]
def wO (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:aR c r)→Fin (p^a h)):(h:aR c r)→Fin (p^a h)
  | ⟨i',v⟩=>if hh:i'=i then ⟨e (hh▸v),by subst hh; exact he v⟩
      else if i< i' then dc ⟨i',v⟩ else ⟨0,XD hp _⟩
lemma NR (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:aR c r)→Fin (p^a h)) (v:Fin (r i)):
    (wO hp i e he dc ⟨i,v⟩).val=e v:=by
 rw[wO,dif_pos rfl]
 try rfl
lemma aaK (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:aR c r)→Fin (p^a h)) {u:Fin c} (hu:u< i) (v:Fin (r u)):
    (wO hp i e he dc ⟨u,v⟩).val=0:=by
 rw[wO,dif_neg hu.ne,if_neg (not_lt.mpr hu.le)]
lemma aao (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:aR c r)→Fin (p^a h)) {u:Fin c} (hu:i<u) (v:Fin (r u)):
    wO hp i e he dc ⟨u,v⟩=dc ⟨u,v⟩:=by
 rw[wO,dif_neg hu.ne',if_pos hu]
lemma aZ.zP (S:aZ p a g) (hp:0<p) (i:Fin c)
    (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩) {d:G} (hd:d∈lcs G ((i:ℕ)+1))
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) (v:Fin (r i)):
    (S.nf.coord ((ZR fun w=>g ⟨i,w⟩^e w).prod*d) ⟨i,v⟩).val=e v:=by
  have hdi:d∈lcs G i:=bC (XV _) hd
  have acK:ju g (fun h=> (S.nf.coord d h).val)=d:=
    (S.nf.q5 i (r i) d (S.tP i hdi)).2
  have hdc:∀ h:aR c r,h.1≤ i→(S.nf.coord d h).val=0:=by
   rcases hlast with h1 | rL
   · intro h hh
     have aa3:=(S.nf.q5 ⟨(i:ℕ)+1,h1⟩ (r ⟨(i:ℕ)+1,h1⟩) d
       (S.tP ⟨(i:ℕ)+1,h1⟩ hd)).1
     exact aa3 h (Y7 (XO.mpr (Ws (TZ.mp hh))))
   · have hd1:d=1:=by
       rw[rL]at hd
       exact WB.mp hd
     intro h _
     have hZ:ju g (fun h=> ((⟨0,XD hp _⟩:Fin (p^a h)):ℕ))=1:=by
       unfold ju
       refine Xv fun z hz=>?_
       rw[XC]at hz
       obtain ⟨u,rfl⟩:=hz
       unfold cW
       refine Xv fun z hz=>?_
       rw[XC]at hz
       obtain ⟨w,rfl⟩:=hz
       exact Y6 _
     have hu:S.nf.coord (ju g (fun h=> ((⟨0,XD hp _⟩:Fin (p^a h)):ℕ)))=
         fun h=> ⟨0,XD hp _⟩:=S.nf.uniq _
     rw[hZ, ← hd1]at hu
     rw[hu]
  obtain ⟨E,hE⟩:∃ E,E=wO hp i e he (S.nf.coord d):=⟨_,rfl⟩
  have hEi:∀ w,(E ⟨i,w⟩).val=e w:=by
   intro w
   rw[hE]
   exact NR hp i e he _ w
  have aep:∀ u,u< i→∀ w,(E ⟨u,w⟩).val=0:=by
   intro u hu w
   rw[hE]
   exact aaK hp i e he _ hu w
  have ad_:∀ u,i<u→∀ w,E ⟨u,w⟩=S.nf.coord d ⟨u,w⟩:=by
   intro u hu w
   rw[hE]
   exact aao hp i e he _ hu w
  have hs:=j7 c (cW g fun h=> (E h).val) i fun u hu=>by
    unfold cW
    refine Xv fun z hz=>?_
    rw[XC]at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨u,w⟩^(E ⟨u,w⟩).val=1
    rw[aep u hu w,Y6]
  have hd':=j7 c (cW g fun h=> (S.nf.coord d h).val) i fun u hu=>by
    unfold cW
    refine Xv fun z hz=>?_
    rw[XC]at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨u,w⟩^(S.nf.coord d ⟨u,w⟩).val=1
    rw[hdc ⟨u,w⟩ hu.le,Y6]
  have s8:cW g (fun h=> (S.nf.coord d h).val) i=1:=by
    unfold cW
    refine Xv fun z hz=>?_
    rw[XC]at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨i,w⟩^(S.nf.coord d ⟨i,w⟩).val=1
    rw[hdc ⟨i,w⟩ YD,Y6]
  have hbi:cW g (fun h=> (E h).val) i=(ZR fun w=>g ⟨i,w⟩^e w).prod:=by
    simp only[cW,hEi]
  have f6:(ZR fun u:Fin c=>
        if i<u then cW g (fun h=> (E h).val) u else 1).prod=
      (ZR fun u:Fin c=>
        if i<u then cW g (fun h=> (S.nf.coord d h).val) u else 1).prod:=by
    congr 2
    funext u
    by_cases hu:i<u
    · rw[if_pos hu,if_pos hu]
      simp only[cW,ad_ u hu]
    · rw[if_neg hu,if_neg hu]
  have hdd:d=(ZR fun u:Fin c=>
        if i<u then cW g (fun h=> (S.nf.coord d h).val) u else 1).prod:=by
    have h2:=acK.symm.trans hd'
    rwa[s8,Wn]at h2
  have adk :ju g (fun h=> (E h).val)=(ZR fun w=>g ⟨i,w⟩^e w).prod*d:=by
    calc ju g (fun h=> (E h).val)
        = cW g (fun h=> (E h).val) i*(ZR fun u:Fin c=>
          if i<u then cW g (fun h=> (E h).val) u else 1).prod:=hs
      _=_:=by rw[hbi,f6, ← hdd]
  have hu:=S.nf.uniq E
  rw[adk]at hu
  rw[hu]
  exact hEi v
lemma aZ.Bz (S:aZ p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥):
    ZB (e7 G i)=p^∑ v:Fin (r i),a ⟨i,v⟩:=by
 have hB:∀ e:(v:Fin (r i))→Fin (p^a ⟨i,v⟩),
     (ZR fun w=>g ⟨i,w⟩^(e w).val).prod∈lcs G i:= fun e=>
   Wb _ fun z hz=>by
     rw[XC]at hz
     obtain ⟨w,rfl⟩:=hz
     exact Xm _ (S.mem ⟨i,w⟩) _
 let β:((v:Fin (r i))→Fin (p^a ⟨i,v⟩))→e7 G i:= fun e=>
   Z6 (⟨(ZR fun w=>g ⟨i,w⟩^(e w).val).prod,hB e⟩:lcs G i)
 have eW :Z8 β:=by
  intro e e' hee
  have aeh:(Z6 (⟨(ZR fun w=>g ⟨i,w⟩^(e w).val).prod,hB e⟩:
      lcs G i):e7 G i)=
      Z6 (⟨(ZR fun w=>g ⟨i,w⟩^(e' w).val).prod,hB e'⟩:
        lcs G i):=hee
  have h1:=ZT.mp (WX.mp aeh)
  have hd:((ZR fun w=>g ⟨i,w⟩^(e w).val).prod)⁻¹*
      (ZR fun w=>g ⟨i,w⟩^(e' w).val).prod∈lcs G ((i:ℕ)+1):=h1
  funext v
  apply YL
  have lT:=S.zP hp i (fun w=> (e w).val) (fun w=> (e w).isLt) hd hlast v
  have uL:=S.zP hp i (fun w=> (e' w).val) (fun w=> (e' w).isLt)
    (Yl _) hlast v
  beta_reduce at lT uL
  rw[UH]at uL
  rw[mul_inv_cancel_left]at lT
  exact lT.symm.trans uL
 have j6 : Zn β:=by
  intro q
  obtain ⟨⟨x,hx⟩,rfl⟩:=Z3 q
  refine ⟨fun w=>S.nf.coord x ⟨i,w⟩,?_⟩
  show (Z6 _:e7 G i)=Z6 _
  rw[WX,ZT]
  have hl:=S.nS i hx
  have f6:=lX g S.mem (fun h=> (S.nf.coord x h).val) i
  show (cW g (fun h=> (S.nf.coord x h).val) i)⁻¹*x∈lcs G ((i:ℕ)+1)
  have e1 : (cW g (fun h=> (S.nf.coord x h).val) i)⁻¹*x =
      (ZR fun u:Fin c=>if i<u then
        cW g (fun h=> (S.nf.coord x h).val) u else 1).prod:=by
    calc _ = (cW g (fun h=> (S.nf.coord x h).val) i)⁻¹*
          (cW g (fun h=> (S.nf.coord x h).val) i*(ZR fun u:Fin c=>
            if i<u then cW g (fun h=> (S.nf.coord x h).val) u else 1).prod):=by
          rw[← hl]
      _=_:=inv_mul_cancel_left _ _
  rw[e1]
  exact f6
 rw [← YJ (Pq β ⟨eW,j6⟩),YA,
   P6]
 simp only[Zz]
 rw[XB]
lemma Gt {K:Subgroup G} {M:Type*} [Monoid M] (π:K→*M) {n:ℕ}
    (f:Fin n→G) (hf:∀ v,f v∈K) (h:(ZR f).prod∈K):
    π ⟨(ZR f).prod,h⟩=(ZR fun v=>π ⟨f v,hf v⟩).prod:=by
  have e:(⟨(ZR f).prod,h⟩:K)=(ZR fun v=> (⟨f v,hf v⟩:K)).prod:=by
    apply Zu
    rw[SubmonoidClass.coe_list_prod,Vv]
    try rfl
  rw[e,RO,Vv]
  try rfl
lemma aZ.oT (S:aZ p a g) (i:Fin c) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (j3:∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (e:Fin (r i)→ℕ) {d:G} (hd:d∈lcs G ((i:ℕ)+1)) {x:G} (hx:x∈lcs G i)
    (Cv:x =(ZR fun v=>g ⟨i,v⟩^e v).prod*d):
    π ⟨x,hx⟩=∏ v,π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩^e v:=by
  have hf:∀ v,g ⟨i,v⟩^e v∈lcs G i:= fun v=>Xm _ (S.mem ⟨i,v⟩) _
  have hB:(ZR fun v=>g ⟨i,v⟩^e v).prod∈lcs G i:=
    Wb _ fun z hz=>by
      rw[XC]at hz
      obtain ⟨v,rfl⟩:=hz
      exact hf v
  have hdi:d∈lcs G i:=bC (XV _) hd
  have e1:(⟨x,hx⟩:lcs G i)=⟨_,hB⟩*⟨d,hdi⟩:=Zu Cv
  rw[e1,YP,j3 ⟨d,hdi⟩ hd,UH,Gt π _ hf hB,Oc]
  refine TQ rfl fun v _=>?_
  rw[← map_pow]
  exact congrArg π (Zu (by simp))
lemma aZ.aal (S:aZ p a g) (i:Fin c) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (j3:∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (j:Fin (r i)):
    π ⟨g ⟨i,j⟩,S.mem ⟨i,j⟩⟩^(p^a ⟨i,j⟩)=
      ∏ v∈ZU.filter (fun v:Fin (r i)=>v<j),
        π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩^(S.c_ ⟨i,j⟩ ⟨i,v⟩).val:=by
  have hpow:=S.CH.pow i j
  have f6:=lX g S.mem (fun h=> (S.c_ ⟨i,j⟩ h).val) i
  have cI:g ⟨i,j⟩^p^a ⟨i,j⟩∈lcs G i:=Xm _ (S.mem ⟨i,j⟩) _
  have hb:=S.oT i π j3 (fun v=> (S.c_ ⟨i,j⟩ ⟨i,v⟩).val) f6 cI hpow
  rw[← map_pow]
  have e1:(⟨g ⟨i,j⟩,S.mem ⟨i,j⟩⟩:lcs G i)^(p^a ⟨i,j⟩)=⟨_,cI⟩:=
    Zu (Vg _ _)
  rw[e1,hb,Finset.prod_filter]
  refine TQ rfl fun v _=>?_
  by_cases hv:v<j
  · rw[if_pos hv]
  · rw[if_neg hv,S.q6 i j v (not_lt.mp hv),Y6]
lemma aZ.tO (S:aZ p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (hπ:Zn π)
    (j3:∀ x:lcs G i,π x =1↔(x:G)∈lcs G ((i:ℕ)+1)):
    ZB L=p^∑ v:Fin (r i),a ⟨i,v⟩:=by
 have acO:π.ker=(lcs G ((i:ℕ)+1)).subgroupOf (lcs G i):=by
  ext x
  rw[Zm,ZT,j3]
 rw[← S.Bz hp i hlast]
 exact (YJ ((QuotientGroup.quotientMulEquivOfEq acO).symm.trans
   (Xj π hπ)).toEquiv).symm
lemma aZ.rP (S:aZ p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) {L:Type*} [CommGroup L] [Finite L]
    (π:lcs G i→*L) (hπ:Zn π)
    (j3:∀ x:lcs G i,π x =1↔(x:G)∈lcs G ((i:ℕ)+1))
    (b:Fin (r i)→Fin (r i)→ℕ) (hb:∀ j v,(S.c_ ⟨i,j⟩ ⟨i,v⟩).val=b j v):
    ∃ φ :((Fin (r i)→ℤ)⧸iz p (fun v=>a ⟨i,v⟩) b)≃+Additive L,
      ∀ x:Fin (r i)→ℤ,φ (ZP x)=
        jS (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩) x:=by
  have abF:∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1:=
    fun x hx => (j3 x).2 hx
  have dV:ZA (ZF fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩)=⊤:=by
    rw[Yo]
    intro z _
    obtain ⟨⟨x,hx⟩,rfl⟩:=hπ z
    rw [S.oT i π abF (fun v=> (S.nf.coord x ⟨i,v⟩).val)
      (lX g S.mem (fun h=> (S.nf.coord x h).val) i) hx (S.nS i hx)]
    exact Subgroup.prod_mem _ fun v _=>
      Xm _ (ZD (Tk v)) _
  have dS:=S.tO hp i hlast π hπ j3
  have m_:∀ j,jS (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩)
      (k7 p (fun v=>a ⟨i,v⟩) b j)=0:=by
    intro j
    apply Ej
    beta_reduce
    rw[← ofMul_pow,S.aal i π abF j,ofMul_prod]
    simp only[ofMul_pow,hb]
  obtain ⟨φ, -,hφ⟩:=Ls hp _ b _ dV dS m_
  exact ⟨φ,hφ⟩
lemma aZ.qg (S:aZ p a g) (i:Fin c) {L:Type*}
    [CommGroup L] (π:lcs G i→*L)
    (j3:∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (b:Fin (r i)→Fin (r i)→ℕ)
    (φ:((Fin (r i)→ℤ)⧸iz p (fun v=>a ⟨i,v⟩) b)≃+Additive L)
    (hφ:∀ x:Fin (r i)→ℤ,φ (ZP x)=
      jS (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩) x) {x:G} (hx:x∈lcs G i):
    φ (ZP (fun v=> ((S.nf.coord x ⟨i,v⟩:ℕ):ℤ)))=
      ZC (π ⟨x,hx⟩):=by
  rw [hφ,y9,S.oT i π j3 (fun v=> (S.nf.coord x ⟨i,v⟩).val)
    (lX g S.mem (fun h=> (S.nf.coord x h).val) i) hx (S.nS i hx),ofMul_prod]
  simp only[ofMul_pow,natCast_zsmul]
lemma aZ.Ly [Finite G] (S:aZ p a g) (hp:0<p) (h0:0<c)
    (hlast:1<c∨lcs G 1=⊥) (b:Fin (r ⟨0,h0⟩)→Fin (r ⟨0,h0⟩)→ℕ)
    (hb:∀ j v,(S.c_ ⟨⟨0,h0⟩,j⟩ ⟨⟨0,h0⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨0,h0⟩)→ℤ)⧸iz p (fun v=>a ⟨⟨0,h0⟩,v⟩) b)≃+
        Additive (Abelianization G),
      ∀ x,φ (ZP x)=jS (fun v=>
        (ZJ.comp (lcs G 0).subtype) ⟨g ⟨⟨0,h0⟩,v⟩,S.mem ⟨⟨0,h0⟩,v⟩⟩) x:=by
  refine S.rP hp ⟨0,h0⟩ hlast (ZJ.comp (lcs G 0).subtype)
    ?_ ?_ b hb
  · intro z
    obtain ⟨x,rfl⟩:=jv z
    exact ⟨⟨x,Nu x⟩,rfl⟩
  · intro x
    rw [Y0,UF, ← Zm,WV,
      eO]
    try exact U8
lemma aZ.Ll [Finite G] (S:aZ p a g) (hp:0<p) (h1:1<c)
    (hlast:2<c∨lcs G 2=⊥) (b:Fin (r ⟨1,h1⟩)→Fin (r ⟨1,h1⟩)→ℕ)
    (hb:∀ j v,(S.c_ ⟨⟨1,h1⟩,j⟩ ⟨⟨1,h1⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨1,h1⟩)→ℤ)⧸iz p (fun v=>a ⟨⟨1,h1⟩,v⟩) b)≃+Additive (gY G),
      ∀ x,φ (ZP x)=
        jS (fun v=>f9 G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩) x:=
  S.rP hp ⟨1,h1⟩ hlast (f9 G) nI (fun x =>jT x) b hb
lemma aZ.LY [Finite G] (S:aZ p a g) (hp:0<p) (h2:2<c)
    (hlast:3<c∨lcs G 3=⊥) (b:Fin (r ⟨2,h2⟩)→Fin (r ⟨2,h2⟩)→ℕ)
    (hb:∀ j v,(S.c_ ⟨⟨2,h2⟩,j⟩ ⟨⟨2,h2⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨2,h2⟩)→ℤ)⧸iz p (fun v=>a ⟨⟨2,h2⟩,v⟩) b)≃+Additive (oI G),
      ∀ x,φ (ZP x)=
        jS (fun v=>jK G ⟨g ⟨⟨2,h2⟩,v⟩,S.mem ⟨⟨2,h2⟩,v⟩⟩) x:=
  S.rP hp ⟨2,h2⟩ hlast (jK G) (nZ G) (fun x =>jP x)
    b hb
end LfSimsLift
section LfFiber
variable {p:ℕ}
def je {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:a9 m)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    Set (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):=
  {C | ∃ G∈T,dW hp m G (⟨D,(B,C)⟩:cQ p m)}
end LfFiber
section LfLead
def dK {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L):
    L≃*Multiplicative Q where
  toFun x:=Zi (φ.symm (ZC x))
  invFun y:=ZW (φ (Vk y))
  left_inv x:=by simp
  right_inv y:=by simp
  map_mul' x y:=by
    show Zi (φ.symm (ZC x+ZC y))=_
    exact (congrArg Zi (map_add φ.symm _ _)).trans (ofAdd_add _ _)
lemma Mt {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L) (x:L):
    dK φ x =Zi (φ.symm (ZC x)):=rfl
lemma wW {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L) {x:L}
    {q:Q} (h:φ q=ZC x):dK φ x =Zi q:=by
 rw[Mt, ← h,AddEquiv.symm_apply_apply]
abbrev kL {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):Type:=
  (Fin n→ℤ)⧸iz p a b
lemma JL {n:ℕ} (x:Fin n→ℤ) (j:Fin n):
    Yz j (x j)=x j•(Yz j (1:ℤ):Fin n→ℤ):=by
 funext i
 by_cases h:i=j
 · subst h
   simp
 · simp[Um,h]
lemma uY {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    ZA (ZF fun j:Fin n=>
      Zi (ZP (Yz j (1:ℤ)):kL p a b))=⊤:=by
  rw[Yo]
  rintro z -
  obtain ⟨x,hx⟩:=UG (Vk z)
  have hz:z=Zi (ZP x:kL p a b):=by
   rw[hx]
   rfl
  rw[hz]
  have key:∀ s:Finset (Fin n),Zi
      (ZP (∑ j∈s,Yz j (x j)):kL p a b)∈
      ZA (ZF fun j:Fin n=>
        Zi (ZP (Yz j (1:ℤ)):kL p a b)):=by
    intro s
    refine Xn s ?_ ?_
    · rw[P7,Oi,ofAdd_zero]
      exact Yl _
    · intro j s hj ih
      rw[TV hj,Oj,ofAdd_add]
      refine Yq _ ?_ ih
      rw[JL x j,Ol,ofAdd_zsmul]
      exact Ry _ (ZD (Tk j)) _
  have h:=key ZU
  rwa[Finset.univ_sum_single]at h
lemma Dm {n p:ℕ} {a:Fin n→ℕ} {b:Fin n→Fin n→ℕ} {L:Type*} [CommGroup L]
    (φ:kL p a b≃+Additive L) {N:ℕ} (hL:ZB L=N):
    ZB (Multiplicative (kL p a b))=N:=by
 rw [← hL,YJ (Vk:Multiplicative (kL p a b)≃_),
   YJ φ.toEquiv]
 exact YJ ZW
abbrev aP {c:ℕ} (h2:2<c):Fin c:=⟨0,by omega⟩
abbrev aY {c:ℕ} (h2:2<c):Fin c:=⟨1,by omega⟩
abbrev bY {c:ℕ} (h2:2<c):Fin c:=⟨2,h2⟩
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G}
def aZ.iW (S:aZ p a g) (h2:2<c):
    Fin (r (aP h2))→Fin (r (aP h2))→Fin (r (aY h2))→ℕ:=
  fun j k v=> (S.nf.coord ⁅g ⟨aP h2,j⟩,g ⟨aP h2,k⟩⁆ ⟨aY h2,v⟩).val
def aZ.lR (S:aZ p a g) (h2:2<c):
    Fin (r (aY h2))→Fin (r (aP h2))→Fin (r (bY h2))→ℕ:=
  fun j k v=> (S.nf.coord ⁅g ⟨aY h2,j⟩,g ⟨aP h2,k⟩⁆ ⟨bY h2,v⟩).val
structure aZ.kP (S:aZ p a g) (h2:2<c)
    (b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ)
    (b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ)
    (b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ) where
  φ1:kL p (fun v=>a ⟨aP h2,v⟩) b0≃+Additive (Abelianization G)
  φ2:kL p (fun v=>a ⟨aY h2,v⟩) b1≃+Additive (gY G)
  φ3:kL p (fun v=>a ⟨bY h2,v⟩) b2≃+Additive (oI G)
  ac8:∀ x,φ1 (ZP x)=jS (fun v=>
    (ZJ.comp (lcs G 0).subtype) ⟨g ⟨aP h2,v⟩,S.mem ⟨aP h2,v⟩⟩) x
  abT:∀ x,φ2 (ZP x)=
    jS (fun v=>f9 G ⟨g ⟨aY h2,v⟩,S.mem ⟨aY h2,v⟩⟩) x
  ac7:∀ x,φ3 (ZP x)=
    jS (fun v=>jK G ⟨g ⟨bY h2,v⟩,S.mem ⟨bY h2,v⟩⟩) x
  abI:ZB (gY G)=p^∑ v,a ⟨aY h2,v⟩
  abE:ZB (oI G)=p^∑ v,a ⟨bY h2,v⟩
lemma aZ.uh [Finite G] (S:aZ p a g) (hp:0<p)
    (h2:2<c) (hlast:3<c∨lcs G 3=⊥)
    (b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ)
    (b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ)
    (b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ)
    (Fj:∀ j v,(S.c_ ⟨aP h2,j⟩ ⟨aP h2,v⟩).val=b0 j v)
    (s8:∀ j v,(S.c_ ⟨aY h2,j⟩ ⟨aY h2,v⟩).val=b1 j v)
    (uj:∀ j v,(S.c_ ⟨bY h2,j⟩ ⟨bY h2,v⟩).val=b2 j v):
    Nonempty (S.kP h2 b0 b1 b2):=by
 obtain ⟨φ1,h1⟩:=S.Ly hp (by omega) (Y7 (by omega)) b0 Fj
 obtain ⟨φ2,jM⟩:=S.Ll hp (by omega) (Y7 h2) b1 s8
 obtain ⟨φ3,h3⟩:=S.LY hp h2 hlast b2 uj
 have c2:=S.tO hp (aY h2) (Y7 (show (1:ℕ)+1<c by omega)) (f9 G)
   nI (fun x =>jT x)
 have c3:=S.tO hp (bY h2) hlast (jK G) (nZ G)
   (fun x =>jP x)
 exact ⟨⟨φ1,φ2,φ3,h1,jM,h3,c2,c3⟩⟩
variable {S:aZ p a g} {h2:2<c} {b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ}
  {b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ} {b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ}
lemma aZ.kP.Nz (I:S.kP h2 b0 b1 b2) (v:Fin (r (aP h2))):
    dK I.φ1 (ZJ (g ⟨aP h2,v⟩))=
      Zi (ZP (Yz v (1:ℤ))):=
  wW _ ((I.ac8 _).trans (qo _ v))
lemma aZ.kP.aar (I:S.kP h2 b0 b1 b2) (v:Fin (r (aY h2))):
    dK I.φ2 (f9 G ⟨g ⟨aY h2,v⟩,S.mem ⟨aY h2,v⟩⟩)=
      Zi (ZP (Yz v (1:ℤ))):=
  wW _ ((I.abT _).trans (qo _ v))
lemma aZ.kP.Fv (I:S.kP h2 b0 b1 b2) {x:G} (hx:x∈lcs G 1):
    dK I.φ2 (f9 G ⟨x,hx⟩)=Zi
      (ZP (fun v=> ((S.nf.coord x ⟨aY h2,v⟩:ℕ):ℤ))):=
  wW _ (S.qg (aY h2) (f9 G) (fun y hy=> (jT y).2 hy)
    b1 I.φ2 I.abT hx)
lemma aZ.kP.Mc (I:S.kP h2 b0 b1 b2) {x:G} (hx:x∈lcs G 2):
    dK I.φ3 (jK G ⟨x,hx⟩)=Zi
      (ZP (fun v=> ((S.nf.coord x ⟨bY h2,v⟩:ℕ):ℤ))):=
  wW _ (S.qg (bY h2) (jK G) (fun y hy=> (jP y).2 hy)
    b2 I.φ3 I.ac7 hx)
variable {G':Type u} [Group G'] {g':aR c r→G'} {S':aZ p a g'}
lemma aZ.Q9 (hp:0<p) (I:S.kP h2 b0 b1 b2)
    (I':S'.kP h2 b0 b1 b2)
    (hT1:qz (dK I.φ1) (dK I.φ2)=qz (dK I'.φ1) (dK I'.φ2))
    (hT2:tQ (dK I.φ1) (dK I.φ2) (dK I.φ3)=
      tQ (dK I'.φ1) (dK I'.φ2) (dK I'.φ3)):
    S.iW h2=S'.iW h2∧S.lR h2=S'.lR h2:=by
 have ha:∀ i,dK I.φ1 (ZJ (g ⟨aP h2,i⟩))=
     dK I'.φ1 (ZJ (g' ⟨aP h2,i⟩)):= fun i=>
   (I.Nz i).trans (I'.Nz i).symm
 constructor
 · funext j k
   have hc:=LZ (dK I.φ1) (dK I.φ2) (dK I'.φ1) (dK I'.φ2) hT1
     (fun i=>g ⟨aP h2,i⟩) (fun i=>g' ⟨aP h2,i⟩) ha j k
   have hc':=((I.Fv (cw (g ⟨aP h2,j⟩) (g ⟨aP h2,k⟩)).2).symm.trans hc).trans
     (I'.Fv (cw (g' ⟨aP h2,j⟩) (g' ⟨aP h2,k⟩)).2)
   exact Jg hp _ b1 I.φ2 I.abI (S.iW h2 j k) (S'.iW h2 j k)
     (fun v=> (S.nf.coord ⁅g ⟨aP h2,j⟩,g ⟨aP h2,k⟩⁆ ⟨aY h2,v⟩).isLt)
     (fun v=> (S'.nf.coord ⁅g' ⟨aP h2,j⟩,g' ⟨aP h2,k⟩⁆ ⟨aY h2,v⟩).isLt)
     (Zi.injective hc')
 · funext j k
   have hw:dK I.φ2 (f9 G ⟨g ⟨aY h2,j⟩,S.mem ⟨aY h2,j⟩⟩)=
       dK I'.φ2 (f9 G' ⟨g' ⟨aY h2,j⟩,S'.mem ⟨aY h2,j⟩⟩):=
     (I.aar j).trans (I'.aar j).symm
   have hc:=LV (dK I.φ1) (dK I.φ2) (dK I.φ3) (dK I'.φ1)
     (dK I'.φ2) (dK I'.φ3) hT2 _ _ hw (g ⟨aP h2,k⟩) (g' ⟨aP h2,k⟩) (ha k)
   have hc':=((I.Mc (uu ⟨g ⟨aY h2,j⟩,S.mem ⟨aY h2,j⟩⟩
       (g ⟨aP h2,k⟩)).2).symm.trans hc).trans
     (I'.Mc (uu ⟨g' ⟨aY h2,j⟩,S'.mem ⟨aY h2,j⟩⟩ (g' ⟨aP h2,k⟩)).2)
   exact Jg hp _ b2 I.φ3 I.abE (S.lR h2 j k) (S'.lR h2 j k)
     (fun v=> (S.nf.coord ⁅g ⟨aY h2,j⟩,g ⟨aP h2,k⟩⁆ ⟨bY h2,v⟩).isLt)
     (fun v=> (S'.nf.coord ⁅g' ⟨aY h2,j⟩,g' ⟨aP h2,k⟩⁆ ⟨bY h2,v⟩).isLt)
     (Zi.injective hc')
end LfLead
section LfLeadCount
variable {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
lemma v6 (hp:p.Prime) (h2:2<c)
    (b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ)
    (b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ)
    (b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ) {s:ℕ} (hs:s≤ r (aP h2))
    (D:Finset (Fin (r (aP h2))×Fin (r (aP h2))))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s)
    (w:Fin (r (aP h2))×Fin (r (aP h2))→Fin (r (aY h2))→ℕ)
    (Λ :Set ((Fin (r (aP h2))→Fin (r (aP h2))→Fin (r (aY h2))→ℕ)×
      (Fin (r (aY h2))→Fin (r (aP h2))→Fin (r (bY h2))→ℕ)))
    (hΛ :∀ x∈Λ,∃ (G:Type u) (_:Group G) (_:Finite G) (g:aR c r→G)
      (S:aZ p a g),
      (∀ j v,(S.c_ ⟨aP h2,j⟩ ⟨aP h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.c_ ⟨aY h2,j⟩ ⟨aY h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.c_ ⟨bY h2,j⟩ ⟨bY h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨aP h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨aP h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.iW h2 q.1 q.2=w q)∧
      x =(S.iW h2,S.lR h2)):
    Λ.ncard≤∑ β∈(ZM (min (∑ v,a ⟨aY h2,v⟩) (∑ v,a ⟨bY h2,v⟩)+1)).filter
        (fun β=> (∑ v,a ⟨bY h2,v⟩)≤ s*β),
      p ^ (s*(β *(r (aY h2)+(∑ v,a ⟨bY h2,v⟩)+1 - β)))*
        p ^(((r (aP h2)).choose 2 - D.card)*(∑ v,a ⟨aY h2,v⟩) -
          (r (aP h2) - s).choose 2*β):=by
  classical
  have n5:=hp.pos
  have:Finite (kL p (fun v=>a ⟨aP h2,v⟩) b0):=(nO n5 _ b0).1
  have:Finite (kL p (fun v=>a ⟨aY h2,v⟩) b1):=(nO n5 _ b1).1
  have:Finite (kL p (fun v=>a ⟨bY h2,v⟩) b2):=(nO n5 _ b2).1
  have:Finite (Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0)):=
    SI _ Zi
  have:Finite (Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1)):=
    SI _ Zi
  have:Finite (Multiplicative (kL p (fun v=>a ⟨bY h2,v⟩) b2)):=
    SI _ Zi
  rcases Λ.eq_empty_or_nonempty with hE | ⟨x0,kH⟩
  · rw[hE,Y3]
    exact Zv _
  obtain ⟨G0,_,_,g0,S0,Fj,s8,uj,hl, -, -, -⟩:=hΛ x0 kH
  obtain ⟨I0⟩:=S0.uh n5 h2 hl b0 b1 b2 Fj s8 uj
  have lU:=Dm I0.φ2 I0.abI
  have jG:=Dm I0.φ3 I0.abE
  have:=qu (L1:=Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0))
    (L2:=Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1))
    (L3:=Multiplicative (kL p (fun v=>a ⟨bY h2,v⟩) b2))
  let gg:Fin (r (aP h2))→Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0):=
    fun j=>Zi (ZP (Yz j (1:ℤ)))
  let yy:Fin (r (aY h2))→Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1):=
    fun j=>Zi (ZP (Yz j (1:ℤ)))
  let vv:Fin (r (aP h2))×Fin (r (aP h2))→
      Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1):=
    fun q=>Zi (ZP (fun v=> ((w q v:ℕ):ℤ)))
  obtain ⟨R, hR⟩:∃ R:((Fin (r (aP h2))→Fin (r (aP h2))→Fin (r (aY h2))→ℕ)×
      (Fin (r (aY h2))→Fin (r (aP h2))→Fin (r (bY h2))→ℕ))→
      ((Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0)→*
          Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0)→*
            Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1))×
        (Multiplicative (kL p (fun v=>a ⟨aY h2,v⟩) b1)→*
          Multiplicative (kL p (fun v=>a ⟨aP h2,v⟩) b0)→*
            Multiplicative (kL p (fun v=>a ⟨bY h2,v⟩) b2)))→Prop,R=
    fun x β=> ∃ (G:Type u) (_:Group G) (g:aR c r→G) (S:aZ p a g)
      (I :S.kP h2 b0 b1 b2),x =(S.iW h2,S.lR h2)∧
        β=(qz (dK I.φ1) (dK I.φ2),tQ (dK I.φ1) (dK I.φ2) (dK I.φ3)):=
    ⟨_,rfl⟩
  have aa2:∀ x x' β,R x β→R x' β→x =x':=by
   intro x x' β h h'
   rw[hR]at h h'
   obtain ⟨G,_,g,S,I,rfl,rfl⟩:=h
   obtain ⟨G',_,g',S',I',rfl,hβ⟩:=h'
   obtain ⟨h1,jM⟩:=Tn.inj hβ
   obtain ⟨e1,e2⟩:=aZ.Q9 n5 I I' h1 jM
   rw[e1,e2]
  have qX:∀ x∈Λ,∃ β,β∈DJ (Multiplicative (kL p (fun v=>a ⟨bY h2,v⟩) b2))
      s gg D vv∧R x β:=by
    intro x hx
    obtain ⟨G,_,_,g,S,Fj,s8,uj,hl,dG,hDw,rfl⟩:=hΛ x hx
    obtain ⟨I⟩:=S.uh n5 h2 hl b0 b1 b2 Fj s8 uj
    refine ⟨_,aac (dK I.φ1) (dK I.φ2) (dK I.φ3)
      (fun j=>g ⟨aP h2,j⟩) gg (fun j=>I.Nz j) dG D vv (fun q hq=>?_),?_⟩
    swap
    · rw[hR]
      exact ⟨G,inferInstance,g,S,I,rfl,rfl⟩
    refine (I.Fv (cw (g ⟨aP h2,q.1⟩) (g ⟨aP h2,q.2⟩)).2).trans ?_
    show _=Zi (ZP (fun v=> ((w q v:ℕ):ℤ)))
    rw[← hDw q hq]
    rfl
  let F:= fun x =>if h:x∈Λ then XP (qX x h) else 1
  have hF:∀ x (h:x∈Λ),F x =XP (qX x h):= fun x h=>dif_pos h
  have oc:∀ x∈Λ,F x∈DJ (Multiplicative (kL p (fun v=>a ⟨bY h2,v⟩) b2))
      s gg D vv:= fun x h=>by
    rw[hF x h]
    exact (Ym (qX x h)).1
  have eW:WP F Λ:=by
   intro x hx x' oQ he
   refine aa2 x x' (F x) ?_ ?_
   · rw[hF x hx]
     exact (Ym (qX x hx)).2
   · rw[he,hF x' oQ]
     exact (Ym (qX x' oQ)).2
  refine (YM F oc eW (Zl _)).trans ?_
  exact NY hp hs lU jG yy (uY p _ b1) gg (uY p _ b0)
    D hD vv
end LfLeadCount
section LfFlat
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.Lr [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (t k:Fin d.n) (hrec:d.q8 t k) (k':aR c (mL r c)):
    ((hS.toaZ hp hn).nf.coord ⁅X t,X k⁆ k').val=d.c t k (hS.aV hn k'):=by
 have vG:⁅X t,X k⁆=gN X (d.c t k):=by
  rcases hrec with ⟨h1,h2,h3⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact hS.e9.DZ t k h1 h2 h3
  · exact hS.e9.Iq t k h1 h2
  · exact hS.e9.IG t k h1 h2
 have hx:=Ym (hS.k8 ⁅X t,X k⁆)
 have h2:=hS.s7 _ (d.c t k) hx.1 (fun v=>hS.bounded.2 t k v) (hx.2.symm.trans vG)
 show XP (hS.k8 ⁅X t,X k⁆) (hS.aV hn k')=_
 rw[h2]
lemma aE.wL [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (k1 k2 k3:aR c (mL r c))
    (hrec:d.q8 (hS.aV hn k1) (hS.aV hn k2)):
    jd d (hS.aV hn k1).val (hS.aV hn k2).val (hS.aV hn k3).val=
      ((hS.toaZ hp hn).nf.coord
        ⁅X (hS.aV hn k1),X (hS.aV hn k2)⁆ k3).val:=by
 unfold jd
 rw [dif_pos (show _∧_∧_ from
   ⟨(hS.aV hn k1).isLt,(hS.aV hn k2).isLt,(hS.aV hn k3).isLt⟩)]
 refine (if_pos ?_).trans ?_
 · exact hrec
 · exact (hS.Lr hp hn _ _ hrec k3).symm
lemma aE.JR (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c) (h0:0<c)
    (dG:lcs G 1≤⁅ZA (u '' ZH d.s),
      ZA (u '' ZH d.s)⁆⊔lcs G 2):
    d.s ≤ r 0∧lcs G 1≤⁅ZA ((fun j:Fin (mL r c ⟨0,h0⟩)=>
        X (hS.aV hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s}),
      ZA ((fun j:Fin (mL r c ⟨0,h0⟩)=>
        X (hS.aV hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s})⁆⊔lcs G 2:=by
  have e0:aD r 0=0:=rfl
  have hsn:=hS.valid.yA
  have kB:d.s≤ r 0:=by
   rcases Yj d.s with h | h
   · omega
   · have hl:=hS.valid.core ⟨d.s - 1,by omega⟩ (show d.s - 1<d.s by omega)
     have:=((hS.fD ⟨d.s - 1,by omega⟩ 0).mp hl).2
     rw[e0]at this
     show d.s≤ r 0
     have h':d.s - 1< r 0:=by simpa using this
     omega
  have hX:∀ (k:ℕ) (hk:k<d.s) (GW:k< mL r c ⟨0,h0⟩),
      X (hS.aV hn ⟨⟨0,h0⟩,⟨k,GW⟩⟩)=u k:=by
   intro k hk GW
   have hv:hS.aV hn ⟨⟨0,h0⟩,⟨k,GW⟩⟩=⟨k,by omega⟩:=by
     apply YL
     rw[hS.o3 hn]
     show aD r 0+k=k
     rw[e0,zero_add]
   rw[hv]
   exact hS.core ⟨k,by omega⟩ hk
  have abx:u '' ZH d.s=(fun j:Fin (mL r c ⟨0,h0⟩)=>
      X (hS.aV hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s}:=by
    ext z
    constructor
    · rintro ⟨k,hk,rfl⟩
      have lQ:k<d.s:=hk
      exact ⟨⟨k,show k< r 0 by omega⟩,lQ,hX k lQ _⟩
    · rintro ⟨j,hj,rfl⟩
      have mC:(j:ℕ)<d.s:=hj
      exact ⟨j.val,mC,(hX j.val mC j.isLt).symm⟩
  rw[abx]at dG
  exact ⟨kB,dG⟩
lemma aE.v8 [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (h2:2<c) (j k:Fin (mL r c (aP h2))) (uW:j<k)
    (v:Fin (mL r c (aY h2))):
    jd d (hS.aV hn ⟨aP h2,j⟩).val (hS.aV hn ⟨aP h2,k⟩).val
        (hS.aV hn ⟨aY h2,v⟩).val=(hS.toaZ hp hn).iW h2 j k v:=
  hS.wL hp hn _ _ _ (Y7 ⟨hS.j4 hn _,hS.j4 hn _,by
    rw[XO,hS.o3 hn,hS.o3 hn]
    exact VN uW _⟩)
lemma aE.Gk [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (h2:2<c) (j:Fin (mL r c (aY h2)))
    (k:Fin (mL r c (aP h2)))
    (hk:(k:ℕ)≤(d.df (hS.aV hn ⟨aY h2,j⟩)).2.val) (v:Fin (mL r c (bY h2))):
    jd d (hS.aV hn ⟨aY h2,j⟩).val (hS.aV hn ⟨aP h2,k⟩).val
        (hS.aV hn ⟨bY h2,v⟩).val=(hS.toaZ hp hn).lR h2 j k v:=
  hS.wL hp hn _ _ _ (XQ (Y7 ⟨hS.j4 hn _,by
    rw[hS.o3 hn]
    show 0+(k:ℕ)≤_
    omega⟩))
end LfFlat
section LfCBGen
lemma NV (d:aO) (t k w:Fin d.n) (hrec:d.q8 t k):
    jd d t.val k.val w.val=d.c t k w:=by
 unfold jd
 rw[dif_pos ⟨t.isLt,k.isLt,w.isLt⟩]
 exact if_pos hrec
lemma Q1 {p:ℕ} (n5:0<p) {d:aO} (hb:d.Bounded p) (i j k:ℕ):
    jd d i j k<p^lL d k:=by
 unfold jd lL
 by_cases h:i<d.n∧j<d.n∧k<d.n
 · rw[dif_pos h,dif_pos h.2.2]
   split_ifs
   · exact hb.2 _ _ _
   · exact XD n5 _
 · rw[dif_neg h]
   exact XD n5 _
end LfCBGen
section LfCBGroup
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.vZ (hS:aE p u d X r):
    lcs G 1≤⁅ZA (u '' ZH d.s),ZA (u '' ZH d.s)⁆⊔
      lcs G 2:=by
 refine (hS.w7 1).trans (sup_le_sup_right ?_ _)
 rw[ZE]
 rintro _ ⟨t,ht,rfl⟩
 have iQ:d.lv t=1:=ht
 have lH:=hS.e9.Fk t (by omega)
 have h1:(d.df t).1< (d.df t).2:=hS.valid.oR t iQ
 have h2:((d.df t).2:ℕ)<d.s:=hS.valid.kR t (by omega)
 have hf:((d.df t).1:ℕ)<d.s:=Uj (XO.mp h1) h2
 rw[Xb,lH,hS.core _ hf,hS.core _ h2]
 exact Zo (ZD ⟨_,hf,rfl⟩)
   (ZD ⟨_,h2,rfl⟩)
lemma aE.I7 (hS:aE p u d X r) {c:ℕ} (hn:d.n=aD r c)
    (hc:1≤ c):lcs G c=⊥:=by
 rw[eq_bot_iff]
 refine (hS.Kd c hc).trans ?_
 rw[ZE]
 rintro _ ⟨t,ht,rfl⟩
 exfalso
 have h1:=hS.GK hn t
 have h2:c≤d.lv t:=ht
 omega
lemma aE.u8 (hS:aE p u d X r) (hn:d.n=aD r 3) {i j k:ℕ}
    (h:jd d i j k≠0):
    (i < j∧j<aD r 1∧aD r 1≤k∧k<aD r 3)∨
      (aD r 1≤ i∧i<aD r 2∧j<aD r 1∧j≤b9 d r (i - aD r 1)∧
        aD r 2≤k∧k<aD r 3):=by
 unfold jd at h
 by_cases hr :i<d.n∧j<d.n∧k<d.n
 swap
 · rw[dif_neg hr]at h
   exact absurd rfl h
 rw[dif_pos hr]at h
 by_cases hrec:d.q8 ⟨i,hr.1⟩ ⟨j,hr.2.1⟩
 swap
 · rw[if_neg hrec]at h
   exact absurd rfl h
 rw[if_pos hrec]at h
 have L9:=hS.valid.Aa _ _ _ h
 have hk3:=hS.GK hn ⟨k,hr.2.2⟩
 obtain ⟨ki1, -⟩:=(hS.fD ⟨k,hr.2.2⟩ (d.lv ⟨k,hr.2.2⟩)).mp rfl
 have ki1':aD r (d.lv ⟨k,hr.2.2⟩)≤k:=ki1
 have e01:aD r 1=aD r 0+r 0:=dM r 0
 have e12:aD r 2=aD r 1+r 1:=dM r 1
 have e0:aD r 0=0:=rfl
 have hkn:k<aD r 3:=by rw[← hn]; exact hr.2.2
 rcases hrec with ⟨h1,h2,h3⟩ | ⟨h1,h2⟩ | ⟨h1, -⟩
 · left
   obtain ⟨-,j2⟩:=(hS.fD ⟨j,hr.2.1⟩ 0).mp h2
   have j2':j<aD r 0+r 0:=j2
   have Bw:aD r 1≤aD r (d.lv ⟨k,hr.2.2⟩):=g5 r (by omega)
   have h3':i<j:=h3
   exact ⟨h3',by omega,by omega,hkn⟩
 · right
   obtain ⟨i1,i2⟩:=(hS.fD ⟨i,hr.1⟩ 1).mp h1
   have i1':aD r 1≤ i:=i1
   have i2':i<aD r 1+r 1:=i2
   have hlk:d.lv ⟨k,hr.2.2⟩=2:=by omega
   rw[hlk]at ki1'
   have EK:=kQ d r ⟨i,hr.1⟩ (i - aD r 1)
     (by show aD r 1+(i - aD r 1)=i; omega)
   have Lh:=hS.valid.kR ⟨i,hr.1⟩ (by omega)
   have hc0:=hS.valid.core (d.df ⟨i,hr.1⟩).2 Lh
   obtain ⟨-,c2⟩:=(hS.fD _ 0).mp hc0
   have c2':((d.df ⟨i,hr.1⟩).2:ℕ)<aD r 0+r 0:= c2
   have jM:j≤((d.df ⟨i,hr.1⟩).2:ℕ):=h2
   refine ⟨i1',by omega,by omega,?_,ki1',hkn⟩
   rw[EK]
   exact jM
 · exfalso
   omega
lemma aE.Mr (hp:p.Prime) (hS:aE p u d X r) (t:Fin d.n)
    (hl:d.lv t=1) (k:ℕ):
    jd d (d.df t).1.val (d.df t).2.val k=if k=t.val then 1 else 0:=by
  have f5:(d.df t).1< (d.df t).2:=hS.valid.oR t hl
  have Lh:((d.df t).2:ℕ)<d.s:=hS.valid.kR t (by omega)
  have hl0:d.lv (d.df t).1=0:=by
   have:=hS.valid.wY t (by omega)
   omega
  have acA:d.lv (d.df t).2=0:=hS.valid.core _ Lh
  have vG:=hS.e9.DZ _ _ hl0 acA f5
  have lH:=hS.e9.Fk t (by omega)
  have hbd:∀ v,delta t 1 v<p^d.a v:=by
   intro v
   unfold delta
   split_ifs
   · exact one_lt_pow' hp.one_lt (by have:=hS.a_pos v; omega)
   · exact XD hp.pos _
  have heq:=hS.s7 (d.c (d.df t).1 (d.df t).2) (delta t 1)
    (fun v=>hS.bounded.2 _ _ v) hbd
    (vG.symm.trans (lH.symm.trans (by rw[KV,pow_one])))
  by_cases hk:k<d.n
  · show jd d (d.df t).1.val (d.df t).2.val (⟨k,hk⟩:Fin d.n).val=_
    rw[NV d (d.df t).1 (d.df t).2 ⟨k,hk⟩ (Y7 ⟨hl0,acA,f5⟩),heq]
    show (if (⟨k,hk⟩:Fin d.n)=t then 1 else 0)=_
    by_cases qB:k=t.val
    · rw[if_pos (YL qB:(⟨k,hk⟩:Fin d.n)=t),if_pos qB]
    · rw[if_neg (fun h'=>qB (congrArg Ty h')),if_neg qB]
  · have h1:jd d (d.df t).1.val (d.df t).2.val k=0:=by
      unfold jd
      rw[dif_neg (fun h'=>hk h'.2.2)]
    rw[h1,if_neg (by have:=t.isLt; omega)]
lemma aE.JI (hp:p.Prime) (hS:aE p u d X r) (bU:2≤d.s) {j:ℕ}
    (hj:j< r 1) (k:ℕ):
    jd d (t5 d r j) (b9 d r j) k=if k=aD r 1+j then 1 else 0:=by
  obtain ⟨h,hl⟩:=hS.pO bU j hj
  rw[r5 d r ⟨aD r 1+j,h⟩ j rfl,kQ d r ⟨aD r 1+j,h⟩ j rfl]
  exact hS.Mr hp ⟨aD r 1+j,h⟩ hl k
lemma aE.qL (hS:aE p u d X r) (bU:2≤d.s) {j:ℕ}
    (hj:j< r 1):t5 d r j<b9 d r j:=by
 obtain ⟨h,hl⟩:=hS.pO bU j hj
 rw[r5 d r ⟨aD r 1+j,h⟩ j rfl,kQ d r ⟨aD r 1+j,h⟩ j rfl]
 exact hS.valid.oR _ hl
lemma aE.y7 (hS:aE p u d X r) (bU:2≤d.s) {j j':ℕ}
    (hj:j< r 1) (mC:j'< r 1) (h1:t5 d r j=t5 d r j')
    (h2:b9 d r j=b9 d r j'):j=j':=by
 obtain ⟨h,hl⟩:=hS.pO bU j hj
 obtain ⟨h',hl'⟩:=hS.pO bU j' mC
 rw[r5 d r ⟨aD r 1+j,h⟩ j rfl,r5 d r ⟨aD r 1+j',h'⟩ j' rfl]at h1
 rw[kQ d r ⟨aD r 1+j,h⟩ j rfl,kQ d r ⟨aD r 1+j',h'⟩ j' rfl]at h2
 have e:=hS.KT _ _ hl hl' (YL h1) (YL h2)
 have e':aD r 1+j=aD r 1+j':= congrArg Ty e
 omega
lemma aE.aaf [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (h2:2<c) (r':Fin c→ℕ) (hr :∀ i:Fin c,r i.val=r' i)
    (a':aR c r'→ℕ) (ha:∀ k:aR c r',a' k=lL d (aD r k.1.val+k.2.val)):
    ∃ (g':aR c r'→G) (S:aZ p a' g'),
      (∀ (i:Fin c) (j v:Fin (r' i)),(S.c_ ⟨i,j⟩ ⟨i,v⟩).val=
        tB d (aD r i.val+j.val) (aD r i.val+v.val))∧
      (∀ (j k:Fin (r' (aP h2))) (v:Fin (r' (aY h2))),j<k→
        S.iW h2 j k v=jd d (aD r 0+j.val) (aD r 0+k.val) (aD r 1+v.val))∧
      (∀ (j:Fin (r' (aY h2))) (k:Fin (r' (aP h2))) (v:Fin (r' (bY h2))),
        k.val≤b9 d r j.val→
        S.lR h2 j k v=jd d (aD r 1+j.val) (aD r 0+k.val) (aD r 2+v.val))∧
      lcs G 1≤⁅ZA ((fun j=>g' ⟨aP h2,j⟩) '' {j | (j:ℕ)<d.s}),
        ZA ((fun j=>g' ⟨aP h2,j⟩) '' {j | (j:ℕ)<d.s})⁆⊔lcs G 2:=by
  have hr':mL r c=r':= funext hr
  subst hr'
  have u6:a'= fun k=>d.a (hS.aV hn k):=
    funext fun k=> (ha k).trans (hS.sI hn k)
  subst u6
  refine ⟨fun k=>X (hS.aV hn k),hS.toaZ hp hn,fun i j v=>?_,
    fun j k v uW=>?_,fun j k v hk=>?_,?_⟩
  · exact (hS.uZ hp hn ⟨i,j⟩ ⟨i,v⟩).symm
  · exact (hS.v8 hp hn h2 j k uW v).symm
  · have lQ:(k:ℕ)≤(d.df (hS.aV hn ⟨aY h2,j⟩)).2.val:=by
      rw[← kQ d r (hS.aV hn ⟨aY h2,j⟩) j.val rfl]
      exact hk
    exact (hS.Gk hp hn h2 j k lQ v).symm
  · exact (hS.JR hn (by omega) hS.vZ).2
end LfCBGroup
section LfCBCount
def kM {p m:ℕ} (D:a9 m)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)) (i j k:ℕ):ℕ:=
  if h:i<D.2.2.1.tot∧j<D.2.2.1.tot∧k<D.2.2.1.tot then
    (C ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩).val
  else 0
def acs {p m:ℕ} (D:a9 m) (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i j:ℕ):ℕ:=
  if h:i<D.2.2.1.tot∧j<D.2.2.1.tot then (B ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
def ac2 {m:ℕ} (D:a9 m) (k:ℕ):ℕ:=
  if h:k<D.2.1.val - 1 then (D.2.2.2.1.1 ⟨k,h⟩).val else 0
def dQ {m:ℕ} (D:a9 m) (j:ℕ):ℕ:=
  if h:j<D.2.2.1.r2 then (D.2.2.2.2.1.1 ⟨j,h⟩).val else 0
lemma M7 {p m:ℕ} (D:a9 m)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i j k:Fin D.2.2.1.tot):kM D C i.val j.val k.val=(C i j k).val:=by
 unfold kM
 rw[dif_pos ⟨i.isLt,j.isLt,k.isLt⟩]
lemma aE.kS {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO}
    {X:Fin d.n→G} {r :ℕ→ℕ} [Finite G] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m) {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.k_ hp m bZ bU hsum=⟨D,(B,C)⟩):
    hS.nL=D.1.val∧d.s=D.2.1.val∧(∀ i<hS.nL,r i=aW D i)∧lL d=qQ D ∧
      kM D C=jd d∧acs D B=tB d∧(∀ k<d.s - 1,og d r k=ac2 D k)∧
      (∀ j< r 1,t5 d r j=dQ D j):=by
 refine ⟨(hS.JP hp bZ bU hsum).symm.trans (congrArg rdC e),
   (hS.Ka hp bZ bU hsum).symm.trans (congrArg rdS e),fun i hi=>?_,?_,?_,?_,
   fun k hk=>?_,fun j hj=>?_⟩
 · have h:= congrFun (congrArg rdR e) i
   rw[hS.DU hp bZ bU hsum,dif_pos hi]at h
   exact h
 · funext j
   exact (hS.DS hp bZ bU hsum j).symm.trans (congrFun (congrArg rdA e) j)
 · funext i j k
   exact ((hS.Fp hp bZ bU hsum i j k).symm.trans
     (congrFun (congrFun (congrFun (congrArg QF e) i) j) k)).symm
 · funext i j
   exact ((hS.DM hp bZ bU hsum i j).symm.trans
     (congrFun (congrFun (congrArg rdB e) i) j)).symm
 · have h:= congrFun (congrArg QO e) k
   rw[hS.Cn hp bZ bU hsum,dif_pos hk]at h
   exact h
 · have h:= congrFun (congrArg rdF e) j
   rw [hS.J4 hp bZ bU hsum,dif_pos (show j< (hS.f7 hp bZ).r2 by
     rw[hS.oa hp bZ bU]; exact hj)]at h
   exact h
lemma zO {G₁ G₂:Type u} [Group G₁] [Group G₂] {p:ℕ} {u₁:ℕ→G₁}
    {d₁:aO} {X₁:Fin d₁.n→G₁} {r₁:ℕ→ℕ} {u₂:ℕ→G₂} {d₂:aO}
    {X₂:Fin d₂.n→G₂} {r₂:ℕ→ℕ} (jE:aE p u₁ d₁ X₁ r₁)
    (lM:aE p u₂ d₂ X₂ r₂) (oE:2≤d₁.s) (hs:d₁.s=d₂.s) (jB:r₁ 1=r₂ 1)
    (pC:∀ k<d₁.s - 1,og d₁ r₁ k= og d₂ r₂ k):
    ∀ j< r₁ 1,b9 d₁ r₁ j=b9 d₂ r₂ j:=by
 have oL:2≤d₂.s:=by omega
 have adg :∀ k,((ZM (r₁ 1)).filter (fun j=>b9 d₁ r₁ j=k)).card=
     ((ZM (r₁ 1)).filter (fun j=>b9 d₂ r₂ j=k)).card:=by
   intro k
   by_cases hk:1≤k∧k<d₁.s
   · have h:=pC (k - 1) (by omega)
     unfold og at h
     rw[← jB,show k - 1+1=k by omega]at h
     exact h
   · have e1:(ZM (r₁ 1)).filter (fun j=>b9 d₁ r₁ j=k)= ∅ :=
       WC.mpr fun j hj=>by
         have:=jE.jC oE j (Zt.mp hj)
         omega
     have e2:(ZM (r₁ 1)).filter (fun j=>b9 d₂ r₂ j=k)= ∅ :=
       WC.mpr fun j hj=>by
         have mC:j< r₂ 1:=by rw[← jB]; exact Zt.mp hj
         have:=lM.jC oL j mC
         omega
     rw[e1,e2]
 intro j hj
 exact vY _ _ _ (fun i j hij hj=>jE.w_ oE i j hij hj)
   (fun i j hij hj=>lM.w_ oL i j hij (by rw[← jB]; exact hj)) adg j hj
abbrev ko {m:ℕ} (D:a9 m) (h2:2<D.1.val):Type:=
  (Fin (aF D (aP h2))→Fin (aF D (aP h2))→Fin (aF D (aY h2))→ℕ)×
    (Fin (aF D (aY h2))→Fin (aF D (aP h2))→Fin (aF D (bY h2))→ℕ)
abbrev DO (p:ℕ) {m:ℕ} (D:a9 m) (h2:2<D.1.val):Type:=
  (v:Fin (aF D (bY h2)))→Fin (p^bT D ⟨bY h2,v⟩)
def jN {p m:ℕ} (D:a9 m) (h2:2<D.1.val)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):ko D h2:=
  (fun j k v=>kM D C (aD (aW D) 0+j.val) (aD (aW D) 0+k.val)
      (aD (aW D) 1+v.val),
    fun j k v=>kM D C (aD (aW D) 1+j.val) (aD (aW D) 0+k.val)
      (aD (aW D) 2+v.val))
def qy {p m:ℕ} (n5:0<p) (D:a9 m) (h2:2<D.1.val)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    Fin (aF D (aP h2))×Fin (aF D (aP h2))→DO p D h2:=
  fun q v=> ⟨kM D C (aD (aW D) 0+q.1.val) (aD (aW D) 0+q.2.val)
      (aD (aW D) 2+v.val) % p^bT D ⟨bY h2,v⟩,W3 _ (XD n5 _)⟩
def mO {m:ℕ} (D:a9 m) (h2:2<D.1.val) (co:ℕ→ℕ) (x:ko D h2):
    ko D h2:=
  (fun j k v=>if j<k then x.1 j k v else 0,
    fun j k v=>if k.val≤ co j.val then x.2 j k v else 0)
def gP {m:ℕ} (D:a9 m) (h2:2<D.1.val) (f co:ℕ→ℕ):
    Finset (Fin (aF D (aP h2))×Fin (aF D (aP h2))):=
  ZU.filter (fun q=> ∃ j:Fin (aF D (aY h2)),q.1.val= f j.val∧q.2.val= co j.val)
def Cm {m:ℕ} (D:a9 m) (h2:2<D.1.val) (f co:ℕ→ℕ)
    (q:Fin (aF D (aP h2))×Fin (aF D (aP h2))) (v:Fin (aF D (aY h2))):ℕ:=
  if q.1.val= f v.val∧q.2.val= co v.val then 1 else 0
def iw {p m:ℕ} (D:a9 m) (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i:Fin D.1.val) (j v:Fin (aF D i)):ℕ:=
  acs D B (aD (aW D) i.val+j.val) (aD (aW D) i.val+v.val)
def wZ (p:ℕ) {m:ℕ} (D:a9 m) (h2:2<D.1.val)
    (b0:Fin (aF D (aP h2))→Fin (aF D (aP h2))→ℕ)
    (b1:Fin (aF D (aY h2))→Fin (aF D (aY h2))→ℕ)
    (b2:Fin (aF D (bY h2))→Fin (aF D (bY h2))→ℕ)
    (Dp:Finset (Fin (aF D (aP h2))×Fin (aF D (aP h2))))
    (w:Fin (aF D (aP h2))×Fin (aF D (aP h2))→Fin (aF D (aY h2))→ℕ):
    Set (ko D h2):=
  {x | (∃ (G:Type) (_:Group G) (_:Finite G) (g:aR D.1.val (aF D)→G)
      (S:aZ p (bT D) g),
      (∀ j v,(S.c_ ⟨aP h2,j⟩ ⟨aP h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.c_ ⟨aY h2,j⟩ ⟨aY h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.c_ ⟨bY h2,j⟩ ⟨bY h2,v⟩).val=b2 j v)∧
      (3<D.1.val∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨aP h2,j⟩) '' {j | (j:ℕ)<D.2.1.val}),
        ZA ((fun j=>g ⟨aP h2,j⟩) '' {j | (j:ℕ)<D.2.1.val})⁆⊔lcs G 2∧
      (∀ q∈Dp,S.iW h2 q.1 q.2=w q)∧
      x =(S.iW h2,S.lR h2))∧
    (∀ j k v,x.1 j k v<p^bT D ⟨aY h2,v⟩)∧
    (∀ j k v,x.2 j k v<p^bT D ⟨bY h2,v⟩)}
def lN (p:ℕ) {m:ℕ} (n5:0<p) (D:a9 m) (h2:2<D.1.val)
    (Dp:Finset (Fin (aF D (aP h2))×Fin (aF D (aP h2)))):
    Set (Fin (aF D (aP h2))×Fin (aF D (aP h2))→DO p D h2):=
  {c | ∀ q,q∉(ZU.filter
      (fun q:Fin (aF D (aP h2))×Fin (aF D (aP h2))=>q.1<q.2)) \ Dp→
    c q= fun _=> ⟨0,XD n5 _⟩}
structure Dq (p:ℕ) {m:ℕ} (n5:0<p) (D:a9 m) (h2:2<D.1.val)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)) (co:ℕ→ℕ)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):Prop where
  zero : ∀ i j k,kM D C i j k≠0→
    (i < j∧j<aD (aW D) 1∧aD (aW D) 1≤k∧k<aD (aW D) 3)∨
      (aD (aW D) 1≤ i∧i<aD (aW D) 2∧j<aD (aW D) 1∧
        aD (aW D) 2≤k∧k<aD (aW D) 3)
  bd:∀ i j k,kM D C i j k<p^qQ D k
  acB :∃ x∈wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2))
      (gP D h2 (dQ D) co) (Cm D h2 (dQ D) co),jN D h2 C=mO D h2 co x
  Kd:qy n5 D h2 C∈lN p n5 D h2 (gP D h2 (dQ D) co)
lemma aE.Qk {G:Type} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:aO}
    {X:Fin d.n→G} {r :ℕ→ℕ} (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m) {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.k_ hp m bZ bU hsum=⟨D,(B,C)⟩) (h2:2<D.1.val) (h3:D.1.val=3)
    (co:ℕ→ℕ) (EK:∀ j< r 1,b9 d r j= co j):
    Dq p hp.pos D h2 B co C:=by
 obtain ⟨cf1,cf2,cf3,cf4,cf5,cf6, -,cf8⟩:=hS.kS hp bZ bU hsum e
 have hn:d.n=aD r D.1.val:=by rw[← cf1]; exact hS.g6.symm
 have xO:∀ w≤D.1.val,aD r w=aD (aW D) w:=
   k9 (fun w hw=>cf3 w (by rw[cf1]; exact hw))
 have hn3:d.n=aD r 3:=by rw[hn,h3]
 have f1:=xO 1 (by omega)
 have f2:=xO 2 (by omega)
 have f3:=xO 3 (by omega)
 have e0:aD r 0=0:=rfl
 have e0':aD (aW D) 0=0:=rfl
 have e01:aD r 1=aD r 0+r 0:=dM r 0
 have e12:aD r 2=aD r 1+r 1:=dM r 1
 have j_:r 0=aW D 0:= cf3 0 (by rw[cf1]; omega)
 have jB:r 1=aW D 1:= cf3 1 (by rw[cf1]; omega)
 obtain ⟨g',S,hpw,HR,hl2,dG⟩:=hS.aaf hp hn h2 (aF D)
   (fun i=>cf3 i.val (by rw[cf1]; exact i.isLt)) (bT D) (fun k=>by
     show qQ D (aD (aW D) k.1.val+k.2.val)=_
     rw[cf4,xO _ k.1.isLt.le])
 have abb:∀ (i:Fin D.1.val) (j v:Fin (aF D i)),
     (S.c_ ⟨i,j⟩ ⟨i,v⟩).val=iw D B i j v:=by
  intro i j v
  rw[hpw, ← cf6]
  unfold iw
  rw[xO _ i.isLt.le]
 refine ⟨fun i j k h=>?_,fun i j k=>?_,
   ⟨(S.iW h2,S.lR h2),⟨⟨G,inferInstance,inferInstance,g',S,abb (aP h2),
     abb (aY h2),abb (bY h2),?_,?_,?_,rfl⟩,fun j k v=>Fin.isLt _,
     fun j k v=>Fin.isLt _⟩,?_⟩,?_⟩
 ·
   rw[cf5]at h
   have hz:=hS.u8 hn3 h
   rw[f1,f2,f3]at hz
   rcases hz with ⟨a1,a2,a3,a4⟩ | ⟨b1,b2,b3, -,b5,b6⟩
   · exact Y7 ⟨a1,a2,a3,a4⟩
   · exact XQ ⟨b1,b2,b3,b5,b6⟩
 ·
   rw[cf5, ← cf4]
   exact Q1 hp.pos hS.bounded i j k
 ·
   have hb:=hS.I7 hn (by omega)
   rw[h3]at hb
   exact XQ hb
 ·
   rw[← cf2]
   exact dG
 ·
   intro q hq
   obtain ⟨j,tM,zB⟩:=(ZI.mp hq).2
   have jW:j.val< r 1:=by
    have:j.val<aW D 1:=j.isLt
    omega
   rw[← cf8 _ jW]at tM
   rw[← EK _ jW]at zB
   have f5:q.1<q.2:=by
    show q.1.val<q.2.val
    rw[tM,zB]
    exact hS.qL bU jW
   funext v
   have hv:v.val< r 1:=by
    have:v.val<aW D 1:=v.isLt
    omega
   rw [HR q.1 q.2 v f5,e0,XL,XL,tM,zB,
     hS.JI hp bU jW]
   unfold Cm
   rw[tM,zB, ← cf8 _ hv, ← EK _ hv]
   by_cases hvj:v.val=j.val
   · rw[if_pos (by omega),if_pos ⟨by rw[hvj],by rw[hvj]⟩]
   · rw[if_neg (by omega),if_neg]
     rintro ⟨pL,jM⟩
     exact hvj (hS.y7 bU hv jW pL.symm jM.symm)
 ·
   refine V7 (funext fun j=>funext fun k=>funext fun v=>?_)
     (funext fun j=>funext fun k=>funext fun v=>?_)
   · show kM D C (aD (aW D) 0+j.val) (aD (aW D) 0+k.val)
         (aD (aW D) 1+v.val)=if j<k then S.iW h2 j k v else 0
     rw[cf5,e0', ← f1]
     split_ifs with uW
     · rw[HR j k v uW,e0]
     · by_contra d8
       have hj0:j.val<aW D 0:=j.isLt
       rcases hS.u8 hn3 d8 with ⟨a1, -⟩ | ⟨b1, -⟩
       · exact uW (by show j.val<k.val; omega)
       · omega
   · show kM D C (aD (aW D) 1+j.val) (aD (aW D) 0+k.val)
         (aD (aW D) 2+v.val)=if k.val≤ co j.val then S.lR h2 j k v else 0
     have tM:j.val< r 1:=by
      have:j.val<aW D 1:=j.isLt
      omega
     rw[cf5,e0', ← f1, ← f2, ← EK j.val tM]
     split_ifs with hk
     · rw[hl2 j k v hk,e0]
     · by_contra d8
       have Br :k.val<aW D 0:=k.isLt
       rcases hS.u8 hn3 d8 with ⟨a1,a2, -, -⟩ | ⟨-, -, -,b4, -, -⟩
       · omega
       · rw[Yb]at b4
         exact hk (by omega)
 ·
   simp only[lN,Set.mem_ofPred_eq]
   intro q hq
   funext v
   apply YL
   have hz:jd d q.1.val q.2.val (aD r 2+v.val)=0:=by
    by_cases f5:q.1<q.2
    · have hqD:q∈gP D h2 (dQ D) co:=by
        by_contra hc
        exact hq (Xq.mpr ⟨ZI.mpr ⟨Zb _,f5⟩,hc⟩)
      obtain ⟨j,tM,zB⟩:=(ZI.mp hqD).2
      have jW:j.val< r 1:=by
       have:j.val<aW D 1:=j.isLt
       omega
      rw[tM,zB, ← cf8 _ jW, ← EK _ jW,hS.JI hp bU jW,if_neg (by omega)]
    · by_contra d8
      have hq0:q.1.val<aW D 0:=q.1.isLt
      rcases hS.u8 hn3 d8 with ⟨a1, -⟩ | ⟨b1, -⟩
      · exact f5 a1
      · omega
   show kM D C (aD (aW D) 0+q.1.val) (aD (aW D) 0+q.2.val)
       (aD (aW D) 2+v.val) % p^bT D ⟨bY h2,v⟩=0
   rw[cf5,e0',XL,XL, ← f2,hz,Nat.zero_mod]
lemma JH {p m:ℕ} (n5:0<p) {D:a9 m} (h2:2<D.1.val)
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)} {co:ℕ→ℕ}
    {C C':Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hC:Dq p n5 D h2 B co C) (Ot:Dq p n5 D h2 B co C')
    (h1:jN D h2 C=jN D h2 C') (h3:qy n5 D h2 C=qy n5 D h2 C'):
    C=C':=by
 have e0:aD (aW D) 0=0:=rfl
 have e01:aD (aW D) 1=aD (aW D) 0+aW D 0:=dM _ 0
 have e12:aD (aW D) 2=aD (aW D) 1+aW D 1:=dM _ 1
 have e23:aD (aW D) 3=aD (aW D) 2+aW D 2:=dM _ 2
 have K1:∀ j0 k0 v (hj:j0<aW D 0) (hk:k0<aW D 0) (hv:v<aW D 1),
     kM D C (aD (aW D) 0+j0) (aD (aW D) 0+k0) (aD (aW D) 1+v)=
       kM D C' (aD (aW D) 0+j0) (aD (aW D) 0+k0) (aD (aW D) 1+v):=
   fun j0 k0 v hj hk hv=>congrFun (congrFun (congrFun (congrArg W9 h1)
     (⟨j0,hj⟩:Fin (aF D (aP h2)))) (⟨k0,hk⟩:Fin (aF D (aP h2))))
     (⟨v,hv⟩:Fin (aF D (aY h2)))
 have K2:∀ j0 k0 v (hj:j0<aW D 1) (hk:k0<aW D 0) (hv:v<aW D 2),
     kM D C (aD (aW D) 1+j0) (aD (aW D) 0+k0) (aD (aW D) 2+v)=
       kM D C' (aD (aW D) 1+j0) (aD (aW D) 0+k0) (aD (aW D) 2+v):=
   fun j0 k0 v hj hk hv=>congrFun (congrFun (congrFun (congrArg PO h1)
     (⟨j0,hj⟩:Fin (aF D (aY h2)))) (⟨k0,hk⟩:Fin (aF D (aP h2))))
     (⟨v,hv⟩:Fin (aF D (bY h2)))
 have K3 :∀ j0 k0 v (hj:j0<aW D 0) (hk:k0<aW D 0) (hv:v<aW D 2),
     kM D C (aD (aW D) 0+j0) (aD (aW D) 0+k0) (aD (aW D) 2+v) %
         p^qQ D (aD (aW D) 2+v)=
       kM D C' (aD (aW D) 0+j0) (aD (aW D) 0+k0) (aD (aW D) 2+v) %
         p^qQ D (aD (aW D) 2+v):=
   fun j0 k0 v hj hk hv=>congrArg Ty (congrFun (congrFun h3
     ((⟨j0,hj⟩:Fin (aF D (aP h2))),(⟨k0,hk⟩:Fin (aF D (aP h2)))))
     (⟨v,hv⟩:Fin (aF D (bY h2))))
 have key:∀ i j k,kM D C i j k=kM D C' i j k:=by
  intro i j k
  by_cases h0:kM D C i j k=0∧kM D C' i j k=0
  · rw[h0.1,h0.2]
  have hz:(i<j∧j<aD (aW D) 1∧aD (aW D) 1≤k∧k<aD (aW D) 3)∨
      (aD (aW D) 1≤ i∧i<aD (aW D) 2∧j<aD (aW D) 1∧
        aD (aW D) 2≤k∧k<aD (aW D) 3):=by
   rcases not_and_or.mp h0 with h | h
   · exact hC.zero i j k h
   · exact Ot.zero i j k h
  rcases hz with ⟨a1,a2,a3,a4⟩ | ⟨b1,b2,b3,b4,b5⟩
  · by_cases hk:k<aD (aW D) 2
    · have:=K1 i j (k - aD (aW D) 1) (by omega) (by omega) (by omega)
      rwa[e0,XL,XL,Wt a3]at this
    · have:=K3 i j (k - aD (aW D) 2) (by omega) (by omega) (by omega)
      rw [e0,XL,XL,
        Wt (show aD (aW D) 2≤k by omega)]at this
      rwa[Xw (hC.bd i j k),Xw (Ot.bd i j k)]at this
  · have:=K2 (i - aD (aW D) 1) j (k - aD (aW D) 2) (by omega) (by omega) (by omega)
    rwa[e0,XL,Wt b1,Wt b4]at this
 funext i j k
 apply YL
 rw[← M7 D C i j k, ← M7 D C' i j k]
 exact key _ _ _
lemma y8 {p m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (D:a9 m) (h2:2<D.1.val) (h3:D.1.val=3)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    (je hp T D B).ncard≤
      (∑ β ∈(ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 - aF D (aY h2))*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β))*
        p ^(((aF D (aP h2)).choose 2 - aF D (aY h2))*
          ∑ v,bT D ⟨bY h2,v⟩):=by
  rcases (je hp T D B).eq_empty_or_nonempty with hE | ⟨C0,hC0⟩
  · rw[hE,Y3]
    exact Zv _
  obtain ⟨G0, -,u0,d0,X0,r0,mJ,aaV,k6,aag,e0⟩:=hC0
  obtain ⟨c1,c2,c3, -, -, -,c7,c8⟩:=mJ.kS hp aaV k6 aag e0
  have hn0:d0.n=aD r0 D.1.val:=by rw[← c1]; exact mJ.g6.symm
  have FN:r0 0=aW D 0:= c3 0 (by rw[c1]; omega)
  have abw:r0 1=aW D 1:= c3 1 (by rw[c1]; omega)
  have abk:=(mJ.JR hn0 (by omega) mJ.vZ).1
  have u9:∀ C∈je hp T D B,Dq p hp.pos D h2 B (b9 d0 r0) C:=by
   rintro C ⟨G, -,u,d,X,r,hS,bZ,bU,hsum,e⟩
   obtain ⟨g1,g2,g3, -, -, -,g7, -⟩:=hS.kS hp bZ bU hsum e
   refine hS.Qk hp bZ bU hsum e h2 h3 _
     (zO hS mJ bU (g2.trans c2.symm) ?_ ?_)
   · rw[g3 1 (by rw[g1]; omega),abw]
   · intro k hk
     rw[g7 k hk,c7 k (by rw[c2, ← g2]; exact hk)]
  have jW:∀ j:Fin (aF D (aY h2)),j.val< r0 1:= fun j=>by
    have:j.val<aW D 1:=j.isLt
    omega
  have En:∀ q∈gP D h2 (dQ D) (b9 d0 r0),q.1<q.2∧(q.1:ℕ)<D.2.1.val:=by
   intro q hq
   obtain ⟨j,tM,zB⟩:=(ZI.mp hq).2
   rw[← c8 _ (jW j)]at tM
   refine ⟨?_,?_⟩
   · show q.1.val<q.2.val
     rw[tM,zB]
     exact mJ.qL k6 (jW j)
   · rw[tM, ← c2]
     have:=mJ.DN k6 j.val (jW j)
     omega
  have s8:∀ j:Fin (aF D (aY h2)),dQ D j.val<aF D (aP h2):=by
   intro j
   show dQ D j.val<aW D 0
   rw[← c8 _ (jW j), ← FN]
   have:=mJ.DN k6 j.val (jW j)
   omega
  have uj:∀ j:Fin (aF D (aY h2)),b9 d0 r0 j.val<aF D (aP h2):=by
   intro j
   show b9 d0 r0 j.val<aW D 0
   rw[← FN]
   have:=mJ.jC k6 j.val (jW j)
   omega
  obtain ⟨F,hF⟩:∃ F:Fin (aF D (aY h2))→
      Fin (aF D (aP h2))×Fin (aF D (aP h2)),
      ∀ j,(F j).1.val=dQ D j.val∧(F j).2.val=b9 d0 r0 j.val:=
    ⟨fun j=> (⟨_,s8 j⟩,⟨_,uj j⟩),fun j=> ⟨rfl,rfl⟩⟩
  have Qm:Z8 F:=by
   intro j j' Er
   have e1:dQ D j.val=dQ D j'.val:=by rw[← (hF j).1, ← (hF j').1,Er]
   have e2:b9 d0 r0 j.val=b9 d0 r0 j'.val:=by rw[← (hF j).2, ← (hF j').2,Er]
   rw[← c8 _ (jW j), ← c8 _ (jW j')]at e1
   exact YL (mJ.y7 k6 (jW j) (jW j') e1 e2)
  have qv:gP D h2 (dQ D) (b9 d0 r0)=ZU.image F:=by
   ext q
   simp only[gP,ZI,Zb,true_and,Xp]
   constructor
   · rintro ⟨j,h1,jM⟩
     exact ⟨j,V7 (YL ((hF j).1.trans h1.symm)) (YL ((hF j).2.trans jM.symm))⟩
   · rintro ⟨j,rfl⟩
     exact ⟨j,(hF j).1,(hF j).2⟩
  have zE:(gP D h2 (dQ D) (b9 d0 r0)).card=aF D (aY h2):=by
   rw[qv,XG _ Qm,Y4,Zz]
  have abK:=v6 (p:=p) (c:=D.1.val) (r :=aF D) (a:=bT D) hp h2
    (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2)) (s:=D.2.1.val)
    (by show D.2.1.val≤aW D 0; rw[← c2, ← FN]; exact abk)
    (gP D h2 (dQ D) (b9 d0 r0)) En (Cm D h2 (dQ D) (b9 d0 r0))
    (wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2))
      (gP D h2 (dQ D) (b9 d0 r0)) (Cm D h2 (dQ D) (b9 d0 r0))) (fun x hx =>hx.1)
  rw[zE]at abK
  have I9:=rG (Γ:=DO p D h2)
    (m6 (p:=p) (fun v:Fin (aF D (bY h2))=>bT D ⟨bY h2,v⟩))
    (gP D h2 (dQ D) (b9 d0 r0)) (fun q hq=> (En q hq).1)
    (fun _ _=> ⟨0,XD hp.pos _⟩)
  rw[zE]at I9
  have hΛfin:(wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2))
      (gP D h2 (dQ D) (b9 d0 r0)) (Cm D h2 (dQ D) (b9 d0 r0))).Finite:=by
   refine (OY (fun y:(Fin (aF D (aP h2))→Fin (aF D (aP h2))→
       (v:Fin (aF D (aY h2)))→Fin (p^bT D ⟨aY h2,v⟩))×
       (Fin (aF D (aY h2))→Fin (aF D (aP h2))→
         (v:Fin (aF D (bY h2)))→Fin (p^bT D ⟨bY h2,v⟩))=>
       ((fun j k v=> (y.1 j k v).val,fun j k v=> (y.2 j k v).val):ko D h2))).subset ?_
   rintro x ⟨-,Lg,hx2⟩
   exact ⟨(fun j k v=> ⟨x.1 j k v,Lg j k v⟩,fun j k v=> ⟨x.2 j k v,hx2 j k v⟩),rfl⟩
  have eW:WP (fun C=> (jN D h2 C,qy hp.pos D h2 C))
      (je hp T D B):=by
    intro C hC C' Ot he
    exact JH hp.pos h2 (u9 C hC) (u9 C' Ot) (congrArg W9 he)
      (congrArg PO he)
  have oc:∀ C∈je hp T D B,(fun C=> (jN D h2 C,qy hp.pos D h2 C)) C∈
      (mO D h2 (b9 d0 r0) '' wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2))
        (iw D B (bY h2)) (gP D h2 (dQ D) (b9 d0 r0))
        (Cm D h2 (dQ D) (b9 d0 r0)))×ˢ
        lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0)):=by
    intro C hC
    obtain ⟨x,hx,Cv⟩:=(u9 C hC).acB
    show (jN D h2 C,qy hp.pos D h2 C)∈_
    exact Sj ⟨x,hx,Cv.symm⟩ (u9 C hC).Kd
  calc (je hp T D B).ncard
      ≤ ((mO D h2 (b9 d0 r0) '' wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2))
          (iw D B (bY h2)) (gP D h2 (dQ D) (b9 d0 r0))
          (Cm D h2 (dQ D) (b9 d0 r0)))×ˢ
          lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=
        YM _ oc eW
          ((hΛfin.image (mO D h2 (b9 d0 r0))).prod (Zl _))
    _= (mO D h2 (b9 d0 r0) '' wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2))
          (iw D B (bY h2)) (gP D h2 (dQ D) (b9 d0 r0))
          (Cm D h2 (dQ D) (b9 d0 r0))).ncard*
          (lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=RM
    _ ≤ (wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2))
          (iw D B (bY h2)) (gP D h2 (dQ D) (b9 d0 r0))
          (Cm D h2 (dQ D) (b9 d0 r0))).ncard*
          (lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=
        Za _ (Tm hΛfin)
    _≤_:=Zr abK I9
end LfCBCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section LfsTransport
variable {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
end LfsTransport
section LfsIdent
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G} {S:aZ p a g} {h2:2<c}
  {b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ}
  {b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ} {b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ}
end LfsIdent
section LfsLeadCount
variable {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
end LfsLeadCount
section LfsGroup
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
end LfsGroup
section LfsCount
end LfsCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
section CNT3MainDefs
def Jk {m:ℕ} (r1 r2 s m2 m3:ℕ) (D:a9 m):Prop:=
  ∃ h2:2<D.1.val,D.1.val=3∧D.2.1.val=s∧aF D (aP h2)=r1∧
    aF D (aY h2)=r2∧(∑ v,bT D ⟨aY h2,v⟩)=m2 - m3∧
    (∑ v,bT D ⟨bY h2,v⟩)=m3
def m5 (s m2 m3:ℕ):Finset ℕ:=
  (ZM (min (m2 - m3) m3+1)).filter (fun β=>m3≤ s*β)
def pI (r1 r2 s m2 m3 b2:ℕ):ℕ:=
  2 ^ (s*(b2*(r2+m3+1 - b2)))*
    2 ^((r1.choose 2 - r2)*(m2 - m3) - (r1 - s).choose 2*b2)*
      2^((r1.choose 2 - r2)*m3)
def abP:Prop:=
  ∀ m r1 r2 s lam m2 m3 r3:ℕ,∀ G∈fF m r1 r2 s lam m2 m3 r3,
    ∃ D:cQ 2 m,dW Ze m G D ∧Jk r1 r2 s m2 m3 D.1∧
      kC (bT D.1)≤kv r1 r2 r3 lam m2 m3
def abY:Prop:=
  ∃ C0:ℝ,∀ m:ℕ,1≤ m→
    (Zq (a9 m):ℝ)≤(2:ℝ)^(C0*m*((YZ 2 m:ℝ)+1))
end CNT3MainDefs
section CNT3MainArith
lemma Fe {s m2 m3 β:ℕ}:
    β∈m5 s m2 m3↔β≤ min (m2 - m3) m3∧m3≤ s*β:=by
 unfold m5
 rw[ZI,Zt,Nat.lt_add_one_iff]
lemma Gw (s m2 m3:ℕ):(m5 s m2 m3).card≤ min (m2 - m3) m3+1:=
  (Rd _ _).trans (Xf _).le
lemma qK (n:ℕ):(n+1).choose 2=n+n.choose 2:=by
 have h:=Uq n 1
 rw[U6]at h
 exact h
lemma yQ (a b:ℕ):a.choose 2+b.choose 2≤(a+b).choose 2:=by
 induction b with
 | zero=>rw[T8,Nat.choose_eq_zero_of_lt (by norm_num:0<2),T8]
 | succ b ih=>
   rw[← Nat.add_assoc,qK (a+b),qK b]
   omega
lemma oG (e:ℕ):((2^e:ℕ):ℝ)=(2:ℝ)^(e:ℝ):=by
 rw[Wl]
 norm_cast
lemma J9 {r1 r2 s m2 m3 β:ℕ} (kB:s≤ r1) (q7:r2≤ s.choose 2)
    (MG:m3≤ m2) (uj:β≤ m2 - m3) (hb3:β≤ m3):
    (pI r1 r2 s m2 m3 β:ℝ)=(2:ℝ)^(oB r1 r2 s m2 m3 β):=by
 have hK:(r1 - s).choose 2+s.choose 2≤ r1.choose 2:=by
  have:=yQ (r1 - s) s
  rwa[Vf kB]at this
 have hC:r2≤ r1.choose 2:=by omega
 have hKb:(r1 - s).choose 2*β≤(r1.choose 2 - r2)*(m2 - m3):=
   Zr (by omega) uj
 have s8:β≤ r2+m3+1:=by omega
 have e :pI r1 r2 s m2 m3 β=2^(s*(β *(r2+m3+1 - β))+
     ((r1.choose 2 - r2)*(m2 - m3) - (r1 - s).choose 2*β)+
       (r1.choose 2 - r2)*m3):=by
  unfold pI
  rw[Xh,Xh]
 rw[e,oG]
 congr 1
 unfold oB
 push_cast[UN hKb,UN hC,UN MG,UN s8]
 ring
lemma Fo {I:Finset ℕ} {n:ℕ} (hI:I.card≤n+1) (g e:ℕ→ℝ) (b:ℕ)
    (hg:∀ β∈I,g β≤(2:ℝ)^(e β)) (hb:∀ β∈I,e β≤e b):
    ∑ β∈I,g β≤((n:ℝ)+1)*(2:ℝ)^(e b):=by
 calc ∑ β∈I,g β≤∑ _β∈I,(2:ℝ)^(e b):=Z9 fun β h=>
       (hg β h).trans (Wm (by norm_num) (hb β h))
   _=(I.card:ℝ)*(2:ℝ)^(e b):=by rw[Y5,nsmul_eq_mul]
   _ ≤ ((n:ℝ)+1)*(2:ℝ)^(e b):=by
       gcongr
       exact_mod_cast hI
lemma QJ {N m n PW:ℕ} {C0 E:ℝ}
    (hD:∀ m:ℕ,1≤ m→
      (Zq (a9 m):ℝ)≤(2:ℝ)^(C0*m*((YZ 2 m:ℝ)+1)))
    (hm:1≤ m) (hn:n≤ m) (hN:1≤N)
    (h:(N:ℝ)≤(Zq (a9 m):ℝ)*2^PW*(((n:ℝ)+1)*(2:ℝ)^E)):
    OM 2 (N:ℝ)≤(C0+1)*(m:ℝ)*((YZ 2 m:ℝ)+1)+(PW:ℝ)+E:=by
 have h1:=hD m hm
 have h2n:n+1≤2^(YZ 2 m+1):=by
  have h':m<2^(YZ 2 m+1):=V6 (by norm_num) m
  omega
 have hL:(n:ℝ)+1≤(2:ℝ)^((YZ 2 m:ℝ)+1):=by
  have h':((n+1:ℕ):ℝ)≤((2^(YZ 2 m+1):ℕ):ℝ):=by exact_mod_cast h2n
  rw[oG]at h'
  push_cast at h'
  exact h'
 have adK:(2:ℝ)^PW=(2:ℝ)^(PW:ℝ):=(Wl 2 PW).symm
 have adf:(0:ℝ)<N:=by exact_mod_cast hN
 have hm':(1:ℝ)≤ m:=by exact_mod_cast hm
 have zv:(0:ℝ)≤(YZ 2 m:ℝ):= Om _
 rw[Real.logb_le_iff_le_rpow (by norm_num) adf]
 calc (N :ℝ)≤(Zq (a9 m):ℝ)*2^PW*(((n:ℝ)+1)*(2:ℝ)^E):=h
   _ ≤ (2 :ℝ)^(C0*m*((YZ 2 m:ℝ)+1))*(2:ℝ)^(PW:ℝ)*
         ((2:ℝ)^((YZ 2 m:ℝ)+1)*(2:ℝ)^E):=by
       rw[adK]
       gcongr
   _ = (2 :ℝ)^(C0*m*((YZ 2 m:ℝ)+1)+(PW:ℝ)+
         (((YZ 2 m:ℝ)+1)+E)):=by
       rw [← Vw (by norm_num), ← Vw (by norm_num),
         ← Vw (by norm_num)]
   _ ≤ (2:ℝ)^((C0+1)*(m:ℝ)*((YZ 2 m:ℝ)+1)+(PW:ℝ)+E):=by
       apply Wm (by norm_num)
       nlinarith[mul_nonneg (sub_nonneg.mpr hm') zv]
lemma ab4:abY:=by
 refine ⟨7,fun m hm=>?_⟩
 have h1:=B4 m hm
 have f5:m<2^(YZ 2 m+1):=V6 (by norm_num) m
 have h2:(m+1)^(5*m+2)≤2^((YZ 2 m+1)*(5*m+2)):=by
  rw[X5]
  exact XR (by omega) _
 have h3:(YZ 2 m+1)*(5*m+2)≤7*m*(YZ 2 m+1):=by
  rw[Nat.mul_comm (YZ 2 m+1)]
  exact Za _ (by omega)
 have h4:Zq (a9 m)≤2^(7*m*(YZ 2 m+1)):=
   h1.trans (h2.trans (Zk (by norm_num) h3))
 calc (Zq (a9 m):ℝ)≤((2^(7*m*(YZ 2 m+1)):ℕ):ℝ):=by
       exact_mod_cast h4
   _ = (2:ℝ)^((7:ℝ)*m*((YZ 2 m:ℝ)+1)):=by
       rw[oG]
       congr 1
       norm_num
end CNT3MainArith
section CNT3MainCount
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma KB (D:a9 m) (hL:Jk r1 r2 s m2 m3 D)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)):
    (je Ze (fF m r1 r2 s lam m2 m3 r3) D B).ncard≤
      ∑ β∈m5 s m2 m3,pI r1 r2 s m2 m3 β:=by
 obtain ⟨h2,h3,hs,jB,q7,bU,hs3⟩:=hL
 have h:=y8 Ze (fF m r1 r2 s lam m2 m3 r3) D h2 h3 B
 rw[bU,hs3,jB,q7]at h
 refine h.trans (WT ?_)
 rw[hs,Wi]
 rfl
lemma Z_ (hPW:abP) (d8:(fF m r1 r2 s lam m2 m3 r3).Nonempty):
    1 ≤ m∧s≤ r1∧r2≤ s.choose 2∧m3≤ m2∧r2≤ m2 - m3∧
      (m5 s m2 m3).Nonempty∧1≤(f8 m r1 r2 s lam m2 m3 r3).ncard:=by
 obtain ⟨G,hG⟩:=d8
 have hm:=Ci hG
 obtain ⟨c1,c2, -,c4, -, -⟩:=wT hG
 have:Fact (Vd 2):=⟨Ze⟩
 obtain ⟨-, -, -, -, -, -, -,w8,ED, -⟩:=(jc G).mp hG
 have MG:m3≤ m2:=by
  have cO:ZB (lcs G 2)≤ZB (lcs G 1):=
    YG (bC (by norm_num))
  rw[w8,ED]at cO
  exact lD (p:=2) (Tw 2) cO
 obtain ⟨Df,xP,hL, -⟩:=hPW m r1 r2 s lam m2 m3 r3 G hG
 have adc:r2≤ m2 - m3:=by
  obtain ⟨h2, -, -, -,q7,bU, -⟩:=hL
  have hsum:∑ _v:Fin (aF Df.1 (aY h2)),1≤∑ v,bT Df.1 ⟨aY h2,v⟩:=
    Z9 fun v _=>CX Df.1 _
  have dS:∑ _v:Fin (aF Df.1 (aY h2)),(1:ℕ)=aF Df.1 (aY h2):=by
   rw[Y5,Y4,Zz,smul_eq_mul,UH]
  omega
 have hC:Df.2.2∈je Ze (fF m r1 r2 s lam m2 m3 r3) Df.1 Df.2.1:=
   ⟨G,hG,xP⟩
 have hA:=KB (lam:=lam) (r3:=r3) Df.1 hL Df.2.1
 have rV:0<
     (je Ze (fF m r1 r2 s lam m2 m3 r3) Df.1 Df.2.1).ncard:=
   (Set.ncard_pos (Zl _)).mpr ⟨Df.2.2,hC⟩
 have abj:(m5 s m2 m3).Nonempty:=by
  rcases Finset.eq_empty_or_nonempty (m5 s m2 m3) with h | h
  · rw[h,P7]at hA
    omega
  · exact h
 have Dh:1≤(f8 m r1 r2 s lam m2 m3 r3).ncard:=
   (Set.ncard_pos tL).mpr ⟨_,G,hG,rfl⟩
 exact ⟨by omega,c2,c4,MG,adc,abj,Dh⟩
end CNT3MainCount
section CNT3MainThm
end CNT3MainThm
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section C3PWArith
lemma Ec {c:ℕ} {r :Fin c→ℕ} (a:aR c r→ℕ) (hc:c=3)
    (R0 R1 R2 S0 S1 S2:ℕ)
    (hr :∀ i:Fin c,r i=if i.val=0 then R0 else if i.val=1 then R1 else R2)
    (hs:∀ i:Fin c,sL a i=if i.val=0 then S0 else if i.val=1 then S1 else S2):
    kC a=(R0*(S1+S2)+(R0 - 1)*(S0 - R0))+(R1*S2+(R1 - 1)*(S1 - R1))+
      (R2 - 1)*(S2 - R2):=by
  subst hc
  have j_:r 0=R0:=by simp +decide [hr]
  have jB:r 1=R1:=by simp +decide [hr]
  have q7:r 2=R2:=by simp +decide [hr]
  have k6:sL a 0=S0:=by simp +decide [hs]
  have O9:sL a 1=S1:=by simp +decide [hs]
  have bU:sL a 2=S2:=by simp +decide [hs]
  have hm0:nQ a 0=S1+S2:=by
   unfold nQ
   rw[Xd,Vh]
   simp +decide [O9,bU]
  have hm1:nQ a 1=S2:=by
   unfold nQ
   rw[Xd,Vh]
   simp +decide [bU]
  have w8:nQ a 2=0:=by
   unfold nQ
   rw[Xd,Vh]
   simp +decide
  unfold kC
  simp only[Vh,hm0,hm1,w8,k6,O9,bU,j_,jB,q7]
  ring
end C3PWArith
section C3Layer
lemma n6 {H:Type u} [Group H] (i:ℕ):
    ZB (e7 H i)*ZB (lcs H (i+1))=ZB (lcs H i):=by
 have h1:=Z4 ((lcs H (i+1)).subgroupOf (lcs H i))
 have h2:=YJ (XM
   (bC (XV i):lcs H (i+1)≤lcs H i)).toEquiv
 rw[h2]at h1
 rw[mul_comm]
 exact h1
lemma nW {p m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:a9 m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:dW hp m H (⟨D,(B,C)⟩:cQ p m)) (i:Fin D.1.val)
    (hlast:i.val+1<D.1.val∨lcs H (i.val+1)=⊥):
    ZB (e7 H i.val)=p^sL (bT D) i:=by
 obtain ⟨u,d,X,r,hS,bZ,bU,hsum,e⟩:=hc
 obtain ⟨c1, -,c3,c4, -⟩:=hS.kS hp bZ bU hsum e
 have hn:d.n=aD r hS.nL:=hS.g6.symm
 have hi:i.val<hS.nL:=by rw[c1]; exact i.isLt
 have hl:i.val+1<hS.nL∨lcs H (i.val+1)=⊥:=by rw[c1]; exact hlast
 have h:=(hS.toaZ hp hn).Bz hp.pos ⟨i.val,hi⟩ hl
 refine h.trans ?_
 congr 1
 show ∑ v:Fin (r i.val),d.a (hS.aV hn ⟨⟨i.val,hi⟩,v⟩)=
   ∑ v:Fin (aW D i.val),qQ D (aD (aW D) i.val+v.val)
 have e1:∑ v:Fin (r i.val),d.a (hS.aV hn ⟨⟨i.val,hi⟩,v⟩)=
     ∑ v:Fin (r i.val),lL d (aD r i.val+v.val):=
   Zw rfl (fun v _=> (hS.sI hn ⟨⟨i.val,hi⟩,v⟩).symm)
 rw [e1,XF (fun v=>lL d (aD r i.val+v)) (r i.val),
   XF (fun v=>qQ D (aD (aW D) i.val+v)) (aW D i.val),
   c3 i.val hi,k9 (c:=i.val) (fun w hw=>c3 w (by omega)) i.val YD,c4]
end C3Layer
section C3Ranks
variable {G:Type u} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:aO}
  {X:Fin d.n→G} {r :ℕ→ℕ}
lemma aE.abA (hp:p.Prime) (hS:aE p u d X r) (bU:2≤d.s)
    (h3:lcs G 2≠⊥) (h4:lcs G 3=⊥):hS.nL=3:=by
 have h1:=hS.tA bU
 rcases XU hS.nL 4 with f5 | Ep
 · rcases (show hS.nL=2∨hS.nL=3 by omega) with h | h
   · exfalso
     have hb:=hS.I7 hS.g6.symm (by omega)
     rw[h]at hb
     exact h3 hb
   · exact h
 · exfalso
   have rV:=hS.Nq hp 3 (by omega)
   have dS:=hS.kV 3
   rw[h4,Wf]at dS
   have hK:1≤ZB (dC p G 3):=Xi
   have hP:p≤p^r 3:=by
    calc p=p^1:=(pow_one p).symm
      _≤p^r 3:=Zk hp.pos rV
   have hm:=Zr hP hK
   rw[UH,dS]at hm
   have:=hp.two_le
   omega
lemma aE.abe (hp:p.Prime) (hS:aE p u d X r):r 0=ZV G:=by
 have:Fact p.Prime:=⟨hp⟩
 have nD:IsPGroup p G:=YK hS.e9.card
 have h1:p^r 0*ZB (cE p G)=ZB (lcs G 0):=hS.kV 0
 have h2:=VO (frattini G)
 rw[k5 nD,ew nD]at h2
 have h3:ZB (lcs G 0)=ZB G:=by rw[lcs_zero,Yn]
 have h4:0<ZB (cE p G):=Xi
 have h6:p^r 0*ZB (cE p G)=p^ZV G*ZB (cE p G):=by
  rw[← h2, ← h3,h1]
 exact Zd hp.two_le (Yc h4 h6)
lemma aE.aa8 [hp:Fact p.Prime] (hS:aE p u d X r):r 1=r2 p G:=by
 have h1:p^r 1*ZB (pN p G)=ZB (lcs G 1):=hS.kV 1
 have h2:ZB (lcs G 1)=ZB (pN p G)*p^r2 p G:=xT
 have h4:0<ZB (pN p G):=Xi
 have h6:p^r 1*ZB (pN p G)=p^r2 p G*ZB (pN p G):=by
  rw[h1,h2,mul_comm]
 exact Zd hp.out.two_le (Yc h4 h6)
omit [Finite G] in
lemma rJ (h4:lcs G 3=⊥):commutator (lcs G 2)=⊥:=by
 rw[eq_bot_iff,WE,Z7]
 intro x _ y _
 rw[WB]
 have h:⁅(x:G),(y:G)⁆∈lcs G 3:=a8 x.2 (y:G)
 rw[h4,WB]at h
 have e:((⁅x,y⁆:lcs G 2):G)=⁅(x:G),(y:G)⁆:=by
  simp only[commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv]
 exact Zu (e.trans h)
lemma aE.abd (hp:p.Prime) (hS:aE p u d X r) (h4:lcs G 3=⊥):
    r 2=ZV (lcs G 2):=by
 have:Fact p.Prime:=⟨hp⟩
 have nD:IsPGroup p G:=YK hS.e9.card
 have hK:IsPGroup p (lcs G 2):=nD.to_subgroup _
 have vG:=rJ h4
 have Nm:(cE p (lcs G 2)).map (lcs G 2).subtype=dC p G 2:=by
  show (ZA (ZF (fun g:lcs G 2=>g^p))⊔
      commutator (lcs G 2)).map (lcs G 2).subtype=
    lcs G 3⊔ZA (ZF (fun g:lcs G 2=> (g:G)^p))
  rw[vG,sup_bot_eq,h4,bot_sup_eq,XT, ← WJ]
  refine congrArg ZA (congrArg ZF ?_)
  funext g
  exact map_pow (lcs G 2).subtype g p
 have lT:ZB ((cE p (lcs G 2)).map (lcs G 2).subtype)=
     ZB (cE p (lcs G 2)):=
   (YJ (Subgroup.equivMapOfInjective _ _ (lcs G 2).subtype_injective).toEquiv).symm
 rw[Nm]at lT
 have h1:p^r 2*ZB (dC p G 2)=ZB (lcs G 2):=hS.kV 2
 have h2:=Z4 (cE p (lcs G 2))
 have h3:(cE p (lcs G 2)).index =p^ZV (lcs G 2):= oA hK
 rw[h3]at h2
 have h5:0<ZB (cE p (lcs G 2)):=Xi
 have h6:p^r 2*ZB (cE p (lcs G 2))=
     p^ZV (lcs G 2)*ZB (cE p (lcs G 2)):=
   calc p^r 2*ZB (cE p (lcs G 2))=p^r 2*ZB (dC p G 2):=by rw[lT]
     _=ZB (lcs G 2):=h1
     _=ZB (cE p (lcs G 2))*p^ZV (lcs G 2):=h2.symm
     _=p^ZV (lcs G 2)*ZB (cE p (lcs G 2)):=mul_comm _ _
 exact Zd hp.two_le (Yc h5 h6)
omit [Finite G] in
lemma aE.KI (hS:aE p u d X r):bD G≤d.s:=by
 unfold bD
 apply WK
 refine ⟨fun i:Fin d.s=>u i.val,?_⟩
 have e:ZF (fun i:Fin d.s=>u i.val)=u '' ZH d.s:=by
   ext y
   constructor
   · rintro ⟨i,rfl⟩
     exact ⟨i.val,i.isLt,rfl⟩
   · rintro ⟨i,hi,rfl⟩
     exact ⟨⟨i,hi⟩,rfl⟩
 rw[e]
 exact hS.vZ
end C3Ranks
section CNT3Codes
variable {m r1 r2 s lam m2 m3 r3:ℕ}
noncomputable def lV (m r1 r2 s lam m2 m3 r3:ℕ):Finset (a9 m):=by
 classical
 exact ZU.filter (fun D =>D.2.1.val=s∧∃ G∈fF m r1 r2 s lam m2 m3 r3,
   ∃ x:(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m))×
     (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)),
     dW Ze m G (⟨D,x⟩:cQ 2 m))
lemma tW {D:a9 m}:
    D ∈ lV m r1 r2 s lam m2 m3 r3↔D.2.1.val=s∧∃ G∈fF m r1 r2 s lam m2 m3 r3,
      ∃ x:(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m))×
        (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)),
        dW Ze m G (⟨D,x⟩:cQ 2 m):=by
 simp only[lV,ZI,Zb,true_and]
lemma abZ:∀ G∈fF m r1 r2 s lam m2 m3 r3,∃ D:cQ 2 m,
    dW Ze m G D ∧D.1∈lV m r1 r2 s lam m2 m3 r3:=by
 intro G hG
 have:Fact (Vd 2):=⟨Ze⟩
 have hsG:bD G=s:=((jc G).mp hG).2.2.2.2.2.1
 have wJ:lcs G 1≠⊥:=by
  intro h
  apply hG.2.1
  rw[eq_bot_iff, ← h]
  exact bC (by norm_num)
 obtain ⟨u,d,X,r,bU,oW, -, -, -, -,bZ, -,hS⟩:=qW Ze hG.1 wJ
 have hsum:∑ t,d.a t=m:=by
  have h1:=hS.e9.card
  rw[hG.1]at h1
  exact (Zd (Tw 2) h1).symm
 have C5:2≤d.s:=by rw[oW]; exact bU
 have hc:dW Ze m G (hS.k_ Ze m bZ C5 hsum):=
   ⟨u,d,X,r,hS,bZ,C5,hsum,rfl⟩
 have hDs:(hS.k_ Ze m bZ C5 hsum).1.2.1.val=s:= oW.trans hsG
 exact ⟨_,hc,tW.mpr ⟨hDs,G,hG,(hS.k_ Ze m bZ C5 hsum).2,hc⟩⟩
lemma xQ {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3)
    {D:a9 m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)}
    (hc:dW Ze m G (⟨D,(B,C)⟩:cQ 2 m)):
    D.1.val=3∧aW D 0=r1∧aW D 1=r2∧aW D 2=r3∧s≤D.2.1.val∧m3≤ m2∧
      (∀ h:0<D.1.val,sL (bT D) ⟨0,h⟩=r1+lam)∧
      (∀ h:1<D.1.val,sL (bT D) ⟨1,h⟩=m2 - m3)∧
      (∀ h:2<D.1.val,sL (bT D) ⟨2,h⟩=m3):=by
 have:Fact (Vd 2):=⟨Ze⟩
 obtain ⟨dS,h3,h4,jB,q7,hs, -,w8,ED,hr3⟩:=(jc G).mp hG
 have hm:=Ci hG
 have hc':=hc
 obtain ⟨u,d,X,r,hS,bZ,bU,hsum,e⟩:=hc
 obtain ⟨c1,c2,c3, -⟩:=hS.kS Ze bZ bU hsum e
 have hnL:=hS.abA Ze bU h3 h4
 have hD3:D.1.val=3:= c1.symm.trans hnL
 have L1:∀ h:1<D.1.val,sL (bT D) ⟨1,h⟩+m3=m2:=by
  intro h
  have a1:ZB (e7 G 1)=2^sL (bT D) ⟨1,h⟩:=
    nW Ze hc' ⟨1,h⟩ (Y7 (show 1+1<D.1.val by omega))
  have a2:ZB (e7 G 1)*ZB (lcs G 2)=ZB (lcs G 1):=
    n6 1
  rw[a1,w8,ED, ← Xh]at a2
  exact Zd (Tw 2) a2
 have h1D:1<D.1.val:=by omega
 have aee:m3≤ m2:=by
  have:=L1 h1D
  omega
 refine ⟨hD3,?_,?_,?_,?_,aee,?_,?_,?_⟩
 · rw[← c3 0 (by omega),hS.abe Ze,jB]
 · rw[← c3 1 (by omega),hS.aa8,q7]
 · rw[← c3 2 (by omega),hS.abd Ze h4,hr3]
 · rw[← c2, ← hs]
   exact hS.KI
 · intro h
   have a1:ZB (e7 G 0)=2^sL (bT D) ⟨0,h⟩:=
     nW Ze hc' ⟨0,h⟩ (Y7 (show 0+1<D.1.val by omega))
   have a2:ZB (e7 G 0)*ZB (lcs G 1)=ZB (lcs G 0):=
     n6 0
   rw[a1,w8,lcs_zero,Yn,dS, ← Xh]at a2
   have:=Zd (Tw 2) a2
   omega
 · intro h
   have:=L1 h
   omega
 · intro h
   have a1:ZB (e7 G 2)=2^sL (bT D) ⟨2,h⟩:=
     nW Ze hc' ⟨2,h⟩ (XQ h4)
   have a2:ZB (e7 G 2)*ZB (lcs G 3)=ZB (lcs G 2):=
     n6 2
   rw[a1,h4,Wf,UH,ED]at a2
   exact Zd (Tw 2) a2
lemma l8 {D:a9 m} (hD:D∈lV m r1 r2 s lam m2 m3 r3):
    D.1.val=3∧aW D 0=r1∧aW D 1=r2∧aW D 2=r3∧D.2.1.val=s∧m3≤ m2∧
      (∀ h:0<D.1.val,sL (bT D) ⟨0,h⟩=r1+lam)∧
      (∀ h:1<D.1.val,sL (bT D) ⟨1,h⟩=m2 - m3)∧
      (∀ h:2<D.1.val,sL (bT D) ⟨2,h⟩=m3):=by
 obtain ⟨hDs,G,hG,⟨B,C⟩,hc⟩:=tW.mp hD
 obtain ⟨a1,a2,a3,a4, -,a6⟩:=xQ hG hc
 exact ⟨a1,a2,a3,a4,hDs,a6⟩
lemma BL {D:a9 m} (hD:D∈lV m r1 r2 s lam m2 m3 r3)
    (h2:2<D.1.val):
    aF D (aP h2)=r1∧aF D (aY h2)=r2∧aF D (bY h2)=r3∧
      D.2.1.val=s∧m3≤ m2∧
      ∑ v,bT D ⟨aP h2,v⟩=r1+lam∧∑ v,bT D ⟨aY h2,v⟩=m2 - m3∧
      ∑ v,bT D ⟨bY h2,v⟩=m3:=by
 obtain ⟨-,hR0,hR1,hR2,hs,hm,mJ,MQ,Mz⟩:=l8 hD
 exact ⟨hR0,hR1,hR2,hs,hm,mJ (by omega),MQ (by omega),Mz h2⟩
lemma Ie {D:a9 m} (hD:D∈lV m r1 r2 s lam m2 m3 r3):
    kC (bT D)=kv r1 r2 r3 lam m2 m3:=by
 obtain ⟨h3,hR0,hR1,hR2, -,hm,mJ,MQ,Mz⟩:=l8 hD
 rw[Ec (bT D) h3 r1 r2 r3 (r1+lam) (m2 - m3) m3 ?_ ?_]
 · unfold kv
   rw[Vf hm,Yb]
 · rintro ⟨i,hi⟩
   have:i<3:=by omega
   interval_cases i
   · show aW D 0=_
     simp[hR0]
   · show aW D 1=_
     simp[hR1]
   · show aW D 2=_
     simp[hR2]
 · rintro ⟨i,hi⟩
   have:i<3:=by omega
   interval_cases i
   · rw[mJ hi]
     simp
   · rw[MQ hi]
     simp
   · rw[Mz hi]
     simp
lemma QE {D:a9 m} (hD:D∈lV m r1 r2 s lam m2 m3 r3):
    kC (bT D)≤kv r1 r2 r3 lam m2 m3:=
  (Ie hD).le
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
end CbtAbstract
section CbtRed
end CbtRed
section CbtTup
def DX {r n:ℕ} {M:Type*} [Neg M] [Zero M] (y:Fin r→Fin r→Fin n→M):
    Fin n→Matrix (Fin r) (Fin r) M:=
  fun v j k=>if j<k then y j k v else if k<j then -y k j v else 0
def gT (p:ℕ) {r n:ℕ} (x:Fin r→Fin r→Fin n→ℕ):
    Fin n→Matrix (Fin r) (Fin r) (ZMod p):=
  DX (fun j k v=> (x j k v:ZMod p))
lemma L6 {r n:ℕ} {M:Type*} [Neg M] [Zero M] {y y':Fin r→Fin r→Fin n→M}
    (h:∀ j k,j<k→∀ v,y j k v=y' j k v):DX y=DX y':=by
 funext v
 ext j k
 show (if j<k then y j k v else if k<j then -y k j v else 0)=
   (if j<k then y' j k v else if k<j then -y' k j v else 0)
 split_ifs with h1 h2
 · exact h j k h1 v
 · rw[h k j h2 v]
 · rfl
lemma D3 {F:Type*} [Field F] {r n:ℕ} (y:Fin r→Fin r→Fin n→F)
    (M:Fin n→Matrix (Fin r) (Fin r) F) (hA:∀ v,Alt2.kG (M v))
    (h:∀ j k,j<k→∀ v,M v j k=y j k v):DX y=M:=by
 funext v
 ext j k
 show (if j<k then y j k v else if k<j then -y k j v else 0)=M v j k
 split_ifs with h1 h2
 · exact (h j k h1 v).symm
 · rw[(hA v).2 k j,h k j h2 v]
 · have uW:j=k:=le_antisymm (not_lt.1 h2) (not_lt.1 h1)
   subst uW
   exact ((hA v).1 _).symm
lemma LL (p:ℕ) {m:ℕ} (D:a9 m) (h2:2<D.1.val) (co:ℕ→ℕ)
    (x:ko D h2):gT p (mO D h2 co x).1=gT p x.1:=
  L6 fun j k uW v=>by
    show (((if j<k then x.1 j k v else 0:ℕ)):ZMod p)=_
    rw[if_pos uW]
end CbtTup
section CbtLead
variable {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
end CbtLead
section CbtBasis
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G}
lemma aZ.Q6 [hp:Fact p.Prime] [Finite G] (S:aZ p a g)
    (h0:0<c) (j_:p^r ⟨0,h0⟩*ZB (cE p G)=ZB G):
    ∃ bV:Basis (Fin (r ⟨0,h0⟩)) (ZMod p) (Additive (VQ p G)),
      ∀ j,bV j=ZC (dH p G (g ⟨⟨0,h0⟩,j⟩)):=by
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
 let w:Fin (r ⟨0,h0⟩)→ Additive (VQ p G):= fun j=>
   ZC (dH p G (g ⟨⟨0,h0⟩,j⟩))
 have key : ∀ x:G,ZC (dH p G x)∈ZQ (ZMod p) (ZF w):=by
  intro x
  have hx:x∈lcs G ((⟨0,h0⟩:Fin c):ℕ):=ZO x
  have hb:=S.oT ⟨0,h0⟩ ((dH p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype)
    (fun y hy=>by
      show dH p G (y:G)=1
      refine (Zm).1 ?_
      rw[Ky]
      exact dD p 0 hy)
    (fun v=> (S.nf.coord x ⟨⟨0,h0⟩,v⟩).val)
    (lX g S.mem (fun h=> (S.nf.coord x h).val) ⟨0,h0⟩) hx
    (S.nS ⟨0,h0⟩ hx)
  have e : ZC (dH p G x)=∑ v,(S.nf.coord x ⟨⟨0,h0⟩,v⟩).val•w v:=by
   calc Additive.ofMul (dH p G x)=ZC
         ((dH p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype ⟨x,hx⟩):=rfl
     _ = ZC (∏ v:Fin (r ⟨0,h0⟩),
         (dH p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype
           ⟨g ⟨⟨0,h0⟩,v⟩,S.mem ⟨⟨0,h0⟩,v⟩⟩^(S.nf.coord x ⟨⟨0,h0⟩,v⟩).val):=
         congrArg ZC hb
     _ = _:=by
         rw[ofMul_prod]
         exact Zw rfl fun v _=>ofMul_pow _ _
  rw[e]
  exact sum_mem fun v _=>nsmul_mem (Z1 (Tk (f:=w) v):
    w v∈ZQ (ZMod p) (ZF w)) _
 have qU:⊤≤ZQ (ZMod p) (ZF w):=by
  intro y _
  obtain ⟨x,hx⟩:= cV (p:=p) (G:=G) (ZW y)
  have e:y=ZC (dH p G x):=by
   rw[hx]
   rfl
  rw[e]
  exact key x
 have dS:Zq (Fin (r ⟨0,h0⟩))=WA (ZMod p) (Additive (VQ p G)):=by
  rw[Zz]
  have h1:=i8 (p:=p) (cE p G)
  rw[wX (p:=p) (G:=G)]at h1
  have h3:=Z4 (cE p G)
  rw[h1, ← j_,mul_comm (p^r ⟨0,h0⟩)]at h3
  have rV:0<ZB (cE p G):=Xi
  exact (Zd hp.out.two_le (WR rV h3)).symm
 refine ⟨basisOfTopLeSpanOfCardEqFinrank w qU dS,fun j=>?_⟩
 rw[RP]
end CbtBasis
section CbtTuple
variable {G:Type} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
end CbtTuple
section CbtBrDef
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
end CbtBrDef
section CbtReal
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G} {S:aZ p a g} {h2:2<c}
  {b0:Fin (r (aP h2))→Fin (r (aP h2))→ℕ}
  {b1:Fin (r (aY h2))→Fin (r (aY h2))→ℕ}
  {b2:Fin (r (bY h2))→Fin (r (bY h2))→ℕ}
end CbtReal
section CbtLeadBreadth
variable {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
end CbtLeadBreadth
section CbtCount
end CbtCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
section CNT3Final
lemma adr :abP:=by
 intro m r1 r2 s lam m2 m3 r3 G hG
 obtain ⟨D,hc,hD⟩:=abZ G hG
 have h3:D.1.1.val=3:=(l8 hD).1
 have h2:2<D.1.1.val:=by omega
 obtain ⟨jB,q7, -,hs, -, -,bU,hs3⟩:=BL hD h2
 exact ⟨D,hc,⟨h2,h3,hs,jB,q7,bU,hs3⟩,QE hD⟩
variable {m r1 r2 s lam m2 m3 r3:ℕ}
end CNT3Final
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
open Module
universe u
section M3tPivot
variable {F:Type*} [Field F] {n:ℕ}
def n9 (s:ℕ):(Fin n→F)→ₗ[F] (Fin n→F) where
  toFun w:= fun t=>if s≤t.val then w t else 0
  map_add':=by
    intro a b
    funext t
    simp only[Vc]
    split_ifs<;>simp
  map_smul':=by
    intro c a
    funext t
    simp only[Te,smul_eq_mul,Pe]
    split_ifs<;>simp
lemma l4 (s:ℕ) (w:Fin n→F) (t:Fin n):
    n9 (F:=F) s w t=if s≤t.val then w t else 0:=rfl
lemma D5 (s:ℕ) (K:Submodule F (Fin n→F))
    (hK:∀ w∈K,(∀ t:Fin n,s≤t.val→w t=0)→w=0):
    ∃ P:Finset (Fin n),P.card= finrank F K∧(∀ t∈P,s≤t.val)∧
      ∀ t∈P,∃ w∈K,∀ t'∈P,w t'=if t'=t then 1 else 0:=by
  classical
  set f:=n9 (F:=F) (n:=n) s with hf
  have eW:Z8 (f.comp K.subtype):=by
   intro a b hab
   apply Zu
   have h:=hK ((a:Fin n→F) - b) (K.sub_mem a.2 b.2) (fun t ht=>by
     have h1:= congrFun hab t
     have e1:(f.comp K.subtype) a t=(a:Fin n→F) t:=by
      show n9 s (a:Fin n→F) t=_
      rw[l4,if_pos ht]
     have e2:(f.comp K.subtype) b t=(b:Fin n→F) t:=by
      show n9 s (b:Fin n→F) t=_
      rw[l4,if_pos ht]
     rw[e1,e2]at h1
     rw[SH,h1,sub_self])
   exact sub_eq_zero.mp h
  have F5:finrank F (PX (f.comp K.subtype))= finrank F K:=
    LinearMap.finrank_range_of_inj eW
  obtain ⟨S,hS, -,j6⟩:=Alt2.BK (PX (f.comp K.subtype))
  have QG:∀ t∈S,s≤t.val:=by
   intro t ht
   by_contra f5
   obtain ⟨v,hv,hvt⟩:=j6 (fun i=>if i=⟨t,ht⟩ then 1 else 0)
   obtain ⟨w,rfl⟩:=Ra.mp hv
   have h1:=hvt ⟨t,ht⟩
   rw[if_pos rfl]at h1
   have h2:(f.comp K.subtype) w t=0:=by
    show n9 s (w:Fin n→F) t=0
    rw[l4,if_neg f5]
   exact zero_ne_one (h2.symm.trans h1)
  refine ⟨S,hS.trans F5,QG,fun t ht=>?_⟩
  obtain ⟨v,hv,hvt⟩:=j6 (fun i=>if i=⟨t,ht⟩ then 1 else 0)
  obtain ⟨w,rfl⟩:=Ra.mp hv
  refine ⟨w,w.2,fun t' iQ=>?_⟩
  have h1:=hvt ⟨t',iQ⟩
  have h2:(f.comp K.subtype) w t'=(w:Fin n→F) t':=by
   show n9 s (w:Fin n→F) t'=_
   rw[l4,if_pos (QG t' iQ)]
  rw[← h2]
  refine h1.trans ?_
  by_cases KW:t'=t
  · rw[if_pos (Zu KW),if_pos KW]
  · rw[if_neg (fun h=>KW (congrArg XJ h)),if_neg KW]
lemma Bn {V:Type*} [AddCommGroup V] [Module F V] [Finite V]:
    Finite (Submodule F V):=
  YH (fun q:Submodule F V=>fun x:V=>x∈q)
    (fun _ _ hpq=>SetLike.ext fun x =>Iff.of_eq (congrFun hpq x))
end M3tPivot
section M3tKC
def Bp (p:ℕ) {r1 r2:ℕ} (s:ℕ) (K:Submodule (ZMod p) (Fin r1→ZMod p))
    (M:Fin r2→Matrix (Fin r1) (Fin r1) (ZMod p)):Prop:=
  ∀ w∈K,∀ j:Fin r1,(j:ℕ)<s→∀ v,∑ t,M v j t *w t=0
def i9 (r1 s:ℕ):Finset (Fin r1×Fin r1):=
  ZU.filter (fun q=>q.1<q.2∧(q.1:ℕ)<s)
lemma lW {r1 s:ℕ} {q:Fin r1×Fin r1}:
    q∈i9 r1 s↔q.1<q.2∧(q.1:ℕ)<s:=by
 unfold i9
 rw[ZI]
 exact ⟨fun h=>h.2,fun h=> ⟨Zb _,h⟩⟩
lemma ND (r1 s:ℕ):(i9 r1 s).card+(r1 - s).choose 2=r1.choose 2:=by
 classical
 set T:=(ZU:Finset (Fin r1×Fin r1)).filter (fun q=>q.1<q.2) with qM
 have Ij:T.card=r1.choose 2:=by
  have h0:=jY r1 0
  rw[UK]at h0
  rw[← h0,qM]
  congr 1
  ext q
  simp
 have Lj:i9 r1 s=T.filter (fun q=> (q.1:ℕ)<s):=by
   ext q
   rw[lW,qM,ZI,ZI]
   simp
 have Eo:(T.filter (fun q=> ¬ (q.1:ℕ)<s)).card=(r1 - s).choose 2:=by
   rw[← jY r1 s,qM]
   congr 1
   ext q
   simp
 rw[Lj, ← Eo,Uh,Ij]
lemma l5 (p:ℕ) {r n:ℕ} (x:Fin r→Fin r→Fin n→ℕ) (v:Fin n)
    (j k:Fin r):gT p x v j k=
      if j<k then ((x j k v:ℕ):ZMod p) else if k<j then -((x k j v:ℕ):ZMod p) else 0:=
  rfl
variable {p:ℕ} [hpf:Fact p.Prime]
lemma Qn {r1 r2 s:ℕ} {K:Submodule (ZMod p) (Fin r1→ZMod p)} {P:Finset (Fin r1)}
    (hP:∀ t∈P,s≤t.val) {x x':Fin r1→Fin r1→Fin r2→ℕ}
    (hx:Bp p s K (gT p x)) (oQ:Bp p s K (gT p x'))
    (GQ:∀ j t',(j,t')∈i9 r1 s→t'∉P→x j t'=x' j t')
    {t:Fin r1} (ht:t∈P) {w:Fin r1→ZMod p} (hwK:w∈K)
    (hw:∀ t'∈P,w t'=if t'=t then 1 else 0) {j:Fin r1} (hj:(j:ℕ)<s)
    (v:Fin r2):((x j t v:ℕ):ZMod p)=((x' j t v:ℕ):ZMod p):=by
  have e1:=hx w hwK j hj v
  have e2:= oQ w hwK j hj v
  have hst:=hP t ht
  have hjt:j<t:=XO.mpr (by omega)
  have key : ∑ t',(gT p x v j t' - gT p x' v j t')*w t'=
      (gT p x v j t - gT p x' v j t)*w t:=by
   refine Ue t (fun t' _ iQ=>?_) (fun h=>absurd (Zb t) h)
   by_cases htP:t'∈P
   · rw[hw t' htP,if_neg iQ,mul_zero]
   · have hc :gT p x v j t'=gT p x' v j t':=by
       rw[l5,l5]
       by_cases h1:j<t'
       · rw[if_pos h1,if_pos h1,GQ j t' (lW.mpr ⟨h1,hj⟩) htP]
       · by_cases h2:t'<j
         · have hq:(t',j)∈i9 r1 s:=
             lW.mpr ⟨h2,show (t':ℕ)<s by have:=XO.mp h2; omega⟩
           have hjP:j∉P:= fun hjP=>by have:=hP j hjP; omega
           rw[if_neg h1,if_pos h2,if_neg h1,if_pos h2,GQ t' j hq hjP]
         · rw[if_neg h1,if_neg h2,if_neg h1,if_neg h2]
     rw[hc,sub_self,zero_mul]
  have hsum:∑ t',(gT p x v j t' - gT p x' v j t')*w t'=0:=by
   simp only[sub_mul,RZ]
   rw[e1,e2,sub_self]
  rw [key,hw t ht,if_pos rfl,UH,sub_eq_zero,l5,l5,
    if_pos hjt,if_pos hjt]at hsum
  exact hsum
lemma GU {y a:ℕ} (ha:1≤a) (hy:y<p^a):y/p<p^(a - 1):=by
 rw[W2 hpf.out.pos, ← Xr,Vf ha]
 exact hy
lemma Lz {r1 r2 s:ℕ} (hs:s≤ r1) (a:Fin r2→ℕ) (ha:∀ v,1≤a v)
    (K:Submodule (ZMod p) (Fin r1→ZMod p))
    (hK:∀ w∈K,(∀ t:Fin r1,s≤t.val→w t=0)→w=0)
    (Dp:Finset (Fin r1×Fin r1)) (En:∀ q∈Dp,q.1<q.2∧(q.2:ℕ)<s)
    (wD:Fin r1×Fin r1→Fin r2→ℕ)
    (Λ:Set (Fin r1→Fin r1→Fin r2→ℕ))
    (hΛ:∀ x∈Λ,Bp p s K (gT p x)∧(∀ j k v,x j k v<p^a v)∧
      ∀ q∈Dp,x q.1 q.2=wD q):
    ((fun x:Fin r1→Fin r1→Fin r2→ℕ=>fun q:↥(i9 r1 s)=>x q.1.1 q.1.2) '' Λ).ncard*
        p^(s*finrank (ZMod p) K*r2)≤
      p^((∑ v,a v)*((i9 r1 s).card - Dp.card)):=by
  classical
  obtain ⟨P,Lj,Eo,hPw⟩:=D5 (F:=ZMod p) s K hK
  choose! wv ad4 hwv using hPw
  set Pc:=i9 r1 s with Dd
  set Sc:Finset (Fin r1):=ZU.filter (fun j:Fin r1=> (j:ℕ)<s) with acJ
  set Pv:Finset (Fin r1×Fin r1):=Sc×ˢ P with acM
  set A:=(Pc \ Pv) \ Dp with abO
  have abG:Pv⊆Pc:=by
   intro q hq
   obtain ⟨h1,h2⟩:=XH.mp hq
   have hj:((q.1:Fin r1):ℕ)<s:=(ZI.mp h1).2
   have ht:=Eo q.2 h2
   exact lW.mpr ⟨XO.mpr (by omega),hj⟩
  have ac6:Dp⊆Pc \ Pv:=by
   intro q hq
   obtain ⟨h1,h2⟩:=En q hq
   refine Xq.mpr ⟨lW.mpr ⟨h1,by have:=XO.mp h1; omega⟩,?_⟩
   intro hv
   have:=Eo q.2 (XH.mp hv).2
   omega
  have acF:Sc.card=s:=by
   have e:Sc=(ZU:Finset (Fin s)).map (Fin.castLEEmb hs):=by
    ext j
    rw[acJ,ZI,Finset.mem_map]
    constructor
    · rintro ⟨-,hj⟩
      exact ⟨⟨j,hj⟩,Zb _,YL rfl⟩
    · rintro ⟨i, -,rfl⟩
      exact ⟨Zb _,i.isLt⟩
   rw[e,Finset.card_map,Y4,Zz]
  have ab5:Pv.card=s*finrank (ZMod p) K:=by
   rw[acM,Finset.card_product,acF,Lj]
  have aeM:A.card+Dp.card+Pv.card=Pc.card:=by
   have h1:=XX ac6
   have h2:=XX abG
   rw[abO]
   omega
  have adv:∀ q∈A,q∈Pc:= fun q hq=>
    (Xq.mp (Xq.mp hq).1).1
  let ψ:= fun x:Fin r1→Fin r1→Fin r2→ℕ=>fun q:↥Pc=>x q.1.1 q.1.2
  let Φ :(↥Pc→Fin r2→ℕ)→
      (↥A→(v:Fin r2)→Fin (p^a v))×(↥Pv→(v:Fin r2)→Fin (p^(a v - 1))):=
    fun y=> (fun q v=> ⟨y ⟨q.1,adv q.1 q.2⟩ v % p^a v,W3 _ (XD hpf.out.pos _)⟩,
      fun q v=> ⟨(y ⟨q.1,abG q.2⟩ v/p) % p^(a v - 1),
        W3 _ (XD hpf.out.pos _)⟩)
  have eW:WP Φ (ψ '' Λ):=by
   rintro _ ⟨x,hx,rfl⟩ _ ⟨x',oQ,rfl⟩ hΦ
   obtain ⟨hkx,hbx,hdx⟩:=hΛ x hx
   obtain ⟨adC,acG,adW⟩:=hΛ x' oQ
   have aed:∀ q (hq:q∈A),x q.1 q.2=x' q.1 q.2:=by
    intro q hq
    funext v
    have h:= congrArg (fun F=> ((F.1 ⟨q,hq⟩ v:Fin _):ℕ)) hΦ
    simp only[Φ,ψ]at h
    rwa[Xw (hbx _ _ _),Xw (acG _ _ _)]at h
   have GQ:∀ j t',(j,t')∈Pc→t'∉P→x j t'=x' j t':=by
    intro j t' hq iQ
    by_cases hD:(j,t')∈Dp
    · exact (hdx _ hD).trans (adW _ hD).symm
    · refine aed (j,t') ?_
      rw[abO,Xq,Xq]
      exact ⟨⟨hq,fun hv=>iQ (XH.mp hv).2⟩,hD⟩
   funext q v
   show x q.1.1 q.1.2 v=x' q.1.1 q.1.2 v
   have acj:=lW.mp q.2
   by_cases hqv:q.1∈Pv
   · have ht:q.1.2∈P:=(XH.mp hqv).2
     have acL:=Qn Eo hkx adC GQ ht (ad4 _ ht) (hwv _ ht) acj.2 v
     rw[ZMod.natCast_eq_natCast_iff']at acL
     have aa0:= congrArg (fun F=> ((F.2 ⟨q.1,hqv⟩ v:Fin _):ℕ)) hΦ
     simp only[Φ,ψ]at aa0
     rw [Xw (GU (ha v) (hbx _ _ _)),
       Xw (GU (ha v) (acG _ _ _))]at aa0
     rw [← Wa (x q.1.1 q.1.2 v) p, ← Wa (x' q.1.1 q.1.2 v) p,aa0,
       acL]
   · refine congrFun (GQ q.1.1 q.1.2 q.2 (fun ht=>hqv ?_)) v
     exact XH.mpr ⟨ZI.mpr ⟨Zb _,acj.2⟩,ht⟩
  have cO:=YM Φ (fun _ _=>Set.mem_univ _) eW
    (Zl (RG:Set ((↥A→(v:Fin r2)→Fin (p^a v))×
      (↥Pv→(v:Fin r2)→Fin (p^(a v - 1))))))
  rw [Set.ncard_univ,W7,Xl,Xl,m6,m6,
    YA (α:=↥A),WG,YA (α:=↥Pv),
    WG]at cO
  have abN:∑ v,(a v - 1)+r2=∑ v,a v:=by
   have e1:∑ v,a v=∑ v,((a v - 1)+1):=
     Zw rfl fun v _=>by have:=ha v; omega
   rw[e1,Xy]
   simp
  have q7:r2≤∑ v,a v:=by omega
  calc (ψ '' Λ).ncard*p^(s*finrank (ZMod p) K*r2)
      ≤((p ^∑ v,a v)^A.card*(p^∑ v,(a v - 1))^Pv.card)*
          p^(s*finrank (ZMod p) K*r2):=Za _ cO
    _ = p^((∑ v,a v)*(Pc.card - Dp.card)):=by
        rw[← X5, ← X5, ← Xh, ← Xh]
        congr 1
        have e2:Pc.card - Dp.card=A.card+s*finrank (ZMod p) K:=by omega
        have e3:∑ v,(a v - 1)=∑ v,a v - r2:=by omega
        rw[e2,ab5,e3]
        obtain ⟨c,hc⟩:∃ c,∑ v,a v=r2+ c:=⟨∑ v,a v - r2,by omega⟩
        rw[hc,Yb]
        ring
end M3tKC
section M3tSaving
variable {p:ℕ}
def ez {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:a9 m)
    (h2:2<D.1.val) (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (K:Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p)):
    Set (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):=
  {C | C∈je hp T D B∧Bp p D.2.1.val K (gT p (jN D h2 C).1)}
lemma aai (s2 r2 Pc X β:ℕ) (h1:r2≤Pc) (h2:β≤ s2):
    s2*(Pc - r2)+((Pc+X - Pc)*s2 - X*β)=(Pc+X - r2)*s2 - X*β:=by
 obtain ⟨e,rfl⟩:=Rw h1
 obtain ⟨c,rfl⟩:=Rw h2
 have e1:r2+e+X - (r2+e)=X:=by omega
 have e2:r2+e - r2=e:=by omega
 have e3:r2+e+X - r2=e+X:=by omega
 have e4:X*(β+ c) - X*β=X*c:=by
  rw[show X*(β+ c)=X*c+X*β by ring,XI]
 have e5:(e+X)*(β+ c) - X*β=e *(β+ c)+X*c:=by
  rw[show (e+X)*(β+ c)=e *(β+ c)+X*c+X*β by ring,XI]
 rw[e1,e2,e3,e4,e5]
 ring
lemma vV {m : ℕ} [Fact p.Prime] (hp:p.Prime) (T:Set FiniteGrp.{0})
    (D:a9 m) (h2:2<D.1.val) (h3:D.1.val=3)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (K:Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p))
    (hK:∀ w∈K,(∀ t:Fin (aF D (aP h2)),D.2.1.val≤t.val→w t=0)→w=0):
    (ez hp T D h2 B K).ncard*
        p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2))≤
      (∑ β ∈(ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 - aF D (aY h2))*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β))*
        p ^(((aF D (aP h2)).choose 2 - aF D (aY h2))*
          ∑ v,bT D ⟨bY h2,v⟩):=by
  classical
  rcases (ez hp T D h2 B K).eq_empty_or_nonempty with hE | ⟨C0,hC0⟩
  · rw[hE,Y3,R8]
    exact Zv _
  obtain ⟨G0, -,u0,d0,X0,r0,mJ,aaV,k6,aag,e0⟩:=hC0.1
  obtain ⟨c1,c2,c3, -, -, -,c7,c8⟩:=mJ.kS hp aaV k6 aag e0
  have hn0:d0.n=aD r0 D.1.val:=by rw[← c1]; exact mJ.g6.symm
  have FN:r0 0=aW D 0:= c3 0 (by rw[c1]; omega)
  have abw:r0 1=aW D 1:= c3 1 (by rw[c1]; omega)
  have abk:=(mJ.JR hn0 (by omega) mJ.vZ).1
  have kB:D.2.1.val≤aF D (aP h2):=by
   show D.2.1.val≤aW D 0
   rw[← c2, ← FN]
   exact abk
  have u9:∀ C∈je hp T D B,Dq p hp.pos D h2 B (b9 d0 r0) C:=by
   rintro C ⟨G, -,u,d,X,r,hS,bZ,bU,hsum,e⟩
   obtain ⟨g1,g2,g3, -, -, -,g7, -⟩:=hS.kS hp bZ bU hsum e
   refine hS.Qk hp bZ bU hsum e h2 h3 _
     (zO hS mJ bU (g2.trans c2.symm) ?_ ?_)
   · rw[g3 1 (by rw[g1]; omega),abw]
   · intro k hk
     rw[g7 k hk,c7 k (by rw[c2, ← g2]; exact hk)]
  have jW:∀ j:Fin (aF D (aY h2)),j.val< r0 1:= fun j=>by
    have:j.val<aW D 1:=j.isLt
    omega
  have En:∀ q∈gP D h2 (dQ D) (b9 d0 r0),q.1<q.2∧(q.2:ℕ)<D.2.1.val:=by
   intro q hq
   obtain ⟨j,tM,zB⟩:=(ZI.mp hq).2
   rw[← c8 _ (jW j)]at tM
   refine ⟨?_,?_⟩
   · show q.1.val<q.2.val
     rw[tM,zB]
     exact mJ.qL k6 (jW j)
   · rw[zB, ← c2]
     exact (mJ.jC k6 j.val (jW j)).2
  have s8:∀ j:Fin (aF D (aY h2)),dQ D j.val<aF D (aP h2):=by
   intro j
   show dQ D j.val<aW D 0
   rw[← c8 _ (jW j), ← FN]
   have:=mJ.DN k6 j.val (jW j)
   omega
  have uj:∀ j:Fin (aF D (aY h2)),b9 d0 r0 j.val<aF D (aP h2):=by
   intro j
   show b9 d0 r0 j.val<aW D 0
   rw[← FN]
   have:=mJ.jC k6 j.val (jW j)
   omega
  obtain ⟨F,hF⟩:∃ F:Fin (aF D (aY h2))→
      Fin (aF D (aP h2))×Fin (aF D (aP h2)),
      ∀ j,(F j).1.val=dQ D j.val∧(F j).2.val=b9 d0 r0 j.val:=
    ⟨fun j=> (⟨_,s8 j⟩,⟨_,uj j⟩),fun j=> ⟨rfl,rfl⟩⟩
  have Qm:Z8 F:=by
   intro j j' Er
   have e1:dQ D j.val=dQ D j'.val:=by rw[← (hF j).1, ← (hF j').1,Er]
   have e2:b9 d0 r0 j.val=b9 d0 r0 j'.val:=by rw[← (hF j).2, ← (hF j').2,Er]
   rw[← c8 _ (jW j), ← c8 _ (jW j')]at e1
   exact YL (mJ.y7 k6 (jW j) (jW j') e1 e2)
  have qv:gP D h2 (dQ D) (b9 d0 r0)=ZU.image F:=by
   ext q
   simp only[gP,ZI,Zb,true_and,Xp]
   constructor
   · rintro ⟨j,h1,jM⟩
     exact ⟨j,V7 (YL ((hF j).1.trans h1.symm)) (YL ((hF j).2.trans jM.symm))⟩
   · rintro ⟨j,rfl⟩
     exact ⟨j,(hF j).1,(hF j).2⟩
  have zE:(gP D h2 (dQ D) (b9 d0 r0)).card=aF D (aY h2):=by
   rw[qv,XG _ Qm,Y4,Zz]
  set Λ:=wZ p D h2 (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2))
    (gP D h2 (dQ D) (b9 d0 r0)) (Cm D h2 (dQ D) (b9 d0 r0)) with hΛdef
  set ΛK:Set (ko D h2):={x | x∈Λ∧Bp p D.2.1.val K (gT p x.1)} with hΛKdef
  set M := ∑ β ∈(ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 -
              (i9 (aF D (aP h2)) D.2.1.val).card)*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β) with hM
  have pC:∀ y,(ΛK∩(fun x:ko D h2=>
      fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2) ⁻¹' {y}).ncard≤M:=by
    intro y
    refine v6 (p:=p) (c:=D.1.val) (r :=aF D) (a:=bT D) hp h2
      (iw D B (aP h2)) (iw D B (aY h2)) (iw D B (bY h2)) (s:=D.2.1.val) kB
      (i9 (aF D (aP h2)) D.2.1.val) (fun q hq=>lW.mp hq)
      (fun q v=>if h:q∈i9 (aF D (aP h2)) D.2.1.val then y ⟨q,h⟩ v else 0)
      _ (fun x hx =>?_)
    have hy:(fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2)=y:=hx.2
    obtain ⟨G,iG,iF,g,S,Fj,aej,aen,hl,dG, -,Cv⟩:=hx.1.1.1
    refine ⟨G,iG,iF,g,S,Fj,aej,aen,hl,dG,fun q hq=>?_,Cv⟩
    funext v
    show S.iW h2 q.1 q.2 v=
      (if h:q∈i9 (aF D (aP h2)) D.2.1.val then y ⟨q,h⟩ v else 0)
    rw[dif_pos hq, ← hy]
    show S.iW h2 q.1 q.2 v=x.1 q.1 q.2 v
    rw[Cv]
  have U_:=jO ΛK (fun x:ko D h2=>
      fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2) M pC
  have abM:=Lz (p:=p) kB (fun v=>bT D ⟨aY h2,v⟩)
    (fun v=>CX D _) K hK (gP D h2 (dQ D) (b9 d0 r0)) En
    (Cm D h2 (dQ D) (b9 d0 r0)) (W9 '' ΛK) (by
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨⟨⟨G,iG,iF,g,S, -, -, -, -, -,hDw,Cv⟩,hbd, -⟩,hkc⟩:=hx
      refine ⟨hkc,hbd,fun q hq=>?_⟩
      rw[← hDw q hq,Cv])
  have hψ:(fun x:ko D h2=>
      fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2) '' ΛK=
      (fun x:Fin (aF D (aP h2))→Fin (aF D (aP h2))→Fin (aF D (aY h2))→ℕ=>
        fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x q.1.1 q.1.2) '' (W9 '' ΛK):=by
    rw[Set.image_image]
  rw[← hψ,zE]at abM
  have aci:=ND (aF D (aP h2)) D.2.1.val
  have QX:gP D h2 (dQ D) (b9 d0 r0)⊆i9 (aF D (aP h2)) D.2.1.val:=
    fun q hq=>lW.mpr ⟨(En q hq).1,by
      have:=XO.mp (En q hq).1
      have:=(En q hq).2
      omega⟩
  have ac3:aF D (aY h2)≤(i9 (aF D (aP h2)) D.2.1.val).card:=by
   rw[← zE]
   exact VB QX
  have hΛK : ΛK.ncard*p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2))≤
      ∑ β ∈(ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 - aF D (aY h2))*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β):=by
    calc ΛK.ncard*p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2))
        ≤ (((fun x:ko D h2=>
            fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2) '' ΛK).ncard*M)*
          p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2)):=
          Za _ U_
      _ = (((fun x:ko D h2=>
            fun q:↥(i9 (aF D (aP h2)) D.2.1.val)=>x.1 q.1.1 q.1.2) '' ΛK).ncard*
          p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2)))*M:=by
          ring
      _ ≤ p ^((∑ v,bT D ⟨aY h2,v⟩)*
            ((i9 (aF D (aP h2)) D.2.1.val).card - aF D (aY h2)))*M:=
          Za _ abM
      _ = _ := by
          rw[hM,OH]
          refine Zw rfl fun β hβ=>?_
          obtain ⟨hβ1, -⟩:=ZI.mp hβ
          have hβs2:β≤∑ v,bT D ⟨aY h2,v⟩:=by
           have:=Zt.mp hβ1
           have:=min_le_left (∑ v,bT D ⟨aY h2,v⟩) (∑ v,bT D ⟨bY h2,v⟩)
           omega
          rw[mul_left_comm, ← Xh]
          congr 2
          have hC:(aF D (aP h2)).choose 2=
              (i9 (aF D (aP h2)) D.2.1.val).card+
                (aF D (aP h2) - D.2.1.val).choose 2:=aci.symm
          rw[hC]
          exact aai _ _ _ _ _ ac3 hβs2
  have I9:=rG (Γ:=DO p D h2)
    (m6 (p:=p) (fun v:Fin (aF D (bY h2))=>bT D ⟨bY h2,v⟩))
    (gP D h2 (dQ D) (b9 d0 r0)) (fun q hq=> (En q hq).1)
    (fun _ _=> ⟨0,XD hp.pos _⟩)
  rw[zE]at I9
  have hΛfin:ΛK.Finite:=by
   refine (OY (fun y:(Fin (aF D (aP h2))→Fin (aF D (aP h2))→
       (v:Fin (aF D (aY h2)))→Fin (p^bT D ⟨aY h2,v⟩))×
       (Fin (aF D (aY h2))→Fin (aF D (aP h2))→
         (v:Fin (aF D (bY h2)))→Fin (p^bT D ⟨bY h2,v⟩))=>
       ((fun j k v=> (y.1 j k v).val,fun j k v=> (y.2 j k v).val):ko D h2))).subset ?_
   rintro x ⟨⟨-,Lg,hx2⟩, -⟩
   exact ⟨(fun j k v=> ⟨x.1 j k v,Lg j k v⟩,fun j k v=> ⟨x.2 j k v,hx2 j k v⟩),rfl⟩
  have eW:WP (fun C=> (jN D h2 C,qy hp.pos D h2 C))
      (ez hp T D h2 B K):=by
    intro C hC C' Ot he
    exact JH hp.pos h2 (u9 C hC.1) (u9 C' Ot.1) (congrArg W9 he)
      (congrArg PO he)
  have oc:∀ C∈ez hp T D h2 B K,
      (fun C=> (jN D h2 C,qy hp.pos D h2 C)) C∈
      (mO D h2 (b9 d0 r0) '' ΛK)×ˢ
        lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0)):=by
    intro C hC
    obtain ⟨x,hx,Cv⟩:=(u9 C hC.1).acB
    have hkc:Bp p D.2.1.val K (gT p x.1):=by
     have h:=hC.2
     rw[Cv,LL]at h
     exact h
    show (jN D h2 C,qy hp.pos D h2 C)∈_
    exact Sj ⟨x,⟨hx,hkc⟩,Cv.symm⟩ (u9 C hC.1).Kd
  have hCB : (ez hp T D h2 B K).ncard≤ΛK.ncard*
      (lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=
    calc (ez hp T D h2 B K).ncard
        ≤ ((mO D h2 (b9 d0 r0) '' ΛK)×ˢ
            lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=
          YM _ oc eW
            ((hΛfin.image (mO D h2 (b9 d0 r0))).prod (Zl _))
      _= (mO D h2 (b9 d0 r0) '' ΛK).ncard*
            (lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=RM
      _ ≤ ΛK.ncard*(lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=
          Za _ (Tm hΛfin)
  calc (ez hp T D h2 B K).ncard*
        p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2))
      ≤ (ΛK.ncard*(lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard)*
          p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2)):=
        Za _ hCB
    _=(ΛK.ncard*p^(D.2.1.val*finrank (ZMod p) K*aF D (aY h2)))*
          (lN p hp.pos D h2 (gP D h2 (dQ D) (b9 d0 r0))).ncard:=by ring
    _≤_:=Zr hΛK I9
end M3tSaving
section M3tBasis
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:aR c r→ℕ}
  {g:aR c r→G}
lemma aZ.Qw [hp:Fact p.Prime] [Finite G] (S:aZ p a g)
    (h1:1<c) (jB:p^r ⟨1,h1⟩*ZB (pN p G)=ZB (lcs G 1)):
    ∃ bW : Basis (Fin (r ⟨1,h1⟩)) (ZMod p) (Additive (WQ p G)),
      (∀ v,bW v=ZC (jL p G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩))∧
      ∀ (x :G) (hx:x∈lcs G 1) (v:Fin (r ⟨1,h1⟩)),
        bW.repr (ZC (jL p G ⟨x,hx⟩)) v=
          ((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p):=by
 have:Finite (WQ p G):=Zy _ lP
 have:Finite (Additive (WQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (WQ p G)):=inferInstance
 let w:Fin (r ⟨1,h1⟩)→ Additive (WQ p G):= fun v=>
   ZC (jL p G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩)
 have key :∀ (x:G) (hx:x∈lcs G 1),ZC (jL p G ⟨x,hx⟩)=
     ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v:=by
  intro x hx
  have hb:=S.oT ⟨1,h1⟩ (jL p G) (fun y hy=>t6 (eo p hy))
    (fun v=> (S.nf.coord x ⟨⟨1,h1⟩,v⟩).val)
    (lX g S.mem (fun h=> (S.nf.coord x h).val) ⟨1,h1⟩) hx
    (S.nS ⟨1,h1⟩ hx)
  calc Additive.ofMul (jL p G ⟨x,hx⟩)=ZC (∏ v:Fin (r ⟨1,h1⟩),
        jL p G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩^(S.nf.coord x ⟨⟨1,h1⟩,v⟩).val):=
        congrArg ZC hb
    _ = ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v:=by
        rw[ofMul_prod]
        exact Zw rfl fun v _=>
          (ofMul_pow _ _).trans (UJ (ZMod p) _ _).symm
 have qU:⊤≤ZQ (ZMod p) (ZF w):=by
  intro y _
  obtain ⟨⟨x,hxm⟩,hx⟩:=lP (p:=p) (G:=G) (ZW y)
  have e:y=ZC (jL p G ⟨x,hxm⟩):=by
   rw[hx]
   rfl
  rw[e,key x hxm]
  exact sum_mem fun v _=>VE _ _ (Z1 ⟨v,rfl⟩)
 have dS:Zq (Fin (r ⟨1,h1⟩))=WA (ZMod p) (Additive (WQ p G)):=by
  rw[Zz]
  have h:=xT (p:=p) (G:=G)
  rw[← jB,mul_comm (p^r ⟨1,h1⟩)]at h
  have rV:0<ZB (pN p G):=Xi
  exact Zd hp.out.two_le (WR rV h)
 have hbw:∀ v,basisOfTopLeSpanOfCardEqFinrank w qU dS v=w v:= fun v=>by
   rw[RP]
 refine ⟨basisOfTopLeSpanOfCardEqFinrank w qU dS,hbw,fun x hx v=>?_⟩
 have hs:(∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v)=
     ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•
       basisOfTopLeSpanOfCardEqFinrank w qU dS v:=
   Zw rfl fun v _=>by rw[hbw v]
 rw[key x hx,hs,Basis.repr_sum_self]
end M3tBasis
section M3tReindex
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.Oq [Finite G] (hp:p.Prime) (hS:aE p u d X r) {c:ℕ}
    (hn:d.n=aD r c) (h2:2<c) (r':Fin c→ℕ) (hr :∀ i:Fin c,r i.val=r' i)
    (a':aR c r'→ℕ) (ha:∀ k:aR c r',a' k=lL d (aD r k.1.val+k.2.val)):
    ∃ (g':aR c r'→G) (S:aZ p a' g'),
      (∀ (i:Fin c) (j v:Fin (r' i)),(S.c_ ⟨i,j⟩ ⟨i,v⟩).val=
        tB d (aD r i.val+j.val) (aD r i.val+v.val))∧
      (∀ (j k:Fin (r' (aP h2))) (v:Fin (r' (aY h2))),j<k→
        S.iW h2 j k v=jd d (aD r 0+j.val) (aD r 0+k.val) (aD r 1+v.val))∧
      (∀ k:aR c r',g' k=dE d X (aD r k.1.val+k.2.val)):=by
 have hr':mL r c=r':= funext hr
 subst hr'
 have u6:a'= fun k=>d.a (hS.aV hn k):=
   funext fun k=> (ha k).trans (hS.sI hn k)
 subst u6
 refine ⟨fun k=>X (hS.aV hn k),hS.toaZ hp hn,fun i j v=>?_,
   fun j k v uW=>?_,fun k=>?_⟩
 · exact (hS.uZ hp hn ⟨i,j⟩ ⟨i,v⟩).symm
 · exact (hS.v8 hp hn h2 j k uW v).symm
 · show X (hS.aV hn k)=_
   rw[← hS.o3 hn k,K_]
end M3tReindex
section M3tTuple
variable {G:Type} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:aO} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma aE.Cr [Fact p.Prime] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m) {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.k_ hp m bZ bU hsum=⟨D,(B,C)⟩) (h2:2<D.1.val) (hG:IsPGroup p G):
    ∃ (bV:Basis (Fin (aF D (aP h2))) (ZMod p) (Additive (VQ p G)))
      (bW:Basis (Fin (aF D (aY h2))) (ZMod p) (Additive (WQ p G)))
      (hw:∀ v:Fin (aF D (aY h2)),dE d X (aW D 0+v.val)∈lcs G 1),
      (∀ j:Fin (aF D (aP h2)),bV j=ZC (dH p G (dE d X j.val)))∧
      (∀ v,bW v=ZC (jL p G ⟨dE d X (aW D 0+v.val),hw v⟩))∧
      gT p (jN D h2 C).1=Alt2.gW (cP (p:=p) (G:=G)) bV bW:=by
 obtain ⟨cf1, -,cf3,cf4,cf5,cf6, -, -⟩:=hS.kS hp bZ bU hsum e
 have hn:d.n=aD r D.1.val:=by rw[← cf1]; exact hS.g6.symm
 have xO:∀ w≤D.1.val,aD r w=aD (aW D) w:=
   k9 (fun w hw=>cf3 w (by rw[cf1]; exact hw))
 have f1:=xO 1 (by omega)
 have e0:aD r 0=0:=rfl
 have e0':aD (aW D) 0=0:=rfl
 have f1r :aD r 1=aW D 0:=by
  rw[dM,e0,XL]
  exact cf3 0 (by rw[cf1]; omega)
 obtain ⟨g',S, -,HR,hg'⟩:=hS.Oq hp hn h2 (aF D)
   (fun i=>cf3 i.val (by rw[cf1]; exact i.isLt)) (bT D) (fun k=>by
     show qQ D (aD (aW D) k.1.val+k.2.val)=_
     rw[cf4,xO _ k.1.isLt.le])
 have hg0:∀ j:Fin (aF D (aP h2)),g' ⟨aP h2,j⟩=dE d X j.val:=by
  intro j
  rw[hg' ⟨aP h2,j⟩]
  show dE d X (aD r 0+j.val)=_
  rw[e0,XL]
 have hg1:∀ v:Fin (aF D (aY h2)),g' ⟨aY h2,v⟩=dE d X (aW D 0+v.val):=by
  intro v
  rw[hg' ⟨aY h2,v⟩]
  show dE d X (aD r 1+v.val)=_
  rw[f1r]
 have j_:p^aF D ⟨0,by omega⟩*ZB (cE p G)=ZB G:=by
   have h:=hS.kV 0
   rw[cf3 0 (by rw[cf1]; omega),lcs_zero,Yn]at h
   exact h
 have jB:p^aF D ⟨1,by omega⟩*ZB (pN p G)=ZB (lcs G 1):=by
   have h:=hS.kV 1
   rw[cf3 1 (by rw[cf1]; omega)]at h
   exact h
 obtain ⟨bW,adB,hbW⟩:=S.Qw (by omega) jB
 obtain ⟨bV,hbV⟩:=S.Q6 (by omega) j_
 have ado:∀ j k:Fin (aF D (aP h2)),j<k→∀ v:Fin (aF D (aY h2)),
     (jN D h2 C).1 j k v=S.iW h2 j k v:=by
  intro j k uW v
  rw[HR j k v uW]
  show kM D C (aD (aW D) 0+j.val) (aD (aW D) 0+k.val)
    (aD (aW D) 1+v.val)=_
  rw[cf5,e0', ← f1,e0]
 have hM:=Alt2.rF hG bV bW
 have heq:gT p (jN D h2 C).1=Alt2.gW (cP (p:=p) (G:=G)) bV bW:=by
  refine D3 _ _ hM.1 fun j k uW v=>?_
  show bW.repr (cP (bV j) (bV k)) v=(((jN D h2 C).1 j k v:ℕ):ZMod p)
  rw[hbV j,hbV k,CY]
  refine (hbW _ (cw (g' ⟨aP h2,j⟩) (g' ⟨aP h2,k⟩)).2 v).trans ?_
  rw[ado j k uW v]
  rfl
 have hw:∀ v:Fin (aF D (aY h2)),dE d X (aW D 0+v.val)∈lcs G 1:=by
  intro v
  rw[← hg1 v]
  exact S.mem ⟨aY h2,v⟩
 refine ⟨bV,bW,hw,fun j=>?_,fun v=>?_,heq⟩
 · rw[hbV j]
   show ZC (dH p G (g' ⟨aP h2,j⟩))=_
   rw[hg0 j]
 · rw[adB v]
   exact congrArg (fun y:lcs G 1=>ZC (jL p G y)) (Zu (hg1 v))
lemma aE.acp [Fact p.Prime] (hp:p.Prime) (hS:aE p u d X r) {m:ℕ}
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m) {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.k_ hp m bZ bU hsum=⟨D,(B,C)⟩) (h2:2<D.1.val) (hG:IsPGroup p G)
    (kB:d.s=bD G):
    ∃ K :Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p),
      finrank (ZMod p) K= finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G))
        (Mult3.cT (p:=p) (fun j:Fin d.s=>u j.val)))∧
      (∀ w∈K,(∀ t:Fin (aF D (aP h2)),D.2.1.val≤t.val→w t=0)→w=0)∧
      Bp p D.2.1.val K (gT p (jN D h2 C).1):=by
  have:Finite (VQ p G):=Zy _ cV
  have:Finite (Additive (VQ p G)):=inferInstance
  have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
  obtain ⟨bV,bW, -,hbV, -,heq⟩:=hS.Cr hp bZ bU hsum e h2 hG
  obtain ⟨-,cf2, -⟩:=hS.kS hp bZ bU hsum e
  set U:=Mult3.cT (p:=p) (fun j:Fin d.s=>u j.val) with aeO
  set KC:=Mult3.gz (cP (p:=p) (G:=G)) U with aeL
  have hUb:∀ j:Fin (aF D (aP h2)),j.val<D.2.1.val→ bV j∈U:=by
   intro j hj
   have O2:j.val<d.s:=by rw[cf2]; exact hj
   have hjn:j.val<d.n:=lt_of_lt_of_le O2 hS.valid.yA
   rw[hbV j,r7 d X hjn,hS.core ⟨j.val,hjn⟩ O2]
   exact Z1 ⟨⟨j.val,O2⟩,rfl⟩
  have wc:ZF (fun j:Fin d.s=>u j.val)=u '' ZH d.s:=by
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have dG:lcs G 1≤⁅ZA (ZF (fun j:Fin d.s=>u j.val)),
      ZA (ZF (fun j:Fin d.s=>u j.val))⁆⊔lcs G 2:=by
    rw[wc]
    exact hS.vZ
  have rL:=(Mult3.j8 (p:=p) hG
    (fun j:Fin d.s=>u j.val) dG kB).1
  refine ⟨KC.map (bV.equivFun:Additive (VQ p G)≃ₗ[ZMod p] _).toLinearMap,
    W6 _ _,fun w hw QG=>?_,fun w hw j hj v=>?_⟩
  · obtain ⟨x,hx,rfl⟩:=WZ.mp hw
    have hxU:x∈U:=by
     have oQ:x =∑ t,bV.equivFun x t•bV t:=(bV.sum_equivFun x).symm
     rw[oQ]
     refine Submodule.sum_mem _ fun t _=>?_
     by_cases ht:D.2.1.val≤t.val
     · have h0:bV.equivFun x t=0:=QG t ht
       rw[h0,zero_smul]
       exact VA _
     · exact VE _ _ (hUb t (by omega))
    have kH:x∈KC⊓U:=U7.mpr ⟨hx,hxU⟩
    rw[rL,VS]at kH
    rw[kH,map_zero]
  · obtain ⟨x,hx,rfl⟩:=WZ.mp hw
    have key:∀ y:Additive (VQ p G),bW.repr (cP (p:=p) (G:=G) (bV j) y) v=
        ∑ t,Alt2.gW (cP (p:=p) (G:=G)) bV bW v j t *bV.equivFun y t:=by
     intro y
     conv_lhs=>rw[← bV.sum_equivFun y]
     rw[map_sum,map_sum]
     simp only[map_smul,Finsupp.coe_finsetSum,Py,Finsupp.smul_apply,
       smul_eq_mul,Alt2.gW]
     exact Zw rfl fun t _=>mul_comm _ _
    rw[heq]
    show ∑ t,Alt2.gW (cP (p:=p) (G:=G)) bV bW v j t *bV.equivFun x t=0
    rw[← key x]
    have h0:cP (p:=p) (G:=G) x (bV j)=0:=
      (Mult3.v9.mp hx) _ (hUb j hj)
    rw [Mult3.yW _ Mult3.Bd (bV j) x,h0,neg_zero,map_zero,
      Finsupp.coe_zero,Pi.zero_apply]
end M3tTuple
section M3tStrat
variable {p:ℕ}
def FQ {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:a9 m) (h2:2<D.1.val)
    (k:ℕ):
    Set ((Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))×
      (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))):=
  {y | y.1∈tD hp T D ∧∃ K:Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p),
    finrank (ZMod p) K=k∧
    (∀ w∈K,(∀ t:Fin (aF D (aP h2)),D.2.1.val≤t.val→w t=0)→w=0)∧
    y.2∈ez hp T D h2 y.1 K}
lemma lZ {ι α:Type*} [DecidableEq ι] (I:Finset ι) (S:ι→ Set α):
    (⋃ i∈I,S i).ncard≤∑ i∈I,(S i).ncard:=by
 refine Xn I ?_ ?_
 · simp
 · intro a J ha ih
   rw[Sh,TV ha]
   exact (Tj _ _).trans (TE ih _)
lemma Cw {m :ℕ} [Fact p.Prime] (hp:p.Prime) (T:Set FiniteGrp.{0})
    (D:a9 m) (h2:2<D.1.val) (h3:D.1.val=3) (k:ℕ):
    (FQ hp T D h2 k).ncard*p^(D.2.1.val*k*aF D (aY h2))≤
      p^kC (bT D)*(2^aF D (aP h2)*p^(k*(aF D (aP h2) - k)))*
      ((∑ β ∈ (ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 - aF D (aY h2))*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β))*
        p ^(((aF D (aP h2)).choose 2 - aF D (aY h2))*
          ∑ v,bT D ⟨bY h2,v⟩)):=by
  classical
  have:NeZero p:=⟨hp.ne_zero⟩
  have:Finite (Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p)):=Bn
  set R := (∑ β∈(ZM (min (∑ v,bT D ⟨aY h2,v⟩)
          (∑ v,bT D ⟨bY h2,v⟩)+1)).filter
          (fun β=> (∑ v,bT D ⟨bY h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(aF D (aY h2)+(∑ v,bT D ⟨bY h2,v⟩)+1 - β)))*
          p ^ (((aF D (aP h2)).choose 2 - aF D (aY h2))*
              (∑ v,bT D ⟨aY h2,v⟩) - (aF D (aP h2) - D.2.1.val).choose 2*β))*
        p ^(((aF D (aP h2)).choose 2 - aF D (aY h2))*
          ∑ v,bT D ⟨bY h2,v⟩) with hR
  set Gr :Set (Submodule (ZMod p) (Fin (aF D (aP h2))→ZMod p)):=
    {K | finrank (ZMod p) K=k∧
      ∀ w∈K,(∀ t:Fin (aF D (aP h2)),D.2.1.val≤t.val→w t=0)→w=0} with hGr
  set IB:=(Zl (tD hp T D)).toFinset with hIB
  set IK:=(Zl Gr).toFinset with hIK
  have jp:FQ hp T D h2 k⊆ ⋃ B∈IB, ⋃ K∈IK,
      (({B}:Set _)×ˢ ez hp T D h2 B K):=by
   rintro ⟨B,C⟩ ⟨hB,K,hKk,hK,hC⟩
   refine VJ.mpr ⟨B,(Zl _).mem_toFinset.mpr hB,?_⟩
   exact VJ.mpr ⟨K,(Zl _).mem_toFinset.mpr ⟨hKk,hK⟩,
     Sj rfl hC⟩
  have hKb:∀ B,∀ K∈IK,(ez hp T D h2 B K).ncard*
      p^(D.2.1.val*k*aF D (aY h2))≤R:= fun B K hK=>by
    obtain ⟨hKk,hK'⟩:=(Zl _).mem_toFinset.mp hK
    have h:=vV hp T D h2 h3 B K hK'
    rwa[hKk]at h
  have aez:IK.card≤2^aF D (aP h2)*p^(k*(aF D (aP h2) - k)):=by
   have h:=Alt2.A9 (F:=ZMod p) (n:=aF D (aP h2)) k
   rw[TP]at h
   calc IK.card=Gr.ncard:=(Yt Gr (Zl Gr)).symm
     _≤_:=Yk (fun K hK=>hK.1) (Zl _)
     _≤_:=h
  have ad9 :IB.card≤p^kC (bT D):=by
   calc IB.card=(tD hp T D).ncard:=
         (Yt _ (Zl (tD hp T D))).symm
     _ ≤ _ :=(CZ hp T D).trans
           (KJ (p:=p) D.1.val (aF D) (bT D) (CX D))
  calc (FQ hp T D h2 k).ncard*p^(D.2.1.val*k*aF D (aY h2))
      ≤ (∑ B∈IB,∑ K∈IK,(ez hp T D h2 B K).ncard)*
          p^(D.2.1.val*k*aF D (aY h2)):=by
        refine Za _ ((Yk jp (Zl _)).trans ?_)
        refine (lZ IB _).trans (Z9 fun B _=>?_)
        refine (lZ IK _).trans (Z9 fun K _=>?_)
        exact WT (by rw[RM,P5,Nat.one_mul])
    _ = ∑ B∈IB,∑ K∈IK,(ez hp T D h2 B K).ncard*
          p^(D.2.1.val*k*aF D (aY h2)):=by
        rw[Wi]
        exact Zw rfl fun B _=>Wi _ _ _
    _ ≤ ∑ _B∈IB,∑ _K∈IK,R:=
        Z9 fun B _=>Z9 fun K hK=>hKb B K hK
    _ = IB.card*(IK.card*R):=by
        rw[Y5,Y5,smul_eq_mul,smul_eq_mul]
    _ ≤ p ^kC (bT D)*((2^aF D (aP h2)*p^(k*(aF D (aP h2) - k)))*
          R):=Zr ad9 (Za _ aez)
    _=_:=by ring
lemma aE.Kk {m:ℕ} [Fact p.Prime] (hp:p.Prime) (T:Set FiniteGrp.{0})
    {G:FiniteGrp.{0}} (Qb:G∈T) (hG:IsPGroup p G) {u:ℕ→G} {d:aO}
    {X:Fin d.n→G} {r :ℕ→ℕ} (hS:aE p u d X r)
    (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m) {D:a9 m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.k_ hp m bZ bU hsum=⟨D,(B,C)⟩) (h2:2<D.1.val)
    (kB:bD G=D.2.1.val):
    (B, C)∈FQ hp T D h2 (finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G))
        (Mult3.cT (p:=p) (fun j:Fin d.s=>u j.val)))):=by
  obtain ⟨-,cf2, -⟩:=hS.kS hp bZ bU hsum e
  have xP:dW hp m G (⟨D,(B,C)⟩:cQ p m):=⟨u,d,X,r,hS,bZ,bU,hsum,e⟩
  obtain ⟨K,hKk,hK,hkc⟩:=hS.acp hp bZ bU hsum e h2 hG (cf2.trans kB.symm)
  exact ⟨⟨G,Qb,C,xP⟩,K,hKk,hK,⟨G,Qb,xP⟩,hkc⟩
end M3tStrat
section M3tMult
variable {p:ℕ}
lemma zA [Fact p.Prime] (hp:p.Prime) {G:Type} [Group G] [Finite G]
    (hG:IsPGroup p G) {u₁:ℕ→G} {d₁:aO} {X₁:Fin d₁.n→G} {r₁:ℕ→ℕ}
    {u₂:ℕ→G} {d₂:aO} {X₂:Fin d₂.n→G} {r₂:ℕ→ℕ}
    (jE:aE p u₁ d₁ X₁ r₁) (lM:aE p u₂ d₂ X₂ r₂) {m:ℕ}
    (nP:d₁.n≤ m) (oE:2≤d₁.s) (l_:∑ t,d₁.a t=m)
    (n7:d₂.n≤ m) (oL:2≤d₂.s) (l7:∑ t,d₂.a t=m) {D:a9 m}
    {B₁ B₂:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e₁:jE.k_ hp m nP oE l_=⟨D,(B₁,C)⟩)
    (e₂:lM.k_ hp m n7 oL l7=⟨D,(B₂,C)⟩) (h2:2<D.1.val)
    (hW:∀ v<aW D 1,dE d₁ X₁ (aW D 0+v)=dE d₂ X₂ (aW D 0+v))
    {j t:ℕ} (hj:j<aW D 0) (ht:t<aW D 0):
    cP (p:=p) (G:=G) (ZC (dH p G (dE d₁ X₁ j)))
        (ZC (dH p G (dE d₁ X₁ t)))=
      cP (p:=p) (G:=G) (ZC (dH p G (dE d₂ X₂ j)))
        (ZC (dH p G (dE d₂ X₂ t))):=by
 obtain ⟨bV₁,bW₁,hw₁,ab9,adO,adA⟩:=jE.Cr hp nP oE l_ e₁ h2 hG
 obtain ⟨bV₂,bW₂,hw₂,acV,adL,adV⟩:=lM.Cr hp n7 oL l7 e₂ h2 hG
 have hbW:∀ v,bW₁ v=bW₂ v:=by
  intro v
  rw[adO v,adL v]
  exact congrArg (fun y:lcs G 1=>ZC (jL p G y))
    (Zu (hW v.val v.isLt))
 let jj:Fin (aF D (aP h2)):=⟨j,hj⟩
 let tt:Fin (aF D (aP h2)):=⟨t,ht⟩
 have h1:cP (p:=p) (G:=G) (bV₁ jj) (bV₁ tt)=
     ∑ v,gT p (jN D h2 C).1 v jj tt•bW₁ v:=by
  rw[adA]
  exact (bW₁.sum_repr _).symm
 have jM:cP (p:=p) (G:=G) (bV₂ jj) (bV₂ tt)=
     ∑ v,gT p (jN D h2 C).1 v jj tt•bW₂ v:=by
  rw[adV]
  exact (bW₂.sum_repr _).symm
 have e1:bV₁ jj=ZC (dH p G (dE d₁ X₁ j)):=ab9 jj
 have e2:bV₁ tt=ZC (dH p G (dE d₁ X₁ t)):=ab9 tt
 have e3:bV₂ jj=ZC (dH p G (dE d₂ X₂ j)):=acV jj
 have e4:bV₂ tt=ZC (dH p G (dE d₂ X₂ t)):=acV tt
 rw[e1,e2]at h1
 rw[e3,e4]at jM
 rw[h1,jM]
 exact Zw rfl fun v _=>by rw[hbW v]
end M3tMult
section M3tDiv
variable {p:ℕ}
end M3tDiv
section M3tFamily
variable {G:Type u} [Group G]
lemma Ku (p s:ℕ) (u:ℕ→G) {L0 L0':lB G} (hs:0<s)
    (h:∀ a<s,L0.x a=L0'.x a) (w:ℕ):
    a7 p s u L0 (w+1)=a7 p s u L0' (w+1):=by
 induction w with
 | zero=>
   show a7 p s u L0 1=a7 p s u L0' 1
   rw[v7,v7]
   have hc:dN s u 0 L0=dN s u 0 L0':=by
    funext j
    unfold dN
    have e1:fO s 0 j=j % s:=sP
    rw[e1,h (j % s) (W3 _ hs)]
    by_cases hc:j % s<fq s 0 j<;>simp[hc]
   rw[hc,DQ,DQ]
 | succ w ih=>
   rw[p8 p s u L0 (w+1),p8 p s u L0' (w+1),ih]
lemma Ck [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    {s:ℕ} (hs:2≤ s) (u:ℕ→G) (fo:cD (pN p G) u s)
    (hW:dO (pN p G) u s=lcs G 1) (L0:lB G) (kH:∀ a<s,L0.x a=u a)
    (j_:s≤L0.r) (vh:ZA (L0.x '' ZH L0.r)=⊤)
    (QI:∀ i<L0.r,L0.x i∉ZA (L0.x '' ZH i)⊔cE p G):
    ∃ (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ),d.s=s∧d.n≤ m∧∑ t,d.a t=m∧
      r 0=L0.r∧r 1=(a7 p s u L0 1).r∧aE p u d X r∧
      (∀ i<L0.r,dE d X i=L0.x i)∧
      (∀ v< (a7 p s u L0 1).r,dE d X (L0.r+v)=(a7 p s u L0 1).x v):=by
 have:Fact p.Prime:=⟨hp⟩
 have nD:IsPGroup p G:=YK hG
 have:XN G:=nD.isNilpotent
 have k6:0<s:=by omega
 have dG:=DB hp hG hW
 have hU:=MY p s u L0 hp hG k6 kH (by rw[vh,OQ]) dG j_
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=Yh.mp inferInstance
 have hL:lcs G (N+1+1)=⊥:=
   le_bot_iff.mp (hN▸bC (D:=G) (show N≤N+1+1 by omega))
 have AN:∀ w i,i< (a7 p s u L0 w).r→(a7 p s u L0 w).x i∉
     ZA ((a7 p s u L0 w).x '' ZH i)⊔dC p G w:=by
  intro w i hi
  rcases w with _ | w
  · exact QI i hi
  · exact GJ p s u L0 w hi
 have Heq:∀ w,ZA ((a7 p s u L0 w).x '' ZH (a7 p s u L0 w).r)⊔
     dC p G w=lcs G w:=by
  intro w
  rcases w with _ | w
  · show ZA (L0.x '' ZH L0.r)⊔cE p G=lcs G 0
    rw[vh,OQ,lcs_zero]
  · apply le_antisymm
    · refine sup_le ?_ (oO p w)
      rw[ZE]
      rintro _ ⟨i, -,rfl⟩
      exact nT p s u L0 (w+1) i
    · exact (hU w).trans (SD (dD p (w+1)) _)
 have DY:∀ w,p^(a7 p s u L0 w).r*ZB (dC p G w)=ZB (lcs G w):=by
  intro w
  have cI:∀ i,(a7 p s u L0 w).x i∈lcs G w:= fun i=>nT p s u L0 w i
  have hN':∀ j,(ZA ((a7 p s u L0 w).x '' ZH j)⊔
      dC p G w).Normal:=
    fun j=>jU p w _ (by rintro _ ⟨i, -,rfl⟩; exact cI i)
  have h1:=r6 hp hG (dC p G w) (v:=(a7 p s u L0 w).x) (a7 p s u L0 w).r
    (fun k hk=>AN w k hk)
  have h2:=lC hp.pos (dC p G w) (a7 p s u L0 w).x hN'
    (fun j=>qG p w _ (cI j)) (a7 p s u L0 w).r
  rw[Heq w]at h1 h2
  exact le_antisymm h1 h2
 have jq:∀ w i,i< (a7 p s u L0 (w+1)).r→
     (a7 p s u L0 (w+1)).lK i< (a7 p s u L0 w).r :=
   fun w i hi=> (l9 p s u L0 k6 j_ w hi).1
 have jt:∀ w i,i< (a7 p s u L0 (w+1)).r→(a7 p s u L0 (w+1)).gC i<s:=
   fun w i hi=> (l9 p s u L0 k6 j_ w hi).2.1
 have H1:∀ i,i< (a7 p s u L0 1).r→(a7 p s u L0 1).lK i< (a7 p s u L0 1).gC i:=
   fun i hi=> (l9 p s u L0 k6 j_ 0 hi).2.2.1 rfl
 have Hx:∀ w i,i< (a7 p s u L0 (w+1)).r→(a7 p s u L0 (w+1)).x i=
     ⁅(a7 p s u L0 w).x ((a7 p s u L0 (w+1)).lK i),
       (a7 p s u L0 0).x ((a7 p s u L0 (w+1)).gC i)⁆:=by
  intro w i hi
  obtain ⟨-,hc, -,he⟩:=l9 p s u L0 k6 j_ w hi
  have e0:(a7 p s u L0 0).x ((a7 p s u L0 (w+1)).gC i)=
      u ((a7 p s u L0 (w+1)).gC i):=kH _ hc
  rw[e0]
  exact he
 have Mh:∀ k≤ s,∀ a b,a<b→ b<k→⁅u a,u b⁆∈
     ZA ((a7 p s u L0 1).x ''
       {i | i< (a7 p s u L0 1).r∧(a7 p s u L0 1).gC i<k})⊔pN p G:=
   fun k hk a b hab hb=>mK p s u L0 k6 kH hk hab hb
 have AY:∀ i i',i≤ i'→i'< (a7 p s u L0 1).r→
     (a7 p s u L0 1).gC i≤(a7 p s u L0 1).gC i':=
   fun i i' h gJ=>t9 p s u L0 h gJ
 have F8:∀ i i',i< (a7 p s u L0 1).r→i'< (a7 p s u L0 1).r→
     (a7 p s u L0 1).lK i=(a7 p s u L0 1).lK i'→
     (a7 p s u L0 1).gC i=(a7 p s u L0 1).gC i'→i=i':=
   fun i i' hi gJ Ou hc=>Dl p s u L0 hi gJ Ou hc
 have Hw3:∀ i,i< (a7 p s u L0 2).r→
     (a7 p s u L0 2).gC i≤(a7 p s u L0 1).gC ((a7 p s u L0 2).lK i):=
   fun i hi=>Qd p s u L0 hi
 obtain ⟨d,X,oW,nF,rV⟩:=GI (L:=N+1)
   (r := fun w=> (a7 p s u L0 w).r) (xs:= fun w i=> (a7 p s u L0 w).x i)
   (pa:= fun w i=> (a7 p s u L0 w).lK i) (co:= fun w i=> (a7 p s u L0 w).gC i)
   hp hG u j_ jq jt H1 Hx kH vh (fun w _=>hU w) hL (by omega) AN
   (fun w _=>DY w) Mh AY F8 fo Hw3
 have hsum:∑ t,d.a t=m:=by
  have h1:=nF.e9.card
  rw[hG]at h1
  exact (Zd hp.two_le h1).symm
 refine ⟨d,X,bR (N+1) (fun w=> (a7 p s u L0 w).r),oW,?_,hsum,?_,?_,nF,?_,?_⟩
 · rw[← hsum]
   exact nF.Fn
 · exact k4 (Zv _)
 · exact k4 (by omega)
 · intro i hi
   have h:=rV 0 i (Zv _) hi
   have e:∀ q:ℕ→ℕ,aD q 0+i=i:= fun q=>XL i
   rw[e]at h
   exact h
 · intro v hv
   have h:=rV 1 v (by omega) hv
   rw[po]at h
   exact h
def jR (s z:ℕ) (u y:ℕ→G):lB G where
  r :=s+z
  x:= fun i=>if i<s then u i else y (i - s)
  lK:=id
  gC:=id
lemma mo {s z:ℕ} {u y:ℕ→G} {i:ℕ} (h:i<s):(jR s z u y).x i=u i:=
  if_pos h
lemma r9 {s z:ℕ} {u y:ℕ→G} (l:ℕ):(jR s z u y).x (s+l)=y l:=by
 show (if s+l<s then u (s+l) else y (s+l - s))=y l
 rw[if_neg (by omega),Yb]
lemma NZ [Finite G] {p:ℕ} [Fact p.Prime] (nD:IsPGroup p G) {s:ℕ} (u:ℕ→G)
    (gO:∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G)
    (Z:Submodule (ZMod p) (Additive (VQ p G)))
    (hZ:Z⊓Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊥)
    (r8:Z⊔Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊤)
    (z:ℕ) (hz:finrank (ZMod p) Z=z) (x:Fin z→Z) (hx:LinearIndependent (ZMod p) x)
    (y:ℕ→G)
    (hy:∀ l (hl:l<z),ZC (dH p G (y l))=((x ⟨l,hl⟩:Z):Additive (VQ p G))):
    Subgroup.closure ((jR s z u y).x '' ZH (jR s z u y).r)=⊤∧
      ∀ i< (jR s z u y).r,(jR s z u y).x i∉
        ZA ((jR s z u y).x '' ZH i)⊔cE p G:=by
  have:Finite (VQ p G):=Zy _ cV
  have:Finite (Additive (VQ p G)):=inferInstance
  have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
  have ac1:∀ g∈cE p G,ZC (dH p G g)=0:=by
   intro g hg
   have h:g∈(dH p G).ker :=by rw[Ky]; exact hg
   rw[Zm.mp h]
   rfl
  constructor
  · apply eD
    rw[ew nD,Yo]
    intro g _
    have adN:Mult3.cT (p:=p) (fun j:Fin s=>u j.val)≤Mult3.C9 (p:=p)
        (ZA ((jR s z u y).x '' ZH (jR s z u y).r)):=by
      unfold Mult3.cT
      rw[YU]
      rintro _ ⟨j,rfl⟩
      refine Mult3.Ao.mpr ⟨u j.val,ZD ⟨j.val,?_,mo j.isLt⟩,
        rfl⟩
      show j.val<s+z
      have:=j.isLt
      omega
    have qU:ZQ (ZMod p) (ZF x)=⊤:=
      hx.span_eq_top_of_card_eq_finrank' (by rw[Zz,hz])
    have ad6:Z≤Mult3.C9 (p:=p)
        (ZA ((jR s z u y).x '' ZH (jR s z u y).r)):=by
     intro v hv
     have h1:ZQ (ZMod p) (ZF x)≤(Mult3.C9 (p:=p)
         (ZA ((jR s z u y).x '' ZH (jR s z u y).r))).comap
           Z.subtype:=by
      rw[YU]
      rintro _ ⟨l,rfl⟩
      refine Submodule.mem_comap.mpr (Mult3.Ao.mpr ⟨y l.val,
        ZD ⟨s+l.val,?_,r9 l.val⟩,hy l.val l.isLt⟩)
      show s+l.val<s+z
      have:=l.isLt
      omega
     have h2:(⟨v,hv⟩:Z)∈ZQ (ZMod p) (ZF x):=by
      rw[qU]
      exact XK
     exact h1 h2
    have hv:ZC (dH p G g)∈Mult3.C9 (p:=p)
        (ZA ((jR s z u y).x '' ZH (jR s z u y).r)):=by
     have h0:ZC (dH p G g)∈
         Z⊔Mult3.cT (p:=p) (fun j:Fin s=>u j.val):=by
       rw[r8]
       exact XK
     exact (sup_le ad6 adN) h0
    obtain ⟨b,hb,hbg⟩:=Mult3.Ao.mp hv
    have hpe:dH p G g=dH p G b:=(congrArg ZW hbg).symm
    rw[Bb]at hpe
    rw[← inv_mul_cancel_right g b]
    exact Yq _ (ZL hpe) (ZK hb)
  · intro i hi cI
    have gJ:i<s+z:=hi
    by_cases K6:i<s
    · have qv:(jR s z u y).x '' ZH i=u '' ZH i:=
        Set.image_congr (fun j hj=>mo (Uj (Yw.mp hj) K6))
      rw[mo K6,qv]at cI
      exact gO i K6 cI
    · obtain ⟨l,rfl⟩:∃ l,i=s+l:=⟨i - s,by omega⟩
      have hl:l<z:=by omega
      rw[r9]at cI
      obtain ⟨Wv,hWv⟩:∃ Wv:Submodule (ZMod p) (Additive (VQ p G)),
          Wv = Mult3.cT (p:=p) (fun j:Fin s=>u j.val)⊔
            ZQ (ZMod p) ((fun l':Fin z=> ((x l':Z):Additive (VQ p G))) ''
              {l' | l'.val<l}):=⟨_,rfl⟩
      have cO :ZA ((jR s z u y).x '' ZH (s+l))⊔cE p G≤
          Alt2.acR (p:=p) Wv:=by
       refine sup_le ?_ ?_
       · rw [ZE]
         rintro _ ⟨j,hj,rfl⟩
         have mC:j<s+l:=hj
         show ZC (dH p G ((jR s z u y).x j))∈Wv
         rw[hWv]
         by_cases O2:j<s
         · rw[mo O2]
           exact Submodule.mem_sup_left (Z1 ⟨⟨j,O2⟩,rfl⟩)
         · obtain ⟨l',rfl⟩:∃ l',j=s+l':=⟨j - s,by omega⟩
           have hl':l'<z:=by omega
           rw[r9,hy l' hl']
           exact Submodule.mem_sup_right (Z1
             ⟨⟨l',hl'⟩,show l'<l by omega,rfl⟩)
       · intro g hg
         show ZC (dH p G g)∈Wv
         rw[ac1 g hg]
         exact Wv.zero_mem
      have h1:((x ⟨l,hl⟩:Z):Additive (VQ p G))∈Wv:=by
       rw[← hy l hl]
       exact cO cI
      rw[hWv]at h1
      obtain ⟨a,ha,b,hb,hab⟩:=Ru.mp h1
      have hbZ:b∈Z:=by
       refine (YU.mpr ?_) hb
       rintro _ ⟨l', -,rfl⟩
       exact (x l').2
      have haZ:a∈Z:=by
       rw[eq_sub_of_add_eq hab]
       exact Z.sub_mem (x ⟨l,hl⟩).2 hbZ
      have ML:a=0:=by
       have h0:a∈Z⊓Mult3.cT (p:=p) (fun j:Fin s=>u j.val):=
         U7.mpr ⟨haZ,ha⟩
       rw[hZ,VS]at h0
       exact h0
      rw[ML,zero_add]at hab
      have hli:LinearIndependent (ZMod p)
          (fun l':Fin z=> ((x l':Z):Additive (VQ p G))):=
        hx.map' Z.subtype (Submodule.ker_subtype Z)
      apply hli.notMem_span_image (s:={l':Fin z | l'.val<l}) (x:=⟨l,hl⟩) (by simp)
      have h2:((x ⟨l,hl⟩:Z):Additive (VQ p G))∈ZQ (ZMod p)
          ((fun l':Fin z=> ((x l':Z):Additive (VQ p G))) '' {l' | l'.val<l}):=
        hab▸hb
      exact h2
lemma Jn [Finite G] {p m:ℕ} [Fact p.Prime] (hp:p.Prime)
    (hG:ZB G=p^m) {s:ℕ} (hs:2≤ s) (u:ℕ→G)
    (fo:cD (pN p G) u s) (hW:dO (pN p G) u s=lcs G 1)
    (gO:∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G)
    (Z:Submodule (ZMod p) (Additive (VQ p G)))
    (hZ:Z⊓Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊥)
    (r8:Z⊔Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊤)
    (x:Fin (finrank (ZMod p) Z)→Z) (hx:LinearIndependent (ZMod p) x):
    ∃ (d :aO) (X:Fin d.n→G) (r :ℕ→ℕ),d.s=s∧d.n≤ m∧∑ t,d.a t=m∧
      r 0=s+finrank (ZMod p) Z∧r 1=(a7 p s u (gd p s u) 1).r∧aE p u d X r∧
      (∀ j<s,dE d X j=u j)∧
      (∀ l:Fin (finrank (ZMod p) Z),
        ZC (dH p G (dE d X (s+l.val)))=((x l:Z):Additive (VQ p G)))∧
      (∀ v< (a7 p s u (gd p s u) 1).r,
        dE d X (s+finrank (ZMod p) Z+v)=(a7 p s u (gd p s u) 1).x v):=by
  have nD:IsPGroup p G:=YK hG
  obtain ⟨y,hy⟩:∃ y:ℕ→G,∀ l (hl:l<finrank (ZMod p) Z),
      ZC (dH p G (y l))=((x ⟨l,hl⟩:Z):Additive (VQ p G)):=
    ⟨fun l=>if h:l<finrank (ZMod p) Z then
        oq (ZW ((x ⟨l,h⟩:Z):Additive (VQ p G))) else 1,fun l hl=>by
      dsimp only
      rw[dif_pos hl,xZ,ofMul_toMul]⟩
  obtain ⟨vh,QI⟩:=NZ nD u gO Z hZ r8 (finrank (ZMod p) Z) rfl x hx y hy
  obtain ⟨d,X,r,oW,bZ,hsum,j_,jB,hS,abL,adh⟩:=
    Ck hp hG hs u fo hW (jR s (finrank (ZMod p) Z) u y)
      (fun a ha=>mo ha) (by show s≤ s+_; omega) vh QI
  have Q8:a7 p s u (jR s (finrank (ZMod p) Z) u y) 1=a7 p s u (gd p s u) 1:=
    Ku p s u (by omega) (fun a ha=>by rw[mo ha,n8 p s u ha]) 0
  refine ⟨d,X,r,oW,bZ,hsum,j_,jB.trans (by rw[Q8]),hS,fun j hj=>?_,
    fun l=>?_,fun v hv=>?_⟩
  · rw[abL j (by show j<s+_; omega),mo hj]
  · rw[abL (s+l.val) (by show s+l.val<s+_; have:=l.isLt; omega),r9]
    exact hy l.val l.isLt
  · have h:=adh v (by rw[Q8]; exact hv)
    rw[Q8]at h
    exact h
lemma oM [Finite G] {p m:ℕ} [Fact p.Prime] (hp:p.Prime)
    (hG:ZB G=p^m) (wJ:lcs G 1≠⊥):
    2 ≤ bD G∧∃ u:ℕ→G,cD (pN p G) u (bD G)∧
      dO (pN p G) u (bD G)=lcs G 1∧
      (∀ k<bD G,u k∉ZA (u '' ZH k)⊔cE p G)∧
      ∃ Z :Submodule (ZMod p) (Additive (VQ p G)),
        Z⊓Mult3.cT (p:=p) (fun j:Fin (bD G)=>u j.val)=⊥∧
        Z⊔Mult3.cT (p:=p) (fun j:Fin (bD G)=>u j.val)=⊤∧
        finrank (ZMod p) Z+bD G=ZV G∧
        finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G))
          (Mult3.cT (p:=p) (fun j:Fin (bD G)=>u j.val)))+bD G≤
          ZV G:=by
  have nD:IsPGroup p G:=YK hG
  have:Finite (VQ p G):=Zy _ cV
  have:Finite (Additive (VQ p G)):=inferInstance
  have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
  obtain ⟨bU,u,fo,hW,gO,dG⟩:=E4 hp hG wJ
  obtain ⟨Z,hZ⟩:=SU
    (Mult3.cT (p:=p) (fun j:Fin (bD G)=>u j.val))
  have wc:ZF (fun j:Fin (bD G)=>u j.val)=u '' ZH (bD G):=by
    ext w
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have aaJ:lcs G 1≤⁅ZA (ZF (fun j:Fin (bD G)=>u j.val)),
      ZA (ZF (fun j:Fin (bD G)=>u j.val))⁆⊔lcs G 2:=by
    rw[wc]
    exact dG
  obtain ⟨-,F5⟩:=Mult3.j8 (p:=p) nD
    (fun j:Fin (bD G)=>u j.val) aaJ rfl
  have h:=V5 Z
    (Mult3.cT (p:=p) (fun j:Fin (bD G)=>u j.val))
  rw[hZ.symm.inf_eq_bot,hZ.symm.sup_eq_top,finrank_bot,SY,F5]at h
  have hfr :finrank (ZMod p) (Additive (VQ p G))=ZV G:=
    Zd hp.two_le
      ((i8 (p:=p) (cE p G)).symm.trans (My nD))
  have GW:=Mult3.vq (p:=p) nD
    (fun j:Fin (bD G)=>u j.val) aaJ rfl
  refine ⟨bU,u,fo,hW,gO,Z,hZ.symm.inf_eq_bot,hZ.symm.sup_eq_top,?_,GW⟩
  omega
end M3tFamily
section M3tFull
variable {p:ℕ}
lemma B5 [Fact p.Prime] (hp:p.Prime) {G:Type} [Group G] [Finite G]
    (hG:IsPGroup p G) {m s:ℕ} (u:Fin s→G) (Z:Submodule (ZMod p) (Additive (VQ p G)))
    (z0:ℕ) (y:ℕ→G)
    (F:{x:Fin (finrank (ZMod p) Z)→Z//LinearIndependent (ZMod p) x}→ cQ p m)
    (hF :∀ x,∃ (u':ℕ→G) (d:aO) (X:Fin d.n→G) (r :ℕ→ℕ)
      (hS:aE p u' d X r) (bZ:d.n≤ m) (bU:2≤d.s) (hsum:∑ t,d.a t=m),
      hS.k_ hp m bZ bU hsum=F x∧2< (F x).1.1.val∧s≤aW (F x).1 0∧
      z0+finrank (ZMod p) Z≤aW (F x).1 0∧(∀ j:Fin s,dE d X j.val=u j)∧
      (∀ l:Fin (finrank (ZMod p) Z),
        ZC (dH p G (dE d X (z0+l.val)))=((x.1 l:Z):Additive (VQ p G)))∧
      ∀ v<aW (F x).1 1,dE d X (aW (F x).1 0+v)=y v):
    Nat.card (ZMod p)^(finrank (ZMod p) Z*(finrank (ZMod p) Z - 1))≤
      ZB (ZF F)*ZB (ZMod p)^(finrank (ZMod p) Z*
        finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G)) (Mult3.cT (p:=p) u))):=by
 have:NeZero p:=⟨hp.ne_zero⟩
 have:Finite (VQ p G):=Zy _ cV
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Yx (ZMod p) (Additive (VQ p G)):=inferInstance
 have hpc:=Mult3.Jm (cP (p:=p) (G:=G)) Mult3.Bd
   (fun j=>ZC (dH p G (u j))) Z
 refine hpc.trans (Za _ ?_)
 set R:= fun x:{x:Fin (finrank (ZMod p) Z)→Z//LinearIndependent (ZMod p) x}=>
   Mult3.zj (cP (p:=p) (G:=G)) (fun j=>ZC (dH p G (u j)))
     (fun l=> (x.1 l:Additive (VQ p G))) with aeN
 have hRF:∀ x x',F x =F x'→R x =R x':=by
  intro x x' hxx
  obtain ⟨u1,d1,X1,r1',MQ,aeF,aeB,abN,e1,h2a,Ow,hza,lT,hz1,Fd⟩:=hF x
  obtain ⟨u2,d2,X2,r2',Mz,ael,adH,Ql,e2, -, -, -,uL,hz2,H_⟩:=hF x'
  rw[hxx]at e1 h2a Ow hza Fd
  funext l j
  show cP (p:=p) (G:=G) (ZC (dH p G (u j))) (x.1 l:Additive (VQ p G))=
    cP (p:=p) (G:=G) (ZC (dH p G (u j))) (x'.1 l:Additive (VQ p G))
  conv_lhs=>rw[← hz1 l, ← lT j]
  conv_rhs=>rw[← hz2 l, ← uL j]
  revert e1 e2 h2a Ow hza Fd H_
  generalize F x'=q
  obtain ⟨D,B,C⟩:=q
  intro e1 h2a Ow hza Fd e2 H_
  have jM:2<D.1.val:=h2a
  have aeS:s≤aW D 0:= Ow
  have aeV:z0+finrank (ZMod p) Z≤aW D 0:=hza
  exact zA hp hG MQ Mz aeF aeB abN ael adH Ql
    (D:=D) (B₁:=B) (B₂:=B) (C:=C) e1 e2 jM
    (fun v hv=> (Fd v hv).trans (H_ v hv).symm) (by have:=j.isLt; omega)
    (by have:=l.isLt; omega)
 let g:ZF F→ZF R:= fun yy=> ⟨R (XP yy.2),_,rfl⟩
 have hg:Zn g:=by
  rintro ⟨_,x,rfl⟩
  refine ⟨⟨F x,x,rfl⟩,Zu ?_⟩
  exact hRF _ _ (Ym (⟨x,rfl⟩:∃ x',F x'=F x))
 exact YO g hg
lemma wS {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (E:Set (cQ p m)) (A B:ℕ)
    (hT:∀ G∈T,∃ P⊆E,(∀ y∈P,dW hp m G y)∧A≤P.ncard*B):
    (Yd (YF FiniteGrp.{0}) '' T).ncard*A≤
      E.ncard*B:=by
 classical
 rcases T.eq_empty_or_nonempty with hT0 | ⟨G0, -⟩
 · rw[hT0,Ob,Y3,R8]
   exact Zv _
 have:Nonempty FiniteGrp.{0}:=⟨G0⟩
 set Q:=Yd (YF FiniteGrp.{0}) '' T with aeP
 rcases Q.finite_or_infinite with O7 | hQi
 swap
 · rw[hQi.ncard,R8]
   exact Zv _
 have ad3:∀ q∈Q,∃ G∈T,
     Yd (YF FiniteGrp.{0}) G=q:= fun q hq=>hq
 choose! Gs adM acy using ad3
 have hP:∀ q∈Q,∃ P⊆E,(∀ y∈P,dW hp m (Gs q) y)∧A≤P.ncard*B:=
   fun q hq=>hT (Gs q) (adM q hq)
 choose! Ps hPE Lj hPA using hP
 set S:= O7.toFinset with hS
 set Pf:= fun q=> (Zl (Ps q)).toFinset with hPf
 have Gz:∀ q∈S,∀ q'∈S,q≠q'→Disjoint (Pf q) (Pf q'):=by
  intro q hq q' hq' d8
  rw[Rr]
  intro y hy IE
  apply d8
  have hq1:= O7.mem_toFinset.mp hq
  have hq2:= O7.mem_toFinset.mp hq'
  obtain ⟨e⟩:=zF hp (Lj q hq1 y ((Zl _).mem_toFinset.mp hy))
    (Lj q' hq2 y ((Zl _).mem_toFinset.mp IE))
  rw[← acy q hq1, ← acy q' hq2]
  exact Pt ⟨Wj (R7 e)⟩
 have jp:S.biUnion Pf⊆(Zl E).toFinset:=by
  intro y hy
  obtain ⟨q,hq,hyq⟩:=Finset.mem_biUnion.mp hy
  exact (Zl E).mem_toFinset.mpr
    (hPE q (O7.mem_toFinset.mp hq) ((Zl _).mem_toFinset.mp hyq))
 calc Q.ncard*A=∑ _q∈S,A:=by
       rw[Y5,smul_eq_mul,Yt _ O7]
   _ ≤ ∑ q∈S,(Pf q).card*B:=Z9 fun q hq=>by
       rw[hPf]
       dsimp only
       rw[← Yt _ (Zl _)]
       exact hPA q (O7.mem_toFinset.mp hq)
   _=(∑ q∈S,(Pf q).card)*B:=(Wi _ _ _).symm
   _=(S.biUnion Pf).card*B:=by rw[Finset.card_biUnion Gz]
   _≤(Zl E).toFinset.card*B:=Za _ (VB jp)
   _=E.ncard*B:=by rw[← Yt _ (Zl E)]
def AG {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (s k:ℕ):Set (cQ p m):=
  {y | y.1.2.1.val=s∧∃ h2:2<y.1.1.val,y.2∈FQ hp T y.1 h2 k}
def l6 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (k:ℕ) (D:a9 m):
    Set ((Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))×
      (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))):=
  {y | ∃ h2:2<D.1.val,y∈FQ hp T D h2 k}
lemma abo {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (k:ℕ) (D:a9 m)
    (h2:2<D.1.val):l6 hp T k D =FQ hp T D h2 k:=by
 ext y
 exact ⟨fun ⟨_,h⟩=>h,fun h=> ⟨h2,h⟩⟩
def qZ (m s:ℕ):Finset (a9 m):=
  ZU.filter (fun D:a9 m=>D.2.1.val=s)
lemma K5 {m s:ℕ} {D:a9 m}:D∈qZ m s↔D.2.1.val=s:=by
 unfold qZ
 rw[ZI]
 exact ⟨fun h=>h.2,fun h=> ⟨Zb _,h⟩⟩
lemma Iw {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (s k:ℕ):
    AG (m:=m) hp T s k⊆ ⋃ D∈qZ m s,
      (R9 D) '' l6 hp T k D:=by
 intro y hy
 obtain ⟨hs,h2,hy2⟩:=hy
 refine VJ.mpr ⟨y.1,K5.mpr hs,y.2,⟨h2,hy2⟩,rfl⟩
lemma Ea {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (s k:ℕ):
    (AG (m:=m) hp T s k).ncard≤∑ D∈qZ m s,(l6 hp T k D).ncard:=by
 classical
 have A6:(⋃ D∈qZ m s,(R9 D) '' l6 hp T k D).Finite:=
   Set.Finite.biUnion (Finset.finite_toSet _) fun D _=>
     Set.Finite.image _ (Zl (l6 hp T k D))
 have h1:=Yk (Iw hp T s k) A6
 have h2:=lZ (qZ m s)
   (fun D => (R9 D) '' l6 hp T k D)
 have h3:∀ D:a9 m,((R9 D:_→ cQ p m) '' l6 hp T k D).ncard≤
     (l6 hp T k D).ncard:=
   fun D =>Tm (Zl (l6 hp T k D))
 exact h1.trans (h2.trans (Z9 fun D _=>h3 D))
lemma Je {m:ℕ} [Fact p.Prime] (hp:p.Prime) (T:Set FiniteGrp.{0})
    {G:FiniteGrp.{0}} (Qb:G∈T) (hG:ZB G=p^m) {s:ℕ} (hs:2≤ s)
    (kB:bD G=s) (u:ℕ→G) (fo:cD (pN p G) u s)
    (hW:dO (pN p G) u s=lcs G 1)
    (gO:∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G)
    (Z:Submodule (ZMod p) (Additive (VQ p G)))
    (hZ:Z⊓Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊥)
    (r8:Z⊔Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊤)
    (h3:∀ y:cQ p m,dW hp m G y→2<y.1.1.val):
    ∃ P : Set (cQ p m),P⊆AG hp T s (finrank (ZMod p) (Mult3.gz
        (cP (p:=p) (G:=G)) (Mult3.cT (p:=p) (fun j:Fin s=>u j.val))))∧
      (∀ y∈P,dW hp m G y)∧
      p ^ (finrank (ZMod p) Z*(finrank (ZMod p) Z - 1))≤P.ncard*
        p ^(finrank (ZMod p) Z*finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G))
          (Mult3.cT (p:=p) (fun j:Fin s=>u j.val)))):=by
  have nD:IsPGroup p G:=YK hG
  choose d X r oW bZ hsum j_ jB hS hc hz hw using
    fun x:{x:Fin (finrank (ZMod p) Z)→Z//LinearIndependent (ZMod p) x}=>
      Jn hp hG hs u fo hW gO Z hZ r8 x.1 x.2
  have bU:∀ x,2≤(d x).s:= fun x =>by rw[oW x]; exact hs
  obtain ⟨F,hF⟩:∃ F:{x:Fin (finrank (ZMod p) Z)→Z//LinearIndependent (ZMod p) x}→
      cQ p m,∀ x,F x =(hS x).k_ hp m (bZ x) (bU x) (hsum x):=⟨_,fun x =>rfl⟩
  have xP:∀ x,dW hp m G (F x):=
    fun x => ⟨u,d x,X x,r x,hS x,bZ x,bU x,hsum x,(hF x).symm⟩
  have he:∀ x,(hS x).k_ hp m (bZ x) (bU x) (hsum x)=
      ⟨(F x).1,((F x).2.1,(F x).2.2)⟩:= fun x => (hF x).symm
  refine ⟨ZF F,?_,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    have h2:=h3 _ (xP x)
    obtain ⟨-,c2, -⟩:=(hS x).kS hp (bZ x) (bU x) (hsum x) (he x)
    have cI:=(hS x).Kk hp T Qb nD (bZ x) (bU x) (hsum x) (he x) h2
      (kB.trans ((oW x).symm.trans c2))
    have Lh:(F x).1.2.1.val=s:= c2.symm.trans (oW x)
    rw[oW x]at cI
    exact ⟨Lh,h2,cI⟩
  · rintro _ ⟨x,rfl⟩
    exact xP x
  · have U_:=B5 hp nD (fun j:Fin s=>u j.val) Z s
      (a7 p s u (gd p s u) 1).x F (fun x =>by
        have h2:=h3 _ (xP x)
        obtain ⟨c1, -,c3, -⟩:=(hS x).kS hp (bZ x) (bU x) (hsum x) (he x)
        have hf0:aW (F x).1 0=s+finrank (ZMod p) Z:=
          (c3 0 (by rw[c1]; omega)).symm.trans (j_ x)
        have hf1:aW (F x).1 1=(a7 p s u (gd p s u) 1).r :=
          (c3 1 (by rw[c1]; omega)).symm.trans (jB x)
        refine ⟨u,d x,X x,r x,hS x,bZ x,bU x,hsum x,(hF x).symm,h2,?_,?_,
          fun j=>hc x j.val j.isLt,hz x,fun v hv=>?_⟩
        · rw[hf0]
          omega
        · rw[hf0]
        · rw[hf0]
          rw[hf1]at hv
          exact hw x v hv)
    rw[TP,Xt]at U_
    exact U_
lemma Gv {m:ℕ} [Fact p.Prime] (hp:p.Prime) (T:Set FiniteGrp.{0})
    (s z k:ℕ) (hs:2≤ s)
    (hT : ∀ G∈T,ZB G=p^m∧bD G=s∧
      (∀ y:cQ p m,dW hp m G y→2<y.1.1.val)∧
      ∃ u : ℕ→G,cD (pN p G) u s∧dO (pN p G) u s=lcs G 1∧
        (∀ k<s,u k∉ZA (u '' ZH k)⊔cE p G)∧
        ∃ Z :Submodule (ZMod p) (Additive (VQ p G)),
          Z⊓Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊥∧
          Z⊔Mult3.cT (p:=p) (fun j:Fin s=>u j.val)=⊤∧
          finrank (ZMod p) Z=z∧
          finrank (ZMod p) (Mult3.gz (cP (p:=p) (G:=G))
            (Mult3.cT (p:=p) (fun j:Fin s=>u j.val)))=k):
    (Quotient.mk (YF FiniteGrp.{0}) '' T).ncard*
        p^(z*(z - 1))≤
      (∑ D∈qZ m s,(l6 hp T k D).ncard)*p^(z*k):=by
  refine (wS hp T (AG hp T s k) _ _ fun G hG=>?_).trans
    (Za _ (Ea hp T s k))
  obtain ⟨dS,kB,h3,u,fo,hW,gO,Z,hZ,r8,hzz,hkk⟩:=hT G hG
  obtain ⟨P,hPE,Lj,hPA⟩:=Je hp T hG dS hs kB u fo hW gO Z hZ r8 h3
  rw[hzz,hkk]at hPA
  rw[hkk]at hPE
  exact ⟨P,hPE,Lj,hPA⟩
end M3tFull
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
open Module CategoryTheory
section M3CB
def kT (m r1 r2 s m2 m3 r3 z k:ℕ):Set FiniteGrp.{0}:=
  {G | G ∈ fF m r1 r2 s 0 m2 m3 r3∧
    ∃ u : ℕ→G,cD (pN 2 G) u s∧dO (pN 2 G) u s=lcs G 1∧
      (∀ i<s,u i∉ZA (u '' ZH i)⊔cE 2 G)∧
      ∃ Z :Submodule (ZMod 2) (Additive (VQ 2 G)),
        Z⊓Mult3.cT (p:=2) (fun j:Fin s=>u j.val)=⊥∧
        Z⊔Mult3.cT (p:=2) (fun j:Fin s=>u j.val)=⊤∧
        finrank (ZMod 2) Z=z∧
        finrank (ZMod 2) (Mult3.gz (cP (p:=2) (G:=G))
          (Mult3.cT (p:=2) (fun j:Fin s=>u j.val)))=k}
variable {m r1 r2 s m2 m3 r3:ℕ}
lemma Nt {lam:ℕ} {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3):
    lcs G 1≠⊥:=by
 intro h
 apply hG.2.1
 rw[eq_bot_iff, ← h]
 exact bC (by norm_num)
lemma abX {lam:ℕ} {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3):
    2≤ s:=by
 have h:=(oM Ze hG.1 (Nt hG)).1
 rwa[((jc G).mp hG).2.2.2.2.2.1]at h
lemma Nh (z:ℕ):((z*(z - 1):ℕ):ℝ)=(z:ℝ)^2 - z:=by
 rcases z with _ | n
 · simp
 · rw[XI]
   push_cast
   ring
lemma abn {x P E:ℝ} {u v:ℕ} (h:x*2^u≤P*(2:ℝ)^E*2^v):
    x≤P*(2:ℝ)^(E+v - u):=by
 rw [Real.rpow_sub (by norm_num:(0:ℝ)<2),Vw (by norm_num:(0:ℝ)<2),
   Wl,Wl, ← mul_div_assoc,le_div_iff₀ (by positivity),
   ← UQ]
 exact h
lemma QQ:
    (f8 m r1 r2 s 0 m2 m3 r3).ncard≤∑ k∈ZM (r1 - s+1),
      (Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
        kT m r1 r2 s m2 m3 r3 (r1 - s) k).ncard:=by
 classical
 have jp:f8 m r1 r2 s 0 m2 m3 r3⊆ ⋃ k∈ZM (r1 - s+1),
     Yd (isIsomorphicSetoid FiniteGrp.{0}) '' kT m r1 r2 s m2 m3 r3 (r1 - s) k:=by
  rintro _ ⟨G,hG,rfl⟩
  have cI:=(jc G).mp hG
  have hsG:bD G=s:= cI.2.2.2.2.2.1
  have jB:ZV G=r1:= cI.2.2.2.1
  obtain ⟨-,u,fo,hW,gO,Z,hZ,r8,hZr,GW⟩:=
    oM Ze hG.1 (Nt hG)
  rw[hsG]at fo hW gO hZ r8 hZr GW
  exact VJ.2 ⟨_,Zt.2 (by omega),G,
    ⟨hG,u,fo,hW,gO,Z,hZ,r8,by omega,rfl⟩,rfl⟩
 have A6:(⋃ k∈ZM (r1 - s+1),Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
     kT m r1 r2 s m2 m3 r3 (r1 - s) k).Finite:=
   tL.subset (Set.iUnion₂_subset fun k _=>Uw (fun G hG=>hG.1))
 exact (Yk jp A6).trans (rD _ _)
lemma QZ {lam:ℕ} {G:FiniteGrp.{0}} (hG:G∈fF m r1 r2 s lam m2 m3 r3)
    (y:cQ 2 m) (hy:dW Ze m G y):2<y.1.1.val:=by
 obtain ⟨D,B,C⟩:=y
 have h:=(xQ hG hy).1
 show 2<D.1.val
 omega
lemma aaM {z k b2:ℕ} (bU:2≤ s) (hz:z+s=r1) (hk:k+s≤ r1)
    (kB:s≤ r1) (abg:r2≤ s.choose 2) (MG:m3≤ m2)
    (FJ:∀ β∈m5 s m2 m3,oB r1 r2 s m2 m3 β≤oB r1 r2 s m2 m3 b2):
    ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        kT m r1 r2 s m2 m3 r3 z k).ncard:ℝ)≤
      (Fintype.card (a9 m):ℝ)*2^kv r1 r2 r3 0 m2 m3*
        (((min (m2 - m3) m3:ℕ):ℝ)+1)*
        (2 :ℝ)^(oB r1 r2 s m2 m3 b2+((r1+z:ℕ):ℝ) - (z:ℝ)^2+
          (k:ℝ)*(2*(r1:ℝ) - s - k - (s:ℝ)*r2)):=by
 classical
 have GW:k≤ r1:=by omega
 have Dh:=Gv Ze (kT m r1 r2 s m2 m3 r3 z k) s z k bU
   (fun G hG=> ⟨hG.1.1,((jc G).mp hG.1).2.2.2.2.2.1,QZ hG.1,hG.2⟩)
 obtain ⟨S,DK⟩:∃ S:ℕ,S=∑ β∈m5 s m2 m3,pI r1 r2 s m2 m3 β:=⟨_,rfl⟩
 have hD:∀ D∈qZ m s,
     (l6 Ze (kT m r1 r2 s m2 m3 r3 z k) k D).ncard*2^(s*k*r2)≤
       2^kv r1 r2 r3 0 m2 m3*(2^r1*2^(k*(r1 - k)))*S:=by
  intro D hD
  rcases (l6 Ze (kT m r1 r2 s m2 m3 r3 z k) k D).eq_empty_or_nonempty
    with he | ⟨y,h2,hyB, -⟩
  · rw[he,Y3,zero_mul]
    exact Zv _
  obtain ⟨G,Qb,C,hc⟩:=hyB
  have hDc:D∈lV m r1 r2 s 0 m2 m3 r3:=
    tW.2 ⟨K5.1 hD,G,Qb.1,(y.1,C),hc⟩
  have h3:D.1.val=3:=(l8 hDc).1
  obtain ⟨jB,q7, -,hsD, -, -,C5,aeu⟩:=BL hDc h2
  have hpw:=Ie hDc
  rw[abo _ _ _ _ h2]
  have h:=Cw Ze (kT m r1 r2 s m2 m3 r3 z k) D h2 h3 k
  rw[C5,aeu,jB,q7,hpw]at h
  simp only[hsD]at h
  refine h.trans (WT ?_)
  rw[DK,Wi]
  rfl
 have hsum:∑ D∈qZ m s,
     (l6 Ze (kT m r1 r2 s m2 m3 r3 z k) k D).ncard*2^(s*k*r2)≤
       Zq (a9 m)*(2^kv r1 r2 r3 0 m2 m3*(2^r1*2^(k*(r1 - k)))*S):=by
  refine (Z9 hD).trans ?_
  rw[Y5,smul_eq_mul]
  exact Za _ (Finset.card_le_univ _)
 have aae:(Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
       kT m r1 r2 s m2 m3 r3 z k).ncard*2^(z*(z - 1))*2^(s*k*r2)≤
     Zq (a9 m)*(2^kv r1 r2 r3 0 m2 m3*(2^r1*2^(k*(r1 - k)))*S)*
       2^(z*k):=by
  calc _ ≤(∑ D∈qZ m s,(l6 Ze (kT m r1 r2 s m2 m3 r3 z k) k D).ncard)*
        2^(z*k)*2^(s*k*r2):=Za _ Dh
    _ = (∑ D∈qZ m s,(l6 Ze (kT m r1 r2 s m2 m3 r3 z k) k D).ncard*
        2^(s*k*r2))*2^(z*k):=by rw[← Wi]; ring
    _≤_:=Za _ hsum
 have hS:(S:ℝ)≤(((min (m2 - m3) m3:ℕ):ℝ)+1)*(2:ℝ)^(oB r1 r2 s m2 m3 b2):=by
  rw[DK,Nat.cast_sum]
  refine Fo (Gw s m2 m3) (fun β=> (pI r1 r2 s m2 m3 β:ℝ))
    (fun β=>oB r1 r2 s m2 m3 β) b2 (fun β hβ=>?_) FJ
  obtain ⟨hβa, -⟩:=Fe.mp hβ
  exact WT (J9 kB abg MG (le_min_iff.mp hβa).1 (le_min_iff.mp hβa).2)
 have h1:((Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
       kT m r1 r2 s m2 m3 r3 z k).ncard:ℝ)*2^(z*(z - 1))*2^(s*k*r2)≤
     (Zq (a9 m):ℝ)*(2^kv r1 r2 r3 0 m2 m3*
       (2^r1*2^(k*(r1 - k)))*(S:ℝ))*2^(z*k):=by
  exact_mod_cast aae
 have adi :((Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
       kT m r1 r2 s m2 m3 r3 z k).ncard:ℝ)*2^(z*(z - 1)+s*k*r2)≤
     ((Zq (a9 m):ℝ)*2^kv r1 r2 r3 0 m2 m3*
       (((min (m2 - m3) m3:ℕ):ℝ)+1))*(2:ℝ)^(oB r1 r2 s m2 m3 b2)*
         2^(r1+k*(r1 - k)+z*k):=by
  calc _ = ((Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
        kT m r1 r2 s m2 m3 r3 z k).ncard:ℝ)*2^(z*(z - 1))*2^(s*k*r2):=by
        ring
    _≤_:=h1
    _ ≤ (Zq (a9 m):ℝ)*(2^kv r1 r2 r3 0 m2 m3*
        (2 ^r1*2^(k*(r1 - k)))*((((min (m2 - m3) m3:ℕ):ℝ)+1)*
          (2:ℝ)^(oB r1 r2 s m2 m3 b2)))*2^(z*k):=by gcongr
    _=_:=by rw[Xh,Xh]; ring
 refine (abn adi).trans (WT ?_)
 have hzr :(z:ℝ)+s=r1:=by exact_mod_cast hz
 have e1:((z*(z - 1)+s*k*r2:ℕ):ℝ)=(z:ℝ)^2 - z+s*k*r2:=by
  rw[Nat.cast_add,Nh]
  push_cast
  try ring
 have e2:((r1+k*(r1 - k)+z*k:ℕ):ℝ)=r1+k*(r1 - k)+z*k:=by
  push_cast[UN GW]
  try ring
 rw[e1,e2]
 congr 2
 push_cast
 linear_combination (k:ℝ)*hzr
lemma m3cB_H2:
  ∃ C : ℝ, ∀ m r1 r2 s s1 m2 m3 r3:ℕ,∀ S:Set FiniteGrp.{0},
    S = {G : FiniteGrp.{0} | ZB G=2^m∧
        (⊤:Subgroup G).lowerCentralSeries 2≠⊥∧
        (⊤:Subgroup G).lowerCentralSeries 3=⊥∧
        ZV G=r1∧
        Group.rank ((⊤:Subgroup G).lowerCentralSeries 1⧸
          ((⊤:Subgroup G).lowerCentralSeries 2).subgroupOf
            ((⊤:Subgroup G).lowerCentralSeries 1))=r2∧
        sInf {k | ∃ H:Subgroup G,(⊤:Subgroup G).lowerCentralSeries 1=
          ⁅H,H⁆⊔(⊤:Subgroup G).lowerCentralSeries 2∧ZV H=k}=s∧
        ((⊤:Subgroup G).lowerCentralSeries 1).index =2^s1∧
        ZB ((⊤:Subgroup G).lowerCentralSeries 1)=2^m2∧
        ZB ((⊤:Subgroup G).lowerCentralSeries 2)=2^m3∧
        ZV ((⊤:Subgroup G).lowerCentralSeries 2)=r3}→
    s1=r1→(s - 1).choose 2≤ r2→ S.Nonempty→
    ∃ b2 k :ℕ,m3≤ s*b2∧b2≤ m2 - m3∧b2≤ m3∧k≤ r1 - s∧
      Real.logb 2 ((Yd (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard:ℝ)≤
        C*(m:ℝ)*((YZ 2 m:ℝ)+1)+
        ((r1*m2+(r1 - 1)*(s1 - r1)+(r2*m3+(r2 - 1)*(m2 - m3 - r2))+
          (r3 - 1)*(m3 - r3):ℕ):ℝ)+
        (((r1.choose 2:ℝ) - r2)*m2+
          (b2:ℝ)*((s:ℝ)*((r2:ℝ)+m3 - b2+1) - ((r1 - s).choose 2:ℝ))) -
        ((r1 - s:ℕ):ℝ)^2+(k:ℝ)*(2*(r1:ℝ) - s - k - (s:ℝ)*r2):=by
  obtain ⟨C0,hC0⟩:=ab4
  refine ⟨C0+1+3,fun m r1 r2 s s1 m2 m3 r3 S hS O9 _ d8=>?_⟩
  have acf:S= fF m r1 r2 s 0 m2 m3 r3:=by
   rw[hS,O9,fF,T8]
  have Mm:(fF m r1 r2 s 0 m2 m3 r3).Nonempty:=by
   rw[← acf]
   exact d8
  obtain ⟨hm,kB,abg,MG, -,abj,hN⟩:=Z_ adr Mm
  have bU:2≤ s:=abX Mm.some_mem
  obtain ⟨b2,uj,FJ⟩:=
    Vt (m5 s m2 m3) (fun β=>oB r1 r2 s m2 m3 β) abj
  obtain ⟨acd,adG⟩:=Fe.mp uj
  obtain ⟨k0,Br,ac0⟩:=Vt (ZM (r1 - s+1))
    (fun k:ℕ=> (k:ℝ)*(2*(r1:ℝ) - s - k - (s:ℝ)*r2)) ⟨0,Zt.2 (by omega)⟩
  have ad2:k0≤ r1 - s:=by
   rw[Zt]at Br
   omega
  refine ⟨b2,k0,adG,(le_min_iff.mp acd).1,(le_min_iff.mp acd).2,ad2,?_⟩
  have aeT:=Ci Mm.some_mem
  set P:ℝ:=(Zq (a9 m):ℝ)*2^kv r1 r2 r3 0 m2 m3*
    (((min (m2 - m3) m3:ℕ):ℝ)+1) with hP
  set Ψ:ℕ→ℝ:= fun k=>oB r1 r2 s m2 m3 b2+((r1+(r1 - s):ℕ):ℝ) -
    ((r1 - s:ℕ):ℝ)^2+(k:ℝ)*(2*(r1:ℝ) - s - k - (s:ℝ)*r2) with hΨ
  have hP0:0≤P:=by
   rw[hP]
   positivity
  have oN :∀ k∈ZM (r1 - s+1),
      ((Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
        kT m r1 r2 s m2 m3 r3 (r1 - s) k).ncard:ℝ)≤P*(2:ℝ)^(Ψ k0):=by
   intro k hk
   have lQ:k≤ r1 - s:=by
    rw[Zt]at hk
    omega
   have h:=aaM (m:=m) (r3:=r3) (b2:=b2) bU (by omega:r1 - s+s=r1)
     (by omega:k+s≤ r1) kB abg MG FJ
   have Oy:(k:ℝ)*(2*(r1:ℝ) - s - k - (s:ℝ)*r2)≤
       (k0:ℝ)*(2*(r1:ℝ) - s - k0 - (s:ℝ)*r2):=ac0 k hk
   have o4:(2:ℝ)^(Ψ k)≤(2:ℝ)^(Ψ k0):=by
    apply Wm (by norm_num)
    simp only[hΨ]
    linarith[Oy]
   calc _ ≤P*(2:ℝ)^(Ψ k):=by
         rw[hP]
         exact h
     _≤P*(2:ℝ)^(Ψ k0):=mul_le_mul_of_nonneg_left o4 hP0
  have hsum:((f8 m r1 r2 s 0 m2 m3 r3).ncard:ℝ)≤
      ∑ k∈ZM (r1 - s+1),((Yd (isIsomorphicSetoid FiniteGrp.{0}) ''
        kT m r1 r2 s m2 m3 r3 (r1 - s) k).ncard:ℝ):=by
   exact_mod_cast (QQ (m:=m) (r1:=r1) (r2:=r2) (s:=s) (m2:=m2) (m3:=m3)
     (r3:=r3))
  have Ql:((f8 m r1 r2 s 0 m2 m3 r3).ncard:ℝ)≤
      ((r1 - s+1:ℕ):ℝ)*(P*(2:ℝ)^(Ψ k0)):=by
   refine hsum.trans ((Z9 oN).trans (WT ?_))
   rw[Y5,Xf,nsmul_eq_mul]
  have hz2:((r1 - s+1:ℕ):ℝ)≤(2:ℝ)^((YZ 2 m:ℝ)+1):=by
   have h':m<2^(YZ 2 m+1):=V6 (by norm_num) m
   have h'':r1 - s+1≤2^(YZ 2 m+1):=by omega
   have e:(2:ℝ)^((YZ 2 m:ℝ)+1)=(2:ℝ)^(YZ 2 m+1):=by
    rw[← Wl,Nat.cast_add,Rz]
   rw[e]
   exact_mod_cast h''
  have acx:((f8 m r1 r2 s 0 m2 m3 r3).ncard:ℝ)≤
      (Zq (a9 m):ℝ)*2^kv r1 r2 r3 0 m2 m3*
        ((((min (m2 - m3) m3:ℕ):ℝ)+1)*(2:ℝ)^(Ψ k0+((YZ 2 m:ℝ)+1))):=by
   refine Ql.trans ?_
   calc ((r1 - s+1:ℕ):ℝ)*(P*(2:ℝ)^(Ψ k0))
       ≤ (2:ℝ)^((YZ 2 m:ℝ)+1)*(P*(2:ℝ)^(Ψ k0)):=
         mul_le_mul_of_nonneg_right hz2 (mul_nonneg hP0 (Real.rpow_nonneg (by norm_num) _))
     _ = _:=by
         rw[Vw (by norm_num) (Ψ k0) ((YZ 2 m:ℝ)+1),hP]
         ring
  have bZ:min (m2 - m3) m3≤ m:=by omega
  have A6:=QJ hC0 hm bZ hN acx
  have hm':(1:ℝ)≤ m:=by exact_mod_cast hm
  have zv:(0:ℝ)≤(YZ 2 m:ℝ):= Om _
  have hrz:((r1+(r1 - s):ℕ):ℝ)≤2*(m:ℝ):=by
   have:r1+(r1 - s)≤2*m:=by omega
   exact_mod_cast this
  have key:((r1+(r1 - s):ℕ):ℝ)+((YZ 2 m:ℝ)+1)≤
      3*(m:ℝ)*((YZ 2 m:ℝ)+1):=by
   nlinarith[mul_nonneg (by linarith:(0:ℝ)≤ m) zv,
     mul_nonneg (sub_nonneg.mpr hm') (by linarith:(0:ℝ)≤(YZ 2 m:ℝ)+1)]
  simp only[hΨ]at A6
  have aa4 :OM 2 ((f8 m r1 r2 s 0 m2 m3 r3).ncard:ℝ)≤
      (C0 +1+3)*(m:ℝ)*((YZ 2 m:ℝ)+1)+(kv r1 r2 r3 0 m2 m3:ℝ)+
        oB r1 r2 s m2 m3 b2 - ((r1 - s:ℕ):ℝ)^2+
          (k0:ℝ)*(2*(r1:ℝ) - s - k0 - (s:ℝ)*r2):=by
   linarith[A6,key]
  have e1:f8 m r1 r2 s 0 m2 m3 r3=
      Yd (isIsomorphicSetoid FiniteGrp.{0}) '' S:=by
   unfold f8
   rw[acf]
  rw[e1]at aa4
  rw[O9,Nat.sub_self]
  unfold kv oB at aa4
  exact aa4
end M3CB
end OMA.SimsLite
theorem OMA.solution:OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1.H2:= OMA.SimsLite.m3cB_H2
