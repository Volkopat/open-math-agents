import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3
import Mathlib
/-!
Window estimate for R3.H1 by Thomas Fredrickson (@thomasfredrickson) with Codex.
Uses the reduction of @mucoucah and the formal Kelley–Meka input ported by @adammcarter (PR 3222).
The following background proof comes from that PR.

Erdos 142, step lower.R1.H1: r_3(N) <= N / (log N)^2 for all large N (Kelley-Meka bound).
Mathematics: Z. Kelley and R. Meka (2023). Formal proof bundled from a port of the
Kelley-Meka formalization in plby/lean-proofs (src/latest/ErdosProblems/Erdos140, commit
8822f7dd; formal authors credited there), built on YaelDillies/LeanAPAP and AddCombi
(Apache-2.0). The bridge to the formal-conjectures definitions is new. Names are shortened
and whitespace minified to fit the 512 KiB limit.
-/
open Real (log exp pi)
open Set (indicator)
open Fintype (piFinset)
open Function (Injective)
alias Io:= Finset.sum_congr
alias Q0:= AddChar.norm_apply
alias Q1:= Real.exp_pos
alias Q2:= smul_eq_mul
alias Q3:= mul_one
alias Q4:= Nat.le_mul_of_pos_right
alias Q5:= Nat.cast_nonneg
alias Q6:= mul_left_comm
alias Q7:= mul_mul_mul_comm
alias Q8:= abs_nonneg
alias Q9:= div_le_one
alias QA:= congrArg
alias QB:= Real.log_pow
alias QC:= abs_of_nonneg
alias QD:= Finset.sum_comm
alias QE:= Finset.sum_filter
alias QF:= div_le_iff₀
alias QG:= Real.log_le_log
alias QH:= pow_nonneg
alias QI:= Finset.sum_le_sum
alias QJ:= Finset.sum_sub_distrib
alias QK:= Real.norm_eq_abs
alias QL:= mul_pow
alias QM:= mul_pos
alias QN:= mul_right_comm
alias QO:= norm_mul
alias QP:= Nat.mul_pos
alias QQ:= Nat.mul_le_mul_right
alias QR:= Nat.pow_le_pow_right
alias QS:= nsmul_eq_mul
alias QT:= one_mul
alias QU:= pow_mul
alias QV:= lt_of_not_ge
alias QW:= mul_le_mul
alias QX:= Real.log_le_sub_one_of_pos
alias QY:= AddCircle.homeomorphCircle_apply
alias QZ:= translate_apply
alias Qi:= mul_le_mul_of_nonneg_right
alias Qj:= Finset.mul_sum
alias Qk:= Fintype.sum_equiv
alias Ql:= Real.log_mul
alias Qm:= Set.indicator_apply
alias Qn:= mul_nonneg
alias Qo:= mul_assoc
alias Qp:= pow_le_pow_left₀
alias Qr:= Nat.mul_le_mul_left
alias Qs:= le_div_iff₀
alias Qt:= Finset.sum_mul
alias Qu:= Finset.card_le_card
alias Qv:= Real.log_nonneg
alias Qw:= div_eq_mul_inv
alias Qx:= mul_comm
alias Qy:= sub_eq_add_neg
alias Qz:= div_le_div_of_nonneg_right
alias R0:= pow_sub_one_mul
alias R1:= Fintype.card_le_of_injective
alias R2:= ENNReal.some_eq_coe
alias R3:= RCLike.conj_to_real
alias R4:= Nat.pow_le_pow_left
alias R5:= two_mul
alias R6:= one_div
alias R7:= Real.exp_add
alias R8:= Nat.mul_comm
alias R9:= div_le_div_iff_of_pos_right
alias RA:= Real.norm_of_nonneg
alias RB:= pow_succ
alias RD:= Pi.smul_apply
alias RF:= pow_pos
alias RG:= NNReal.smul_def
alias RH:= one_le_pow₀
alias RI:= Subtype.ext
alias RJ:= inv_le_inv₀
alias RK:= map_sum
alias RL:= pow_add
alias RM:= Pi.add_apply
alias RN:= Real.rpow_natCast
alias RO:= AddChar.sub_apply
alias RP:= if_pos
alias RQ:= mul_le_of_le_one_left
alias RR:= nonempty_fintype
alias RS:= div_nonneg
alias RT:= abs_of_pos
alias RU:= map_mul
alias RV:= add_comm
alias RW:= Fintype.expect_equiv
alias RX:= Fintype.mem_piFinset
alias RY:= Nat.lt_floor_add_one
alias RZ:= Nat.add_le_add_right
alias Ra:= Nat.mul_le_mul
alias Rb:= div_le_div_of_nonneg_left
alias Rc:= starRingEnd_apply
alias Rd:= not_lt_of_ge
alias Re:= norm_nonneg
alias Rf:= Complex.norm_real
alias Rg:= pow_ne_zero
alias Rh:= Function.comp_apply
alias Ri:= div_eq_inv_mul
alias Rj:= Fintype.expect_eq_sum_div_card
alias Rk:= Fintype.exists_lt_card_fiber_of_mul_lt_card
alias Rl:= mul_ne_zero
alias Rm:= Nat.cast_mul
alias Rn:= div_pos
alias Ro:= Finset.sum_subset
alias Rp:= Finset.mem_insert
alias Rq:= norm_sum_le
alias Rr:= Nat.le_ceil
alias Rs:= sub_add_cancel
alias Rt:= Pi.one_apply
alias Ru:= Nat.cast_ne_zero
alias Rv:= Nat.cast_pow
alias Rw:= Pi.sub_apply
alias Rx:= Fintype.card_coe
alias Ry:= Finset.sum_le_sum_of_subset_of_nonneg
alias Rz:= AddChar.inv_apply_eq_conj
alias S0:= Real.rpow_mul
alias S2:= NNReal.HolderConjugate.conjExponent
alias S3:= Nat.ceil_mono
alias S4:= Real.rpow_inv_rpow
alias S5:= mul_div_right_comm
alias S6:= DFunLike.congr_fun
alias S7:= Finset.subset_univ
alias S8:= sub_left_injective
alias S9:= NNReal.coe_natCast
alias SA:= Finite.bddAbove_range
alias SB:= Fintype.piFinset_univ
alias SC:= le_antisymm
alias SD:= two_ne_zero
alias SE:= NNReal.coe_inv
alias SF:= le_rfl
alias SG:= le_abs_self
alias SH:= mul_div_cancel_left₀
alias SI:= lt_of_lt_of_le
alias SJ:= pow_le_pow_of_le_one
alias SK:= NNReal.coe_mul
alias SL:= Fintype.card_subtype
alias SM:= lt_of_le_of_ne
alias SN:= Fintype.card_ne_zero
alias SO:= Finset.sum_erase_add
alias SP:= lt_div_iff₀
alias SQ:= Real.rpow_pos_of_pos
alias SR:= congr_fun
alias SS:= boole_mul
alias SU:= abs_mul
alias SV:= RCLike.inner_apply'
alias SW:= Real.log_le_log_iff
alias SX:= Equiv.subLeft_apply
alias SY:= sq_pos_of_pos
alias SZ:= Nat.mul_assoc
alias Sa:= tendsto_natCast_atTop_atTop
alias Sb:= RCLike.inner_apply
alias Sc:= Real.pow_rpow_inv_natCast
alias Sd:= Finset.inter_subset_right
alias Se:= pow_le_pow_right₀
alias Sf:= Real.rpow_le_rpow
alias Sg:= RCLike.wInner_one_eq_sum
alias Sh:= Finset.inter_subset_left
alias Si:= Finset.sum_apply
alias Sj:= le_trans
alias Sk:= mul_lt_mul_of_pos_right
alias Sl:= Nat.mod_eq_of_lt
alias Sm:= Finset.mem_of_mem_erase
alias Sn:= max_le_max_right
alias So:= Nat.cast_two
alias Sp:= Nat.cast_pos
alias Sq:= mul_le_of_le_one_right
alias Sr:= add_le_add
alias Ss:= le_add_of_nonneg_right
alias St:= AddChar.map_add_eq_mul
alias Su:= abs_sub_comm
alias Sv:= Real.log_pos
alias Sw:= Finset.ne_of_mem_erase
alias Sx:= ENNReal.HolderConjugate.eq_top_iff_eq_one
alias Sy:= div_le_div_iff₀
alias Sz:= Finset.mem_univ
alias T0:= starRingEnd_self_apply
alias T2:= even_two_mul
alias T3:= Nat.cast_add
alias T4:= tsub_le_self
alias T6:= mul_lt_mul_of_pos_left
alias T7:= Finset.sum_add_distrib
alias T8:= Real.closedBall_eq_Icc
alias T9:= Nat.le_mul_of_pos_left
alias TA:= inv_mul_le_iff₀
alias TB:= ZMod.natCast_eq_natCast_iff'
alias TC:= Fintype.card_pi
alias TD:= AddCircle.injective_toCircle
alias TE:= abs_div
alias TF:= pow_sum_div_card_le_sum_pow
alias TG:= Fintype.card_piFinset_const
alias TH:= AddChar.expect_apply_eq_ite
alias TI:= pow_two
alias TJ:= smul_mul_assoc
alias TK:= inv_mul_eq_div
alias TL:= add_sub_cancel
alias TM:= true_and
alias TN:= NNReal.coe_one
alias TO:= neg_le_neg
alias TP:= Finset.sum_div
alias TQ:= Finset.abs_sum_le_sum_abs
alias TR:= Pi.conj_apply
alias TS:= Real.rpow_neg

alias TU:= apply_ite
alias TV:= AddChar.map_neg_eq_conj
alias TW:= Finset.prod_mul_distrib
alias TX:= Finset.exists_max_image
alias TY:= div_pow
alias TZ:= le_of_mul_le_mul_right
alias Ta:= Real.mul_self_sqrt
alias Tb:= Set.mem_vadd_set_iff_neg_vadd_mem
alias Tc:= mul_add
alias Td:= mul_ite
alias Te:= inv_pow
alias Tf:= eq_or_ne
alias Tg:= Real.coe_toNNReal
alias Th:= Real.rpow_le_rpow_of_exponent_ge
alias Ti:= Nat.floor_le
alias Tj:= Finset.sum_le_univ_sum_of_nonneg
alias Tk:= ENNReal.HolderConjugate.ne_zero
alias Tl:= RCLike.conj_conj
alias Tm:= and_assoc
alias Tn:= Real.rpow_nonneg
alias To:= not_nonempty_iff
alias Tp:= Finset.sum_sub_sum_mem_addSpan
alias Tq:= Finset.sum_const
alias Tr:= Nat.lt_succ_self
alias Ts:= AddCircle.norm_coe_eq_abs_iff
alias Tt:= Finset.sum_lt_sum_of_nonempty
alias Tu:= le_max_left
alias Tv:= div_lt_iff₀
alias Tw:= mul_inv_cancel₀
alias Tx:= pos_iff_ne_zero
alias Ty:= Nat.succ_le_iff
alias Tz:= div_mul_cancel₀
alias U0:= NNReal.coe_le_coe
alias U1:= one_pos
alias U2:= AddChar.neg_apply
alias U3:= AddChar.add_apply
alias U4:= Real.sqrt_eq_rpow
alias U5:= Nat.zero_lt_of_lt
alias U6:= Nat.mul_left_comm
alias UA:= Complex.norm_natCast
alias UB:= Fintype.sum_mul_sum
alias UC:= isEmpty_or_nonempty
alias UD:= ENNReal.none_eq_top
alias UE:= translate_sub_right
alias UF:= Finset.mem_symmDiff
alias UG:= addRothNumber_spec
alias UH:= CharP.cast_eq_zero
alias UI:= algebraMap.coe_pow
alias UJ:= ENNReal.toReal_pos
alias UK:= ENNReal.toReal_mul
alias UL:= Fintype.sum_ite_eq
alias UM:= one_add_mul_le_pow
alias UN:= Finset.sum_eq_zero
alias UO:= Finset.prod_le_one
alias UP:= abs_add_le
alias UQ:= not_ne_iff
alias UR:= tendsto_rpow_atTop
alias US:= add_mul
alias UT:= sub_div
alias UU:= Finset.mem_filter
alias UW:= div_le_one_of_le₀
alias UX:= Complex.conj_mul'
alias UY:= mul_sub
alias UZ:= Finset.sum_nonneg
alias Ua:= Finset.mem_union_right
alias Ub:= AddCircle.toCircle_add
alias Uc:= Nat.floor_lt
alias Ud:= AddChar.map_neg_eq_inv
alias Ue:= ENNReal.toReal_natCast
alias Uf:= Real.sq_sqrt
alias Ug:= Finset.mem_vadd_finset
alias Uh:= Real.exp_neg
alias Ui:= Real.log_div
alias Uj:= le_of_mul_le_mul_left
alias Uk:= Complex.normSq_nonneg
alias Ul:= Fintype.sum_prod_type
alias Um:= Finset.mem_union_left
alias Un:= Complex.re_ofReal_mul
alias Uo:= Classical.choose_spec
alias Up:= norm_inv
alias Uq:= ne_of_gt
alias Ur:= Function.mem_support
alias Us:= zero_le_one
alias Ut:= Equiv.subRight_apply
alias Uu:= congrFun
alias Uv:= min_le_left
alias Uw:= one_le_inv₀
alias Ux:= Finset.card_powerset
alias Uy:= pow_le_one₀
alias Uz:= vadd_eq_add
alias iO:= mul_le_mul_of_nonneg_left
open MeasureTheory
section
namespace w1
open Erdos142 Finset
def yG (k N:ℕ):Set ℕ:=
 {Finset.card S | (S) (_:S⊆Finset.Icc 1 N) (_:(S:Set ℕ).IsAPOfLengthFree k)}
lemma qi {k N x:ℕ}:x∈yG k N ↔
  ∃ S:Finset ℕ,S⊆Finset.Icc 1 N∧(S:Set ℕ).IsAPOfLengthFree k∧S.card=x:=by
 constructor
 ·rintro ⟨S,h1,h2,h3⟩
  exact ⟨S,h1,h2,h3⟩
 ·rintro ⟨S,h1,h2,h3⟩
  exact ⟨S,h1,h2,h3⟩
lemma Cx (k:ℕ):(∅:Set ℕ).IsAPOfLengthFree k:=by
 intro t ht D3
 have h:=D3.card
 rw[Set.subset_empty_iff.mp ht] at h
 simp at h
 simp[←h]
lemma w2 (k N:ℕ):BddAbove (yG k N):=by
 refine ⟨N, ?_⟩
 intro x hx
 obtain ⟨S,hS, -,rfl⟩:=qi.1 hx
 simpa using card_le_card hS
lemma xi (k N:ℕ):(yG k N).Nonempty:=
 ⟨0,qi.2 ⟨∅,by simp,by simpa using Cx k,by simp⟩⟩
lemma M0 {k N:ℕ} (S:Finset ℕ) (hS:S⊆Finset.Icc 1 N)
  (hf:(S:Set ℕ).IsAPOfLengthFree k):S.card≤r k N:=
 le_csSup (w2 k N) (qi.2 ⟨S,hS,hf,rfl⟩)
lemma FL (k N:ℕ): ∃ S:Finset ℕ,S⊆Finset.Icc 1 N ∧
  (S:Set ℕ).IsAPOfLengthFree k∧S.card=r k N:=
 qi.1 (Nat.sSup_mem (xi k N) (w2 k N))
lemma FM {k:ℕ} (hk:2≤k) (S:Set ℕ) :
  S.IsAPOfLengthFree k↔ ∀ a d:ℕ,0<d→ ¬ (∀ i<k,a+i*d∈S):=by
 constructor
 ·intro h a d hd z9
  have hinj:Injective (fun i:ℕ=>a+i*d):=by
   intro i j hij
   have:i*d=j*d:=by simpa using hij
   exact Nat.eq_of_mul_eq_mul_right hd this
  have D3:Set.IsAPOfLength (((Finset.range k).image (fun i=>a+i*d):Finset ℕ):Set ℕ) (k:ℕ∞):=by
   refine ⟨a,d, ?_, ?_⟩
   ·show Set.encard _=_
    rw[Set.encard_coe_eq_coe_finsetCard,card_image_of_injective _ hinj,card_range]
   ·ext x
    simp[Q2]
  have l4:(((Finset.range k).image (fun i=>a+i*d):Finset ℕ):Set ℕ)⊆S:=by
   intro x hx
   simp only[coe_image,coe_range,Set.mem_image,Set.mem_Iio] at hx
   obtain ⟨i,hi,rfl⟩:=hx
   exact z9 i hi
  have:=h _ l4 D3
  have:k≤1:=by exact_mod_cast this
  omega
 ·intro h t ht D3
  exfalso
  obtain ⟨a,d,ch,heq⟩:=D3
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·subst hd
   have:t={a}:=by
    rw[heq]
    ext x
    simp only[smul_zero,add_zero,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    ·rintro ⟨n, -,rfl⟩
     rfl
    ·rintro rfl
     exact ⟨0,by exact_mod_cast(by omega:0<k),rfl⟩
   rw[this] at ch
   simp at ch
   have:k=1:=by exact_mod_cast ch.symm
   omega
  ·apply h a d hd
   intro i hi
   apply ht
   rw[heq]
   exact ⟨i,by exact_mod_cast hi,by simp[Q2]⟩
lemma tR (S:Set ℕ):S.IsAPOfLengthFree ((3:ℕ):ℕ∞)↔ThreeAPFree S:=by
 rw[FM (by norm_num)]
 constructor
 ·intro h a ha b hb c hc pK
  by_contra vH
  rcases lt_or_gt_of_ne vH with xS | PY
  ·apply h a (b-a) (by omega)
   intro i hi
   interval_cases i
   ·simpa using ha
   ·have e:a+1*(b-a)=b:=by omega
    rw[e]
    exact hb
   ·have e:a+2*(b-a)=c:=by omega
    rw[e]
    exact hc
  ·apply h c (b-c) (by omega)
   intro i hi
   interval_cases i
   ·simpa using hc
   ·have e:c+1*(b-c)=b:=by omega
    rw[e]
    exact hb
   ·have e:c+2*(b-c)=a:=by omega
    rw[e]
    exact ha
 ·intro h a d hd z9
  have h0:=z9 0 (by norm_num)
  have h1:=z9 1 (by norm_num)
  have h2:=z9 2 (by norm_num)
  have:=h h0 h1 h2 (by ring)
  omega
lemma r4 (N:ℕ):r 3 N=addRothNumber (Finset.Icc 1 N):=by
 apply SC
 ·obtain ⟨S,hS,hf,hc⟩:=FL 3 N
  rw[←hc]
  exact((tR _).1 hf).le_addRothNumber hS
 ·obtain ⟨S,hS,hc,hf⟩:=UG (Finset.Icc 1 N)
  rw[←hc]
  exact M0 S hS ((tR _).2 hf)
end w1
end
section
open Finset Function
section
variable {ι α ip:Type*}
section CommMonoidWithZero
variable [CommMonoidWithZero ip] [DecidableEq α]
lemma mQ [Fintype α] (s:Finset ι) (t:ι→Finset α) (x:α) :
  (indicator (↑(s.inf t)) fun _↦(1:ip)) x= ∏ i∈s,(indicator (t i) fun _↦(1:_)) x:=by simp[Qm,mem_inf,prod_boole]
end CommMonoidWithZero
end
end
section
open scoped Pointwise
section
variable {α G ip:Type*}
section yH
variable [One ip] [Zero ip] [AddGroup G] [AddAction G α]
@[simp] lemma D4 (g:G) (s:Set α) (a:α):(indicator (g+ᵥ s) fun _↦(1:ip)) a=(indicator s fun _↦(1:_)) (-g+ᵥ a):=by
 classical simp[Qm,Tb]
end yH
end
end
section
open scoped Pointwise
section
variable {G ip:Type*}
section yH
variable [One ip] [Zero ip] [AddGroup G]
@[simp] lemma FJ (s:Set G) (a:G):(indicator (-s) fun _↦(1:ip)) a=(indicator s fun _↦(1:_)) (-a):=by
 classical simp[Qm]
end yH
end
end
section
section
variable {F α β ip nO:Type*}
namespace Set
variable [MonoidWithZero ip] [MonoidWithZero nO] {s:Set α}
lemma iq (s t:Set α) (x:α):(indicator (s∩t) fun _↦(1:ip)) x=(indicator s fun _↦(1:_)) x*(indicator t fun _↦(1:_)) x:=by
 classical simp[indicator_apply, ←ite_and,and_comm]
lemma rj [FunLike F ip nO] [MonoidWithZeroHomClass F ip nO] (f:F) (s:Set α)
  (x:α):f ((indicator s fun _↦(1:_)) x)=(indicator s fun _↦(1:_)) x:=by classical exact MonoidWithZeroHom.map_ite_one_zero ..
variable [Nontrivial ip] {a:α}
lemma qn:(indicator s fun _↦(1:ip)) a≠0↔a∈s:=by
 classical exact one_ne_zero.ite_ne_right_iff
variable (ip) in
@[simp] lemma j0:(indicator s fun _↦(1:ip)).support=s:=by
 ext; exact qn
end Set
end
end
section
section
open scoped Pointwise translate
variable {G ip:Type*}
section Semiring
variable [One ip] [Zero ip] [AddCommGroup G]
variable (ip) in
lemma sU (a:G) (s:Set G):τ a (indicator s fun _↦(1:ip))=(indicator (a+ᵥ s) fun _↦(1:_)):=by
 classical ext; simp[Qm,Tb,sub_eq_neg_add]
end Semiring
end
end

section
section
open ENNReal
namespace MeasureTheory
variable {𝕜 α:Type*} {m:MeasurableSpace α} {μ:Measure α} [NormedRing 𝕜]
lemma qV {p q r:ℝ≥0∞} {f g:α→𝕜} (hf:AEStronglyMeasurable f μ)
  (hg:AEStronglyMeasurable g μ) [HolderTriple p q r] :
  eLpNorm (f*g) r μ≤eLpNorm f p μ*eLpNorm g q μ:=by
 simpa using eLpNorm_smul_le_mul_eLpNorm hg hf
end MeasureTheory
end
end
section
section
open Finset Fintype Function
open scoped ComplexConjugate NNReal Pointwise translate
variable {G H R S:Type*} [DecidableEq G] [AddCommGroup G]
section CommSemiring
variable [CommSemiring R]
def uK:G→R:=fun a↦if a=0 then 1 else 0
@[simp] lemma yI (a:G):(uK a:R)=if a=0 then 1 else 0:=rfl
variable [StarRing R]
end CommSemiring
variable [Fintype G]
section CommSemiring
variable [CommSemiring R] {f g:G→R}
def aC (f g:G→R):G→R:=fun a↦ ∑ x:G × G with x.1+x.2=a ,f x.1*g x.2
lemma f7 (f g:G→R) (a:G) :
  ((aC f g)) a= ∑ x:G × G with x.1+x.2=a,f x.1*g x.2:=rfl
lemma Cy (f g h:G→R):(aC ((f+g)) h)=(aC f h)+(aC g h):=by
 ext; simp[f7,US,sum_add_distrib]
lemma tn [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (aC (c•f) g)=c•((aC f g)):=by ext a; simp[f7,smul_sum,TJ]
lemma Bv [DistribSMul H R] [SMulCommClass H R R] (c:H) (f g:G→R) :
  (aC f (c•g))=c•((aC f g)):=by ext a; simp[f7,smul_sum,mul_smul_comm]
@[simp] lemma FN (a:G) (f g:G→R):(aC (τ a f) g)=τ a ((aC f g)):=
 funext fun b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_add_eq_add_sub]) (by simp)
lemma fA (f g:G→R):(aC f g)=(aC g f):=
 funext fun a↦sum_equiv (Equiv.prodComm _ _) (by simp[RV])<| by simp[Qx]
lemma uL [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c d:H) (f g:G→R):(c*d)•((aC f g))=(aC (c•f) (d•g)):=by
 rw[tn,Bv,mul_smul]
lemma iS (f g h:G→R):(aC ((aC f g)) h)=(aC f (((aC g h)))):=by
 ext a
 simp only[sum_mul,mul_sum,f7,Finset.sum_sigma']
 apply sum_nbij' (fun ⟨(_b,c),(d,e)⟩↦⟨(d,e+c),(e,c)⟩)
  (fun ⟨(b,_c),(d,e)⟩↦⟨(b+d,e),(b,d)⟩)<;>aesop (add simp[add_assoc,Qo])
lemma xj (f g h:G→R):(aC f (((aC g h))))=(aC g (((aC f h)))):=by
 rw[←iS, ←iS,fA g]
lemma ir (f g h i:G→R):(aC ((aC f g)) (((aC h i))))=(aC ((aC f h)) (((aC g i)))):=by
 rw[iS,iS,xj g]
lemma xT [CommSemiring S] (m:R→+* S) (f g:G→R) (a:G) :
  m (((aC f g)) a)=((aC (m ∘ f) (m ∘ g))) a:=by simp[f7,RK,RU]
lemma rk (f g:G→R) (a:G):((aC f g)) a= ∑ t,f (a-t)*g t:=by
 rw[f7]; apply sum_nbij' Prod.snd (fun b↦(a-b,b))<;>aesop
lemma cR (f g:G→R) (a:G):((aC f g)) a= ∑ t,f t*g (a-t):=by
 rw[fA,rk]; simp_rw[Qx]
lemma r5 (f g:G→R) (a b:G):((aC f g)) (a+b)= ∑ t,f (a+t)*g (b-t):=
 (rk _ _ _).trans<| Qk (Equiv.subLeft b) _ _ fun t↦by
  simp[add_sub_assoc]
lemma tS (f g h:G→R): ∑ a,((aC f g)) a*h a= ∑ a, ∑ b,f a*g b*h (a+b):=by
 simp_rw[cR,sum_mul]
 rw[sum_comm]
 exact sum_congr rfl fun x _↦Qk (Equiv.subRight x) _ _ fun y↦by simp
lemma uM (f g:G→R): ∑ a,((aC f g)) a=(∑ a,f a)* ∑ a,g a:=by
 simpa only[UB,Rt,Q3] using tS f g 1
lemma tT (f g:G→R):support ((aC f g))⊆support f+support g:=by
 rintro a ha
 obtain ⟨x,hx,h⟩:=exists_ne_zero_of_sum_ne_zero ha
 exact ⟨_,left_ne_zero_of_mul h,_,right_ne_zero_of_mul h,(mem_filter.1 hx).2⟩
variable [StarRing R]
def al (f g:G→R):G→R:=fun a↦ ∑ x:G × G with x.1-x.2=a,f x.1*conj g x.2
lemma en (f g:G→R) (a:G) :
  ((al f g)) a= ∑ x:G × G with x.1-x.2=a ,f x.1*conj g x.2:=rfl
@[simp] lemma I1 (f:G→R):(al f 0)=0:=by ext; simp[en]
@[simp] lemma I2 (f:G→R):(al 0 f)=0:=by ext; simp[en]
@[simp] lemma FO (f:G→R):(al f ((fun _↦0)))=0:=by ext; simp[en]
lemma Bw (f g h:G→R):(al f ((g+h)))=(al f g)+(al f h):=by
 ext; simp[en,Tc,sum_add_distrib]
lemma Bx (f g h:G→R):(al ((f+g)) h)=(al f h)+(al g h):=by
 ext; simp[en,US,sum_add_distrib]
lemma oB [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (al (c•f) g)=c•((al f g)):=by ext; simp[en,smul_sum,TJ]
lemma oC [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c:H)
  (f g:G→R):(al f (c•g))=star c•((al f g)):=by
 ext; simp[en,smul_sum,mul_smul_comm,Rc,star_smul]
@[simp] lemma rl (a:G) (f g:G→R):(al (τ a f) g)=τ a ((al f g)):=
 funext fun b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_right_comm _ a]) (by simp)
@[simp] lemma iM (f g:G→R):(aC f (conjneg g))=(al f g):=
 funext fun a↦sum_equiv ((Equiv.refl _).prodCongr<| Equiv.neg _) (by simp) (by simp)
@[simp] lemma FK (f g:G→R) (a:G):conj (((aC f g)) a)=((aC (conj f) (conj g))) a:=by
 simp only[TR,f7,RK,RU]
@[simp] lemma pL (f g:G→R):conjneg ((aC f g))=(aC (conjneg f) (conjneg g)):=by
 funext a
 simp only[f7,conjneg_apply,RK,RU]
 exact sum_equiv (Equiv.neg _) (by simp[←neg_eq_iff_eq_neg,RV]) (by simp)
@[simp] lemma xU (f g:G→R):conjneg ((al f g))=(al g f):=by
 simp_rw[←iM,pL,conjneg_conjneg,fA]
lemma kr (f g h i:G→R):(aC ((al f g)) (((al h i))))=(al ((aC f h)) (((aC g i)))):=by
 simp_rw[←iM,pL,ir]
lemma eL (f g:G→R) (a:G):((al f g)) a= ∑ t,f t*conj (g (t-a)):=by
 simp[←iM,cR]
lemma wT (f g:G→R) (a:G):((al f g)) (-a)=conj (((al g f)) a):=by
 rw[←xU f,conjneg_apply,Complex.conj_conj]
lemma rm (f g:G→R) (a b:G) :
  ((al f g)) (a-b)= ∑ t,f (a+t)*conj (g (b+t)):=by
 simp[←iM,Qy,r5,RV]
lemma lM (f g h:G→R) :
  ∑ a,((al f g)) a*h a= ∑ a, ∑ b,f a*conj (g b)*h (a-b):=by
 simp_rw[eL,sum_mul]
 rw[sum_comm]
 exact Fintype.sum_congr _ _ fun x↦Qk (Equiv.subLeft x) _ _ fun y↦by simp
lemma jJ (f g:G→R): ∑ a,((al f g)) a=(∑ a,f a)* ∑ a,conj (g a):=by
 simpa only[UB,Rt,Q3] using lM f g 1
end CommSemiring
section CommRing
variable [CommRing R]
@[simp] lemma Cz (f g:G→R):(aC (-f) g)= -((aC f g)):=by ext; simp[f7]
lemma CA (f g h:G→R):(aC ((f-g)) h)=(aC f h)-(aC g h):=by
 simp only[Qy,Cy,Cz]
variable [StarRing R]
@[simp] lemma By (f g:G→R):(al f (-g))= -((al f g)):=by ext; simp[en]
@[simp] lemma Bz (f g:G→R):(al (-f) g)= -((al f g)):=by ext; simp[en]
lemma BA (f g h:G→R):(al f ((g-h)))=(al f g)-(al f h):=by
 simp only[Qy,Bw,By]
lemma BB (f g h:G→R):(al ((f-g)) h)=(al f h)-(al g h):=by
 simp only[Qy,Bx,Bz]
end CommRing
namespace RCLike
variable {𝕜:Type} [RCLike 𝕜] (f g:G→ℝ) (a:G)
@[simp] lemma rx:(↑(((aC f g)) a):𝕜)=((aC ((↑) ∘ f) ((↑) ∘ g))) a:=
 xT (algebraMap ℝ 𝕜) _ _ _
@[simp] lemma lg:(↑(((al f g)) a):𝕜)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[en]
@[simp] lemma oD:((↑):ℝ→𝕜) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)):=funext<| rx _ _
@[simp] lemma gF:((↑):ℝ→𝕜) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=funext<| lg _ _
end RCLike
namespace Complex
variable (f g:G→ℝ) (n:ℕ) (a:G)
@[simp] lemma zI:(↑(((aC f g)) a):ℂ)=((aC ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.rx _ _ _
@[simp] lemma yJ:(↑(((al f g)) a):ℂ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.lg _ _ _
@[simp] lemma qo:((↑):ℝ→ℂ) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| zI _ _
@[simp] lemma pB:((↑):ℝ→ℂ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| yJ _ _
end Complex
namespace NNReal
variable (f g:G→ℝ≥0) (a:G)
@[simp] lemma rx:(↑(((aC f g)) a):ℝ)=((aC ((↑) ∘ f) ((↑) ∘ g))) a:=xT NNReal.toRealHom _ _ _
@[simp] lemma lg:(↑(((al f g)) a):ℝ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[en,coe_sum]
@[simp] lemma oD:((↑):_→ℝ) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| rx _ _
@[simp] lemma gF:((↑):_→ℝ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| lg _ _
end NNReal
section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
def ep (f:G→R):ℕ→G→R
 | 0=>uK
 | n+1=>(aC (ep f n) f)
@[simp] lemma IY (f:G→R):(ep f 0)=uK:=rfl
lemma vl (f:G→R) (n:ℕ):(ep f ((n+1)))=(aC ((ep f n)) f):=rfl
lemma yK (f:G→R) (n:ℕ):(ep f ((n+1)))=(aC f ((ep f n))):=fA _ _
@[simp] lemma vm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c:H) (f:G→R): ∀ n,(ep ((c•f)) n)=c^n•(ep f n)
 | 0=>by simp
 | n+1=>by simp_rw[vl,vm _ _ n,RB,uL]
variable [StarRing R]
end CommSemiring

end
end

section
open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate
section
variable {K L α G:Type*}
section DivisionSemiring
variable [DivisionSemiring K] [DivisionSemiring L] {s:Finset α}
noncomputable def mu (s:Finset α):α→K:=(#s:K)⁻¹ •(indicator s fun _↦(1:_))
lemma mu_apply [DecidableEq α] (x:α):mu s x=(#s:K)⁻¹ *ite (x∈s) 1 0:=by
 simp[mu,Qm]
@[simp] lemma FQ:(mu ∅:α→K)=0:=by ext; simp[mu]
lemma xV (f:K→+* L) (s:Finset α) (x:α):f (mu s x)=mu s x:=by
 simp_rw[mu,RD,Q2,RU,Set.rj,map_inv₀,map_natCast]
section Nontrivial
variable [CharZero K] {a:α}
@[simp] lemma FR:(@mu K _ _) s a=0↔a∉s:=by
 classical
 simp only[mu_apply,mul_boole,ite_eq_right_iff,inv_eq_zero,Nat.cast_eq_zero,card_eq_zero]
 refine imp_congr_right fun ha↦ ?_
 simp only[ne_empty_of_mem ha]
variable (K)
@[simp] lemma jo (s:Finset α):support ((@mu K _ _) s)=s:=by ext; simp
end Nontrivial
variable (K)
lemma l5 [CharZero K] (s:Finset α): #s•(@mu K _ _) s=(indicator s fun _↦(1:_)):=by
 classical
 ext x:1
 simp only[RD,mu_apply,Td,Q3,mul_zero,smul_ite,QS,
  Qm,SetLike.mem_coe]
 split_ifs with h
 ·have:s.Nonempty:=⟨_,h⟩
  simp[this.ne_empty]
 ·simp
lemma qr [CharZero K] (s:Finset α) (x:α): #s•(@mu K _ _) s x=(indicator s fun _↦(1:_)) x:=
 SR (l5 K _) _
@[simp] lemma kW [CharZero K] [Fintype α] (hs:s.Nonempty): ∑ x,(@mu K _ _) s x=1:=by
 classical
 simpa[mu_apply] using Tw (Nat.cast_ne_zero.2 hs.card_pos.ne')
section Group
variable [AddGroup G] [AddAction G α] [DecidableEq α]
@[simp] lemma NL (g:G) (s:Finset α) (a:α):(@mu K _ _) (g+ᵥ s) a=mu s (-g+ᵥ a):=by
 simp[mu_apply,neg_vadd_mem_iff]
end Group
section Group
variable [AddGroup α] [DecidableEq α]
@[simp] lemma N4 (s:Finset α) (a:α):(@mu K _ _) (-s) a=mu s (-a):=by simp[mu]
end Group
lemma vI [AddCommGroup G] [DecidableEq G] (a:G) (s:Finset G) :
  τ a ((@mu K _ _) s)=mu (a+ᵥ s):=by
 ext; simp[mu_apply, ←neg_vadd_mem_iff,sub_eq_neg_add]
end DivisionSemiring
section Semifield
variable (K) [Semifield K] {s:Finset G}
variable [StarRing K]
@[simp] lemma CB [AddCommGroup G] [DecidableEq G] (s:Finset G) :
  conjneg ((@mu K _ _) s)=mu (-s):=by ext; simp[mu_apply]; split_ifs<;>simp
end Semifield

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {s:Finset α}
@[simp] lemma cC:0≤(@mu K _ _) s:=fun a↦by classical rw[mu_apply]; split_ifs<;>simp
end LinearOrderedSemifield
namespace Complex
variable (s:Finset α) (a:α)
@[simp] lemma D5: ↑((@mu (ℝ) _ _) s a)=(@mu (ℂ) _ _) s a:=xV (algebraMap ℝ ℂ) ..
@[simp] lemma yL:(↑) ∘ (@mu (ℝ) _ _) s=(@mu (ℂ) _ _) s:=funext<| D5 _
end Complex
namespace RCLike
variable {𝕜:Type*} [RCLike 𝕜] (s:Finset α) (a:α)
@[simp] lemma Aa: ↑((@mu (ℝ) _ _) s a)=(@mu 𝕜 _ _) s a:=xV (algebraMap ℝ 𝕜) _ _
@[simp] lemma iF:(↑) ∘ (@mu (ℝ) _ _) s=(@mu 𝕜 _ _) s:=funext<| Aa _
end RCLike
namespace NNReal
open scoped NNReal
@[simp] lemma Aa (s:Finset α) (x:α): ↑((@mu (ℝ≥0) _ _) s x)=(@mu (ℝ) _ _) s x:=xV NNReal.toRealHom _ _
@[simp] lemma iF (s:Finset α):(↑) ∘ (@mu (ℝ≥0) _ _) s=(@mu (ℝ) _ _) s:=funext<| Aa _
end NNReal

end
end
section
section
open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate
variable {G R γ:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
lemma j1 (s:Finset G) :
  ∀ (n:ℕ) (a:G),((ep ((indicator s fun _↦(1:R))) n)) a= #{x∈(piFinset fun _:Fin n↦s) | ∑ i,x i=a}
 | 0,a=>by simp[TU card,eq_comm]
 | n+1,a=>by
  simp_rw[yK,cR,j1,Qm,
   SS,sum_ite,mem_coe,filter_univ_mem,sum_const_zero,add_zero, ←Nat.cast_sum,
   ←Finset.card_sigma]
  congr 1
  refine card_equiv ((Equiv.sigmaEquivProd ..).trans<| Fin.consEquiv fun _↦G) ?_
  aesop (add simp[Fin.sum_cons,Fin.forall_fin_succ])
lemma pn (s:Finset G) (n:ℕ) (f:G→R) :
  (aC ((ep ((indicator s fun _↦(1:_))) n)) f)= ∑ a∈(piFinset fun _:Fin n↦s),τ (∑ i,a i) f:=by
 ext b
 simp only[cR,j1,Si,QZ,
  ←QS, ←sum_const,Finset.sum_fiberwise']
variable [StarRing R]
end CommSemiring
section Semifield
variable [Semifield R] [CharZero R]
lemma vJ (s:Finset G) (n:ℕ) (f:G→R) :
  (aC ((ep (mu s) n)) f)=𝔼 a∈piFinset (fun _:Fin n↦s),τ (∑ i,a i) f:=by
 simp only[mu,vm,Te,tn,pn,expect,
  card_piFinset_const,Rv]
 rw[←NNRat.cast_smul_eq_nnqsmul R]
 push_cast
 rfl
variable [StarRing R]
end Semifield

end
end
section
section
open Finset hiding card
open Function ProbabilityTheory Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def c2 (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p (uniformOn .univ)
@[simp] lemma yM:0≤(c2 p f):=by simp[c2]

variable [Finite α]

omit [Finite α]
variable [DiscreteMeasurableSpace α] [Fintype α]
lemma mR (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (c2 p f)=(𝔼 i, ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[c2,uniformOn,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,
  integral_fintype,cond_apply,expect_eq_sum_div_card,Ri, ←mul_sum,Measure.real]
lemma tp {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (c2 p f)=(𝔼 i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ):=
 mR (by simpa using hp) (by simp) _
lemma qs {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (c2 p f)^(p:ℝ)=𝔼 i, ‖f i‖ ^(p:ℝ):=by
 rw[tp hp,S4]<;>positivity
lemma qW {p:ℕ} (hp:p≠0) (f:α→E) :
  (c2 p f)^p=𝔼 i, ‖f i‖ ^p:=by
 simpa using qs (Nat.cast_ne_zero.2 hp) f
lemma ry (f:α→E):(c2 2 f)^2=𝔼 i, ‖f i‖ ^2:=by
 simpa using qW SD _
lemma tq (f:α→E):(c2 1 f)=𝔼 i, ‖f i‖:=by
 simp[mR]
omit [Fintype α]
variable [Finite α]
lemma oE (f:α→E):(c2 (∞) f)= ⨆ i, ‖f i‖:=by
 cases UC α<;>simp[c2,lpNorm_exponent_top_eq_essSup]
omit [Finite α]
end NormedAddCommGroup
end MeasureTheory

end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def aJ (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p .count
@[simp] lemma d8:0≤(aJ p f):=by simp[aJ]
@[simp] lemma n7 (f:α→E):(aJ 0 f)=0:=by simp[aJ]
@[simp] lemma Ac (p:ℝ≥0∞):(aJ p ((0:α→E)))=0:=by simp[aJ]
lemma r6 (f g:α→E) (p:ℝ≥0∞):(aJ p (f-g))=(aJ p (g-f)):=by
 simp[aJ,lpNorm_sub_comm]
@[simp] lemma Ad (hf:StronglyMeasurable f) (p:ℝ≥0∞):(aJ p (fun i↦ ‖f i‖))=(aJ p f):=
 lpNorm_norm hf.aestronglyMeasurable _
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
lemma vK [Module 𝕜 E] [NormSMulClass 𝕜 E] (c:𝕜) (f:α→E) :
  (aJ p (c•f))= ‖c‖ *(aJ p f):=by simp[aJ,lpNorm_const_smul]
lemma zJ [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) :
  (aJ p (n•f))=n•(aJ p f):=by simp[aJ,lpNorm_nsmul]
variable [NormedSpace ℝ 𝕜]
end NormedField
section RCLike
variable {p:ℝ≥0∞}
@[simp] lemma Ae [RCLike R] (f:α→R):(aJ p (conj f))=(aJ p f):=lpNorm_conj ..
end RCLike
section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]
lemma yN (hp:1≤p):(aJ p (f+g))≤(aJ p f)+(aJ p g):=
 lpNorm_add_le .of_discrete hp
lemma yO (hp:1≤p):(aJ p (f-g))≤(aJ p f)+(aJ p g):=
 lpNorm_sub_le .of_discrete hp
lemma wU [Module ℚ≥0 E] [NormedSpace ℝ E] {ι:Type*} {s:Finset ι} {f:ι→α→E}
  (hp:1≤p):(aJ p (𝔼 i∈s,f i))≤𝔼 i∈s,(aJ p (f i)):=
 lpNorm_expect_le (fun _ _↦ .of_discrete) hp
lemma er (hp:1≤p) :
  (aJ p (f-h))≤(aJ p (f-g))+(aJ p (g-h)):=
 lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp
end DiscreteMeasurableSpace
variable [Fintype α]

variable [DiscreteMeasurableSpace α]
lemma iv (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[aJ,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,integral_fintype]
lemma ln {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ):=
 iv (by simpa using hp) (by simp) _
lemma iT {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)^(p:ℝ)= ∑ i, ‖f i‖ ^(p:ℝ):=by
 rw[ln hp,S4 (by positivity) (mod_cast hp)]
lemma gz {p:ℕ} (hp:p≠0) (f:α→E):(aJ p f)^p= ∑ i, ‖f i‖ ^p:=by
 simpa using iT (Nat.cast_ne_zero.2 hp) f
lemma ts (f:α→E):(aJ 2 f)^2= ∑ i, ‖f i‖ ^2:=by
 simpa using gz SD _
lemma ek (f:α→E):(aJ 1 f)= ∑ i, ‖f i‖:=by simp[iv]
omit [Fintype α]
variable [Finite α]
lemma dw (f:α→E):(aJ (∞) f)= ⨆ i, ‖f i‖:=by
 cases UC α<;>simp[aJ,lpNorm_exponent_top_eq_essSup]
lemma vw {i:α}: ‖f i‖ ≤(aJ (∞) f):=by
 rw[dw]; exact le_ciSup (f:=fun i↦ ‖f i‖) (SA _) i
omit [Finite α]
variable [Fintype α]
end MeasureTheory

end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
namespace MeasureTheory
variable {ι G 𝕜 E R:Type*} [Finite ι] {I3:MeasurableSpace ι} [DiscreteMeasurableSpace ι]
section Indicator
variable [RCLike R] {s:Finset ι} {p:ℝ≥0}
lemma kX (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) fun _↦(1:R))))^(p:ℝ)= #s:=by
 classical
 cases RR ι
 have: ∀ x,(ite (x∈s) 1 0:ℝ)^(p:ℝ) =
  ite (x∈s) (1^(p:ℝ)) (0^(p:ℝ)):=fun x↦by split_ifs<;>simp
 simp[iT,hp,Qm,TU norm, -sum_const,
  card_eq_sum_ones]
lemma n8 (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) fun _↦(1:R))))= #s^(p⁻¹ :ℝ):=by
 refine(eq_rpow_inv ?_ ?_ ?_).2 (kX ?_ _)<;>first | positivity | exact d8
lemma rA {p:ℕ} (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) fun _↦(1:R))))^(p:ℝ)= #s:=by
 simpa using kX (Nat.cast_ne_zero.2 hp) s
lemma r7 (s:Finset ι):(aJ 2 ((indicator ((s:Set ι)) fun _↦(1:R))))^2= #s:=by
 simpa using rA SD s
@[simp] lemma tU (s:Finset ι):(aJ 2 ((indicator ((s:Set ι)) fun _↦(1:R))))=Real.sqrt #s:=by
 rw[eq_comm,sqrt_eq_iff_eq_sq,r7]<;>first | positivity | exact d8
lemma rB (hp:1≤p) (hs:s.Nonempty):(aJ p ((@mu R _ _) s))= #s^((p:ℝ)⁻¹ -1):=by
 rw[mu,vK ((#s)⁻¹ :R) ((indicator ((s:Set ι)) fun _↦(1:R))),n8,Up,
  RCLike.norm_natCast,TK, ←Real.rpow_sub_one]<;>positivity
lemma zK (hp:1≤p):(aJ p ((@mu R _ _) s))≤ #s^(p⁻¹ -1:ℝ):=by
 obtain rfl | hs:=s.eq_empty_or_nonempty
 ·simp only[FQ,Ac,card_empty,UH,SE]
  positivity
 ·exact(rB hp hs).le
@[simp] lemma uN (hs:s.Nonempty):(aJ 1 ((@mu R _ _) s))=1:=by
 simpa using rB SF hs
lemma rn:(aJ 1 ((@mu R _ _) s))≤1:=by simpa using zK SF
@[simp] lemma CD (hs:s.Nonempty):(aJ 2 ((@mu R _ _) s))= #s^(-2⁻¹ :ℝ):=by
 have:(2⁻¹ -1:ℝ)= -2⁻¹:=by norm_num
 simpa[sqrt_eq_rpow,this] using rB one_le_two (R:=R) hs
end Indicator
section aJ
variable {mG:MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
 {p:ℝ≥0∞}
@[simp] lemma jY [NormedAddCommGroup E] (a:G) (f:G→E):(aJ p (τ a f))=(aJ p f):=by
 cases RR G
 obtain p | p:=p
 ·simp only[dw,UD,QZ]
  exact(Equiv.subRight _).iSup_congr fun _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n7,R2,ENNReal.coe_zero]
 ·simp only[ln hp,R2,QZ]
  congr 1
  exact Qk (Equiv.subRight _) _ _ fun _↦rfl
@[simp] lemma G4 [RCLike E] (f:G→E):(aJ p (conjneg f))=(aJ p f):=by
 cases RR G
 simp only[conjneg,Ae]
 obtain p | p:=p
 ·simp only[dw,UD]
  exact(Equiv.neg _).iSup_congr fun _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n7,R2,ENNReal.coe_zero]
 ·simp only[ln hp,R2]
  congr 1
  exact Qk (Equiv.neg _) _ _ fun _↦rfl
lemma pM [NormedAddCommGroup E] (hp:1≤p) {ι:Type*} (s:Finset ι)
  (a:ι→G) (f:G→E):(aJ p (τ (∑ i∈s,a i) f-f))≤ ∑ i∈s,(aJ p (τ (a i) f-f)):=by
 induction s using Finset.cons_induction with
 | empty=>simp
 | cons i s ih hs =>
 calc
  _=(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)+(τ (∑ j∈s,a j) f-f))):=by
   rw[sum_cons,translate_add',UE,sub_add_sub_cancel]
  _≤(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)))+ ∑ j∈s,(aJ p ((τ (a j) f-f))):=by
   grw[yN hp,hs]
  _=_:=by rw[jY,sum_cons]
end aJ
end MeasureTheory
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal Pointwise translate
variable {G 𝕜:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
section RCLike
variable [RCLike 𝕜] {p:ℝ≥0∞}
lemma tV (f g:G→𝕜) (a:G):((al f g)) a=conj ⟪f,τ a g⟫_[𝕜]:=by
 simp[wInner_one_eq_sum,eL,RK,Qx]
lemma qt (f g h:G→𝕜):⟪f,(al g h)⟫_[𝕜]=⟪conj g,(aC (conj f) (conj h))⟫_[𝕜]:=by
 calc
  _= ∑ b, ∑ a,g a*conj (h b)*conj (f (a-b)):=by
   simp_rw[wInner_one_eq_sum,Sb,lM]
   exact sum_comm
  _= ∑ b, ∑ a,conj (f a)*conj (h b)*g (a+b):=by
   simp_rw[←Fintype.sum_prod_type']
   exact Qk ((Equiv.refl _).prodShear Equiv.subRight) _ _
    (by simp[mul_rotate,QN])
  _=_:=by
   simp_rw[wInner_one_eq_sum,Sb,tS,TR,
    Tl]
   exact sum_comm
lemma wV (f g h:G→𝕜):⟪f,(aC g h)⟫_[𝕜]=⟪conj g,(al (conj f) (conj h))⟫_[𝕜]:=by
 simp_rw[qt,Tl]
lemma vL (f g h:G→𝕜):⟪(al f g),h⟫_[𝕜]=⟪(aC (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,qt,conj_wInner_symm]
lemma ro (f g h:G→𝕜):⟪(aC f g),h⟫_[𝕜]=⟪(al (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,wV,conj_wInner_symm]
lemma kY (f g h:G→𝕜) :
  ⟪(al f g),h⟫_[𝕜]=⟪f,(aC h g)⟫_[𝕜]:=by
 rw[vL]; simp[wInner_one_eq_sum,Qx]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma wW {p:ℝ≥0} (hp:1≤p) (f g:G→𝕜) :
  (aJ p ((aC f g)))≤(aJ p f)*(aJ 1 g):=by
 obtain rfl | hp:=hp.eq_or_lt
 ·simp_rw[ENNReal.coe_one,ek,sum_mul_sum,cR]
  calc
   _ ≤ ∑ x, ∑ y, ‖f y*g (x-y)‖:=
    sum_le_sum fun x _↦Rq _ _
   _=_:= ?_
  rw[sum_comm]
  simp_rw[QO]
  exact sum_congr rfl fun x _↦Qk (Equiv.subRight x) _ _ fun _↦rfl
 have iu:=zero_lt_one.trans hp
 have h1:=d8 (p:=(p:ℝ≥0∞)) (f:=aC f g)
 have h2:=d8 (p:=(p:ℝ≥0∞)) (f:=f)
 have h3:=d8 (p:=1) (f:=g)
 rw[←rpow_le_rpow_iff _ _ iu,mul_rpow]
 any_goals positivity
 dsimp
 simp_rw[iT iu.ne',cR]
 have I4:(p:ℝ).HolderConjugate (1-(p:ℝ)⁻¹)⁻¹:=
  ⟨by simp,mod_cast iu,by bound⟩
 have (x:G): ‖∑ y,f y*g (x-y)‖ ^(p:ℝ) ≤
   (∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ):=by
  rw[←le_rpow_inv_iff_of_pos,mul_rpow, ←rpow_mul,sub_one_mul,Tw]
  any_goals positivity
  calc
   _≤ ∑ y, ‖f y*g (x-y)‖:=Rq _ _
   _= ∑ y, ‖f y‖ * ‖g (x-y)‖ ^(p:ℝ)⁻¹ * ‖g (x-y)‖ ^(1-(p:ℝ)⁻¹):= ?_
   _≤_:=inner_le_Lp_mul_Lq _ _ _ I4
   _=_:= ?_
  ·congr with t
   rw[QO,Qo, ←rpow_add' (by positivity),TL,rpow_one]
   simp
  ·have:1-(p:ℝ)⁻¹ ≠0:=sub_ne_zero.2 (inv_ne_one.2<| NNReal.coe_ne_one.2 hp.ne').symm
   simp[mul_rpow,rpow_nonneg,iu.ne',this,abs_rpow_of_nonneg]
 calc
  _ ≤
    ∑ x,(∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ):=
   sum_le_sum fun i _↦this _
  _=_:= ?_
 have hg: ∀ x, ∑ y, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ek]
  exact fun x↦Qk (Equiv.subLeft _) _ _ fun _↦rfl
 have hg': ∀ y, ∑ x, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ek]
  exact fun x↦Qk (Equiv.subRight _) _ _ fun _↦rfl
 simp_rw[hg]
 rw[←sum_mul,sum_comm]
 simp_rw[←mul_sum,hg']
 rw[←sum_mul,Qo, ←rpow_one_add' (by positivity),TL]
 rw[TL]
 positivity
end RCLike
section Real
variable [MeasurableSpace G] [DiscreteMeasurableSpace G] {f g:G→ℝ} {n:ℕ}
lemma yP (hf:0≤f) (hg:0≤g):(aJ 1 ((aC f g)))=(aJ 1 f)*(aJ 1 g):=by
 have: ∀ x,0≤ ∑ y,f y*g (x-y):=fun x↦sum_nonneg fun y _↦Qn (hf _) (hg _)
 simp[ek, ←uM,cR,norm_of_nonneg (this _),
  norm_of_nonneg (hf _),norm_of_nonneg (hg _)]
lemma xW (hf:0≤f) (hg:0≤g):(aJ 1 ((al f g)))=(aJ 1 f)*(aJ 1 g):=by
 simpa using yP hf (conjneg_nonneg.2 hg)
end Real
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal NNRat
variable {ι 𝕜 S:Type*} [Fintype ι]
namespace RCLike
variable [RCLike 𝕜] {I3:MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f:ι→𝕜}
@[simp] lemma xX {_:MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f:ι→𝕜) :
  ⟪f,f⟫_[𝕜]=(((aJ 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[ts,wInner_one_eq_sum]
end RCLike
namespace MeasureTheory
section Real
variable {α:Type*} {w3:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q:ℝ≥0∞}
 {f g:α→ℝ}
lemma ng (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ⟪f,g⟫_[ℝ]≤(aJ p f)*(aJ q g):=by
 have xY := Tk p q
 have xZ := Tk q p
 have yQ:⟪f,g⟫_[ℝ]= ∑ i,f i*g i:=by simp[wInner_one_eq_sum,Qx]
 have N5 i:f i*g i≤ ‖f i‖ * ‖g i‖:=
  (SG _).trans_eq (by rw[SU]; simp[QK])
 obtain rfl | Af:=Tf p ∞
 ·obtain rfl:q=1:=(Sx ∞ q).mp rfl
  simp only[yQ,ek,norm_eq_abs,dw,mul_sum]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 obtain rfl | MF:=Tf q ∞
 ·obtain rfl:p=1:=(Sx ∞ p).mp rfl
  simp only[yQ,ek,norm_eq_abs,dw,sum_mul]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 have N6 := UJ xY Af
 have N7 := UJ xZ MF
 have uO:Real.HolderConjugate p.toReal q.toReal:=by
  simpa using ENNReal.HolderTriple.toReal (p:=p) (q:=q) (r:=1) N6 N7
 rw[yQ,iv xY Af,iv xZ MF]
 simpa using Real.inner_le_Lp_mul_Lq Finset.univ f g uO
end Real
section mv
variable {α:Type*} {w3:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
lemma vM (f g:α→𝕜): ‖⟪f,g⟫_[𝕜]‖ ≤⟪fun a↦ ‖f a‖,fun a↦ ‖g a‖⟫_[ℝ]:=by
 grw[wInner_one_eq_sum,Rq]; simp[wInner_one_eq_sum]
lemma lq (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ‖⟪f,g⟫_[𝕜]‖ ≤(aJ p f)*(aJ q g):=
 calc
  _≤⟪fun a↦ ‖f a‖,fun a↦ ‖g a‖⟫_[ℝ]:=vM _ _
  _≤(aJ p (fun a↦ ‖f a‖))*(aJ q (fun a↦ ‖g a‖)):=ng _ _
  _=(aJ p f)*(aJ q g):=by simp_rw[Ad .of_discrete]
omit [Fintype α]
variable [Finite α]
lemma yR (p q:ℝ≥0∞) [p.HolderTriple q r]:(aJ r (f*g))≤(aJ p f)*(aJ q g):=by
 cases RR α
 change lpNorm (f*g) r .count≤lpNorm f p .count*lpNorm g q .count
 have N5:AEStronglyMeasurable (f*g) .count:= .of_discrete
 grw[←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete,
  ←UK, ←qV (r:=r) .of_discrete .of_discrete]
 exact(ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne
end mv
end MeasureTheory
end
end
section
open Finset Fintype Nat Real
variable {ι:Type*} {A:Finset ι} {m n:ℕ}
lemma step_one (hA:A.Nonempty) (f:ι→ℝ) (a:Fin n→ι)
  (hf: ∀ i, ∑ a∈(piFinset fun _:Fin n↦A),f (a i)=0) :
  |∑ i,f (a i)| ^(m+1) ≤
   (∑ b∈(piFinset fun _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^(m+1))/ #A^n:=by
 let B:=(piFinset fun _:Fin n↦A)
 calc
  _
   = |∑ i,(f (a i)-(∑ b∈B,f (b i))/ #B)| ^(m+1):=by
   simp only[B,hf,sub_zero,zero_div]
  _= |(∑ b∈B, ∑ i,(f (a i)-f (b i)))/ #B| ^(m+1):=by
   simp only[sum_sub_distrib]
   rw[sum_const,UT,sum_comm,sum_div,QS,card_piFinset,prod_const,
    Finset.card_univ,Fintype.card_fin,Rv,SH]
   positivity
  _= |∑ b∈B, ∑ i,(f (a i)-f (b i))| ^(m+1)/ #B^(m+1):=by
   rw[TE,TY,Nat.abs_cast]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^(m+1):=by
   gcongr; exact IsAbsoluteValue.abv_sum _ _ _
  _=(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^m/ #B:=by
   rw[div_div, ←pow_succ]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(m+1))/ #B:=by
   gcongr; exact TF (fun _ _↦Q8 _) _
  _=_:=by simp[B]
lemma D6 (hA:A.Nonempty) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset fun _:Fin n↦A),f (a i)=0) (m:ℕ)
  (a:Fin n→ι) :
  |∑ i,f (a i)| ^m≤(∑ b∈(piFinset fun _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^m)/ #A^n:=by
 cases m
 ·simp only[pow_zero,sum_const,prod_const,Nat.smul_one_eq_cast,Finset.card_fin,
   card_piFinset, ←Rv]
  rw[div_self]
  rw[Ru, ←Tx]
  exact RF (Finset.card_pos.2 hA) _
 exact step_one hA f a hf
lemma Ag (A:Finset ι) (f:ι→ℝ) (ε:Fin n→ℝ)
  (hε:ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ)))) (g:(Fin n→ℝ)→ℝ) :
  ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A),g (ε*(f ∘ a-f ∘ b)) =
   ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A),g (f ∘ a-f ∘ b):=by
 rw[←sum_product', ←sum_product']
 let n9:(Fin n→ι) × (Fin n→ι)→(Fin n→ι) × (Fin n→ι):=by
  intro xy
  exact(fun i↦if ε i=1 then xy.1 i else xy.2 i,fun i↦if ε i=1 then xy.2 i else xy.1 i)
 have h₁: ∀ a∈((piFinset fun _:Fin n↦A)) ×ˢ ((piFinset fun _:Fin n↦A)),n9 a∈((piFinset fun _:Fin n↦A)) ×ˢ ((piFinset fun _:Fin n↦A)):=by
  simp only[mem_product,mem_piFinset, ←forall_and,n9]
  intro a h i
  split_ifs
  ·exact h i
  ·exact(h i).symm
 have h₂: ∀ a∈((piFinset fun _:Fin n↦A)) ×ˢ ((piFinset fun _:Fin n↦A)),n9 (n9 a)=a:=fun a _↦by
  ext<;>simp only[n9]<;>split_ifs<;>rfl
 refine sum_nbij' n9 n9 h₁ h₁ h₂ h₂ ?_
 ·rintro ⟨a,b⟩ _
  congr with i:1
  simp only[mem_piFinset,mem_insert,mem_singleton] at hε
  simp only[Pi.mul_apply,Rw,Rh,n9]
  split_ifs with h
  ·simp[h]
  rw[(hε i).resolve_right h]
  ring
lemma FT (f:ι→ℝ) :
  ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A),(∑ i,(f (a i)-f (b i)))^(2*m) =
   2⁻¹ ^n* ∑ ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
    ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m):=by
 let B:=(piFinset fun _:Fin n↦A)
 have: ∀ ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
  ∑ a∈B, ∑ b∈B,(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈B, ∑ b∈B,(∑ i,(f (a i)-f (b i)))^(2*m):=
  fun ε hε↦Ag A f _ hε fun z:Fin n→ℝ↦univ.sum z^(2*m)
 rw[Io rfl this,sum_const,card_piFinset_const,card_pair,QS,
  Rv,So,Te,inv_mul_cancel_left₀]
 ·positivity
 ·norm_num
lemma CE (f:ι→ℝ) :
  ∑ ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
   ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ (2*m),
     (multinomial univ k* ∏ t,(f (a t)-f (b t))^k t) *
      ∑ ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t:=by
 simp only[@sum_comm _ _ (Fin n→ℝ) _ _ ((piFinset fun _:Fin n↦A)),sum_pow_eq_sum_piAntidiag]
 refine sum_congr rfl fun a _↦ ?_
 refine sum_congr rfl fun b _↦ ?_
 simp only[QL,prod_mul_distrib, @sum_comm _ _ (Fin n→ℝ), ←mul_sum, ←sum_mul]
 refine sum_congr rfl fun k _↦ ?_
 rw[←Qo,QN]
lemma D7 {k:Fin n→ℕ} :
  ∑ ε∈(piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t=2^n*ite (∀ i,Even (k i)) 1 0:=by
 calc
  _= ∏ i, ∑ j∈({-1,1}:Finset ℝ),j^k i:=by rw[←sum_prod_piFinset]
  _= ∏ i,if Even (k i) then 2 else 0:=by
   congr with i
   split_ifs<;>simp_all[sum_pair (show(-1:ℝ)≠1 by norm_num),one_add_one_eq_two]
  _=_:=by simp[Fintype.prod_ite_zero]
lemma FU {f:ι→ℝ} {a b:Fin n→ι} :
  ∑ k∈piAntidiag univ m,
    (multinomial univ fun a↦2*k a:ℝ)* ∏ i,(f (a i)-f (b i))^(2*k i) ≤
   m^m*(∑ i,(f (a i)-f (b i))^2)^m:=by
 rw[sum_pow_eq_sum_piAntidiag,mul_sum]
 refine sum_le_sum fun k hk↦ ?_
 rw[mem_piAntidiag] at hk
 simp only[←Qo,QU]
 gcongr
 norm_cast
 refine multinomial_two_mul_le_mul_multinomial.trans ?_
 rw[hk.1]
lemma CF {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*(∑ i,(f (a i)-f (b i))^2:ℝ)^m ≤
   m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m:=by
 rw[←QL, ←QL, ←QL,Qo,mul_sum _ _ (2:ℝ)]
 gcongr with i
 exact add_sq_le.trans_eq (by simp)
lemma CI {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m ≤
   m^m*2^(m+(m-1)) *
    ((∑ i,f (a i)^2)^m+(∑ i,f (b i)^2)^m):=by
 rw[RL, ←Qo _ _ (2^_),Qo _ (2^(m-1)),sum_add_distrib]
 gcongr
 refine add_pow_le ?_ ?_ m<;>positivity
lemma FV {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ (piFinset fun _ : Fin n ↦ A), ∑ b ∈ (piFinset fun _ : Fin n ↦ A), ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (4 * m) ^ m * ∑ a ∈ (piFinset fun _ : Fin n ↦ A), (∑ i, f (a i) ^ 2) ^ m:= by
  let B:= (piFinset fun _ : Fin n ↦ A)
  calc
    _

      ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n:= by
      gcongr; exact FU.trans <| CF.trans CI
    _ = _:= by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2, ← _root_.pow_succ',
        add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity
section
namespace Real
lemma tu (m:ℕ) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m* ∑ a∈(piFinset fun _:Fin n↦A),(∑ i,f (a i)^2)^m:=by
 obtain rfl | hm:=m.eq_zero_or_pos
 ·simp
 have w4:1≤ m:=by rwa[Ty]
 obtain rfl | hA:=A.eq_empty_or_nonempty
 ·cases n<;>cases m<;>simp
 let B:=(piFinset fun _:Fin n↦A)
 calc
  ∑ a∈B,(∑ i,f (a i))^(2*m)
   ≤ ∑ a∈(piFinset fun _:Fin n↦A),(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(2*m))/ #A^n:=by
   gcongr; simpa[QU,sq_abs] using D6 hA f hf (2*m) _
  _=(∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ (2*m) with ∀ i,2∣k i,
    multinomial univ (fun i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[←sum_div]
   simp only[QU,sq_abs]
   simp only[←QU]
   rw[FT,CE,Qx,Te, ←Qw,div_div]
   simp only[D7,Td,mul_zero,Q3, ←sum_filter, ←sum_mul,even_iff_two_dvd]
   rw[Qx,mul_div_mul_left]
   positivity
  _=(∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A), ∑ k∈(piAntidiag univ m).map
     ⟨(2•·),fun _ _ h↦funext fun i↦mul_right_injective₀ SD (SR h i)⟩,
    multinomial univ (fun i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[map_nsmul_piAntidiag_univ m (ι:=Fin n) (n:=2) SD]; congr!
  _=(∑ a∈(piFinset fun _:Fin n↦A), ∑ b∈(piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ m,
    multinomial univ (fun i↦2*k i)* ∏ t,(f (a t)-f (b t))^(2*k t))/ #A^n:=by
   simp
  _≤_:=FV w4 hA
lemma g8 (hm:m≠0) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m*n^(m-1)* ∑ a∈(piFinset fun _:Fin n↦A), ∑ i,f (a i)^(2*m):=by
 obtain _ | m:=m
 ·simp at hm
 obtain rfl | hn:=n.eq_zero_or_pos
 ·simp
 calc
  ∑ a∈(piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*(m+1))
   ≤ (4* ↑(m+1))^(m+1)* ∑ a∈(piFinset fun _:Fin n↦A),(∑ i,f (a i)^2)^(m+1):=
   tu _ f hf
  _≤(4* ↑(m+1))^(m+1)*(∑ a∈(piFinset fun _:Fin n↦A),n^m* ∑ i,f (a i)^(2*(m+1))):= ?_
  _≤(4* ↑(m+1))^(m+1)*n^m* ∑ a∈(piFinset fun _:Fin n↦A), ∑ i,f (a i)^(2*(m+1)):=by
   simp_rw[Qo,mul_sum]; rfl
 gcongr with a
 rw[←div_le_iff₀' (by positivity)]
 simpa only[Finset.card_fin,QU] using
  TF (f:=fun i↦f (a i)^2) (s:=univ) (fun i _↦by positivity) m
end Real
namespace RCLike
variable {𝕜:Type*} [RCLike 𝕜]
lemma g8 (hm:m≠0) (f:ι→𝕜) (hf: ∀ i, ∑ a∈(piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset fun _:Fin n↦A), ‖∑ i,f (a i)‖ ^(2*m) ≤
   (8*m)^m*n^(m-1)* ∑ a∈(piFinset fun _:Fin n↦A), ∑ i, ‖f (a i)‖ ^(2*m):=by
 let f₁ x:ℝ:=re (f x)
 let f₂ x:ℝ:=im (f x)
 let B:=(piFinset fun _:Fin n↦A)
 have K0 i: ∑ a∈B,f₁ (a i)=0:=by rw[←RK,hf,map_zero]
 have K1 i: ∑ a∈B,f₂ (a i)=0:=by rw[←RK,hf,map_zero]
 have h₁:=Real.g8 hm _ K0
 have h₂:=Real.g8 hm _ K1
 simp only[QU,RCLike.norm_sq_eq_def]
 simp only[←sq,RK,RK]
 calc
  ∑ a∈B,((∑ i,re (f (a i)))^2+(∑ i,im (f (a i)))^2)^m ≤
    ∑ a∈B,
     2^(m-1)*(((∑ i,re (f (a i)))^2)^m+((∑ i,im (f (a i)))^2)^m):=by
   gcongr with a; apply add_pow_le<;>positivity
  _=2^(m-1)*(∑ a∈B,(∑ i,re (f (a i)))^(2*m) +
     ∑ a∈B,(∑ i,im (f (a i)))^(2*m)):=by
   simp only[←sum_add_distrib,mul_sum,QU]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,re (f (a i))^(2*m)+(4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,im (f (a i))^(2*m)):=by gcongr
  _=2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,(re (f (a i))^(2*m)+im (f (a i))^(2*m))):=by
   simp_rw[sum_add_distrib,Tc]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,2*(re (f (a i))^2+im (f (a i))^2)^m):=by
   simp_rw[QU]; gcongr; apply pow_add_pow_le'<;>positivity
  _=(8*m)^m*n^(m-1)* ∑ a∈B, ∑ i,(re (f (a i))^2+im (f (a i))^2)^m:=by
   simp_rw[←mul_sum,show(8:ℝ)=2*4 by norm_num,QL, ←R0 hm (2:ℝ)]
   ring
end RCLike
end
end
section
open scoped Pointwise Combinatorics.Additive translate

section
variable {α:Type*} {g:α→ℝ} {c ε:ℝ} {A:Finset α}
open Finset
lemma D8 (hc:0<c) (hg: ∀ a∈A,0≤g a) (h: ∑ a∈A,g a≤ε*c* #A) :
  (1-ε)* #A≤ #{a∈A | g a≤c}:=by
 classical
 have:=h.trans'
  (sum_le_sum_of_subset_of_nonneg (filter_subset (¬g ·≤c) A) fun i hi _↦hg _ hi)
 have:=
  (card_nsmul_le_sum _ _ c (by simp+contextual [le_of_lt])).trans this
 rw[QS,QN] at this
 have:=TZ this hc
 rw[filter_not,cast_card_sdiff (filter_subset _ _)] at this
 linarith only[this]
lemma x0 (hc:0≤c) (hε:0≤ε) (hg: ∀ a∈A,0≤g a)
  (h: ∑ a∈A,g a≤ε*c* #A):(1-ε)* #A≤ #{a∈A | g a≤c}:=by
 rcases hc.lt_or_eq with (hc | rfl)
 ·exact D8 hc hg h
 simp only[mul_zero,zero_mul] at h
 classical
 rw[one_sub_mul,sub_le_comm, ←cast_card_sdiff (filter_subset _ A), ←filter_not,
  filter_false_of_mem]
 ·simp only[card_empty,UH]; positivity
 intro i hi
 rw[(sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi]
 simp
end
open Finset Real
open scoped BigOperators Pointwise NNReal ENNReal
variable {G:Type*} [Fintype G] {A S:Finset G} {f:G→ℂ} {x ε K:ℝ} {k m:ℕ}
section
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
open MeasureTheory in
lemma BC (hε:0<ε) (hm:1≤ m) (hk:64*m/ε^2≤k) :
  (8*m)^m*k^(m-1)* #A^k*k*(2*(aJ (2*m) f):ℝ)^(2*m) ≤
   1/2*((k*ε)^(2*m)* ∑ i:G, ‖f i‖ ^(2*m))* #A^k:=by
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have w4:2*m≠0:=by
  refine Rl two_pos.ne' ?_
  rw[←Tx, ←Ty]
  exact hm
 rw[QL (2:ℝ), ←yS, ←gz w4 f, ←Qo, ←Qo,
  QN _ (#A^k:ℝ),QN _ (#A^k:ℝ),
  QN _ (#A^k:ℝ)]
 rw[div_le_iff₀' (by positivity)] at hk
 have N8:=d8 (p:=((2*m:ℕ):ℝ≥0∞)) (f:=f)
 gcongr ?_*_*_
 calc
  (8*m:ℝ)^m*k^(m-1)*k*2^(2*m)
   = (8*m)^m*2^(2*m)*(k^(m-1)*k):=by ring
  _=(64*m*k/2)^m:=by rw[R0 (by omega),QU, ←QL]; ring
  _≤(ε^2*k*k/2)^m:=by gcongr
  _=(k*ε)^(2*m)/2^m:=by ring_nf; simp_rw[R6]
  _≤(k*ε)^(2*m)/2^1:=by gcongr; norm_num
  _=1/2*(k*ε)^(2*m):=by ring
end
variable [DecidableEq G] [AddCommGroup G]
lemma xk (hm:1≤ m) (x:G) :
  ∑ a∈(piFinset fun _:Fin k↦A), ‖∑ i,f (x-a i)-(k•((aC (mu A) f))) x‖ ^(2*m) ≤
   (8*m)^m*k^(m-1) *
    ∑ a∈(piFinset fun _:Fin k↦A), ∑ i, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m):=by
 let f':G→ℂ:=fun a↦f (x-a)-((aC (mu A) f)) x
 refine(RCLike.g8 (by linarith only[hm]) f' ?_).trans_eq' ?_
 ·intro i
  rw[Fintype.sum_piFinset_apply,sum_sub_distrib]
  simp only[sum_const]
  rw[←RD (card A), ←tn,l5,cR]
  simp only[SS,Qm,mem_coe]
  rw[←sum_filter,filter_mem_eq_inter,univ_inter,sub_self,smul_zero]
 congr with a:1
 simp only[sum_sub_distrib,RD,sum_const,card_fin,f']
variable [MeasurableSpace G]
namespace gl
def CJ (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G) (a:Fin k→G):Prop:=
 (aJ (2*m) (fun x:G↦ ∑ i,f (x-a i)-(k•((aC (mu A) f))) x))≤k*ε*(aJ (2*m) f)
noncomputable instance:DecidablePred (CJ k m ε f A):=Classical.decPred _
noncomputable def l (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G):Finset (Fin k→G):=
 {x∈(piFinset fun _:Fin k↦A) | CJ k m ε f A x}
lemma yT (hε:0<ε) (hm:1≤ m)
  (h: ∑ a∈(piFinset fun _:Fin k↦A),
    ((aJ (2*m) (fun x:G↦ ∑ i:Fin k,f (x-a i)-(k•((aC (mu A) f))) x))^(2*m):ℝ) ≤
   1/2*(k*ε*(aJ (2*m) f))^(2*m)* #A^k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 rw[←Rv, ←TG] at h
 have N8:=d8 (p:=2*m) (f:=f)
 have:=x0 (by positivity) (by norm_num)
  (fun _ _↦QH d8 _) h
 norm_num1 at this
 rw[TG,Qx,mul_one_div,Rv] at this
 refine this.trans_eq ?_
 rw[l]
 congr with a:3
 refine pow_le_pow_iff_left₀ ?_ ?_ ?_<;>first | positivity | exact d8
variable [DiscreteMeasurableSpace G]
open MeasureTheory in
lemma xl (hm:1≤ m) (hA:A.Nonempty) :
  (8*m)^m*k^(m-1)* ∑ a∈(piFinset fun _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ _a∈(piFinset fun _:Fin k↦A), ∑ _i:Fin k,(2*(aJ (2*m) f))^(2*m):=by
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have w4:1<2*m:=(Qr 2 hm).trans_lt'<| by norm_num1
 have M1:(1:ℝ≥0∞)≤2*m:=by rw[←yS,Nat.one_le_cast]; exact w4.le
 gcongr
 ·exact d8
 refine(yO M1).trans ?_
 rw[jY,R5 (aJ (2*m) f),add_le_add_iff_left]
 have K2:((2*m:ℝ≥0):ℝ≥0∞)=2*m:=by
  rw[ENNReal.coe_mul,ENNReal.coe_two,ENNReal.coe_natCast]
 have:(1:ℝ≥0)<2*m:=by
  rw[←So, ←Rm,Nat.one_lt_cast]
  exact w4
 rw[←K2,fA]
 refine(wW this.le _ _).trans ?_
 rw[uN hA,Q3]
open MeasureTheory in
lemma Ho (hε:0<ε) (hm:1≤ m) (hk:(64:ℝ)*m/ε^2≤k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 have:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  refine hk.trans_lt' ?_
  refine Rn (QM (by norm_num1) ?_) (RF hε _)
  rw[Sp, ←Ty]
  exact hm
 rcases A.eq_empty_or_nonempty with (rfl | hA)
 ·simp[zero_pow this.ne']
 refine yT hε hm ?_
 have w4:2*m≠0:=by linarith
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 rw[←yS,QL]
 simp only[gz w4]
 rw[sum_comm]
 have: ∀ x:G, ∑ a∈(piFinset fun _:Fin k↦A),
   ‖∑ i,f (x-a i)-(k•((aC (mu A) f))) x‖ ^(2*m) ≤
  (8*m)^m*k^(m-1) *
   ∑ a∈(piFinset fun _:Fin k↦A), ∑ i, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m):=
  xk hm
 refine(sum_le_sum fun x _↦this x).trans ?_
 rw[←mul_sum]
 simp only[@sum_comm _ _ G]
 have (a:Fin k→G) (i:Fin k) :
   ∑ x, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m)=(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m):=by
  rw[←yS,gz w4]
  simp only[Rw,QZ]
 simp only[this]
 have :
  (8*m)^m*k^(m-1)* ∑ a∈(piFinset fun _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ a∈(piFinset fun _:Fin k↦A), ∑ i,(2*(aJ (2*m) f))^(2*m):=
  xl hm hA
 refine Sj (mod_cast this) ?_
 simpa[Qo] using BC hε hm hk
open MeasureTheory in
lemma pN {t:G} {a:Fin k→G} (ha:a∈l k m ε f A)
  (mS:(a+fun _↦t)∈l k m ε f A) (hk:0<k) (hm:1≤ m) :
  (aJ (2*m) (τ (-t) ((aC (mu A) f))-(aC (mu A) f)))≤2*ε*(aJ (2*m) f):=by
 let f₁:G→ℂ:=fun x↦ ∑ i,f (x-a i)
 let f₂:G→ℂ:=fun x↦ ∑ i,f (x-a i-t)
 have hp:(1:ℝ≥0∞)≤2*m:=by norm_cast; linarith
 have h₁:(aJ (2*m) (f₁-k•((aC (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU] at ha ; exact ha.2
 have h₂:(aJ (2*m) (f₂-k•((aC (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU,CJ] at mS
  refine mS.2.trans_eq' ?_
  congr with i:1
  simp[sub_sub,f₂]
 have h₃:f₂=τ t f₁:=by
  ext i:1
  rw[QZ]
  refine Io rfl fun j _↦ ?_
  rw[sub_right_comm]
 have Hp:(aJ (2*m) (τ t f₁-k•((aC (mu A) f))))=(aJ (2*m) (τ (-t) (τ t f₁-k•((aC (mu A) f))))):=by
  rw[jY]
 have M3:(aJ (2*m) (τ t f₁-k•((aC (mu A) f))))=(aJ (2*m) (f₁-τ (-t) (k•((aC (mu A) f))))):=by
  rw[Hp,UE,translate_translate]
  simp
 have NM:(aJ (2*m) (τ (-t) (k•((aC (mu A) f)))-f₁))≤k*ε*(aJ (2*m) f):=by
  rwa[r6, ←M3, ←h₃]
 have:(0:ℝ)<k:=by positivity
 refine Uj ?_ this
 rw[←QS, ←zJ _ (_-(aC (mu A) f)),nsmul_sub, ←
  translate_smul_right (-t) ((aC (mu A) f)) k,Qo,Q6,R5 ((k:ℝ)*_), ←
  Qo]
 calc
  _
   ≤ (aJ (2*m) (τ (-t) (k•((aC (mu A) f)))-f₁))+(aJ (2*m) (f₁-k•((aC (mu A) f)))):=
   er (mod_cast hp)
  _≤k*ε*(aJ (2*m) f)+k*ε*(aJ (2*m) f):=by gcongr
end gl
end
section
section
open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise
variable {G R:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
section lr
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g:G→R}
lemma zL (hf:0≤f) (hg:0≤g):0≤(aC f g):=
 fun _a↦sum_nonneg fun _x _↦Qn (hf _) (hg _)
lemma pC (hf:0≤f) (hg:0≤g) (a:G):0≤((aC f g)) a:=
 zL hf hg _
variable [StarRing R] [StarOrderedRing R]
lemma iN (hf:0≤f) (hg:0≤g):0≤(al f g):=
 fun _a↦sum_nonneg fun _x _↦Qn (hf _)<| star_nonneg_iff.2<| hg _
lemma dM (hf:0≤f) (hg:0≤g) (a:G):0≤((al f g)) a:=
 iN hf hg _
end lr
section iw
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g:G→R}
@[simp] lemma tW (hf:0≤f) (hg:0≤g) :
  support ((aC f g))=support f+support g:=by
 refine(tT _ _).antisymm ?_
 rintro _ ⟨a,ha,b,hb,rfl⟩
 rw[mem_support,r5]
 exact Uq<| sum_pos' (fun c _↦Qn (hf _)<| hg _) ⟨0,mem_univ _,
  QM ((hf _).lt_of_ne'<| by simpa using ha)<| (hg _).lt_of_ne'<| by simpa using hb⟩
variable [StarRing R] [StarOrderedRing R]
@[simp] lemma f8 (hf:0≤f) (hg:0≤g):support ((al f g))=support f-support g:=by
 simpa[Qy] using tW hf (conjneg_nonneg.2 hg)
end iw

end
end
section
section
open Finset Function Real MeasureTheory
open scoped ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 E:Type*} [MeasurableSpace α]
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {w:α→ℝ≥0} {f g h:α→E}
noncomputable def b0 (p:ℝ≥0∞) (w:α→ℝ≥0) (f:α→E):ℝ:=
 lpNorm f p<| .sum fun i↦w i• .dirac i
@[simp] lemma tX:0≤(b0 p w f):=by simp[b0]
@[simp] lemma I5 (w:α→ℝ≥0):(b0 p w ((0:α→E)))=0:=by simp[b0]
@[simp] lemma KR (w:α→ℝ≥0) (f:α→E):(b0 p w (-f))=(b0 p w f):=by
 simp[b0]
lemma Ah [NormedField 𝕜] [NormedSpace 𝕜 E] (c:𝕜) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (c•f))= ‖c‖₊*(b0 p w f):=lpNorm_const_smul ..
lemma zM [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (n•f))=n•(b0 p w f):=lpNorm_nsmul ..

variable [Finite α]
variable [Fintype α] [DiscreteMeasurableSpace α]
lemma lu (iu:p≠0) (hp:p≠∞) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)=(∑ i,w i• ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[b0,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,RG,
  integral_finsetSum_measure]
lemma r8 {p:ℝ≥0} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^(p:ℝ)= ∑ i,w i• ‖f i‖ ^(p:ℝ):=by
 rw[lu (mod_cast hp) (by simp),ENNReal.coe_toReal,
  S4 _ (mod_cast hp)]
 simp only[RG,Q2]
 positivity
lemma jd {p:ℕ} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^p= ∑ i,w i• ‖f i‖ ^p:=by
 simpa using r8 (Nat.cast_ne_zero.2 hp) w f
omit [Fintype α]
section one_le
lemma yU (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w (f+g))≤(b0 p w f)+(b0 p w g):=lpNorm_add_le .of_discrete hp
lemma qX (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w f)≤(b0 p w (f+g))+(b0 p w g):=by simpa using yU hp w (f+g) (-g)
end one_le
end NormedAddCommGroup

end
end
section
section
namespace Finset
variable {α R:Type*} [Fintype α] [Semiring R]
@[simp] lemma rp (s:Finset α): ∑ x,(indicator ((s:Set α)) fun _↦(1:R)) x= #s:=by
 classical simp[Qm]
lemma lN (s:Finset α): #s= ∑ x,(indicator ((s:Set α)) fun _↦(1:_)) x:=
 (rp _).symm
end Finset
end
end
section
section
namespace Set
variable {α M:Type*} [Zero M] [One M]
section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s:Set α}
@[simp] lemma cY:0≤ s.indicator (fun _↦(1:M)):=
 indicator_nonneg (by simp)
end Preorder

end Set
end
end
section
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped ENNReal NNReal Pointwise
variable {G:Type*} [DecidableEq G] [Fintype G] [AddCommGroup G] {p:ℕ} {aL a0 A:Finset G}
 {ε δ:ℝ}
private def c (p:ℕ) (A:Finset G) (s:Fin p→G):Finset G:=univ.inf fun i↦s i+ᵥ A
private lemma Ca (p:ℕ) (aL a0 A:Finset G) (f:G→ℝ) :
  ∑ s,⟪(al ((indicator (↑(aL∩c p A s)) fun _↦(1:(ℝ)))) ((indicator (↑(a0∩c p A s)) fun _↦(1:_)))),f⟫_[ℝ] =
   (#aL* #a0)• ∑ x,((al ((@mu (ℝ) _ _) aL) (mu a0))) x*((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_))))) x^p*f x:=by
 simp_rw[Qo]
 simp only[wInner_one_eq_sum,inner_apply',R3,mul_sum,sum_mul,smul_sum,
  @sum_comm _ _ (Fin p→G),lM,rm,Fintype.sum_pow,
  Set.rj]
 congr with ey
 congr with b₂
 refine Qk (Equiv.neg _) _ _ fun s↦ ?_
 rw[←TJ,mul_smul_mul_comm,qr,qr,
  coe_inter,coe_inter,Set.iq,Set.iq,
  Q7,prod_mul_distrib]
 simp[c,mQ,Qy,Qo,RV]
private lemma K3 (p:ℕ) (B A:Finset G): ∑ s, #(B∩c p A s)= #A^p* #B:=by
 simp only[lN,Set.iq,c,mQ,
  mul_sum,sum_mul,coe_inter,coe_vadd_finset,sum_pow', @sum_comm G,SB,
  ←sU,QZ]
 congr with x
 exact Qk (Equiv.subLeft fun _↦x) _ _ fun s↦Qx _ _
private lemma x1 (p:ℕ) (B A:Finset G) :
  ∑ s,(#(B∩c p A s):ℝ)= #A^p* #B:=by
 rw[←Nat.cast_sum,K3]; norm_cast
variable [MeasurableSpace G]
noncomputable def s (p:ℝ≥0) (ε:ℝ) (aL a0 A:Finset G):Finset G:=
 {x | (1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))<((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_))))) x}
@[simp] lemma K4 {p:ℝ≥0} {ε:ℝ} {aL a0 A:Finset G} {x:G} :
  x∈s p ε aL a0 A ↔
   (1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))<((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_))))) x:=by simp[s]
lemma I6 {p : ℝ≥0} {ε : ℝ} {aL a0 A : Finset G} {x : G} :
    x ∈ s p ε aL a0 A ↔ (1 - ε) * (_root_.b0 p ((_root_.al (_root_.mu aL) (_root_.mu a0))) ((_root_.al ((@_root_.mu (ℝ) _ _) A) (_root_.mu A)))) < ((_root_.al (_root_.mu A) (_root_.mu A))) x:= by
  obtain rfl | hA:= A.eq_empty_or_nonempty
  · simp
  · simp [← l5, -nsmul_eq_mul, oB, oC, zM, hA.card_pos]
variable [DiscreteMeasurableSpace G]
private lemma jq (hp:p≠0) (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  (0:ℝ)<(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p:=by
 rw[jd (by positivity)]
 refine sum_pos' (fun x _↦by positivity) ⟨0,mem_univ _,smul_pos ?_<| RF ?_ _⟩
 ·rwa[Tx, ←Ur,f8,jo,jo,
   ←coe_sub,mem_coe,zero_mem_sub_iff,not_disjoint_iff_nonempty_inter]<;>exact cC
 ·rw[norm_pos_iff, ←Ur,f8,Set.j0]
  any_goals exact Set.cY
  exact hA.to_set.zero_mem_sub
lemma N9 (hp₂:2≤p) (f:G→ℝ≥0) (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∈f.support)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0 ∧
   ⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p
    ≤ 2* ∑ x,((al (mu aL) (mu a0))) x*((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))) x^p*f x ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #aX/ #aL ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #a3/ #a0:=by
 have:=hB.mono inter_subset_left
 have:=hB.mono inter_subset_right
 have iu:p≠0:=by positivity
 have:=jq iu hB hA
 set M:ℝ:=
  2 ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p*(sqrt #aL*sqrt #a0)/ #A^p
   with Ai
 have hM:0<M:=by rw[Ai]; positivity
 replace hf:0< ∑ x,((al ((@mu (ℝ) _ _) aL) (mu a0))) x*((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_))))) x^p*f x:=by
  have:0≤(al ((@mu (ℝ) _ _) aL) (mu a0))*((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_)))))^p*(↑) ∘ f:=
   Qn (Qn (iN cC cC)<| QH
    (iN Set.cY Set.cY) _) fun _↦by simp
  refine Fintype.sum_pos<| this.lt_iff_ne'.2<| support_nonempty_iff.1 ?_
  simp only[support_comp_eq,Set.Nonempty,Tm,support_mul',f8,
   Set.cY,cC,Set.j0,jo,
   NNReal.coe_eq_zero,iff_self,forall_const,Set.mem_inter_iff, ←coe_sub,mem_coe,
   support_pow' _ iu,hf]
 set aX:=fun s↦aL∩c p A s
 set a3:=fun s↦a0∩c p A s
 set g:(Fin p→G)→ℝ:=fun s↦ #(aX s)* #(a3 s) with D9
 have hg: ∀ s,0≤g s:=fun s↦by rw[D9]; dsimp; positivity
 have Aj: ∑ s,g s= #aL* #a0*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p:=by
  have Ea:0≤(al ((indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_)))):=
   iN Set.cY Set.cY
  simpa only[jd iu,norm_of_nonneg (Ea _),RG,
   NNReal.lg,NNReal.iF,wInner_one_eq_sum,Rt,inner_apply',
   ←coe_inter,conj_to_real,Q3,jJ,rp,QS,
   Rm,g,aX,a3] using! Ca p aL a0 A 1
 suffices ∑ s,⟪(al ((indicator (aX s) fun _↦(1:(ℝ)))) ((indicator (a3 s) fun _↦(1:_)))),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p
  < ∑ s,(indicator (({s | M^2≤g s}:Finset _)) fun _↦(1:_)) s*g s *
    (2* ∑ x,((al (mu aL) (mu a0))) x*((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))) x^p*f x) by
  obtain ⟨s, -,hs⟩:=exists_lt_of_sum_lt this
  refine ⟨_,inter_subset_left (s₂:=c p A s),_,inter_subset_left (s₂:=c p A s), ?_⟩
  simp only[Qm,SS] at hs
  split_ifs at hs with h; swap
  ·simp only[zero_mul,wInner_one_eq_sum,Rh,SV,
    R3] at hs
   have:0≤(al ((indicator ((aX s:Set G)) fun _↦(1:(ℝ)))) ((indicator (a3 s) fun _↦(1:_)))):=
    iN Set.cY Set.cY
   cases hs.not_ge<|
    Qn (sum_nonneg fun x _↦Qn (this _)<| by positivity)<| by positivity
  have:(4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
   ≤ #(aX s)/ #aL*(#(a3 s)/ #a0):=by
   rw[div_mul_div_comm,Qs (by positivity)]
   simpa[D9,Ai,QL,TY,pow_mul',show(2:ℝ)^2=4 by norm_num,
    S5] using h
  refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' ?_)<| hg s).le,this.trans<|
   Sq ?_<| UW ?_ ?_,this.trans<|
   RQ ?_<| UW ?_ ?_⟩
  ·simp_rw[aX,a3,g, ←l5,oB,oC, ←Nat.cast_smul_eq_nsmul ℝ,
    wInner_smul_left,Q2,star_trivial,Qo,aX,a3]
  any_goals positivity
  all_goals exact Nat.cast_le.2<| card_mono inter_subset_left
 rw[←sum_mul,Ca,QS,Rm, ←sum_mul,QN, ←Aj,
  Q6, ←Qo]
 simp only[Qm,SS,mem_coe,mem_filter,mem_univ,TM, ←sum_filter,
  mul_lt_mul_iff_left₀ hf,Rh]
 by_cases h: ∀ s,g s≠0→M^2≤g s
 ·rw[←sum_filter_ne_zero (s:=filter _ _),Finset.filter_comm,
   filter_true_of_mem fun s hs↦h s (mem_filter.1 hs).2, ←sum_filter_ne_zero]
  refine lt_mul_of_one_lt_left (sum_pos (fun s hs↦(h _ (mem_filter.1 hs).2).trans_lt'<|
   by positivity) ?_) one_lt_two
  rw[←sum_filter_ne_zero] at Aj
  exact nonempty_of_sum_ne_zero<| Aj.trans_ne<| by positivity
 push Not at h
 obtain ⟨s,hs⟩:=h
 suffices h:(2:ℝ)* ∑ s with g s<M^2,g s< ∑ s,g s by
  refine(le_or_lt_of_add_le_add ?_).resolve_left h.not_ge
  simp_rw[←not_le, ←compl_filter, ←R5, ←Tc,sum_compl_add_sum]
  rfl
 rw[←lt_div_iff₀' (zero_lt_two' ℝ),Ri]
 calc
  ∑ s with g s<M^2,g s= ∑ s with g s<M^2∧g s≠0,Real.sqrt (g s)*Real.sqrt (g s)
    := by simp_rw[mul_self_sqrt (hg _), ←filter_filter,sum_filter_ne_zero]
  _< ∑ s with g s<M^2∧g s≠0,M*Real.sqrt (g s)
   := sum_lt_sum_of_nonempty ⟨s,mem_filter.2 ⟨mem_univ _,hs.symm⟩⟩ ?_
  _≤ ∑ s,M*Real.sqrt (g s):=sum_le_univ_sum_of_nonneg fun s↦by positivity
  _=M*(∑ s,Real.sqrt #(aX s)*Real.sqrt #(a3 s))
   := by simp_rw[mul_sum,g,sqrt_mul<| Q5 _]
  _≤M*(Real.sqrt (∑ s, #(aX s))*Real.sqrt (∑ s, #(a3 s))):=by
   gcongr; exact sum_sqrt_mul_sqrt_le _ fun i↦by positivity fun i↦by positivity
  _=_:= ?_
 ·simp only[mem_filter,mem_univ,TM,and_imp]
  exact fun s Oa hs↦Sk ((sqrt_lt' hM).2 Oa)<|
   sqrt_pos.2<| (hg _).lt_of_ne' hs
 rw[x1,x1,sqrt_mul',sqrt_mul',Q7 (Real.sqrt _),mul_self_sqrt,
  ←Qo,Ai,Tz, ←sqrt_mul,Qo,mul_self_sqrt,Aj,QN,
  Qo]
 all_goals positivity
lemma Hq (aL a0:Finset G) (hε:0<ε) (Ak:ε≤1) (Cc:0<δ) (hp:Even p)
  (hp₂:2≤p) (FW:ε⁻¹ *log (2/δ)≤p) (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∉s p ε aL a0 A) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0∧1-δ≤ ∑ x∈s p ε aL a0 A,((al (mu aX) (mu a3))) x ∧
    (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #aX/ #aL ∧
     (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #a3/ #a0:=by
 obtain ⟨aX,I7,a3,I8,h,r9,sa⟩:=
  N9 hp₂ (indicator ((s p ε aL a0 A)ᶜ) fun _↦(1:_))
   (by simpa only[Set.j0,coe_compl,Set.mem_compl_iff,mem_coe]) hB hA
 refine ⟨aX,I7,a3,I8, ?_,r9,sa⟩
 have iu:0<p:=by positivity
 have aux (c:Finset G) (r)
  (h:(4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)≤ #c/r) :
  c.Nonempty:=by
  simp_rw[nonempty_iff_ne_empty]
  rintro rfl
  simp[pow_mul',TA (zero_lt_four' ℝ),div_nonpos_iff,
   (RF (jq iu.ne' hB hA) 2).not_ge,iu.ne',hA.ne_empty] at h
 have fY:aX.Nonempty:=aux _ _ r9
 have g9:a3.Nonempty:=aux _ _ sa
 clear r9 sa aux
 rw[sub_le_comm]
 calc
  _= ∑ x∈(s p ε aL a0 A)ᶜ,((al (mu aX) (mu a3))) x:= ?_
  _=⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ (indicator ((s (↑p) ε aL a0 A)ᶜ) fun _↦(1:(ℝ≥0)))⟫_[ℝ]:=by
   simp[wInner_one_eq_sum, -mem_compl, -K4,Qm]
   simp only[←ite_not (_∈s p ε aL a0 A), ←mem_compl,TU]
   simp[-mem_compl]
  _≤_:=(Qs<| jq iu.ne' hB hA).2 h
  _≤_:= ?_
 ·simp_rw[sub_eq_iff_eq_add',sum_add_sum_compl,jJ,xV]
  rw[kW _ fY,kW _ g9,QT]
 rw[QF (jq iu.ne' hB hA), ←le_div_iff₀' (zero_lt_two' ℝ)]
 simp only[TU NNReal.toReal,Qm,TN,NNReal.coe_zero,
  mul_boole,Fintype.sum_ite_mem,S5, ←coe_compl,mem_coe]
 calc
  ∑ x∈(s p ε aL a0 A)ᶜ,((al (mu aL) (mu a0))) x*((al ((indicator A fun _↦(1:_))) ((indicator A fun _↦(1:_))))) x^p ≤
    ∑ x∈(s p ε aL a0 A)ᶜ,
     ((al (mu aL) (mu a0))) x*((1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_)))))))^p:=by
   gcongr with x hx
   ·exact dM cC cC x
   ·exact dM Set.cY Set.cY _
   ·simpa using hx
  _≤ ∑ x,((al (mu aL) (mu a0))) x*((1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_)))))))^p:=by
   gcongr
   ·intros
    exact Qn (dM cC cC _)<| hp.pow_nonneg _
   ·exact subset_univ _
  _=(aJ 1 ((@mu (ℝ) _ _) aL))*(aJ 1 ((@mu (ℝ) _ _) a0))*((1-ε)^p*(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^p)
   := ?_
  _≤_:=
   RQ (Qn (hp.pow_nonneg _)<| hp.pow_nonneg _)<|
    mul_le_one₀ rn d8 rn
  _≤_:=Qi ?_<| hp.pow_nonneg _
 ·have:0≤(al ((@mu (ℝ) _ _) aL) (mu a0)):=iN cC cC
  simp_rw[←xW cC cC,ek,
   RA (this _),sum_mul,QL]
 calc
  (1-ε)^p≤exp (-ε)^p:=by gcongr; exact one_sub_le_exp_neg _
  _=exp (-(ε*p)):=by rw[←neg_mul,exp_mul,rpow_natCast]
  _≤exp (-log (2/δ)):=
   (exp_monotone<| TO<| (TA<| by positivity).1 FW)
  _=δ/2:=by rw[exp_neg,exp_log,inv_div]; positivity
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ} {ε:ℝ} {p:ℕ}
lemma wX {f:G→ℂ} (hf:(al g g)=f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  0≤⟪f^k,(↑) ∘ ν⟫_[ℂ]:=by
 calc
  0≤ ∑ z:Fin k→G,(‖∑ x,(∏ i,conj (g (x+z i)))*h x‖ :ℂ)^2:=by positivity
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) (yz.1-yz.2))^k:= ?_
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) x)^k:=by
    congr! with x _ yz Ob
    simpa using Ob
  _=_:=by
   rw[←hf, ←f9,wInner_one_eq_sum]
   simp only[Pi.pow_apply,Sb,map_pow]
   simp_rw[en h,sum_mul]
 simp_rw[rm,sum_fiberwise, ←univ_product_univ,sum_product]
 simp only[sum_pow',sum_mul_sum,RU,T0,SB,
  ←UX,RK,map_prod]
 simp only[mul_sum, @sum_comm _ _ (Fin k→G),Qx (conj _),prod_mul_distrib,TR]
 rw[sum_comm]
 congr with x
 congr with y
 congr with z
 group
lemma xm {f:G→ℝ} (hf:(al g g)=(↑) ∘ f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ]:=by
 simpa[←Complex.zero_le_real,wInner_one_eq_sum,Qx] using wX hf f9 k
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {ι κ 𝕜:Type*} [Fintype ι]
namespace RCLike
variable [RCLike 𝕜] {I3:MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f:ι→𝕜}
@[simp] lemma wInner_cWeight_self (f:ι→𝕜) :
  ⟪f,f⟫ₙ_[𝕜]=(((c2 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[ry,wInner_cWeight_eq_expect]
end RCLike
namespace MeasureTheory
section mv
variable {α:Type*} {w3:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Fintype α]
variable [Finite α]
lemma yV (p q:ℝ≥0∞) (_hr₀:r≠0) [PS:ENNReal.HolderTriple p q r] :
  (c2 r (f*g))≤(c2 p f)*(c2 q g):=by
 cases RR α
 set μ:=ProbabilityTheory.uniformOn (Set.univ:Set α) with Hr
 have Oc:IsFiniteMeasure μ:=by rw[Hr]; infer_instance
 have M4:MemLp (f*g) r μ:=MemLp.of_discrete
 have FX:MemLp f p μ:=MemLp.of_discrete
 have FY:MemLp g q μ:=MemLp.of_discrete
 have Od: ∀ᵐ x ∂μ, ‖f x*g x‖₊≤(1:NNReal)* ‖f x‖₊* ‖g x‖₊:=
  .of_forall fun x↦by rw[QT]; exact nnnorm_mul_le _ _
 have key:eLpNorm (fun x↦f x*g x) r μ
   ≤ ((1:NNReal):ℝ≥0∞)*eLpNorm f p μ*eLpNorm g q μ:=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p:=p) (q:=q) (r:=r)
   FX.aestronglyMeasurable FY.aestronglyMeasurable (·*·) 1 Od
 change lpNorm _ _ μ≤lpNorm _ _ μ*lpNorm _ _ μ
 rw[←toReal_eLpNorm M4.aestronglyMeasurable,
   ←toReal_eLpNorm FX.aestronglyMeasurable,
   ←toReal_eLpNorm FY.aestronglyMeasurable,
   ←UK]
 apply ENNReal.toReal_mono
 ·exact ENNReal.mul_ne_top FX.eLpNorm_ne_top FY.eLpNorm_ne_top
 ·simpa[Pi.mul_def] using key
end mv

section mv
variable {α:Type*} {w3:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Fintype α] in
lemma tY [Finite α] (p q:ℝ≥0∞) [hpq:ENNReal.HolderConjugate p q] :
  (c2 1 (f*g))≤(c2 p f)*(c2 q g):=yV _ _ one_ne_zero
end mv
end MeasureTheory
end
end
section
section
open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal translate
variable {G:Type*} [AddCommGroup G] [Fintype G] {f:G→ℂ} {ψ:AddChar G ℂ} {n:ℕ}
noncomputable def dft (f:G→ℂ):AddChar G ℂ→ℂ:=fun ψ↦⟪ψ,f⟫_[ℂ]
lemma dft_apply (f:G→ℂ) (ψ:AddChar G ℂ):dft f ψ=⟪ψ,f⟫_[ℂ]:=rfl
lemma pD [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ)
  (ψ:AddChar G ℂ): ‖dft f ψ‖ ≤(aJ 1 f):=by
 grw[dft_apply,lq ∞ 1,dw]
 simp[Q0]
lemma qY [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ) :
  (c2 (∞) (dft f))≤(aJ 1 f):=by
 rw[oE]; exact ciSup_le fun ψ↦pD f ψ
@[simp] lemma vN (f g:G→ℂ):⟪dft f,dft g⟫ₙ_[ℂ]=⟪f,g⟫_[ℂ]:=by
 classical
 unfold dft
 simp_rw[wInner_one_eq_sum,wInner_cWeight_eq_expect,inner_apply',RK,RU,
  T0,sum_mul,mul_sum,expect_sum_comm,Q7 _ (conj<| f _),
  ←expect_mul, ←Rz, ←map_neg_eq_inv, ←map_add_eq_mul,
  TH,add_neg_eq_zero,SS,UL]
@[simp] lemma w5 [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ) :
  (c2 2 (dft f))=(aJ 2 f):=by
 refine(sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1<| Complex.ofReal_injective ?_
 push_cast
 simpa[c2,aJ,RCLike.wInner_cWeight_self,xX] using vN f f
lemma vn (f:G→ℂ) (a:G):𝔼 ψ,dft f ψ*ψ a=f a:=by
 classical
 simp_rw[dft,wInner_one_eq_sum,inner_apply',sum_mul,expect_sum_comm,QN _ (f _),
  ←expect_mul, ←Rz,TK, ←map_sub_eq_div,
  TH,sub_eq_zero,SS,UL]
@[simp] lemma Al [DecidableEq G]:dft (uK:G→ℂ)=1:=by
 ext; simp[yI,dft_apply,wInner_one_eq_sum]
variable [DecidableEq G]
lemma sb (f g:G→ℂ) (ψ:AddChar G ℂ):dft ((aC f g)) ψ=dft f ψ*dft g ψ:=by
 simp_rw[dft,wInner_one_eq_sum,inner_apply,cR,mul_sum,sum_mul,
  ←sum_product',univ_product_univ]
 refine Qk ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _)  _ _ fun (a,b)↦ ?_
 simp[Q7, ←RU, ←map_add_eq_mul]
@[simp] lemma x2 (f g:G→ℂ):dft ((aC f g))=dft f*dft g:=funext<| sb _ _
@[simp] lemma vO (f:G→ℂ): ∀ n,dft ((ep f n))=dft f^n
 | 0=>Al
 | n+1=>by simp[vl,RB,vO]
@[simp] lemma vP (f:G→ℂ) (n:ℕ) (ψ:AddChar G ℂ) :
  dft ((ep f n)) ψ=dft f ψ^n:=SR (vO _ _) _
end
end
section
open scoped BigOperators
namespace ay
open Finset
abbrev AddCharacter (G:Type*) [AddCommGroup G]:=G→+ AddCircle (1:ℝ)
structure aj (G:Type*) [AddCommGroup G] where
 eX:Finset (AddCharacter G)
 width:AddCharacter G→NNReal
namespace aj
variable {G H:Type*} [AddCommGroup G] [AddCommGroup H]
def rank (B:aj G):ℕ:=B.eX.card
def ai (B:aj G) (t:NNReal):aj G where
 eX:=B.eX
 width γ:=t*B.width γ
@[simp] lemma KS (B:aj G) (t:NNReal) :
  (B.ai t).eX=B.eX:=rfl
@[simp] lemma oF (B:aj G) (t:NNReal) (γ:AddCharacter G) :
  (B.ai t).width γ=t*B.width γ:=rfl
@[simp] lemma f6 (B:aj G) (t:NNReal) :
  (B.ai t).rank=B.rank:=rfl
@[simp] lemma oG (B:aj G):B.ai 1=B:=by
 cases B
 simp[ai]
@[simp] lemma vo (B:aj G) (s t:NNReal) :
  (B.ai s).ai t=B.ai (t*s):=by
 cases B
 simp[ai,Qo]
noncomputable def carrier [Fintype G] (B:aj G):Finset G:=by
 classical
 exact Finset.univ.filter fun x ↦
  ∀ γ∈B.eX, ‖γ x‖ ≤(B.width γ:ℝ)
@[simp] lemma mem_carrier [Fintype G] (B:aj G) (x:G) :
  x∈B.carrier↔ ∀ γ∈B.eX, ‖γ x‖ ≤(B.width γ:ℝ):=by
 classical
 simp[carrier]
lemma se [Fintype G] (B:aj G):0∈B.carrier:=by
 rw[mem_carrier]
 intro γ oa
 simp
lemma aE [Fintype G] (B:aj G):B.carrier.Nonempty:=
 ⟨0,B.se⟩
lemma ec [Fintype G] {B:aj G} {x:G} :
  -x∈B.carrier↔x∈B.carrier:=by
 simp only[mem_carrier]
 constructor<;>intro hx γ oa
 ·simpa only[map_neg,norm_neg] using hx γ oa
 ·simpa only[map_neg,norm_neg] using hx γ oa
lemma b5 [Fintype G] {B:aj G} {s t:NNReal} (pE:s≤t) :
  (B.ai s).carrier⊆(B.ai t).carrier:=by
 intro x hx
 rw[mem_carrier] at hx ⊢
 intro γ oa
 have d5:(s:ℝ)*(B.width γ:ℝ) ≤
   (t:ℝ)*(B.width γ:ℝ):=by
  gcongr
 exact(hx γ oa).trans d5
lemma e8 [Fintype G] {B:aj G} {s t:NNReal} {x y:G}
  (hx:x∈(B.ai s).carrier) (hy:y∈(B.ai t).carrier) :
  x+y∈(B.ai (s+t)).carrier:=by
 rw[mem_carrier] at hx hy ⊢
 intro γ oa
 rw[map_add]
 calc
  _ ≤ ‖γ x‖ + ‖γ y‖:=norm_add_le _ _
  _≤(s:ℝ)*(B.width γ:ℝ)+(t:ℝ)*(B.width γ:ℝ):=
   Sr (hx γ oa) (hy γ oa)
  _=((s+t:NNReal):ℝ)*(B.width γ:ℝ):=by
   push_cast
   ring
lemma j2 [Fintype G] {B:aj G} {s t:NNReal} {x y:G}
  (hx:x∈(B.ai s).carrier) (hy:y∈(B.ai t).carrier) :
  x-y∈(B.ai (s+t)).carrier:=by
 rw[Qy]
 exact e8 hx (ec.mpr hy)
noncomputable def map (B:aj G) (e:G ≃+ H):aj H:=by
  classical
  exact
    { eX:=B.eX.image fun γ↦γ.comp e.symm.toAddMonoidHom
      width:=fun δ↦B.width (δ.comp e.toAddMonoidHom) }
@[simp] lemma MG (B:aj G) (e:G ≃+ H) (δ:AddCharacter H) :
    (B.map e).width δ=B.width (δ.comp e.toAddMonoidHom):=by
  classical
  simp[map]
@[simp] lemma vQ (B:aj G) (e:G ≃+ H) (δ:AddCharacter H) :
  δ∈(B.map e).eX ↔
   ∃ γ∈B.eX,γ.comp e.symm.toAddMonoidHom=δ:=by
 classical
 simp[map]
private lemma vx (e:G ≃+ H) :
  Injective (fun γ:AddCharacter G↦γ.comp e.symm.toAddMonoidHom):=by
 intro γ δ h
 ext x
 have hx:=S6 h (e x)
 simpa using hx
@[simp] lemma Am (B:aj G) (e:G ≃+ H) :
  (B.map e).rank=B.rank:=by
 classical
 rw[rank,rank,map]
 exact Finset.card_image_iff.mpr (vx e).injOn
private lemma sf (B:aj G) (e:G ≃+ H)
    (γ:AddCharacter G) :
    (B.map e).width (γ.comp e.symm.toAddMonoidHom)=B.width γ:=by
  change B.width ((γ.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom)=B.width γ
  apply QA B.width
  ext x
  simp
@[simp] lemma oH [Fintype G] [Fintype H]
  (B:aj G) (e:G ≃+ H) (x:G) :
  e x∈(B.map e).carrier↔x∈B.carrier:=by
 classical
 rw[mem_carrier,mem_carrier]
 constructor
 ·intro hx γ oa
  have CK :=
         vQ B e _ |>.mpr ⟨γ,oa,rfl⟩
  have hh:=hx (γ.comp e.symm.toAddMonoidHom) CK
  rw[sf] at hh
  have An:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rwa[An] at hh
 ·intro hx δ Cc
  rcases (vQ B e δ).mp Cc with ⟨γ,oa,rfl⟩
  rw[sf]
  have An:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rw[An]
  exact hx γ oa
@[simp] lemma kA [Fintype G] [Fintype H]
  (B:aj G) (e:G ≃+ H) :
  (B.map e).carrier.card=B.carrier.card:=by
 classical
 symm
 apply Finset.card_bijective e e.bijective
 intro x
 exact(oH B e x).symm
noncomputable def eK (N:ℕ) (hN:Odd N):ZMod N ≃+ ZMod N:=by
  let f:ZMod N→+ ZMod N:=
    { toFun:=fun x↦x+x
      map_zero':=by simp
      map_add':=by
        intro x y
        abel }
  have K5:IsUnit (2:ZMod N):=
    (ZMod.isUnit_iff_coprime 2 N).2 (Nat.coprime_two_left.mpr hN)
  have Hs :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp K5
  have M5:Function.Bijective f:=by
    simpa only[f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,R5] using Hs
  exact AddEquiv.ofBijective f M5
@[simp] lemma sV (N:ℕ) (hN:Odd N) (x:ZMod N) :
    eK N hN x=x+x:=by
  simp[eK]
@[simp] lemma tZ (N:ℕ) [NeZero N] (hN:Odd N)
  (B:aj (ZMod N)) :
  (B.map (eK N hN)).carrier.card=B.carrier.card:=
 kA B (eK N hN)
end aj
end ay
end
section
open Finset
open scoped NNReal
namespace ay.br
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
structure aY (G:Type*) [AddCommGroup G] [Fintype G]
  [DecidableEq G] where
 ba:aj G
 outer:ℝ≥0
 inner:ℝ≥0
 regular:0< inner∧inner≤outer ∧
  (ba.ai (outer+inner)).carrier.card ≤
   2*(ba.ai (outer-inner)).carrier.card
 set:Finset G
 nonempty:set.Nonempty
 mw:set⊆(ba.ai outer).carrier
namespace aY
def e9 (s:aY G):Finset G:=
 (s.ba.ai s.outer).carrier
def density (s:aY G):ℝ:=
 (s.set.card:ℝ)/s.e9.card
def rank (s:aY G):ℕ:=s.ba.rank
def card (s:aY G):ℕ:=s.e9.card
lemma sg (s:aY G):s.e9.Nonempty:=
 (s.ba.ai s.outer).aE
lemma dI (s:aY G):0<s.density:=
       Rn (by exact_mod_cast s.nonempty.card_pos)
  (by exact_mod_cast s.sg.card_pos)
lemma density_le_one (s:aY G):s.density≤1:=by
 rw[density,Q9 (by exact_mod_cast s.sg.card_pos)]
 exact_mod_cast Qu s.mw
end aY
def dk (q:ℝ) (aq:ℕ) (aU:ℝ)
  (s t:aY G):Prop:=
 q*s.density≤t.density ∧
  t.rank≤ s.rank+aq ∧
  exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)
inductive eu (q:ℝ) (aq:ℕ) (aU:ℝ) :
  ℕ→aY G→aY G→Prop
 | nil (s:aY G):eu q aq aU 0 s s
 | cons {n:ℕ} {s t u:aY G}
   (pE:dk q aq aU s t)
   (x3:eu q aq aU n t u) :
   eu q aq aU (n+1) s u
namespace eu
lemma qZ {q:ℝ} {aq:ℕ} {aU:ℝ}
  (hq:0≤q) {n:ℕ} {s t:aY G}
  (h:eu q aq aU n s t) :
  q^n*s.density≤t.density:=by
 induction h with
 | nil s=>simp
 | @cons n s t u pE x3 ih =>
   have uP := QH hq n
   calc
    _ =q^n*(q*s.density):=by
     rw[RB]
     ring
    _≤q^n*t.density:=
     iO pE.1 uP
    _≤u.density:=ih
lemma card_bound {q:ℝ} {aq:ℕ} {aU:ℝ}
  {n:ℕ} {s t:aY G}
  (h:eu q aq aU n s t) :
  exp (-(n:ℝ)*aU)*(s.card:ℝ)≤(t.card:ℝ):=by
 induction h with
 | nil s=>simp
 | @cons n s t u pE x3 ih =>
   have BD:0≤exp (-(n:ℝ)*aU):=
    (Q1 _).le
   calc
    _ =
      exp (-(n:ℝ)*aU) *
       (exp (-aU)*(s.card:ℝ)):=by
     rw[show-((n+1:ℕ):ℝ)*aU =
       (-(n:ℝ)*aU)+(-aU) by
      push_cast
      ring,
      R7]
     ring
    _≤exp (-(n:ℝ)*aU)*(t.card:ℝ):=
     iO pE.2.2 BD
    _≤(u.card:ℝ):=ih
end eu
def nK (L:ℕ) (density:ℝ):Prop:=
 1/(2:ℝ)^L≤density
end
end ay.br
end
section
open Finset Function
open scoped BigOperators NNReal
namespace ay
section Moments
variable {X:Type*} [Fintype X] [DecidableEq X]
def iP (ν f:X→ℝ) (k:ℕ):ℝ:=
 ∑ x:X,ν x*f x^k
def aK (ν f:X→ℝ) (k:ℕ):ℝ:=
 ∑ x:X,ν x* |f x| ^k
omit [DecidableEq X] in
lemma dx {ν f:X→ℝ} (f9: ∀ x,0≤ν x) (k:ℕ) :
  0≤aK ν f k:=
       sum_nonneg fun x _↦Qn (f9 x) (QH (Q8 _) _)
noncomputable def cP (ε:ℝ):ℕ:=
 Nat.ceil (60/ε^2)
noncomputable def dJ (ε:ℝ) (p:ℕ):ℕ:=
 2*p*cP ε
lemma ix {ε:ℝ} (hε:0<ε) :
  0<cP ε:=by
 rw[cP,Nat.ceil_pos]
 positivity
lemma sh (ε:ℝ) (p:ℕ) :
  Even (dJ ε p):=by
 refine ⟨p*cP ε, ?_⟩
 simp[dJ,R5,US]
lemma sW {ε:ℝ} {p:ℕ} (hε:0<ε) (hp:p≠0) :
  0<dJ ε p:=by
 simp[dJ,ix hε,Nat.pos_of_ne_zero hp]
lemma q0 {ε:ℝ} (_hε:0<ε) :
  60/ε^2≤cP ε:=by
 simpa[cP] using Rr (60/ε^2)
private lemma oI {a b:ℝ} {n:ℕ}
  (ha:0≤a) (hb:0≤b) (hn:1≤n) :
  (a+b)^n≤2^(n-1)*(a^n+b^n):=by
 let a':ℝ≥0:=⟨a,ha⟩
 let b':ℝ≥0:=⟨b,hb⟩
 have h:=NNReal.rpow_add_le_mul_rpow_add_rpow a' b'
  (p:=(n:ℝ)) (by exact_mod_cast hn)
 exact_mod_cast h
omit [DecidableEq X] in
lemma mV
  {ν f:X→ℝ} {ε:ℝ} {p:ℕ}
  (f9: ∀ x,0≤ν x) (ob: ∑ x:X,ν x=1)
  (Ao: ∀ k:ℕ,0≤ iP ν f k)
  (qu:0<ε) (Ak:ε≤1) (hp:5≤p) (CL:Odd p)
  (iU:ε^p≤aK ν f p) :
  ∃ p':ℕ,0<p'∧Even p'∧p'≤dJ ε p ∧
   (1+ε/2)^p'≤aK ν (f+1) p':=by
 classical
 have xY:p≠0:=Uq (SI (by norm_num) hp)
 have FZ:Even (p-1):=Nat.Odd.sub_odd CL odd_one
 have Eb :
   ε^p≤2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
  calc
   ε^p≤aK ν f p:=iU
   _= ∑ i:X,ν i*((f^(p-1)) i* |f i|):=by
    unfold aK
    apply sum_congr rfl
    intro i _
    congr 1
    change |f i| ^p=f i^(p-1)* |f i|
    rw[←QC (FZ.pow_nonneg (f i)),abs_pow,
     R0 xY]
   _≤ iP ν f p +
     ∑ i:X,ν i*((f^(p-1)) i* |f i|):=
    le_add_of_nonneg_left (Ao p)
   _= ∑ i:X,ν i*((f^(p-1)) i*(f i+ |f i|)):=by
    simp[iP,Tc,sum_add_distrib,R0 xY]
   _= ∑ i:X,ν i*((f^(p-1)) i*(2•(f i)⁺)):=by
    simp[add_abs_eq_two_nsmul_posPart]
   _=2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
    simp[mul_sum]
    ring_nf
 let P:Finset X:=Finset.univ.filter fun i↦0≤f i
 let T:Finset X:=Finset.univ.filter fun i↦3/4*ε≤f i
 have Oe:T⊆P:=by
  intro i hi
  simp only[P,T,mem_filter,mem_univ,TM] at hi ⊢
  exact Sj (by positivity) hi
 have hP :
   (2:ℝ)⁻¹ *ε^p≤ ∑ i∈P,ν i*(f^p) i:=by
  rw[TA (by norm_num:(0:ℝ)<2),sum_filter]
  simpa[P,Pi.posPart_apply,posPart_eq_ite,R0 xY] using Eb
 have Ap :
   ∑ i∈P \ T,ν i*(f^p) i≤(4:ℝ)⁻¹ *ε^p:=by
  calc
   _≤ ∑ i∈P \ T,ν i*(3/4*ε)^p:=by
    apply sum_le_sum
    intro i hi
    have G5:=hi
    simp only[mem_sdiff,P,T,mem_filter,mem_univ,TM,not_le] at G5
    exact iO (Qp G5.1 G5.2.le p) (f9 i)
   _=(3/4)^p*ε^p* ∑ i∈P \ T,ν i:=by
    rw[←sum_mul]
    simp[QL]
    ring
   _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i:=by
    have hpow:(3/4:ℝ)^p≤(4:ℝ)⁻¹:=by
     calc
      (3/4:ℝ)^p≤(3/4:ℝ)^5:=by
       exact SJ (by norm_num) (by norm_num) hp
      _≤(4:ℝ)⁻¹:=by norm_num
    calc
     (3/4)^p*ε^p* ∑ i∈P \ T,ν i ≤
       (4:ℝ)⁻¹ *ε^p* ∑ i∈P \ T,ν i:=
      Qi
       (Qi hpow (QH qu.le p))
       (sum_nonneg fun i _↦f9 i)
     _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i:=
      iO
       (sum_le_univ_sum_of_nonneg fun i↦f9 i)
       (Qn (by norm_num) (QH qu.le p))
   _=(4:ℝ)⁻¹ *ε^p:=by rw[ob,Q3]
 have Aq :
   (4:ℝ)⁻¹ *ε^p≤ ∑ i∈T,ν i*(f^p) i:=by
  calc
   (4:ℝ)⁻¹ *ε^p =
     (2:ℝ)⁻¹ *ε^p-(4:ℝ)⁻¹ *ε^p:=by ring
   _≤(∑ i∈P,ν i*(f^p) i) -
     ∑ i∈P \ T,ν i*(f^p) i:=sub_le_sub hP Ap
   _= ∑ i∈T,ν i*(f^p) i:=by
    rw[sum_sdiff_eq_sub Oe]
    ring
 have G6:0≤ ∑ i∈T,ν i*(f^p) i:=
  (Qn (by norm_num) (QH qu.le p)).trans Aq
 have Of :
   (∑ i∈T,ν i*(f^p) i)^2 ≤
    (∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:=by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul T
  ·intro i _
   exact f9 i
  ·intro i _
   exact Qn (f9 i) ((T2 p).pow_nonneg (f i))
  ·intro i _
   dsimp
   rw[show 2*p=p*2 by omega,QU,QL]
   ring_nf
   exact SF
 have I9 :
   ((4:ℝ)⁻¹ *ε^p)^2 ≤
    (∑ i∈T,ν i)*aK ν f (2*p):=by
  calc
   _≤(∑ i∈T,ν i*(f^p) i)^2:=
    Qp (Qn (by norm_num) (QH qu.le p)) Aq 2
   _≤(∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:= Of
   _≤(∑ i∈T,ν i)*aK ν f (2*p):=by
    apply iO _ (sum_nonneg fun i _↦f9 i)
    unfold aK
    have heq :
      (∑ i∈T,ν i*(f^(2*p)) i) =
       ∑ i∈T,ν i* |f i| ^(2*p):=by
     apply sum_congr rfl
     intro i _
     simp only[Pi.pow_apply]
     rw[(T2 p).pow_abs]
    rw[heq]
    apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
    intro i _ _
    exact Qn (f9 i) (QH (Q8 _) _)
 let q:ℕ:=2*p
 by_cases F0:(2:ℝ)^q≤aK ν (f+1) q
 ·refine ⟨q,by dsimp[q]; omega,T2 p, ?_, ?_⟩
  ·dsimp[q,dJ]
   exact Q4 _ (ix qu)
  ·exact(Qp (by positivity) (by linarith) q).trans F0
 ·have dV:aK ν (f+1) q<(2:ℝ)^q:=QV F0
  have hq:1≤q:=by dsimp[q]; omega
  have Og:aK ν f q≤(2:ℝ)^(2*q):=by
   calc
    aK ν f q ≤
      (2:ℝ)^(q-1)*(aK ν (f+1) q+1):=by
     unfold aK
     calc
      (∑ x:X,ν x* |f x| ^q) ≤
        ∑ x:X,ν x *
         ((2:ℝ)^(q-1)*(|f x+1| ^q+1^q)):=by
       apply sum_le_sum
       intro i _
       apply iO _ (f9 i)
       calc
        |f i| ^q≤(|f i+1| +1)^q:=by
         apply Qp (Q8 _) _ q
         calc
          |f i| = |(f i+1)-1|:=by ring_nf
          _≤ |f i+1| + |(1:ℝ)|:=abs_sub _ _
          _= |f i+1| +1:=by norm_num
        _≤(2:ℝ)^(q-1)*(|f i+1| ^q+1^q):=
         oI (Q8 _) (by norm_num) hq
      _=(2:ℝ)^(q-1) *
        (∑ x:X,ν x* |(f+1) x| ^q+1):=by
       simp only[RM,Rt,one_pow]
       calc
        (∑ x:X,ν x*(2^(q-1)*(|f x+1| ^q+1))) =
          2^(q-1)*(∑ x:X,ν x* |f x+1| ^q) +
           2^(q-1)* ∑ x:X,ν x:=by
         simp_rw[Tc]
         rw[sum_add_distrib]
         congr 1
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _=2^(q-1)*((∑ x:X,ν x* |f x+1| ^q)+1):=by
         rw[ob]
         ring
    _≤(2:ℝ)^(q-1)*((2:ℝ)^q+1):=by
     gcongr
    _≤(2:ℝ)^(q-1)*(2:ℝ)^(q+1):=by
     gcongr
     calc
      (2:ℝ)^q+1≤(2:ℝ)^q+(2:ℝ)^q:=by
       gcongr
       exact RH (by norm_num:(1:ℝ)≤2)
      _=(2:ℝ)^(q+1):=by rw[RB]; ring
    _=(2:ℝ)^(2*q):=by rw[←RL]; congr 1; omega
  have Ja:(ε/8)^(2*p)≤ ∑ i∈T,ν i:=by
   have M6:aK ν f (2*p)≤(2:ℝ)^(4*p):=by
    convert Og using 1; simp[q]; omega
   have M7 :
     ((4:ℝ)⁻¹ *ε^p)^2 ≤
      (∑ i∈T,ν i)*(2:ℝ)^(4*p):=
    I9.trans (iO M6 (sum_nonneg fun i _↦f9 i))
   have si:(16:ℝ)*(2:ℝ)^(4*p)≤(8:ℝ)^(2*p):=by
    have Oh:(16:ℝ)≤4^p:=by
     calc
      (16:ℝ)=4^2:=by norm_num
      _≤4^p:=Se (by norm_num:(1:ℝ)≤4) (by omega)
    rw[show(2:ℝ)^(4*p)=16^p by rw[QU]; norm_num,
     show(8:ℝ)^(2*p)=64^p by rw[QU]; norm_num]
    calc
     (16:ℝ)*16^p≤4^p*16^p:=
      Qi Oh (QH (by norm_num) p)
     _=64^p:=by rw[←QL]; norm_num
   rw[TY]
   apply(QF (RF (by norm_num:(0:ℝ)<8) (2*p))).2
   have pO:=iO M7 (by norm_num:(0:ℝ)≤16)
   calc
    ε^(2*p)=16*((4:ℝ)⁻¹ *ε^p)^2:=by
     rw[show 2*p=p+p by omega,RL,TI]
     ring
    _≤16*((∑ i∈T,ν i)*(2:ℝ)^(4*p)):=pO
    _=(∑ i∈T,ν i)*(16*(2:ℝ)^(4*p)):=by ring
    _≤(∑ i∈T,ν i)*(8:ℝ)^(2*p):=
     iO si (sum_nonneg fun i _↦f9 i)
  let m:ℕ:=cP ε
  have G7:0< m:=ix qu
  have Ht:60/ε^2≤(m:ℝ):=by
   simpa[m] using q0 qu
  have eO :
    1+ε/6≤(1+3*ε/4)/(1+ε/2):=by
   apply(Qs (by positivity:0<1+ε/2)).2
   nlinarith
  have x4 :
    8/ε≤((1+3*ε/4)/(1+ε/2))^m:=by
   calc
    8/ε≤1+(m:ℝ)*(ε/6):=by
     have:=Qi Ht (by positivity:0≤ε/6)
     field_simp at this ⊢
     nlinarith[SY qu]
    _≤(1+ε/6)^m:=UM (by linarith) m
    _≤((1+3*ε/4)/(1+ε/2))^m:=
     Qp (by positivity) eO m
  have CM :
    (1+ε/2)^m≤(ε/8)*(1+3*ε/4)^m:=by
   have Hu:0<(1+ε/2)^m:=RF (by positivity) m
   rw[TY] at x4
   have Jb:=(Qs Hu).1 x4
   calc
    (1+ε/2)^m =
      (ε/8)*((8/ε)*(1+ε/2)^m):=by field_simp
    _≤(ε/8)*(1+3*ε/4)^m:=
     iO Jb (by positivity)
  have Ar :
    (1+ε/2)^(2*p*m) ≤
     (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
   calc
    (1+ε/2)^(2*p*m)=((1+ε/2)^m)^(2*p):=by
     rw[←QU,R8 m (2*p)]
    _≤((ε/8)*(1+3*ε/4)^m)^(2*p):=
     Qp (by positivity) CM (2*p)
    _=(ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
     rw[QL, ←QU,R8 m (2*p)]
  have mx:Even (2*p*m):=by
   simp[SZ]
  refine ⟨2*p*m,by positivity,mx, ?_, ?_⟩
  ·simp[dJ,m]
  ·calc
    (1+ε/2)^(2*p*m) ≤
      (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=Ar
    _≤(∑ i∈T,ν i)*(1+3*ε/4)^(2*p*m):=
     Qi Ja (QH (by positivity) _)
    _= ∑ i∈T,ν i*(1+3*ε/4)^(2*p*m):=by
     rw[←sum_mul]
    _≤ ∑ i∈T,ν i* |(f+1) i| ^(2*p*m):=by
     apply sum_le_sum
     intro i hi
     apply iO _ (f9 i)
     apply Qp (by positivity) _ _
     have G5:3/4*ε≤f i:=by simpa[T] using hi
     have Jc:0≤(f+1) i:=by
      simp only[RM,Rt]
      nlinarith
     rw[QC Jc]
     simp only[RM,Rt]
     nlinarith
    _≤aK ν (f+1) (2*p*m):=by
     unfold aK
     apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
     intro i _ _
     exact Qn (f9 i) (QH (Q8 _) _)
end Moments
section vy
open Fintype MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder ENNReal
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma rC {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ}
  (hf:(al g g)=(↑) ∘ f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ]:=
 xm hf f9 k
end vy
end ay
end
section
open Finset
open scoped BigOperators
namespace ay
namespace an
variable {X:Type*} [Fintype X] [DecidableEq X]
structure cw (ν:X→ℝ):Prop where
 nonneg: ∀ x,0≤ν x
 sum_eq_one: ∑ x,ν x=1
noncomputable def aM (ν f:X→ℝ) (p:ℕ):ℝ:=
 if p=0 then 0 else
  (aK ν f p)^(1/(p:ℝ))
omit [DecidableEq X] in
lemma dG (ν f:X→ℝ) {p:ℕ} (hp:0<p) :
  aM ν f p =
   (aK ν f p)^(1/(p:ℝ)):=by
 simp[aM,hp.ne']
omit [DecidableEq X] in
lemma j3 {ν:X→ℝ} (f9:cw ν)
  (f:X→ℝ) (p:ℕ) :
  0≤aM ν f p:=by
 classical
 unfold aM
 split
 ·exact SF
 ·exact Tn (dx f9.nonneg p) _
omit [DecidableEq X] in
lemma jr {ν f:X→ℝ} (f9:cw ν)
  {p:ℕ} (hp:0<p) :
  aM ν f p^p=aK ν f p:=by
 classical
 rw[dG _ _ hp, ←RN,
  ←S0 (dx f9.nonneg p)]
 have Ec:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
 simp
private lemma xo {x:ℝ} {p q:ℕ} (hp:0<p) :
  (|x| ^p)^((q:ℝ)/(p:ℝ))= |x| ^q:=by
 rw[←RN]
 rw[←S0 (Q8 x)]
 rw[←RN]
 congr 1
 have Ec:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
omit [DecidableEq X] in
lemma gG
  {ν f:X→ℝ} (f9:cw ν)
  {p q:ℕ} (hp:0<p) (hpq:p≤q) :
  aM ν f p≤aM ν f q:=by
 classical
 have hq:0<q:=hp.trans_le hpq
 have Ec:(0:ℝ)<p:=by exact_mod_cast hp
 have Jd:(0:ℝ)<q:=by exact_mod_cast hq
 have M8:(p:ℝ)≤q:=by exact_mod_cast hpq
 have eO:(1:ℝ)≤(q:ℝ)/(p:ℝ):=by
  exact(Qs Ec).2 (by simpa using M8)
 have As:0≤aK ν f p:=
  dx f9.nonneg p
 have M9:0≤aK ν f q:=
  dx f9.nonneg q
 have Hv :
   (aK ν f p)^((q:ℝ)/(p:ℝ)) ≤
    aK ν f q:=by
  have h:=Real.rpow_arith_mean_le_arith_mean_rpow
   (Finset.univ:Finset X) ν (fun x↦ |f x| ^p)
   (fun x _↦f9.nonneg x) (by simpa using f9.sum_eq_one)
   (fun x _↦QH (Q8 _) _) eO
  simpa only[aK,mem_univ,xo hp] using h
 rw[dG _ _ hp,dG _ _ hq]
 have kB :
   0≤(aK ν f p)^((q:ℝ)/(p:ℝ)):=
  Tn As _
 have wJ:=Sf kB Hv
  (RS Us Jd.le)
 calc
  (aK ν f p)^(1/(p:ℝ)) =
    ((aK ν f p)^((q:ℝ)/(p:ℝ))) ^
     (1/(q:ℝ)):=by
   rw[←S0 As]
   congr 1
   field_simp
  _≤(aK ν f q)^(1/(q:ℝ)):=wJ
omit [DecidableEq X] in
lemma lv
  {μ ν f g:X→ℝ} (Je:cw μ) (f9:cw ν)
  {p:ℕ} (hp:0<p)
  (yW:aK μ f p≤2*aK ν g p) :
  aM μ f p≤2*aM ν g p:=by
 classical
 have Ec:(0:ℝ)<p:=by exact_mod_cast hp
 have ha:0≤(1/(p:ℝ)):=by positivity
 have K6:(1/(p:ℝ))≤1:=by
  rw[Q9 Ec]
  exact_mod_cast hp
 have Ed:0≤aK μ f p:=
  dx Je.nonneg p
 have zj:0≤aK ν g p:=
  dx f9.nonneg p
 rw[dG _ _ hp,dG _ _ hp]
 calc
  (aK μ f p)^(1/(p:ℝ)) ≤
    (2*aK ν g p)^(1/(p:ℝ)):=
   Sf Ed yW ha
  _=(2:ℝ)^(1/(p:ℝ)) *
    (aK ν g p)^(1/(p:ℝ)):=by
   rw[Real.mul_rpow (by norm_num:(0:ℝ)≤2) zj]
  _≤2*(aK ν g p)^(1/(p:ℝ)):=by
   apply Qi _ (Tn zj _)
   simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num:(1:ℝ)≤2) K6
def bS (p:ℕ):ℕ:=2*p
lemma sX (p:ℕ):Even (bS p):=
       ⟨p,by simp[bS,R5]⟩
lemma t3 {p:ℕ} (hp:0<p) :
  p≤bS p:=by
 simp only[bS]
 omega
def cF (p:ℕ):ℕ:=
 2*bS p+3
lemma pP (p:ℕ) :
  Odd (cF p):=by
 simp[cF,bS,Nat.odd_iff]
lemma fK {p:ℕ} (hp:0<p) :
  5≤cF p:=by
 simp only[cF,bS]
 omega
lemma je (p:ℕ) :
  bS p≤cF p:=by
 simp only[cF]
 omega
omit [DecidableEq X] in
lemma js
  {ν f:X→ℝ} (f9:cw ν) {p:ℕ} (hp:0<p) :
  aM ν f (bS p) ≤
   aM ν f (cF p):=by
 classical
 apply gG f9
 ·exact QP (by norm_num) hp
 ·exact je p
noncomputable def cz (ε:ℝ) (p:ℕ):ℕ:=
 dJ (ε/2) (cF p)
lemma t4 (ε:ℝ) (p:ℕ) :
  Even (cz ε p):=
       sh _ _
lemma uQ {ε:ℝ} {p:ℕ}
  (hε:0<ε) (hp:0<p) :
  0<cz ε p:=by
 apply sW (p:=cF p)
 ·positivity
 ·have Pw:=fK hp
  omega
lemma pF (ε:ℝ) (p:ℕ) :
  cz ε p =
   (8*p+6)*cP (ε/2):=by
 unfold cz dJ cF
  bS
 ring
lemma po {ε:ℝ} {p:ℕ} (hp:0<p) :
  cz ε p ≤
   14*cP (ε/2)*p:=by
 rw[pF]
 have Cd:8*p+6≤14*p:=by omega
 have h:=QQ (cP (ε/2)) Cd
 simpa[Qo,Qx,Q6] using h
omit [DecidableEq X] in
lemma pQ
  {ν:X→ℝ} (f9:cw ν)
  {f fB:X→ℝ} {η bo:ℝ}
  (Jf:0<η) (Jg:η≤1) (fF:0<bo)
  {p:ℕ} (hp:5≤p) (CL:Odd p)
  (Ao: ∀ k:ℕ,0≤ iP ν f k)
  (iU:η^p≤aK ν f p)
  (c3: ∀ x,fB x=bo*(1+f x)) :
  ∃ r:ℕ,0<r∧Even r∧r≤dJ η p ∧
   (1+η/2)*bo≤aM ν fB r:=by
 classical
 obtain ⟨r,hr,At,yX,tv⟩:=
  mV f9.nonneg f9.sum_eq_one Ao
   Jf Jg hp CL iU
 refine ⟨r,hr,At,yX, ?_⟩
 have Au :
   aK ν fB r =
    bo^r*aK ν (f+1) r:=by
  unfold aK
  rw[Qj]
  apply sum_congr rfl
  intro x _
  rw[c3 x,SU,RT fF,QL]
  simp only[RM,Rt]
  ring_nf
 have Ar :
   ((1+η/2)*bo)^r ≤
    aK ν fB r:=by
  rw[Au,QL]
  simpa[Qx] using
   (Qi tv (QH fF.le r))
 rw[dG _ _ hr]
 have dc:0≤(1+η/2)*bo:=by positivity
 have wJ:=Sf (QH dc r) Ar
  (by positivity:0≤(r:ℝ)⁻¹)
 rw[Sc dc hr.ne'] at wJ
 simpa[R6] using wJ
omit [DecidableEq X] in
lemma nP
  {μ ν:X→ℝ} (Je:cw μ) (f9:cw ν)
  {balanced gH fB:X→ℝ}
  {ε bo:ℝ} (hε:0<ε) (fF:0<bo)
  {p:ℕ} (hp:0<p)
  (lh :
   aM μ balanced (bS p) ≤
    2*aM ν gH (bS p))
  (CN :
   ε*bo/2<aM ν gH (bS p) →
    ∃ r:ℕ,0<r∧r≤cz ε p ∧
     (1+ε/8)*bo≤aM ν fB r)
  (qv :
   aM ν fB (cz ε p) <
    (1+ε/8)*bo) :
  aM μ balanced p≤ε*bo:=by
 classical
 have Hw:0<ε*bo:=QM hε fF
 by_contra hbound
 have K7:ε*bo<aM μ balanced p:=QV hbound
 have xp :
   aM μ balanced p ≤
    aM μ balanced (bS p):=
  gG Je hp (t3 hp)
 have CO :
   ε*bo/2<aM ν gH (bS p):=by
  nlinarith[Hw,K7.trans_le xp,lh,
   j3 f9 gH (bS p)]
 obtain ⟨r,hr,Jh,tv⟩:=CN CO
 have xq :
   aM ν fB r ≤
    aM ν fB (cz ε p):=
  gG f9 hr Jh
 exact(Rd (tv.trans xq)) qv
end an
end ay
end
section
open Finset Function
namespace ay
section Av
variable {α:Type*} [AddCommMonoid α] [DecidableEq α]
def dL (A:Finset α):ℕ:=
 #(((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)
variable [IsCancelAdd α]
lemma uR {A:Finset α} (hA:ThreeAPFree (A:Set α)) :
  dL A= #A:=by
 classical
 let D:Finset ((α × α) × α):=A.image fun a↦((a,a),a)
 have eI :
   (((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)=D:=by
  ext x
  rcases x with ⟨⟨a,b⟩,c⟩
  simp only[mem_filter,mem_product,D,mem_image]
  constructor
  ·rintro ⟨⟨⟨ha,hb⟩,hc⟩,pK⟩
   have hab:a=b:=hA ha hb hc pK
   have Oi:b=c:=hA.eq_right ha hb hc pK
   exact ⟨b,hb,by simp[hab,Oi]⟩
  ·rintro ⟨d,hd,CP⟩
   have PZ:d=a:=QA (fun x↦x.1.1) CP
   have Oj:d=b:=QA (fun x↦x.1.2) CP
   have P1:d=c:=QA (fun x↦x.2) CP
   subst a
   subst b
   subst c
   simp[hd]
 change #(((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)= #A
 rw[eI]
 change #(A.image fun a↦((a,a),a))= #A
 rw[card_image_of_injective]
 intro a b hab
 exact QA (fun x↦x.1.1) hab
end Av
section x5
abbrev aD (N:ℕ):ℕ:=2*N+1
abbrev cn (N:ℕ) (a:ℕ):ZMod (aD N):=a
lemma gA (N:ℕ) :
  Set.InjOn (cn N) (Set.Iic N):=by
 intro a ha b hb hab
 change a≤N at ha
 change b≤N at hb
 have K8:a<aD N:=by
  change a<2*N+1
  omega
 have K9:b<aD N:=by
  change b<2*N+1
  omega
 have yY:=
  (TB a b (aD N)).mp hab
 rwa[Sl K8,Sl K9] at yY
lemma iV {N a b c d:ℕ}
  (ha:a≤N) (hb:b≤N) (hc:c≤N) (hd:d≤N) :
  cn N a+cn N c =
    cn N b+cn N d ↔
   a+c=b+d:=by
 constructor
 ·intro h
  have hcast:((a+c:ℕ):ZMod (aD N)) =
    ((b+d:ℕ):ZMod (aD N)):=by
   simpa only[T3] using h
  have Ji:a+c<aD N:=by
   change a+c<2*N+1
   omega
  have Jj:b+d<aD N:=by
   change b+d<2*N+1
   omega
  have yY:=
   (TB (a+c) (b+d) (aD N)).mp hcast
  rwa[Sl Ji,Sl Jj] at yY
 ·intro h
  simpa only[T3] using
   QA (fun n:ℕ↦(n:ZMod (aD N))) h
def cZ (N:ℕ) (A:Finset ℕ):Finset (ZMod (aD N)):=
 A.image (cn N)
@[simp] lemma fi {N:ℕ} {A:Finset ℕ} {x:ZMod (aD N)} :
  x∈cZ N A↔ ∃ a∈A,cn N a=x:=by
 simp[cZ]
lemma vR {N:ℕ} {A:Finset ℕ}
  (hA: ∀ a∈A,a≤N): #(cZ N A)= #A:=by
 rw[cZ,card_image_iff]
 exact fun a ha b hb h↦gA N (hA a ha) (hA b hb) h
lemma q1 {N:ℕ} {A:Finset ℕ}
  (hA: ∀ a∈A,a≤N) :
  dL (cZ N A)=dL A:=by
 classical
 let f:((ℕ × ℕ) × ℕ)→((ZMod (aD N) × ZMod (aD N)) ×
   ZMod (aD N)):=fun x ↦
  ((cn N x.1.1,cn N x.1.2),cn N x.2)
 let T:Finset ((ℕ × ℕ) × ℕ):=
  ((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2
 let U:Finset ((ZMod (aD N) × ZMod (aD N)) ×
   ZMod (aD N)):=
  (((cZ N A ×ˢ cZ N A) ×ˢ cZ N A).filter fun x ↦
   x.1.1+x.2=x.1.2+x.1.2)
 have Ol:U=T.image f:=by
  ext x
  rcases x with ⟨⟨x,y⟩,z⟩
  constructor
  ·intro F1
   have La :
     x∈cZ N A∧y∈cZ N A∧z∈cZ N A ∧
      x+z=y+y:=by
    simpa[U,Tm] using F1
   rcases La with ⟨hx,hy,hz,uS⟩
   obtain ⟨a,ha,rfl⟩:=fi.mp hx
   obtain ⟨b,hb,rfl⟩:=fi.mp hy
   obtain ⟨c,hc,rfl⟩:=fi.mp hz
   refine mem_image.mpr ⟨((a,b),c), ?_,rfl⟩
   have pK:a+c=b+b:=
    (iV (hA a ha) (hA b hb) (hA c hc) (hA b hb)).1 uS
   simp[T,ha,hb,hc,pK]
  ·intro F1
   obtain ⟨⟨⟨a,b⟩,c⟩,xr,Hx⟩:=mem_image.mp F1
   have CQ:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
    simpa[T,Tm] using xr
   rcases CQ with ⟨ha,hb,hc,pK⟩
   have hx:cn N a∈cZ N A:=
    fi.mpr ⟨a,ha,rfl⟩
   have hy:cn N b∈cZ N A:=
    fi.mpr ⟨b,hb,rfl⟩
   have hz:cn N c∈cZ N A:=
    fi.mpr ⟨c,hc,rfl⟩
   have uS:cn N a+cn N c =
     cn N b+cn N b:=
    (iV (hA a ha) (hA b hb) (hA c hc) (hA b hb)).2 pK
   rw[←Hx]
   simp[U,f,hx,hy,hz,uS]
 have hf:Set.InjOn f T:=by
  rintro ⟨⟨a,b⟩,c⟩ pK ⟨⟨a',b'⟩,c'⟩ CQ heq
  have xr:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
   simpa[T,Tm] using pK
  have Ee:a'∈A∧b'∈A∧c'∈A∧a'+c'=b'+b':=by
   simpa[T,Tm] using CQ
  rcases xr with ⟨ha,hb,hc, -⟩
  rcases Ee with ⟨mS,Om,hc', -⟩
  have On:a=a':=gA N (hA a ha) (hA a' mS)<|
   QA (fun x↦x.1.1) heq
  have Oo:b=b':=gA N (hA b hb) (hA b' Om)<|
   QA (fun x↦x.1.2) heq
  have Oq:c=c':=gA N (hA c hc) (hA c' hc')<|
   QA (fun x↦x.2) heq
  simp[On,Oo,Oq]
 change #U= #T
 rw[Ol,card_image_of_injOn hf]
end x5
end ay
end
section
open Finset Function
open scoped BigOperators translate
namespace ay
noncomputable section
section BE
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def af (A:Finset G) (x:G):ℝ:=
 if x∈A then (#A:ℝ)⁻¹ else 0
def ao (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (x-y)
def aZ (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (y-x)
def qj (f g:G→ℝ):ℝ:=
 ∑ x:G,f x*g x
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma dj {A:Finset G} {x:G} (hx:x∈A) :
  af A x=(#A:ℝ)⁻¹:=by
 simp[af,hx]
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma dO {A:Finset G} {x:G} (hx:x∉A) :
  af A x=0:=by
 simp[af,hx]
omit [AddCommGroup G] [Fintype G] in
lemma bO (A:Finset G) (x:G) :
  0≤af A x:=by
 unfold af
 split_ifs
 ·exact inv_nonneg.mpr (Q5 _)
 ·exact SF
omit [AddCommGroup G] [Fintype G] in
lemma qw {A:Finset G} (hA:A.Nonempty) (x:G) :
  0<af A x↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp only[hx,iff_true]
  exact inv_pos.mpr (Nat.cast_pos.mpr hA.card_pos)
 ·simp[hx]
omit [AddCommGroup G] [Fintype G] in
lemma d6 {A:Finset G} (hA:A.Nonempty) (x:G) :
  af A x≠0↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp[hx,hA.card_ne_zero]
 ·simp[hx]
omit [AddCommGroup G] in
lemma cf {A:Finset G} (hA:A.Nonempty) :
  ∑ x:G,af A x=1:=by
 change(∑ x∈(univ:Finset G),if x∈A then (#A:ℝ)⁻¹ else 0)=1
 rw[←QE]
 have eI:univ.filter (fun x:G↦x∈A)=A:=by ext; simp
 rw[eI]
 simp[hA.card_ne_zero]
omit [DecidableEq G] in
lemma fa {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤ao f g z:=
       sum_nonneg fun x _↦Qn (hf x) (hg (z-x))
omit [DecidableEq G] in
lemma gB {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤aZ f g z:=
       sum_nonneg fun x _↦Qn (hf x) (hg (x-z))
lemma kC (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (#(A.filter fun y↦x-y∈B):ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹:=by
 have eI:(univ.filter fun y:G↦x-y∈B)∩A =
   A.filter fun y↦x-y∈B:=by
  ext y
  simp[and_comm]
 simp[ao,af, ←QE,
  Qo,Q6,eI]
omit [Fintype G] in
lemma lT (A B:Finset G) (x:G) :
  #(A.filter fun y↦x-y∈B)=A.addConvolution B x:=by
 unfold Finset.addConvolution
 refine Finset.card_nbij' (fun y↦(y,x-y)) (fun ab↦ab.1) ?_ ?_ ?_ ?_
 ·intro y hy
  change y∈A.filter (fun y↦x-y∈B) at hy
  change(y,x-y)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x)
  rw[mem_filter] at hy ⊢
  exact ⟨mem_product.mpr hy,by simp⟩
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x) at hab
  change a∈A.filter (fun y↦x-y∈B)
  simp only[mem_filter,mem_product] at hab ⊢
  rcases hab with ⟨⟨ha,hb⟩,hsum⟩
  refine ⟨ha, ?_⟩
  have Ef:x-a=b:=by
   rw[←hsum]
   simp
  simpa[Ef] using hb
 ·intro y _
  rfl
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x) at hab
  simp only[mem_filter,mem_product] at hab
  rcases hab with ⟨-,hsum⟩
  have Ef:x-a=b:=by
   rw[←hsum]
   simp
  simp[Ef]
lemma iy (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (A.addConvolution B x:ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹:=by
 rw[kC,lT]
end BE
section Algebra
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
omit [DecidableEq G] in
lemma fG (f g:G→ℝ) :
  ao f g=ao g f:=by
 funext x
 rw[ao,ao]
 refine Qk (Equiv.subLeft x) _ _ fun y↦ ?_
 simp[Qx]
omit [DecidableEq G] in
lemma iz (f g:G→ℝ) :
  ∑ x:G,ao f g x=(∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[ao,Qt]
 rw[QD]
 apply Io rfl
 intro y _
 rw[←Qj]
 congr 1
 exact Qk (Equiv.subRight y) _ _ fun x↦by simp
omit [DecidableEq G] in
lemma ho (f g:G→ℝ) :
  ∑ x:G,aZ f g x =
   (∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[aZ,Qt]
 rw[QD]
 apply Io rfl
 intro y _
 rw[←Qj]
 congr 1
 exact Qk (Equiv.subLeft y) _ _ fun x↦by simp
end Algebra
section CR
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def df (A C:Finset G):ℕ:=
 #(((A ×ˢ A) ×ˢ C).filter fun x↦x.1.1+x.1.2=x.2+x.2)
omit [Fintype G] in
lemma kZ (A C:Finset G) :
  df A C= ∑ c∈C,A.addConvolution A (c+c):=by
 unfold df Finset.addConvolution
 simp only[Finset.card_eq_sum_ones,QE,Finset.sum_product]
 calc
  _ =
    ∑ a∈A, ∑ c∈C, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   apply Io rfl
   intro a _
   rw[QD]
  _= ∑ c∈C, ∑ a∈A, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   rw[QD]
lemma jK {A C:Finset G}
  (eU:Injective (fun x:G↦x+x)) :
  qj (ao (af A) (af A))
    (af (C.image fun x↦x+x)) =
   (df A C:ℝ)*(#A:ℝ)⁻¹ ^2*(#C:ℝ)⁻¹:=by
 let D := C.image fun x↦x+x
 have Jk: #D= #C:=by
  dsimp[D]
  exact card_image_of_injective _ eU
 have vS (F:G→ℝ) :
   (∑ z:G,F z*af D z) =
    ∑ z∈D,F z*(#D:ℝ)⁻¹:=by
  change(∑ z:G,F z*(if z∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←QE]
  have eI:univ.filter (fun z:G↦z∈D)=D:=by ext; simp
  rw[eI]
 have yZ: ∑ z∈D,A.addConvolution A z=df A C:=by
  rw[kZ]
  dsimp[D]
  rw[Finset.sum_image]
  intro a _ b _ hab
  exact eU hab
 have F2: ∑ z∈D,(A.addConvolution A z:ℝ)=(df A C:ℝ):=by
  exact_mod_cast yZ
 rw[qj,vS]
 simp_rw[iy]
 rw[Jk]
 have gX (z:G) :
   ((A.addConvolution A z:ℝ)*(#A:ℝ)⁻¹ *(#A:ℝ)⁻¹)*(#C:ℝ)⁻¹ =
    (A.addConvolution A z:ℝ) *
     ((#A:ℝ)⁻¹ *(#A:ℝ)⁻¹ *(#C:ℝ)⁻¹):=by ac_rfl
 simp_rw[gX]
 rw[←Qt,F2]
 simp only[TI]
 ac_rfl
omit [Fintype G] in
lemma iA {A A' C:Finset G} (t:G)
  (hA: ∀ x∈A',x-t∈A) (hC: ∀ x∈C,x-t∈A) :
  df A' C≤dL A:=by
 unfold df dL
 let f:((G × G) × G)→((G × G) × G):=fun x ↦
  ((x.1.1-t,x.2-t),x.1.2-t)
 apply Finset.card_le_card_of_injOn f
 ·rintro ⟨⟨a,c⟩,b⟩ pK
  change((a,c),b)∈(((A' ×ˢ A') ×ˢ C).filter fun x ↦
   x.1.1+x.1.2=x.2+x.2) at pK
  change((a-t,b-t),c-t)∈(((A ×ˢ A) ×ˢ A).filter fun x ↦
   x.1.1+x.2=x.1.2+x.1.2)
  simp only[mem_filter,mem_product] at pK ⊢
  rcases pK with ⟨⟨⟨ha,hc⟩,hb⟩,uS⟩
  refine ⟨⟨⟨hA a ha,hC b hb⟩,hA c hc⟩, ?_⟩
  calc
   _ =(a+c)-(t+t):=by
    simp only[Qy,neg_add_rev]
    ac_rfl
   _=(b+b)-(t+t):=QA (fun x↦x-(t+t)) uS
   _=(b-t)+(b-t):=by
    simp only[Qy,neg_add_rev]
    ac_rfl
 ·rintro ⟨⟨a,c⟩,b⟩ _ ⟨⟨a',c'⟩,b'⟩ _ heq
  have Lb := QA (fun x↦x.1.1) heq
  have Lc := QA (fun x↦x.1.2) heq
  have Ld := QA (fun x↦x.2) heq
  have ha:a=a':=calc
   a=(a-t)+t:=(Rs a t).symm
   _=(a'-t)+t:=QA (fun x↦x+t) Lb
   _=a':=Rs a' t
  have hb:b=b':=calc
   b=(b-t)+t:=(Rs b t).symm
   _=(b'-t)+t:=QA (fun x↦x+t) Lc
   _=b':=Rs b' t
  have hc:c=c':=calc
   c=(c-t)+t:=(Rs c t).symm
   _=(c'-t)+t:=QA (fun x↦x+t) Ld
   _=c':=Rs c' t
  simp[ha,hb,hc]
end CR
end
end ay
end
section
open Finset
open scoped BigOperators NNReal symmDiff
namespace ay
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def vT (B:aj G) (a8 eta:ℝ≥0):Prop:=
 0<eta ∧
  ∀ aF:ℝ≥0,aF≤eta →
   (B.ai (a8-aF)).carrier=(B.ai a8).carrier ∧
   (B.ai (a8+aF)).carrier=(B.ai a8).carrier
def pG (B:aj G) (a8 eta:ℝ≥0):Prop:=
 0<eta∧eta≤a8 ∧
  (B.ai (a8+eta)).carrier.card ≤
   2*(B.ai (a8-eta)).carrier.card
def a1 (B:aj G):Prop:=
 let d:ℕ:=max B.rank 1
 ∀ aF:ℝ≥0,
  aF≤1/(100*(d:ℝ≥0)) →
   (1-100*(d:ℝ)*(aF:ℝ))*(B.carrier.card:ℝ) ≤
     ((B.ai (1-aF)).carrier.card:ℝ) ∧
   ((B.ai (1+aF)).carrier.card:ℝ) ≤
     (1+100*(d:ℝ)*(aF:ℝ))*(B.carrier.card:ℝ)
omit [DecidableEq G] in
lemma sj (B:aj G) (a8:ℝ≥0) :
  (B.ai a8).a1 ↔
   let d := max B.rank 1
   ∀ aF:ℝ≥0,
    aF≤1/(100*(d:ℝ≥0)) →
     (1-100*(d:ℝ)*(aF:ℝ)) *
        ((B.ai a8).carrier.card:ℝ) ≤
       ((B.ai ((1-aF)*a8)).carrier.card:ℝ) ∧
     ((B.ai ((1+aF)*a8)).carrier.card:ℝ) ≤
       (1+100*(d:ℝ)*(aF:ℝ)) *
        ((B.ai a8).carrier.card:ℝ):=by
 simp[a1,Qx]
noncomputable def fp (A:Finset G) (t:G):Finset G:=
 A.map (Equiv.addRight t).toEmbedding
omit [DecidableEq G] [Fintype G] in
@[simp] lemma lx {A:Finset G} {t x:G} :
  x∈fp A t↔x-t∈A:=by
 simp[fp,Qy]
lemma k0
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).carrier) :
  (fp (B.ai a8).carrier t) ∆ (B.ai a8).carrier ⊆
   (B.ai (a8+eta)).carrier \ (B.ai (a8-eta)).carrier:=by
 intro x hx
 rw[UF] at hx
 rw[Finset.mem_sdiff]
 constructor
 ·rcases hx with hx | hx
  ·rw[lx] at hx
   have Aw:=e8 hx.1 ht
   simpa using Aw
  ·exact b5 (Ss (by positivity)) hx.1
 ·intro oJ
  have zN :=
         b5 (T4) oJ
  have Jl:x-t∈(B.ai a8).carrier:=by
   have eY := ec.mpr ht
   have xt:=e8 oJ eY
   simpa[Qy,tsub_add_cancel_of_le fC] using xt
  have xu:x∈fp (B.ai a8).carrier t:=by
   rwa[lx]
  rcases hx with hx | hx
  ·exact hx.2 zN
  ·exact hx.2 xu
lemma kD
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).carrier) :
  ((fp (B.ai a8).carrier t) ∆
    (B.ai a8).carrier).card ≤
   (B.ai (a8+eta)).carrier.card -
    (B.ai (a8-eta)).carrier.card:=by
 have sm :
   (B.ai (a8-eta)).carrier ⊆
    (B.ai (a8+eta)).carrier:=
  b5 ((T4).trans (Ss (by positivity)))
 calc
  ((fp (B.ai a8).carrier t) ∆
    (B.ai a8).carrier).card ≤
    ((B.ai (a8+eta)).carrier \
     (B.ai (a8-eta)).carrier).card:=
   Qu (k0 fC ht)
  _=(B.ai (a8+eta)).carrier.card -
    (B.ai (a8-eta)).carrier.card:=
   Finset.card_sdiff_of_subset sm
lemma gY
  (A:Finset G) (t:G) :
  ∑ x:G, |af A (x-t)-af A x| =
   (((fp A t) ∆ A).card:ℝ)/(A.card:ℝ):=by
 have gX (x:G) :
   |af A (x-t)-af A x| =
    if x∈(fp A t) ∆ A then (A.card:ℝ)⁻¹ else 0:=by
  by_cases Aw:x-t∈A<;>by_cases hx:x∈A <;>
   simp[af,UF,lx,
    Aw,hx,QC]
 simp_rw[gX]
 rw[←QE]
 simp[Qw]
lemma jf
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).carrier) :
  ∑ x:G,
    |af (B.ai a8).carrier (x-t) -
     af (B.ai a8).carrier x| ≤
   (((B.ai (a8+eta)).carrier.card -
    (B.ai (a8-eta)).carrier.card:ℕ):ℝ) /
     ((B.ai a8).carrier.card:ℝ):=by
 rw[gY]
 rw[Qw,Qw]
 gcongr
 exact_mod_cast kD fC ht
lemma cN
  {B:aj G} (dF:B.a1) {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).carrier) :
  ∑ x:G,
    |af B.carrier (x-t) -
     af B.carrier x| ≤
   200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ):=by
 let d:ℕ:=max B.rank 1
 have hd:0<d:=by simp[d]
 have Ce:aF≤1/(100*(d:ℝ≥0)):=by
  simpa[d] using dy
 have oK:aF≤1:=by
  apply Ce.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have Eg:=
  jf
   (B:=B) (a8:=(1:ℝ≥0)) (eta:=aF) oK ht
 simp only[oG] at Eg
 simp only[a1] at dF
 have jt:=dF aF (by simpa[d] using Ce)
 have sm :
   (B.ai (1-aF)).carrier.card ≤
    (B.ai (1+aF)).carrier.card:=
  Qu
   (b5
    (tsub_le_self.trans (Ss (show 0≤aF by exact bot_le))))
 have BF:(0:ℝ)<B.carrier.card:=by
  exact_mod_cast B.aE.card_pos
 apply Eg.trans
 rw[Nat.cast_sub sm]
 rw[QF BF]
 nlinarith[jt.1,jt.2]
end aj
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
lemma g7
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (ks: ∀ t,0≤ν t)
  (pR: ∀ t,ν t≠0→t∈(B.ai κ).carrier) :
  ∑ x:G,
    |ao (af B.carrier) ν x -
     (∑ t:G,ν t)*af B.carrier x| ≤
   200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=by
 let E:ℝ:=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)
 have gX (x:G) :
   |ao (af B.carrier) ν x -
     (∑ t:G,ν t)*af B.carrier x| ≤
    ∑ t:G,ν t *
     |af B.carrier (x-t)-af B.carrier x|:=by
  rw[fG]
  simp only[ao]
  rw[Qt, ←QJ]
  simp_rw[←UY]
  calc
   _
                                          ≤
     ∑ t:G, |ν t *
      (af B.carrier (x-t)-af B.carrier x)|:=
    abs_sum_le_sum_abs _ _
   _= ∑ t:G,ν t *
     |af B.carrier (x-t)-af B.carrier x|:=by
    apply Io rfl
    intro t _
    rw[SU,QC (ks t)]
 calc
  _

                                 ≤
    ∑ x:G, ∑ t:G,ν t *
     |af B.carrier (x-t)-af B.carrier x|:=by
   exact QI fun x _↦gX x
  _= ∑ t:G,ν t* ∑ x:G,
     |af B.carrier (x-t)-af B.carrier x|:=by
   rw[QD]
   apply Io rfl
   intro t _
   rw[Qj]
  _≤ ∑ t:G,ν t*E:=by
   apply QI
   intro t _
   by_cases ht:ν t=0
   ·simp[ht]
   ·exact iO
     (aj.cN
      dF qx (pR t ht)) (ks t)
  _=(∑ t:G,ν t)*E:=by rw[Qt]
  _=E* ∑ t:G,ν t:=by ring
  _=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=rfl
lemma f4
  {B:aj G} {a8 eta:ℝ≥0}
  (dF:B.pG a8 eta)
  (ν:G→ℝ)
  (ks: ∀ t,0≤ν t)
  (ob: ∑ t:G,ν t=1)
  (pR: ∀ t,ν t≠0→t∈(B.ai eta).carrier)
  (x:G) :
  af (B.ai a8).carrier x ≤
   2*ao
    (af (B.ai (a8+eta)).carrier) ν x:=by
 let Jm:=(B.ai (a8-eta)).carrier
 let K:=(B.ai a8).carrier
 let my:=(B.ai (a8+eta)).carrier
 have oJ:Jm.card≤K.card:=by
  apply Qu
  exact aj.b5 (T4:a8-eta≤a8)
 have ch :=
  dF.2.2.trans (Qr 2 oJ)
 have x6:(0:ℝ)<K.card:=by
  exact_mod_cast(B.ai a8).aE.card_pos
 have Eh:(0:ℝ)< my.card:=by
  exact_mod_cast(B.ai (a8+eta)).aE.card_pos
 have x7 (hx:x∈K) :
   ao (af my) ν x =
    (my.card:ℝ)⁻¹:=by
  rw[fG]
  simp only[ao]
  calc
   _ =
     ∑ t:G,ν t*(my.card:ℝ)⁻¹:=by
    apply Io rfl
    intro t _
    by_cases ht:ν t=0
    ·simp[ht]
    ·have Aw :=
      aj.j2 hx (pR t ht)
     rw[dj Aw]
   _=(∑ t:G,ν t)*(my.card:ℝ)⁻¹:=by
    rw[Qt]
   _=(my.card:ℝ)⁻¹:=by rw[ob,QT]
 by_cases hx:x∈K
 ·rw[show(B.ai a8).carrier=K by rfl,
   dj hx,x7 hx]
  calc
   _ =1/(K.card:ℝ):=by rw[R6]
   _≤2/(my.card:ℝ):=by
    rw[Sy x6 Eh]
    simpa only[QT] using(show(my.card:ℝ)≤2*K.card by
     exact_mod_cast ch)
   _=2*(my.card:ℝ)⁻¹:=by rw[Qw]
 ·rw[show(B.ai a8).carrier=K by rfl,
   dO hx]
  exact Qn (by norm_num)
   (fa
    (bO my) ks x)
lemma gC
  {B:aj G} (dF:B.a1) {κ:ℝ≥0} (Jn:0<κ)
  (qx:κ≤1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (ks: ∀ t,0≤ν t)
  (ob: ∑ t:G,ν t=1)
  (pR: ∀ t,ν t≠0→t∈(B.ai κ).carrier)
  (x:G) :
  af B.carrier x ≤
   2*ao
    (af (B.ai (1+κ)).carrier) ν x:=by
 let d := max B.rank 1
 have hd:0<d:=by simp[d]
 have Jo:κ≤1/(400*(d:ℝ≥0)):=by simpa[d] using qx
 have Ei:κ≤1/(100*(d:ℝ≥0)):=by
  apply Jo.trans
  apply Rb (by positivity) (by positivity)
  exact Qi (by norm_num:(100:ℝ≥0)≤400) (by positivity)
 have Jp:κ≤1:=by
  apply Ei.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have jt:=dF κ (by simpa[d] using Ei)
 have Ax:(100:ℝ)*d*(κ:ℝ)≤1/4:=by
  have NN:(κ:ℝ)≤1/(400*(d:ℝ)):=by
   exact_mod_cast Jo
  have Os:(0:ℝ)<d:=by exact_mod_cast hd
  calc
   _ ≤100*d*(1/(400*(d:ℝ))):=by gcongr
   _=1/4:=by field_simp; ring
 have Ej :
   ((B.ai (1+κ)).carrier.card:ℝ) ≤
    2*((B.ai (1-κ)).carrier.card:ℝ):=by
  nlinarith[jt.1,jt.2,
   show(0:ℝ)<B.carrier.card by exact_mod_cast B.aE.card_pos]
 have ch :
   (B.ai (1+κ)).carrier.card ≤
    2*(B.ai (1-κ)).carrier.card:=by
  exact_mod_cast Ej
 have Hy:B.pG 1 κ:=⟨Jn,Jp,ch⟩
 simpa only[aj.oG] using
  f4
   Hy ν ks ob pR x
def bs (A:Finset G) (x:G):ℝ:=
 if x∈A then 1 else 0
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma rD {A:Finset G} {x:G} (hx:x∈A) :
  bs A x=1:=by simp[bs,hx]
def cp (A K:Finset G):ℝ:=
 (A.card:ℝ)/K.card
def a9 (A C:Finset G) (x:G):ℝ:=
 ao (bs A) (af C) x
omit [AddCommGroup G] in
lemma jV
  {A K:Finset G} (lO:A⊆K) (_hK:K.Nonempty) :
  ∑ x:G,bs A x*af K x =
   cp A K:=by
 have hsum :
   ∑ x∈A,bs A x*af K x =
    ∑ x:G,bs A x*af K x:=by
  apply Ro (S7 A)
  intro x _ Ek
  simp[bs,Ek]
 rw[←hsum]
 calc
  ∑ x∈A,bs A x*af K x =
    ∑ _x∈A,(K.card:ℝ)⁻¹:=by
   apply Io rfl
   intro x hx
   rw[rD hx,
    dj (lO hx),QT]
  _=cp A K:=by
   simp[cp,Qw]
lemma dP
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {A C:Finset G} (lO:A⊆B.carrier) (hC:C.Nonempty)
  (fN:C⊆(B.ai κ).carrier) :
  |(∑ x:G,af B.carrier x*a9 A C x) -
    cp A B.carrier| ≤
   200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
 let ν:G→ℝ:=fun t↦af C (-t)
 have ks: ∀ t,0≤ν t:=fun t↦bO C (-t)
 have ob: ∑ t:G,ν t=1:=by
  calc
   _ = ∑ t:G,af C t:=
          Qk (Equiv.neg G) _ _ (fun _↦rfl)
   _=1:=cf hC
 have pR: ∀ t,ν t≠0→t∈(B.ai κ).carrier:=by
  intro t ht
  have eY: -t∈C:=(d6 hC (-t)).mp ht
  exact aj.ec.mp (fN eY)
 have x7 :
   ∑ y:G,
     |ao (af B.carrier) ν y -
      af B.carrier y| ≤
    200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
  simpa[ob] using
   g7
    dF qx ν ks pR
 have Ay :
   ∑ x:G,af B.carrier x*a9 A C x =
    ∑ y:G,bs A y *
     ao (af B.carrier) ν y:=by
  simp only[a9,ao,Qj]
  rw[QD]
  apply Io rfl
  intro y _
  apply Io rfl
  intro x _
  dsimp[ν]
  rw[neg_sub]
  ring
 have dc  :=

  jV lO B.aE
 rw[Ay, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  _

                      ≤
    ∑ y:G, |bs A y *
     (ao (af B.carrier) ν y -
      af B.carrier y)|:=abs_sum_le_sum_abs _ _
  _≤ ∑ y:G,
    |ao (af B.carrier) ν y -
     af B.carrier y|:=by
   apply QI
   intro y _
   by_cases hy:y∈A<;>simp[bs,hy]
  _≤200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=x7
lemma kk
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {A pS q2:Finset G}
  (hA:A.Nonempty) (lO:A⊆B.carrier)
  (Lf:pS.Nonempty) (Lg:q2.Nonempty)
  (CS:pS⊆(B.ai κ).carrier)
  (CT:q2⊆(B.ai κ).carrier)
  {ε:ℝ} (_hε:0<ε)
  (dV :
   400*((max B.rank 1:ℕ):ℝ)*(κ:ℝ) ≤
    ε*cp A B.carrier/4) :
  (∃ x∈B.carrier,
    (1-ε)*cp A B.carrier≤a9 A pS x ∧
    (1-ε)*cp A B.carrier≤a9 A q2 x) ∨
   (∃ x:G,
    (1+ε/2)*cp A B.carrier≤a9 A pS x) ∨
   (∃ x:G,
    (1+ε/2)*cp A B.carrier≤a9 A q2 x):=by
 let K:=B.carrier
 let α := cp A K
 let E:ℝ:=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)
 let y0 :=  ∑ x:G,af K x*a9 A pS x
 let y1 :=  ∑ x:G,af K x*a9 A q2 x
 have hK := B.aE
 have P2:0<α:=by
  dsimp[α,K,cp]
  exact Rn (by exact_mod_cast hA.card_pos) (by exact_mod_cast hK.card_pos)
 have Hz: |y0-α| ≤E:=by
  simpa[y0,α,E,K] using
   dP
    dF qx lO Lf CS
 have HA: |y1-α| ≤E:=by
  simpa[y1,α,E,K] using
   dP
    dF qx lO Lg CT
 have z1:α-E≤y0:=by
  have:=(abs_le.mp Hz).1
  linarith
 have Px:α-E≤y1:=by
  have:=(abs_le.mp HA).1
  linarith
 have NO:2*E≤ε*α/4:=by
  calc
   _ =400*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
    dsimp[E]
    ring
   _≤ε*cp A B.carrier/4:=dV
   _=ε*α/4:=by rfl
 by_cases rE :
   ∃ x∈K,
    (1-ε)*α≤a9 A pS x ∧
    (1-ε)*α≤a9 A q2 x
 ·exact Or.inl rE
 by_cases Cf: ∃ x:G,(1+ε/2)*α≤a9 A pS x
 ·exact Or.inr (Or.inl Cf)
 by_cases Cg: ∃ x:G,(1+ε/2)*α≤a9 A q2 x
 ·exact Or.inr (Or.inr Cg)
 exfalso
 let T:ℝ:=2*α-ε*α/2
 have gX: ∀ x∈K,
   a9 A pS x+a9 A q2 x<T:=by
  intro x hx
  have Py :=
   QV (fun h↦Cf ⟨x,h⟩)
  have Pz :=
   QV (fun h↦Cg ⟨x,h⟩)
  have Ap :
    a9 A pS x<(1-ε)*α ∨
     a9 A q2 x<(1-ε)*α:=by
   by_cases h₁:(1-ε)*α≤a9 A pS x
   ·right
    exact QV (fun h₂↦rE ⟨x,hx,h₁,h₂⟩)
   ·left
    exact QV h₁
  rcases Ap with NQ | NR
  ·dsimp[T]
   nlinarith
  ·dsimp[T]
   nlinarith
 have qy :
   ∑ x:G,af K x *
     (a9 A pS x+a9 A q2 x) <
    ∑ x:G,af K x*T:=by
  apply Finset.sum_lt_sum
  ·intro x _
   by_cases hx:x∈K
   ·exact iO (gX x hx).le
     (bO K x)
   ·simp[dO hx]
  ·refine ⟨0,Sz 0, ?_⟩
   have hz := B.se
   exact T6 (gX 0 hz)
    ((qw hK 0).2 hz)
 have CV:y0+y1<T:=by
  calc
   _ = ∑ x:G,af K x *
     (a9 A pS x+a9 A q2 x):=by
    dsimp[y0,y1]
    rw[←T7]
    apply Io rfl
    intro x _
    ring
   _< ∑ x:G,af K x*T:=qy
   _=(∑ x:G,af K x)*T:=by rw[Qt]
   _=T:=by rw[cf hK,QT]
 dsimp[T] at CV
 nlinarith
end
end ay
end
section
open Finset Function Real
open Complex (re)
open scoped BigOperators ComplexConjugate
namespace ay
namespace c5
variable {G:Type*} [Fintype G] [AddCommGroup G]
noncomputable def c6 (A:Finset G) (psi:AddChar G ℂ):ℂ:=
 ∑ x∈A,psi x
noncomputable def cj (A:Finset G) (eta:ℝ):Finset (AddChar G ℂ):=
 Finset.univ.filter fun psi↦eta*A.card≤ ‖c6 A psi‖
@[simp] lemma gm {A:Finset G} {eta:ℝ} {psi:AddChar G ℂ} :
  psi∈cj A eta↔eta*A.card≤ ‖c6 A psi‖:=by
 simp[cj]
end c5
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def dd (f:G→ℝ):ℕ→G→ℝ
 | 0=>af {0}
 | n+1=>ao (dd f n) f
@[simp] lemma Ch (f:G→ℝ) :
  dd f 0=af {0}:=rfl
@[simp] lemma j4 (f:G→ℝ) (n:ℕ) :
  dd f (n+1) =
   ao (dd f n) f:=rfl
lemma sY {f:G→ℝ} (hf: ∀ x,0≤f x) :
  ∀ n x,0≤dd f n x:=by
 intro n
 induction n with
 | zero =>
   exact bO {0}
 | succ n Az =>
   exact fa Az hf
lemma oL {f:G→ℝ} (hf: ∑ x:G,f x=1) :
  ∀ n, ∑ x:G,dd f n x=1:=by
 intro n
 induction n with
 | zero =>
   exact cf (singleton_nonempty 0)
 | succ n Az =>
   rw[j4,iz,Az,hf,QT]
lemma jL
  (B:aj G) (σ:ℝ≥0) :
  ∀ n x,dd (af (B.ai σ).carrier) n x≠0 →
   x∈(B.ai ((n:ℝ≥0)*σ)).carrier:=by
 intro n
 induction n with
 | zero =>
   intro x hx
   have P3:x=0:=by
    simpa using
     (d6 (singleton_nonempty 0) x).mp hx
   subst x
   simp
 | succ n Az =>
   intro x hx
   rw[j4,ao] at hx
   obtain ⟨y, -,hy⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
   have Lh:dd (af (B.ai σ).carrier) n y≠0:=
    (mul_ne_zero_iff.mp hy).1
   have HB:af (B.ai σ).carrier (x-y)≠0:=
    (mul_ne_zero_iff.mp hy).2
   have Jq:=Az y Lh
   have F3:x-y∈(B.ai σ).carrier:=
    (d6
     (B.ai σ).aE (x-y)).mp HB
   have xt:=aj.e8 Jq F3
   have Li:y+(x-y)=x:=by simp
   rw[Li] at xt
   simpa[T3,Nat.cast_one,US] using xt
def cG (w:G→ℝ) (ψ:AddChar G ℂ):ℂ:=
 ∑ x:G,(w x:ℂ)*ψ x
lemma jU (A:Finset G) (ψ:AddChar G ℂ) :
  cG (af A) ψ =
   ((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
 calc
  _ =
    ∑ x∈A,((A.card:ℝ)⁻¹ :ℂ)*ψ x:=by
   rw[cG, ←Ro (s₁:=A) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[af,hx]
   ·simp
   ·intro x MH Ek
    simp[af,Ek]
  _=((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
   rw[c5.c6,Qj]
lemma fy
  (C:aj G) (ψ:AddChar G ℂ)
  (Jr:ψ∉c5.cj C.carrier (1/2)) :
  ‖cG (af C.carrier) ψ‖ <1/2:=by
 have ch:(0:ℝ)<C.carrier.card:=by
  exact_mod_cast C.aE.card_pos
 have El :
   ‖c5.c6 C.carrier ψ‖ <(1/2:ℝ)*C.carrier.card:=by
  apply QV
  intro h
  exact Jr (c5.gm.mpr h)
 calc
  _ =
    (C.carrier.card:ℝ)⁻¹ * ‖c5.c6 C.carrier ψ‖:=by
   rw[jU,QO]
   simp[Up]
  _<(C.carrier.card:ℝ)⁻¹ *
    ((1/2:ℝ)*C.carrier.card):=
   T6 El (inv_pos.mpr ch)
  _=1/2:=by field_simp
omit [DecidableEq G] in
lemma jb (f g:G→ℝ) (ψ:AddChar G ℂ) :
  cG (ao f g) ψ=cG f ψ*cG g ψ:=by
 unfold cG ao
 push_cast
 calc
  _ =
    ∑ x:G, ∑ y:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x:=by
   apply Io rfl
   intro x hx
   rw[Qt]
  _= ∑ y:G, ∑ x:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x:=
   QD
  _ =
    ∑ y:G,((f y:ℂ)*ψ y) *
     ∑ z:G,(g z:ℂ)*ψ z:=by
   apply Io rfl
   intro y hy
   rw[Qj]
   refine Qk (Equiv.subRight y) _ _ fun z↦ ?_
   have Jr:ψ z=ψ y*ψ (z-y):=by
    calc
     _ =ψ (y+(z-y)):=QA ψ (by simp)
     _=ψ y*ψ (z-y):=St ψ y (z-y)
   simp only[Ut]
   rw[Jr]
   ring
  _=(∑ y:G,(f y:ℂ)*ψ y) *
    ∑ z:G,(g z:ℂ)*ψ z:=by
   simpa using
    (Qt (univ:Finset G) (fun y↦(f y:ℂ)*ψ y)
     (∑ z:G,(g z:ℂ)*ψ z)).symm
lemma q3 (f:G→ℝ) (ψ:AddChar G ℂ) :
  ∀ n,cG (dd f n) ψ=cG f ψ^n:=by
 intro n
 induction n with
 | zero =>
   unfold cG
   rw[Fintype.sum_eq_single 0]
   ·simp[af]
   ·intro y hy
    simp[af,hy]
 | succ n Az =>
   rw[j4,jb,Az,RB]
omit [DecidableEq G] in
lemma t5 {w:G→ℝ} (hw: ∀ x,0≤w x)
  (ψ:AddChar G ℂ) :
  ‖cG w ψ‖ ≤ ∑ x:G,w x:=by
 unfold cG
 calc
  _ ≤
    ∑ x:G, ‖(w x:ℂ)*ψ x‖:=Rq _ _
  _= ∑ x:G,w x:=by
   apply Io rfl
   intro x hx
   simp[hw x]
def ed (B:aj G) (σ:ℝ≥0) (n:ℕ):G→ℝ:=
 ao
  (af (B.ai (1+(n:ℝ≥0)*σ)).carrier)
  (dd (af (B.ai σ).carrier) n)
lemma qz (B:aj G) (σ:ℝ≥0) (n:ℕ) (x:G) :
  0≤ed B σ n x:=
       fa
  (bO _)
  (sY (bO _) n) x
lemma sn (B:aj G) (σ:ℝ≥0) (n:ℕ) :
  ∑ x:G,ed B σ n x=1:=by
 rw[ed,iz,
  cf (B.ai (1+(n:ℝ≥0)*σ)).aE,
  oL
   (cf (B.ai σ).aE),QT]
lemma nh
  (B:aj G) (σ:ℝ≥0) (n:ℕ) {x:G} (hx:x∈B.carrier) :
  ed B σ n x =
   (((B.ai (1+(n:ℝ≥0)*σ)).carrier.card:ℝ)⁻¹):=by
 rw[ed,fG]
 simp only[ao]
 calc
  _
                                           =
    ∑ t:G,dd (af (B.ai σ).carrier) n t *
     (((B.ai (1+(n:ℝ≥0)*σ)).carrier.card:ℝ)⁻¹):=by
   apply Io rfl
   intro t ht
   by_cases Js :
     dd (af (B.ai σ).carrier) n t=0
   ·simp[Js]
   ·have Ot :=
     jL B σ n t Js
    have Aw :=

           aj.j2
      (B:=B) (s:=1) (t:=(n:ℝ≥0)*σ)
      (by simpa using hx) Ot
    rw[dj Aw]
  _=(∑ t:G,
     dd (af (B.ai σ).carrier) n t) *
    (((B.ai (1+(n:ℝ≥0)*σ)).carrier.card:ℝ)⁻¹):=by
   rw[Qt]
  _=(((B.ai (1+(n:ℝ≥0)*σ)).carrier.card:ℝ)⁻¹):=by
   rw[oL
    (cf (B.ai σ).aE)]
   simp
omit [DecidableEq G] in
lemma oM
  {B:aj G} (dF:B.a1) {σ:ℝ≥0} (n:ℕ)
  (dV:(n:ℝ≥0)*σ ≤
   1/(100*(max B.rank 1:ℕ):ℝ≥0)) :
  (B.ai (1+(n:ℝ≥0)*σ)).carrier.card ≤
   2*B.carrier.card:=by
 let κ:ℝ≥0:=(n:ℝ≥0)*σ
 let d := max B.rank 1
 have jt:=dF κ (by simpa[κ,d] using dV)
 have oc:(1+100*(d:ℝ)*(κ:ℝ))≤2:=by
  have NS:(κ:ℝ)≤1/(100*(d:ℝ)):=by
   exact_mod_cast(show κ≤1/(100*(d:ℝ≥0)) by
    simpa[κ,d] using dV)
  have hd:(0:ℝ)<d:=by exact_mod_cast(show 0<d by simp[d])
  calc
   _ ≤
     1+100*(d:ℝ)*(1/(100*(d:ℝ))):=by gcongr
   _=2:=by field_simp; ring
 have Jt :
   ((B.ai (1+κ)).carrier.card:ℝ) ≤
    2*(B.carrier.card:ℝ):=by
  calc
   _ ≤
     (1+100*(d:ℝ)*(κ:ℝ))*(B.carrier.card:ℝ):=by
    simpa[κ,d] using jt.2
   _≤2*(B.carrier.card:ℝ):=by gcongr
 exact_mod_cast Jt
lemma ly
  (B:aj G) (σ:ℝ≥0) (n:ℕ) (ψ:AddChar G ℂ) :
  ‖cG (ed B σ n) ψ‖ ≤
   ‖cG (af (B.ai σ).carrier) ψ‖ ^n:=by
 rw[ed,jb,
  q3,QO,norm_pow]
 have ju :
   ‖cG (af
    (B.ai (1+(n:ℝ≥0)*σ)).carrier) ψ‖ ≤1:=by
  simpa[cf
   (B.ai (1+(n:ℝ≥0)*σ)).aE] using
   t5
    (w:=af
     (B.ai (1+(n:ℝ≥0)*σ)).carrier)
    (bO _) ψ
 exact RQ (by positivity) ju
end
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def cx (z:AddCircle (1:ℝ)):ℝ:=
 (QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2) z).1
lemma k1 (z:AddCircle (1:ℝ)) :
  cx z∈Set.Ico (-1/2:ℝ) (1/2):=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 change-1/2≤cx z∧cx z<1/2
 constructor
 ·exact(e z).2.1
 ·have hz:=(e z).2.2
  norm_num at hz ⊢
  exact hz
@[simp] lemma zO (z:AddCircle (1:ℝ)) :
  ((cx z:ℝ):AddCircle (1:ℝ))=z:=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 have h:=e.symm_apply_apply z
 change((cx z:ℝ):AddCircle (1:ℝ))=z
 simpa only[e,cx,QuotientAddGroup.equivIcoMod_symm_apply] using h
lemma t6 (z:AddCircle (1:ℝ)): |cx z| ≤1/2:=by
 have hz:=k1 z
 rw[Set.mem_Ico] at hz
 rw[abs_le]
 constructor<;>linarith
lemma hH (z:AddCircle (1:ℝ)): ‖z‖ = |cx z|:=by
 calc
  ‖z‖ = ‖((cx z:ℝ):AddCircle (1:ℝ))‖:=by rw[zO]
  _= |cx z|:=
   (Ts (1:ℝ) (by norm_num)).2
    (by simpa using t6 z)
lemma gu (z w:AddCircle (1:ℝ)) :
  ‖z-w‖ ≤ |cx z-cx w|:=by
 have tw :
   (((cx z-cx w:ℝ):ℝ):AddCircle (1:ℝ))=z-w:=by
  simp
 rw[←tw]
 simpa only[QK] using
  (QuotientAddGroup.norm_mk_le_norm
   (S:=AddSubgroup.zmultiples (1:ℝ)) :
    ‖((cx z-cx w:ℝ):AddCircle (1:ℝ))‖ ≤
     ‖cx z-cx w‖)
def uT (w r:ℝ):Fin 4:=
 if r< -(w/2) then 0
 else if r<0 then 1
 else if r<w/2 then 2
 else 3
lemma oN {w r s:ℝ}
  (_hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (lP:uT w r=uT w s) :
  |r-s| ≤w/2:=by
 rw[abs_le] at hr hs ⊢
 unfold uT at lP
 split_ifs at lP
 all_goals try { omega }
 all_goals constructor<;>linarith
def gr (B:aj G) (x:↥(B.ai 1).carrier) :
  B.eX→Fin 4:=
 fun γ↦uT (B.width γ.1:ℝ) (cx (γ.1 x.1))
omit [DecidableEq G] in
private lemma nQ (B:aj G)
  {x y:↥(B.ai 1).carrier}
  (ni:B.gr x=B.gr y) :
  x.1-y.1∈(B.ai (1/2)).carrier:=by
 rw[mem_carrier]
 intro γ oa
 have hx:=(mem_carrier (B.ai 1) x.1).mp x.2 γ oa
 have hy:=(mem_carrier (B.ai 1) y.1).mp y.2 γ oa
 simp only[oF,QT,SK] at hx hy ⊢
 rw[map_sub]
 have CW: |cx (γ x.1)| ≤(B.width γ:ℝ):=by
  rwa[←hH]
 have CX: |cx (γ y.1)| ≤(B.width γ:ℝ):=by
  rwa[←hH]
 have vU:=Uu ni ⟨γ,oa⟩
 calc
  _ ≤ |cx (γ x.1)-cx (γ y.1)|:=
   gu _ _
  _≤(B.width γ:ℝ)/2:=
   oN (by positivity) CW CX vU
  _=((1/2:NNReal):ℝ)*(B.width γ:ℝ):=by
   norm_num
   ring
omit [DecidableEq G] in
private lemma qA (B:aj G)
  (a:B.eX→Fin 4) :
  Fintype.card {x:↥(B.ai 1).carrier// B.gr x=a} ≤
   (B.ai (1/2)).carrier.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai 1).carrier// B.gr x=a}
 ·let x₀ :=
   Classical.choice jv
  let f:{x:↥(B.ai 1).carrier// B.gr x=a} →
    ↥(B.ai (1/2)).carrier:=
   fun x↦⟨x.1.1-x₀.1.1,nQ B
    (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have q4:=congr_arg (fun z↦z.1) ni
   dsimp[f] at q4
   exact S8 q4
  calc
   _ ≤
     Fintype.card ↥(B.ai (1/2)).carrier:=
    R1 f hf
   _=(B.ai (1/2)).carrier.card:=Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma de (B:aj G) :
  (B.ai 1).carrier.card ≤
   4^B.rank*(B.ai (1/2)).carrier.card:=by
 classical
 let S:=B.eX→Fin 4
 let q := B.gr
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai 1).carrier// q x=a} ≤
    (B.ai (1/2)).carrier.card:=by
  intro a
  exact qA B a
 have AA:Fintype.card S=4^B.rank:=by
  dsimp[S,rank]
  rw[TC]
  simp
 rw[←Rx (B.ai 1).carrier, ←AA]
 by_contra h
 have xS :
   Fintype.card S*(B.ai (1/2)).carrier.card <
    Fintype.card ↥(B.ai 1).carrier:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) xS
 have Em: #{x | q x=a}≤(B.ai (1/2)).carrier.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Em) ha
omit [DecidableEq G] in
lemma iW (B:aj G) :
  (B.ai 2).carrier.card ≤
   4^(3*B.rank)*(B.ai (1/4)).carrier.card:=by
 classical
 have h₂:=de (B.ai 2)
 have h₁:=de B
 have iB:=de (B.ai (1/2))
 simp only[f6,vo] at h₂ iB
 norm_num at h₂ iB
 calc
  _ ≤4^B.rank*B.carrier.card:=h₂
  _≤4^B.rank*(4^B.rank*(B.ai (1/2)).carrier.card):=by
   gcongr
   simpa using h₁
  _≤4^B.rank *
    (4^B.rank*(4^B.rank*(B.ai (1/4)).carrier.card)):=by
   gcongr
  _=4^(3*B.rank)*(B.ai (1/4)).carrier.card:=by
   rw[←Qo, ←RL, ←Qo, ←RL]
   congr 2
   omega
private lemma nR
  (f:ℝ→ℝ) (hf:Monotone f)
  (rW:f (5/4)-f (1/4)<5) :
  ∃ x∈Set.Icc (1/2:ℝ) 1,
   ∀ y∈Set.Icc (1/4:ℝ) (5/4),
    |f y-f x| ≤60* |y-x|:=by
 classical
 by_contra! xv
 let zk:Set (ℝ × ℝ):={p |
  1/4≤p.1∧p.1<p.2∧p.2≤5/4 ∧
   60*(p.2-p.1)<f p.2-f p.1}
 let center:(ℝ × ℝ)→ℝ:=fun p↦(p.1+p.2)/2
 let radius:(ℝ × ℝ)→ℝ:=fun p↦(p.2-p.1)/2
 have tx {p:ℝ × ℝ} (hp:p∈zk):0<radius p:=by
  dsimp[zk] at hp
  dsimp[radius]
  linarith
 have CY (p:ℝ × ℝ) (hp:p∈zk):radius p≤1/2:=by
  dsimp[zk] at hp
  dsimp[radius]
  linarith
 obtain ⟨u,x8,CZ,HC⟩:=
  Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
   zk center radius (1/2) CY 5 (by norm_num)
 have zP:Set.Icc (1/2:ℝ) 1 ⊆
   ⋃ b:↥u,Metric.ball (center b.1) (6*radius b.1):=by
  intro x hx
  obtain ⟨y,G8,ni⟩:=xv x hx
  let p:ℝ × ℝ:=(min x y,max x y)
  have Lj:p∈zk:=by
   dsimp[zk,p]
   have G9:x∈Set.Icc (1/4:ℝ) (5/4):=by
    constructor<;>linarith[hx.1,hx.2]
   rcases le_total x y with hle | hle
   ·simp only[min_eq_left hle,max_eq_right hle]
    have xw: |f y-f x| =f y-f x:=
     QC (sub_nonneg.mpr (hf hle))
    have C2: |y-x| =y-x:=QC (sub_nonneg.mpr hle)
    rw[xw,C2] at ni
    exact ⟨G9.1,QV (fun heq↦by
     have:y=x:=SC heq hle
     subst y
     norm_num at ni),G8.2,ni⟩
   ·simp only[min_eq_right hle,max_eq_left hle]
    have xw: |f y-f x| =f x-f y:=by
     rw[Su]
     exact QC (sub_nonneg.mpr (hf hle))
    have C2: |y-x| =x-y:=by
     rw[Su]
     exact QC (sub_nonneg.mpr hle)
    rw[xw,C2] at ni
    exact ⟨G8.1,QV (fun heq↦by
     have:x=y:=SC heq hle
     subst y
     norm_num at ni),G9.2,ni⟩
  obtain ⟨b,MI,l4⟩:=HC p Lj
  have Ou:x∈Metric.closedBall (center p) (radius p):=by
   rw[T8]
   dsimp[center,radius,p]
   constructor<;>rcases le_total x y with hle | hle <;>
    simp[hle]<;>linarith
  have Ef:x∈Metric.closedBall (center b) (5*radius b):=l4 Ou
  rw[Metric.mem_closedBall] at Ef
  rw[Set.mem_iUnion]
  refine ⟨⟨b,MI⟩, ?_⟩
  rw[Metric.mem_ball]
  have P4:0<radius b:=tx (x8 MI)
  linarith
 obtain ⟨v,Ci⟩:=isCompact_Icc.elim_finite_subcover
  (fun b:↥u↦Metric.ball (center b.1) (6*radius b.1))
  (fun _↦Metric.isOpen_ball) zP
 have BG:v.Nonempty:=by
  by_contra hv
  rw[Finset.not_nonempty_iff_eq_empty] at hv
  simpa[hv] using Ci (show(1/2:ℝ)∈Set.Icc (1/2) 1 by norm_num)
 have NU:(1/2:ℝ)≤6* ∑ b∈v,(b.1.2-b.1.1):=by
  have hm:MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
    MeasureTheory.volume (⋃ b∈v,
     Metric.ball (center b.1) (6*radius b.1)):=
   MeasureTheory.measure_mono Ci
  have oO:0≤6* ∑ b∈v,(b.1.2-b.1.1):=by
   apply Qn (by norm_num)
   apply UZ
   intro b hb
   have:=tx (x8 b.2)
   dsimp[radius] at this
   linarith
  rw[←ENNReal.ofReal_le_ofReal_iff oO]
  have iB:ENNReal.ofReal (1/2:ℝ) =
    MeasureTheory.volume (Set.Icc (1/2:ℝ) 1):=by
   rw[Real.volume_Icc]
   norm_num
  rw[iB]
  calc
   MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
     MeasureTheory.volume (⋃ b∈v,
      Metric.ball (center b.1) (6*radius b.1)):=hm
   _≤ ∑ b∈v,MeasureTheory.volume
     (Metric.ball (center b.1) (6*radius b.1)):=
    MeasureTheory.measure_biUnion_finset_le v _
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=by
    simp only[Real.volume_ball]
    rw[←ENNReal.ofReal_sum_of_nonneg]
    ·congr 1
     simp only[radius]
     calc
      ∑ b∈v,2*(6*((b.1.2-b.1.1)/2)) =
        ∑ b∈v,6*(b.1.2-b.1.1):=by
       apply Io rfl
       intro b hb
       ring
      _=6* ∑ b∈v,(b.1.2-b.1.1):=by
       rw[Qj]
    ·intro b hb
     have:=tx (x8 b.2)
     dsimp[radius] at this
     positivity
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=rfl
 let e:↥u ↪ (ℝ × ℝ):=⟨Subtype.val,Subtype.val_injective⟩
 let F:Finset (ℝ × ℝ):=v.map e
 have Ha (p:ℝ × ℝ) :
   Metric.closedBall (center p) (radius p)=Set.Icc p.1 p.2:=by
  rw[T8]
  dsimp[center,radius]
  congr<;>ring
 have En: ∀ ⦃z⦄,z∈F →
   (1/4:ℝ)≤z.1∧z.1≤z.2∧z.2≤5/4:=by
  intro z hz
  obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp hz
  have oP:=x8 b.2
  dsimp[zk] at oP
  exact ⟨oP.1,oP.2.1.le,oP.2.2.1⟩
 have BH:(SetLike.coe F).PairwiseDisjoint
   (fun z↦Set.Icc z.1 z.2):=by
  intro z hz w hw Ov
  obtain ⟨bz,P5,rfl⟩:=Finset.mem_map.mp hz
  obtain ⟨bw,P6,rfl⟩:=Finset.mem_map.mp hw
  have vH:(bz:ℝ × ℝ)≠bw:=by
   simpa[e] using Ov
  have hd:=CZ bz.2 bw.2 vH
  change Disjoint (Metric.closedBall (center bz) (radius bz))
   (Metric.closedBall (center bw) (radius bw)) at hd
  rw[Ha,Ha] at hd
  simpa[e] using hd
 have NV: ∑ z∈F,(f z.2-f z.1)≤f (5/4)-f (1/4):=by
  have Na:=F.sum_intervalGapsWithin_add_sum_eq_sub rfl
   (a:=(1/4:ℝ)) (b:=(5/4:ℝ)) f
  calc
   ∑ z∈F,(f z.2-f z.1)≤_:=by
    rw[le_add_iff_nonneg_left]
    apply UZ
    intro i hi
    apply sub_nonneg.mpr
    apply hf
    exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
     En BH
   _=f (5/4)-f (1/4):=Na
 have Nb:60* ∑ b∈v,(b.1.2-b.1.1) <
   ∑ z∈F,(f z.2-f z.1):=by
  rw[Finset.sum_map]
  simp only[e,Function.Embedding.coeFn_mk]
  rw[Qj]
  exact Tt BG
   (fun b hb↦(x8 b.2).2.2.2)
 linarith
omit [DecidableEq G] in
private lemma nS (B:aj G) :
  log ((B.ai (5/4)).carrier.card:ℝ) -
    log ((B.ai (1/4)).carrier.card:ℝ) <
   5*(max B.rank 1:ℕ):=by
 classical
 let d := max B.rank 1
 have ch:(B.ai (5/4)).carrier.card ≤
   4^(3*B.rank)*(B.ai (1/4)).carrier.card:=by
  calc
   _ ≤(B.ai 2).carrier.card:=
    Qu (b5
     (show(5/4:NNReal)≤2 by
      rw[QF (by norm_num:(0:NNReal)<4)]
      norm_num))
   _≤4^(3*B.rank)*(B.ai (1/4)).carrier.card:=
    iW B
 have C3:(0:ℝ)<(B.ai (1/4)).carrier.card:=by
  exact_mod_cast(B.ai (1/4)).aE.card_pos
 have C4:(0:ℝ)<(B.ai (5/4)).carrier.card:=by
  exact_mod_cast(B.ai (5/4)).aE.card_pos
 have ei:=QG C4 (show
   ((B.ai (5/4)).carrier.card:ℝ) ≤
    ((4^(3*B.rank)*(B.ai (1/4)).carrier.card:ℕ):ℝ) by
   exact_mod_cast ch)
 rw[Rm,Rv,Ql (by positivity) C3.ne',
  QB] at ei
 have z2:(0:ℝ)<d:=by
  exact_mod_cast(show 0<d by simp[d])
 have Nc:(B.rank:ℝ)≤d:=by
  exact_mod_cast(Tu B.rank 1)
 have PA:log (4:ℝ)<5/3:=by
  rw[Real.log_four_eq]
  linarith[Real.log_two_lt_d9]
 have fF:(3*B.rank:ℕ)*log (4:ℝ)<5*d:=by
  push_cast
  calc
   _ ≤3*d*log 4:=by
    gcongr
   _<3*d*(5/3):=by gcongr
   _=5*d:=by ring
 dsimp[d] at fF ⊢
 linarith
private noncomputable def fj (B:aj G) (s:ℝ):ℝ:=
 log ((B.ai s.toNNReal).carrier.card:ℝ) /
  (max B.rank 1:ℕ)
omit [DecidableEq G] in
private lemma q5 (B:aj G) :
  Monotone B.fj:=by
 intro s t pE
 dsimp[fj]
 apply Qz _ (by positivity)
 apply QG
 ·exact_mod_cast(B.ai s.toNNReal).aE.card_pos
 ·exact_mod_cast Qu
   (b5 (B:=B) (Real.toNNReal_mono pE))
omit [DecidableEq G] in
private lemma og (B:aj G) :
  B.fj (5/4)-B.fj (1/4)<5:=by
 classical
 have h:=nS B
 have hd:(0:ℝ)<(max B.rank 1:ℕ):=by positivity
 have Ow:Real.toNNReal (5/4:ℝ)=(5/4:NNReal):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 have Ox:Real.toNNReal (1/4:ℝ)=(1/4:NNReal):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 dsimp[fj]
 rw[Ow,Ox]
 rw[div_sub_div_same]
 exact(Tv hd).2 (by simpa[Qx] using h)
omit [DecidableEq G] in
lemma eP (B:aj G) :
  ∃ a8:NNReal,1/2≤a8∧a8≤1 ∧
   (B.ai a8).a1:=by
 classical
 let d:ℕ:=max B.rank 1
 obtain ⟨r,hr,Ju⟩:=nR
  B.fj (q5 B)
   (og B)
 let a8:NNReal:=r.toNNReal
 have jM:(a8:ℝ)=r:=Tg r (by linarith[hr.1])
 have zl:(1/2:NNReal)≤a8:=by
  rw[←U0,jM]
  norm_num
  exact hr.1
 have AD:a8≤1:=by
  rw[←U0,jM]
  norm_num
  exact hr.2
 refine ⟨a8,zl,AD, ?_⟩
 rw[sj]
 dsimp only[f6]
 intro aF dy
 have Jv:0<d:=by simp[d]
 have z2:(0:ℝ)<d:=by exact_mod_cast Jv
 have oK:aF≤1:=by
  apply dy.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have BI:(aF:ℝ)≤1/(100*(d:ℝ)):=by
  exact_mod_cast dy
 let j5:NNReal:=(1-aF)*a8
 let mz:NNReal:=(1+aF)*a8
 have Oy:(aF:ℝ)≤1/100:=by
  calc
   (aF:ℝ)≤1/(100*(d:ℝ)):=BI
   _≤1/100:=by
    apply Rb (by norm_num) (by norm_num)
    have Eo:(1:ℝ)≤d:=by
     exact_mod_cast(show 1≤d by simp[d])
    nlinarith
 have ta:(1/2:ℝ)≤a8∧(a8:ℝ)≤1:=by
  exact ⟨by exact_mod_cast zl,by exact_mod_cast AD⟩
 have BJ:(j5:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[j5]
  rw[NNReal.coe_sub oK]
  simp only[TN]
  have F4:(99/100:ℝ)≤1-(aF:ℝ):=by
   nlinarith
  constructor
  ·calc
    (1/4:ℝ)≤(99/100)*(1/2):=by norm_num
    _≤(1-(aF:ℝ))*(a8:ℝ):=by
     exact QW F4 ta.1 (by norm_num)
      (sub_nonneg.mpr (by exact_mod_cast oK))
  ·calc
    (1-(aF:ℝ))*(a8:ℝ)≤1*a8:=
     Qi (sub_le_self 1 (by positivity)) (by positivity)
    _≤1*1:=iO ta.2 (by norm_num)
    _≤5/4:=by norm_num
 have C5:(mz:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[mz]
  constructor<;>nlinarith
 have Lk: |(j5:ℝ)-r| ≤(aF:ℝ):=by
  rw[←jM]
  dsimp[j5]
  rw[NNReal.coe_sub oK]
  simp only[TN]
  have xx:(0:ℝ)≤a8:=by positivity
  rw[show(1-(aF:ℝ))*(a8:ℝ)-a8= -(aF*a8) by ring,
   abs_neg,QC (Qn (by positivity) xx)]
  nlinarith[ta.2]
 have MJ: |(mz:ℝ)-r| ≤(aF:ℝ):=by
  rw[←jM]
  dsimp[mz]
  have xx:(0:ℝ)≤a8:=by positivity
  rw[show(1+(aF:ℝ))*(a8:ℝ)-a8=aF*a8 by ring,
   QC (Qn (by positivity) xx)]
  nlinarith[ta.2]
 have tb:=Ju (j5:ℝ) BJ
 have uU:=Ju (mz:ℝ) C5
 simp only[fj,Real.toNNReal_coe,
  show r.toNNReal=a8 by rfl] at tb uU
 change
  |log ((B.ai j5).carrier.card:ℝ)/d -
   log ((B.ai a8).carrier.card:ℝ)/d| ≤
    60* |(j5:ℝ)-r| at tb
 change
  |log ((B.ai mz).carrier.card:ℝ)/d -
   log ((B.ai a8).carrier.card:ℝ)/d| ≤
    60* |(mz:ℝ)-r| at uU
 rw[div_sub_div_same,TE,RT z2] at tb uU
 have Ep :
   log ((B.ai a8).carrier.card:ℝ) -
     log ((B.ai j5).carrier.card:ℝ) ≤
    60*d*(aF:ℝ):=by
  have xw:=(QF z2).mp tb
  calc
   _≤ |log ((B.ai j5).carrier.card:ℝ) -
     log ((B.ai a8).carrier.card:ℝ)|:=by
    rw[Su]
    exact SG _
   _≤60* |(j5:ℝ)-r| *d:=xw
   _≤60*(aF:ℝ)*d:=by gcongr
   _=60*d*(aF:ℝ):=by ring
 have F5 :
   log ((B.ai mz).carrier.card:ℝ) -
     log ((B.ai a8).carrier.card:ℝ) ≤
    60*d*(aF:ℝ):=by
  have xw:=(QF z2).mp uU
  calc
   _≤ |log ((B.ai mz).carrier.card:ℝ) -
     log ((B.ai a8).carrier.card:ℝ)|:=SG _
   _≤60* |(mz:ℝ)-r| *d:=xw
   _≤60*(aF:ℝ)*d:=by gcongr
   _=60*d*(aF:ℝ):=by ring
 let u:ℝ:=100*d*(aF:ℝ)
 have Jw:0≤u:=by dsimp[u]; positivity
 have Oz:u≤1:=by
  dsimp[u]
  calc
   100*(d:ℝ)*(aF:ℝ) ≤
     100*d*(1/(100*d)):=by gcongr
   _=1:=by field_simp
 have Er:60*d*(aF:ℝ)=(3/5:ℝ)*u:=by
  dsimp[u]
  ring
 constructor
 ·change(1-u)*((B.ai a8).carrier.card:ℝ) ≤
   ((B.ai j5).carrier.card:ℝ)
  by_cases hu:u=1
  ·rw[hu]
   norm_num
  ·have Ll:u<1:=SM Oz hu
   have Hb:0<1-u:=sub_pos.mpr Ll
   have t7:(0:ℝ)<(B.ai a8).carrier.card:=by
    exact_mod_cast(B.ai a8).aE.card_pos
   have oJ:(0:ℝ)<(B.ai j5).carrier.card:=by
    exact_mod_cast(B.ai j5).aE.card_pos
   rw[←SW (QM Hb t7) oJ]
   rw[Ql (sub_ne_zero.mpr (Ne.symm hu)) t7.ne']
   have HG:=QX Hb
   rw[Er] at Ep
   nlinarith
 ·change((B.ai mz).carrier.card:ℝ) ≤
   (1+u)*((B.ai a8).carrier.card:ℝ)
  have t7:(0:ℝ)<(B.ai a8).carrier.card:=by
   exact_mod_cast(B.ai a8).aE.card_pos
  have ju:(0:ℝ)<(B.ai mz).carrier.card:=by
   exact_mod_cast(B.ai mz).aE.card_pos
  rw[←SW ju (QM (by linarith) t7)]
  rw[Ql (by linarith) t7.ne']
  have HG:=Real.le_log_one_add_of_nonneg Jw
  have PC:(3/5:ℝ)*u≤2*u/(u+2):=by
   rw[Qs (by linarith)]
   nlinarith
  rw[Er] at F5
  linarith
end aj
end
end ay
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.dT
variable {G:Type*} [AddCommGroup G] [Fintype G]
def coeff (f:G→ℂ) (χ:AddChar G ℂ):ℂ:=⟪(χ:G→ℂ),f⟫ₙ_[ℂ]
lemma inversion (f:G→ℂ) (a:G) :
  ∑ χ:AddChar G ℂ,coeff f χ*χ a=f a:=by
 classical
 simp_rw[coeff,wInner_cWeight_eq_expect,inner_apply',expect_mul,
  ←expect_sum_comm,QN _ (f _), ←sum_mul,
  ←Rz,TK, ←map_sub_eq_div,
  AddChar.sum_apply_eq_ite,sub_eq_zero,ite_mul,zero_mul,Fintype.expect_ite_eq]
 simp[NNRat.smul_def (K:=ℂ),SN]
def convolution (f g:G→ℂ) (x:G):ℂ:=
 𝔼 y:G,f y*g (x-y)
def a2 (f g:G→ℂ) (x:G):ℂ:=
 𝔼 y:G,f (x+y)*conj (g y)
lemma mW (f g:G→ℂ) (χ:AddChar G ℂ) :
  coeff (convolution f g) χ=coeff f χ*coeff g χ:=by
 classical
 simp_rw[coeff,wInner_cWeight_eq_expect,inner_apply,convolution,
  mul_expect,expect_mul, ←expect_product',univ_product_univ]
 refine RW ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _) _ _ fun (a,b)↦ ?_
 simp[Q7, ←RU, ←map_add_eq_mul]
lemma zQ (f:G→ℂ) (χ:AddChar G ℂ) :
  coeff (fun x↦conj (f (-x))) χ=conj (coeff f χ):=by
 classical
 simp only[coeff,wInner_cWeight_eq_expect,inner_apply,map_expect,RU,
  Tl]
 refine RW (Equiv.neg _) _ _ fun i↦ ?_
 simp only[Equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply',inv_apply]
lemma l6 (f g:G→ℂ) :
  a2 f g=convolution f (fun x↦conj (g (-x))):=by
 funext x
 simp only[a2,convolution]
 refine RW (Equiv.addLeft x) _ _ fun y↦ ?_
 simp
lemma kt (f g:G→ℂ) (χ:AddChar G ℂ) :
  coeff (a2 f g) χ=coeff f χ*conj (coeff g χ):=by
 rw[l6,mW,zQ]
lemma t8 (f:G→ℂ) (χ:AddChar G ℂ) :
  coeff (a2 f f) χ=(Complex.normSq (coeff f χ):ℂ):=by
 rw[kt]
 exact Complex.mul_conj _
end ay.dT
end
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.jw
open dT
variable {G:Type*} [AddCommGroup G] [Fintype G]

def aK (nu:G→ℝ) (f:G→ℂ) (p:ℕ):ℝ:=
 𝔼 x:G,nu x* ‖f x‖ ^p
def ds (nu:G→ℝ) (fJ:AddChar G ℂ):ℂ:=
 𝔼 x:G,(nu x:ℂ)*fJ x
def fO (nu:G→ℝ):Prop:=
 ∀ fJ:AddChar G ℂ,
  0≤(ds nu fJ).re∧(ds nu fJ).im=0
lemma k2 (a b:G→ℝ) (x:G) :
  (ay.ao a b x:ℂ) =
   (Fintype.card G:ℂ) *
    dT.convolution ((↑) ∘ a) ((↑) ∘ b) x:=by
 unfold ay.ao dT.convolution
 rw[Rj]
 push_cast
 field_simp
 simp[Rh]
lemma ga (a:G→ℝ) (x:G) :
  (ay.aZ a a x:ℂ) =
   (Fintype.card G:ℂ) *
    a2 ((↑) ∘ a) ((↑) ∘ a) x:=by
 unfold ay.aZ dT.a2
 rw[Rj]
 push_cast
 field_simp
 refine Qk (Equiv.subRight x) _ _ fun y↦ ?_
 simp
lemma k3 {nu:G→ℝ}
  (rq:fO nu) (fJ:AddChar G ℂ) :
  ds nu fJ=((ds nu fJ).re:ℂ):=by
 apply Complex.ext
 ·simp
 ·simpa using(rq fJ).2
lemma q6 (nu:G→ℝ) (fJ:AddChar G ℂ) (t:G) :
  (𝔼 x:G,(nu (x-t):ℂ)*fJ x)=fJ t*ds nu fJ:=by
 unfold ds
 rw[mul_expect]
 refine RW (M:=ℂ) (Equiv.subRight t:G ≃ G) _ _ fun y↦ ?_
 simp only[Ut,Qy]
 have hc:fJ y=fJ t*fJ (y+ -t):=by
  rw[←map_add_eq_mul]
  congr 1
  abel
 rw[hc]
 ring
lemma oh {nu:G→ℝ}
  (rq:fO nu) (fJ:AddChar G ℂ) (t:G) :
  ‖𝔼 x:G,(nu (x-t):ℂ)*fJ x‖ =(ds nu fJ).re:=by
 rw[q6,QO,Q0,
  QT,k3 rq]
 simp[QC (rq fJ).1]
lemma gv
  (a b:G→ℝ) :
  fO
   (ay.ao
    (ay.aZ a a)
    (ay.aZ b b)):=by
 let ac:G→ℂ:=(↑) ∘ a
 let bc:G→ℂ:=(↑) ∘ b
 let da := a2 ac ac
 let db := a2 bc bc
 let h := dT.convolution da db
 have t9 (x:G) :
   (ay.ao
     (ay.aZ a a)
     (ay.aZ b b) x:ℂ) =
    (Fintype.card G:ℂ)^3*h x:=by
  rw[k2]
  have OA:((↑) ∘ ay.aZ a a) =
    fun y↦(Fintype.card G:ℂ)*da y:=by
   funext y
   exact ga a y
  have OB:((↑) ∘ ay.aZ b b) =
    fun y↦(Fintype.card G:ℂ)*db y:=by
   funext y
   exact ga b y
  rw[OA,OB]
  simp only[h,da,db,dT.convolution,
   Rj]
  have ch:(Fintype.card G:ℂ)≠0:=by
   exact_mod_cast SN
  field_simp
  rw[Qj]
  apply Io rfl
  intro x hx
  ring
 intro fJ
 have Ay :
   ds
     (ay.ao
      (ay.aZ a a)
      (ay.aZ b b)) fJ =
    (Fintype.card G:ℂ)^3*coeff h (-fJ):=by
  unfold ds
  simp_rw[t9]
  calc
   _ =
     (Fintype.card G:ℂ)^3*(𝔼 x:G,h x*fJ x):=by
    calc
     _=𝔼 x:G,(Fintype.card G:ℂ)^3*(h x*fJ x):=by
      congr 1 with x
      ring
     _=_:=by rw[←mul_expect]
   _=_:=by
    congr 1
    simp[coeff,wInner_cWeight_eq_expect,inner_apply,map_neg_eq_conj]
 have uO :
   ds
     (ay.ao
      (ay.aZ a a)
      (ay.aZ b b)) fJ =
    (((Fintype.card G:ℝ)^3*Complex.normSq (coeff ac (-fJ)) *
     Complex.normSq (coeff bc (-fJ)):ℝ):ℂ):=by
  rw[Ay]
  simp only[h,mW,da,db,t8]
  push_cast
  ring
 rw[uO]
 constructor
 ·simpa only[Complex.ofReal_re] using
   (Qn
   (Qn (by positivity) (Uk _))
   (Uk _))
 ·exact Complex.ofReal_im _
omit [AddCommGroup G] in
lemma iG {I:Type*} {k:ℕ} (_hk:k≠0)
  (nu:G→ℝ) (s:Finset I) (u:I→G→ℂ) :
  (aK nu (∑ i∈s,u i) (2*k):ℂ) =
   ∑ x∈(piFinset fun _:Fin k↦s), ∑ y∈(piFinset fun _:Fin k↦s),
    𝔼 a:G,(nu a:ℂ) *
     ((∏ i,conj (u (x i) a))* ∏ i,u (y i) a):=by
 rw[aK]
 push_cast
 simp_rw[Si]
 calc
  _ =
    𝔼 a:G,(nu a:ℂ) *
     ((∑ i∈s,conj (u i a))^k*(∑ j∈s,u j a)^k):=by
   congr 1 with a
   simp_rw[QU, ←UX,QL,RK]
  _=_:=by
   simp_rw[sum_pow',Finset.sum_mul_sum,mul_sum,expect_sum_comm]
omit [AddCommGroup G] in
lemma dx {nu:G→ℝ} (rq: ∀ x,0≤nu x)
  (f:G→ℂ) (p:ℕ):0≤aK nu f p:=
       expect_nonneg fun x _↦Qn (rq x) (QH (Re _) _)
lemma gw
  {p:ℕ} (hp:p≠0) (mx:Even p)
  (nu:G→ℝ) (rq: ∀ x,0≤nu x)
  (z3:fO nu) (t:G) (f:G→ℂ) :
  aK (fun x↦nu (x-t)) (convolution f f) p ≤
   aK nu (a2 f f) p:=by
 obtain ⟨k,rfl⟩:=mx.two_dvd
 simp only[ne_eq,mul_eq_zero,OfNat.ofNat_ne_zero,false_or] at hp
 let term:(Fin k→ AddChar G ℂ) × (Fin k→ AddChar G ℂ)→ℂ:=
  fun psi ↦
   conj (∏ i,coeff f (psi.1 i)^2) *
    (∏ i,coeff f (psi.2 i)^2) *
     (𝔼 x:G,(nu (x-t):ℂ) *
      ((∑ i,psi.2 i- ∑ i,psi.1 i) x))
 refine Complex.le_of_eq_sum_of_eq_sum_norm term univ
  (dx (fun x↦rq (x-t)) _ _) ?_ ?_
 ·have hinv:convolution f f =
    ∑ fJ:AddChar G ℂ,fun x↦coeff (convolution f f) fJ*fJ x:=by
   funext x
   simpa only[Si] using(inversion (convolution f f) x).symm
  rw[hinv]
  have hm:=iG (G:=G) hp
   (fun x↦nu (x-t)) (univ:Finset (AddChar G ℂ))
   (fun fJ x↦coeff (convolution f f) fJ*fJ x)
  rw[hm]
  simp only[term]
  simp_rw[mW, ←sq,Ul,mul_expect,
   RO]
  simp[Q7,Qx,map_neg_eq_conj,prod_mul_distrib]
  ring_nf
 ·have hinv:a2 f f =
    ∑ fJ:AddChar G ℂ,
     fun x↦coeff (a2 f f) fJ*fJ x:=by
   funext x
   simpa only[Si] using
    (inversion (a2 f f) x).symm
  rw[hinv]
  have hm:=iG (G:=G) hp nu
   (univ:Finset (AddChar G ℂ))
   (fun fJ x↦coeff (a2 f f) fJ*fJ x)
  rw[hm]
  simp only[term]
  simp_rw[kt,Complex.mul_conj',
   Ul,mul_expect]
  congr 1 with psi
  congr 1 with phi
  simp only[RU,map_pow,prod_mul_distrib,Q7,
   map_prod,RO,AddChar.coe_sum,
   Finset.prod_apply,
   Complex.conj_ofReal]
  have Jx :
    (𝔼 x:G,(nu x:ℂ) *
      ((∏ i,conj (psi i x))* ∏ i,phi i x)) =
     ds nu (∑ i,phi i- ∑ i,psi i):=by
   simp[ds,map_neg_eq_conj,Qx,
    RO]
  let a:ℂ:=
   (∏ i,(‖coeff f (psi i)‖ ^2:ℂ)) *
    ∏ i,(‖coeff f (phi i)‖ ^2:ℂ)
  let c :=
   conj (∏ i,coeff f (psi i)^2)* ∏ i,coeff f (phi i)^2
  let eta :=  ∑ i,phi i- ∑ i,psi i
  have kB :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,phi i x))) =
     a*ds nu eta:=by
   calc
    _=𝔼 x:G,a*((nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,phi i x)):=by
      congr 1 with x
      ring
    _=a*(𝔼 x:G,(nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,phi i x)):=by
      rw[←mul_expect]
    _=_:=by simpa only[eta] using QA (a*·) Jx
  have y2 :
    (𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,phi i x)* ∏ i,psi i (-x))) =
     c*(𝔼 x:G,(nu (x-t):ℂ)*eta x):=by
   calc
    _=𝔼 x:G,c*((nu (x-t):ℂ)*eta x):=by
     congr 1 with x
     dsimp only[eta]
     simp[map_neg_eq_conj,RO,Qx,Q6]
     ring
    _=_:=by rw[←mul_expect]
  have Lm :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,phi i x))) =
     (‖𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,phi i x)* ∏ i,psi i (-x))‖ :ℂ):=by
   rw[kB,y2,QO,
    oh z3 eta t]
   rw[k3 z3]
   dsimp only[a,c]
   push_cast
   simp[norm_prod]
  simpa[a,c,TI,prod_mul_distrib,Qo,Qx,Q6] using Lm
lemma jN
  {p:ℕ} (hp:p≠0) (mx:Even p)
  (nu:G→ℝ) (rq: ∀ x,0≤nu x)
  (z3:fO nu) (t:G) (f:G→ℂ) :
  ∑ x:G,nu (x-t)* ‖convolution f f x‖ ^p ≤
   ∑ x:G,nu x* ‖a2 f f x‖ ^p:=by
 have h:=gw
  hp mx nu rq z3 t f
 simp only[aK,Rj] at h
 exact(R9
  (by positivity:(0:ℝ)<Fintype.card G)).mp h
end ay.jw
end
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay
namespace hJ
noncomputable section
open dT
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def c4 (C D:Finset G):G→ℝ:=
 ao
  (aZ (af C) (af C))
  (aZ (af D) (af D))
lemma mT (C D:Finset G) (x:G) :
  0≤c4 C D x:=by
 apply fa
 ·exact gB
   (bO C) (bO C)
 ·exact gB
   (bO D) (bO D)
lemma uV {C D:Finset G}
  (hC:C.Nonempty) (hD:D.Nonempty) :
  ∑ x:G,c4 C D x=1:=by
 rw[c4,iz,
  ho,ho,
  cf hC,cf hD]
 norm_num
lemma hO
  {B:aj G} {eta:ℝ≥0} {C:Finset G}
  (hC:C.Nonempty) (fN:C⊆(B.ai eta).carrier)
  {x:G}
  (hx:aZ
   (af C) (af C) x≠0) :
  x∈(B.ai (2*eta)).carrier:=by
 by_contra C6
 apply hx
 rw[aZ]
 apply UN
 intro y _
 by_cases hy:af C y=0
 ·simp[hy]
 have OC:y∈C:=(d6 hC y).mp hy
 by_cases Es:af C (y-x)=0
 ·simp[Es]
 have Nd:y-x∈C:=
  (d6 hC (y-x)).mp Es
 have AF:=aj.j2 (fN OC) (fN Nd)
 have heq:y-(y-x)=x:=by abel
 rw[heq] at AF
 exact(C6 (by simpa[R5] using AF)).elim
lemma nj
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).carrier)
  (gn:D⊆(B.ai eta).carrier)
  {x:G} (hx:c4 C D x≠0) :
  x∈(B.ai (4*eta)).carrier:=by
 by_contra C6
 apply hx
 rw[c4,ao]
 apply UN
 intro y _
 let Hc:=aZ
  (af C) (af C)
 let Hd:=aZ
  (af D) (af D)
 by_cases hy:Hc y=0
 ·exact mul_eq_zero.mpr (Or.inl (by simpa[Hc] using hy))
 by_cases ni:Hd (x-y)=0
 ·exact mul_eq_zero.mpr (Or.inr (by simpa[Hd] using ni))
 have Jq :=
  hO hC fN hy
 have F3 :=
  hO hD gn ni
 have AF:=aj.e8 Jq F3
 have heq:y+(x-y)=x:=by abel
 rw[heq] at AF
 exact(C6 (by
  simpa[show(2:ℝ≥0)*eta+2*eta=4*eta by ring] using AF)).elim
omit [DecidableEq G] in
lemma lU
  (mu outer nu h:G→ℝ) (R:ℝ)
  (zR: ∀ x,0≤outer x)
  (BK: ∑ x:G,outer x=1)
  (hh: ∀ x,0≤h x)
  (Jy: ∀ x,mu x≤2*ao outer nu x)
  (kE: ∀ t:G, ∑ x:G,nu (x-t)*h x≤R) :
  ∑ x:G,mu x*h x≤2*R:=by
 calc
  _ ≤
    ∑ x:G,(2*ao outer nu x)*h x:=by
   apply QI
   intro x _
   exact Qi (Jy x) (hh x)
  _=2* ∑ x:G,ao outer nu x*h x:=by
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  _=2* ∑ t:G,outer t* ∑ x:G,nu (x-t)*h x:=by
   apply QA (fun z:ℝ↦2*z)
   simp only[ao]
   calc
    _ =
      ∑ x:G, ∑ y:G,(outer y*nu (x-y))*h x:=by
     apply Io rfl
     intro x _
     rw[Qt]
    _= ∑ t:G, ∑ x:G,(outer t*nu (x-t))*h x:=
     QD
    _= ∑ t:G,outer t* ∑ x:G,nu (x-t)*h x:=by
     apply Io rfl
     intro t _
     rw[Qj]
     apply Io rfl
     intro x _
     ring
  _≤2* ∑ t:G,outer t*R:=by
   apply iO
   ·apply QI
    intro t _
    exact iO (kE t) (zR t)
   ·norm_num
  _=2*R:=by rw[←Qt,BK,QT]
lemma gI
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mA:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).carrier)
  (gn:D⊆(B.ai eta).carrier)
  (p:ℕ) (f:G→ℂ)
  (l7: ∀ t:G,
   ∑ x:G,c4 C D (x-t)* ‖convolution f f x‖ ^p ≤
    ∑ x:G,c4 C D x* ‖a2 f f x‖ ^p) :
  ∑ x:G,af B.carrier x* ‖convolution f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 let nu:=c4 C D
 let outer:=af (B.ai (1+4*eta)).carrier
 apply lU
   (af B.carrier) outer nu
   (fun x↦ ‖convolution f f x‖ ^p)
   (∑ x:G,c4 C D x* ‖a2 f f x‖ ^p)
 ·exact bO _
 ·exact cf (B.ai (1+4*eta)).aE
 ·intro x
  positivity
 ·intro x
  exact gC
   dF (by positivity:0<(4:ℝ≥0)*eta) mA nu
   (mT C D) (uV hC hD)
   (fun t ht↦nj hC hD fN gn ht) x
 ·exact l7
lemma kF
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mA:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).carrier)
  (gn:D⊆(B.ai eta).carrier)
  {p:ℕ} (hp:p≠0) (mx:Even p) (f:G→ℂ) :
  ∑ x:G,af B.carrier x* ‖convolution f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 apply gI
  dF fC mA hC hD fN gn p f
 intro t
 apply jw.jN hp mx
   (c4 C D) (mT C D)
 ·simpa only[c4] using
   jw.gv
    (af C) (af D)
end
end hJ
end ay
end
section
namespace ay
open Finset
open scoped BigOperators Pointwise translate ENNReal NNReal
noncomputable def cQ (q:ℕ) (ε:ℝ):ℕ:=
 ⌈(64:ℝ)*q/(ε/2)^2⌉₊
lemma vz
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (q:ℕ) (hq:1≤q) (ε:ℝ) (hε:0<ε) (f:G→ℂ) :
  let k:=cQ q ε
  ∃ T:Finset G,
   T⊆S ∧
   T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (2*q) (τ (t-s) ((aC (mu A) f))-(aC (mu A) f))) ≤
     ε*(aJ (2*q) f):=by
 classical
 let k:=cQ q ε
 let L:=gl.l k q (ε/2) f A
 have Cj:(64:ℝ)*q/(ε/2)^2≤k:=by
  change(64:ℝ)*q/(ε/2)^2 ≤
   (↑⌈(64:ℝ)*q/(ε/2)^2⌉₊:ℝ)
  exact Rr _
 have Ln:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  exact Cj.trans_lt'
   (Rn (QM (by norm_num) (by positivity)) (RF (half_pos hε) 2))
 have Jz:(#A:ℝ)^k/2≤ #L:=
  gl.Ho (half_pos hε) hq Cj
 have Nf:L.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ]
  exact Jz.trans_lt' (by positivity)
 let P:Finset ((Fin k→G) × G):=L ×ˢ S
 let X:Finset (Fin k→G):=(piFinset fun _:Fin k↦((A+S)))
 let φ:((Fin k→G) × G)→(Fin k→G):=fun z↦z.1+fun _↦z.2
 have pT:X.Nonempty:=(hA.add hS).piFinset_const
 have AG: ∀ z∈P,φ z∈X:=by
  rintro ⟨l,s⟩ JA
  simp only[P,mem_product] at JA
  simp only[X,RX,φ,RM]
  have AH:l∈L:=JA.1
  change l∈gl.l k q (ε/2) f A at AH
  rw[gl.l,mem_filter] at AH
  have hl:l∈(piFinset fun _:Fin k↦A):=AH.1
  intro i
  exact Finset.add_mem_add (Fintype.mem_piFinset.1 hl i) JA.2
 have Et: #X= #(A+S)^k:=by simp[X]
 have HI:(#X:ℝ)=(#(A+S):ℝ)^k:=by
  rw[Et]
  norm_cast
 have F6:(#X:ℝ)≠0:=by exact_mod_cast pT.card_ne_zero
 have HJ :
   ∃ x∈X,((#L:ℝ)* #S)/ #X ≤
    ∑ z∈P with φ z=x,(1:ℝ):=by
  refine Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum AG pT ?_
  simp only[QS,sum_const,P,card_product,Rm]
  rw[Qx (#X:ℝ),Tz _ F6,Q3]
 obtain ⟨x,He,hx⟩:=HJ
 let Q:Finset ((Fin k→G) × G):={z∈P | φ z=x}
 let T:Finset G:=Q.image Prod.snd
 have Eu:(#Q:ℝ)= ∑ z∈P with φ z=x,(1:ℝ):=by simp[Q]
 have HK:Set.InjOn Prod.snd (Q:Set ((Fin k→G) × G)):=by
  rintro ⟨JC,s₁⟩ Lo ⟨JE,s₂⟩ Lq hs
  have JF:(JC,s₁)∈Q:=Lo
  have JG:(JE,s₂)∈Q:=Lq
  have OD:JC+(fun _↦s₁)=JE+fun _↦s₂:=
   (mem_filter.1 JF).2.trans (mem_filter.1 JG).2.symm
  cases hs
  apply Prod.ext
  ·funext i
   exact add_right_cancel (SR OD i)
  ·rfl
 have nk: #T= #Q:=card_image_iff.mpr HK
 have Lr:(0:ℝ)< #Q:=by
  have Ev:0<((#L:ℝ)* #S)/ #X:=
   Rn (QM (by exact_mod_cast Nf.card_pos) (by exact_mod_cast hS.card_pos))
    (by exact_mod_cast pT.card_pos)
  exact Ev.trans_le (by simpa[Eu] using hx)
 have uW:T.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ,nk]
  exact Lr
 refine ⟨T, ?_,uW, ?_, ?_⟩
 ·intro s JH
  obtain ⟨z,OE,rfl⟩:=mem_image.1 JH
  exact(mem_product.1 (mem_filter.1 OE).1).2
 ·calc
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k)
     = (((#A:ℝ)^k/2* #S)/ #X):=by rw[HI]
   _≤((#L:ℝ)* #S)/ #X:=by gcongr
   _≤ #Q:=by simpa[Eu] using hx
   _= #T:=by exact_mod_cast nk.symm
 ·intro s JH t OF
  obtain ⟨⟨a,s'⟩,JI,OG⟩:=mem_image.1 JH
  obtain ⟨⟨b,t'⟩,JJ,OH⟩:=mem_image.1 OF
  simp only at OG OH
  subst s'
  subst t'
  have OI:a∈L:=(mem_product.1 (mem_filter.1 JI).1).1
  have OJ:b∈L:=(mem_product.1 (mem_filter.1 JJ).1).1
  have OK:a+(fun _↦s)=x:=(mem_filter.1 JI).2
  have OL:b+(fun _↦t)=x:=(mem_filter.1 JJ).2
  have hab:a+(fun _↦s-t)=b:=by
   funext i
   have ha:=SR OK i
   have hb:=SR OL i
   simp only[RM] at ha hb ⊢
   calc
    a i+(s-t)=(a i+s)-t:=by abel
    _=x i-t:=by rw[ha]
    _=b i:=by rw[←hb]; abel
  have HL:a+(fun _↦s-t)∈L:=by rw[hab]; exact OJ
  have JK:=gl.pN
   (A:=A) (f:=f) (m:=q) (k:=k) (t:=s-t) OI HL Ln hq
  simpa[neg_sub,mul_div_cancel₀ _ (two_ne_zero' ℝ)] using JK
private lemma ua
  {G:Type*} (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty)
  (q:ℕ) (hq:q=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊) :
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤exp 1:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 have tc:0<r:=by
  dsimp[r]
  exact lt_min U1 (Rn (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
 have xA:r≤1:=Uv _ _
 have si:0<1+log r⁻¹:=by
  have Ck:0≤log r⁻¹:=
   Qv ((Uw tc).2 xA)
  linarith
 have x9:1≤q:=by
  rw[hq,Nat.one_le_ceil_iff]
  have Ck:0≤log r⁻¹:=
   Qv ((Uw tc).2 xA)
  dsimp[r] at Ck ⊢
  linarith
 calc
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)
    ≤ r^(-((2*q:ℕ):ℝ)⁻¹):=
   Real.rpow_le_rpow_of_nonpos (by positivity) inf_le_right<| neg_nonpos.2<| by positivity
  _≤r^(-(1+log r⁻¹)⁻¹):=
   Th (by positivity) xA<| TO<| inv_anti₀
    si<| (Rr _).trans<| by
     rw[←hq]
     exact_mod_cast T9 q (by norm_num:0<2)
  _≤r^(-(0+log r⁻¹)⁻¹):=by
   obtain hr | hr:r=1∨r<1:=xA.eq_or_lt
   ·simp[hr]
   have:0<log r⁻¹:=Sv<| (one_lt_inv₀ tc).2 hr
   exact Th (by positivity) xA
    (by gcongr; exact Us)
  _=r^(log r)⁻¹:=by simp[inv_neg]
  _≤exp 1:=Real.rpow_inv_log_le_exp_one
private lemma sZ
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} (B C:Finset G) (u x:G) (q:ℕ) (x9:1≤q) :
  ‖(τ u ((aC (((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))) (mu C))) -
   (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    (aJ (2*q) (τ u ((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((indicator B fun _↦(1:_)))))) *
     (aJ (NNReal.conjExponent (2*q)) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
 let M:ℕ:=2*q
 have z1:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have hM:(M:ℝ≥0).HolderConjugate _:=S2 z1
 have P7:(M:ℝ≥0∞).HolderConjugate _:=hM.coe_ennreal
 set F:G→ℂ:=τ u ((aC (mu A) ((indicator B fun _↦(1:_)))))-(aC (mu A) ((indicator B fun _↦(1:_))))
 have x7 :
   (τ u ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)))-(aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x =
    ((aC F (mu C))) x:=by simp[CA,F]
 have hsum:((aC F (mu C))) x= ∑ y,F y*mu (x+ᵥ -C) y:=by
  rw[cR]
  congr with y
  simp[neg_add_eq_sub]
 calc
  ‖(τ u ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))) -
    (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖
    = ‖∑ y,F y*mu (x+ᵥ -C) y‖:=by rw[x7,hsum]
  _≤ ∑ y, ‖F y*mu (x+ᵥ -C) y‖:=Rq _ _
  _=(aJ 1 (F*mu (x+ᵥ -C))):=by
   rw[ek]
   rfl
  _≤(aJ M F)*(aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=
   yR _ _
  _=_:=by simp[F,M]
private lemma vA
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} {ε:ℝ} (B C:Finset G)
  (hC:C.Nonempty) (u x:G) (q:ℕ) (x9:1≤q)
  (C7 :
   (aJ (2*q) (τ u ((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((indicator B fun _↦(1:_)))))) ≤
    ε/exp 1*(aJ (2*q) (((indicator B fun _↦(1:_)):G→ℂ)))) :
  ‖(τ u ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))) -
   (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/exp 1):=by
 let M:ℕ:=2*q
 have Lu:(M:ℝ≥0)≠0:=by positivity
 have z1:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have hM := S2 z1
 calc
  _

    ≤ (aJ M (τ u ((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((indicator B fun _↦(1:_)))))) *
      (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
     simpa[M] using sZ B C u x q x9
  _≤ε/exp 1* #B^(M:ℝ)⁻¹ *
     (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
   gcongr
   ·exact d8
   have Lv :
     (aJ M (τ u ((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((indicator B fun _↦(1:_)))))) ≤
      ε/exp 1*(aJ M (((indicator B fun _↦(1:_)):G→ℂ))):=by
    simpa only[M,Rm,Nat.cast_ofNat] using C7
   have F7:(aJ M (((indicator B fun _↦(1:_)):G→ℂ)))=(#B:ℝ)^(M:ℝ)⁻¹:=by
    rw[show(M:ℝ≥0∞)=((M:ℝ≥0):ℝ≥0∞) by norm_num,
     n8 Lu]
    norm_num
   rw[←F7]
   exact Lv
  _=ε*(((#C:ℝ)/ #B)^(-(M:ℝ)⁻¹)/exp 1):=by
   rw[←mul_comm_div,rB hM.symm.lt.le hC.neg.vadd_finset,
    card_vadd_finset,card_neg,hM.symm.coe.inv_sub_one,Real.div_rpow,Qo]
   any_goals positivity
   push_cast
   rw[TS,TS, ←Qw,inv_div_inv]
   all_goals positivity
  _=ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/exp 1):=by
   simp[M]
private lemma ss
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} {ε:ℝ} (hε:0<ε) (B C:Finset G)
  (hC:C.Nonempty) (u:G) (q:ℕ) (x9:1≤q)
  (eO:((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤exp 1)
  (C7 :
   (aJ (2*q) (τ u ((aC (mu A) (((indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((indicator B fun _↦(1:_)))))) ≤
    ε/exp 1*(aJ (2*q) (((indicator B fun _↦(1:_)):G→ℂ)))) :
  (aJ (∞) ((τ u ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))) -
   (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 rw[dw]
 refine ciSup_le fun x↦(vA B C hC u x q x9 C7).trans ?_
 refine Sq hε.le ((Q9 (by positivity)).2 ?_)
 exact eO
lemma q7
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty) :
  let q:=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=cQ q (ε/exp 1)
  ∃ T:Finset G,
   T⊆S∧T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (∞) ((τ (t-s) ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))) -
     (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 let m:ℝ:=1+log r⁻¹
 have tc:0<r:=by
  dsimp[r]
  exact lt_min U1 (Rn (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
 have xA:r≤1:=Uv _ _
 have PE:0< m:=by
  have:0≤log r⁻¹:=Qv ((Uw tc).2 xA)
  positivity
 have Hf:1≤⌈m⌉₊:=Nat.one_le_iff_ne_zero.2 (by positivity)
 obtain ⟨T,Ew,uW,ch,hT⟩:=
  vz hA hS ⌈m⌉₊ Hf (ε/exp 1) (by positivity)
   ((indicator B fun _↦(1:_)):G→ℂ)
 refine ⟨T,Ew,uW, ?_, ?_⟩
 ·simpa[r,m] using ch
 ·intro s hs t ht
  apply ss hε B C hC (t-s) ⌈m⌉₊ Hf
   (ua B C hB hC ⌈m⌉₊ (by simp[r,m]))
  simpa[r,m] using hT s hs t ht
lemma mX
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (m:ℕ) (hm:m≠0)
  (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty) :
  let q:=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=cQ q ((ε/m)/exp 1)
  ∃ (T:Finset G) (z:G),
   T⊆S∧z∈T ∧
   (-z+ᵥ T).Nonempty∧(-z+ᵥ T)⊆S-S ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   (aJ (∞) (((aC ((ep (mu (-z+ᵥ T)) m)) (((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))))) -
    (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 have G7:(0:ℝ)< m:=by exact_mod_cast(Nat.pos_iff_ne_zero.2 hm)
 have Cc := Rn hε G7
 obtain ⟨T,Ew,uW,ch,jl⟩:=
  q7 hA hS (ε/(m:ℝ)) Cc B C hB hC
 obtain ⟨z,hz⟩:=uW
 let X := -z+ᵥ T
 have pT:X.Nonempty:=by
  refine ⟨0, ?_⟩
  change 0∈ -z+ᵥ T
  rw[mem_vadd_finset]
  exact ⟨z,hz,by simp⟩
 have F8: ∀ x∈X,
   (aJ (∞) ((τ x ((aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))) -
    (aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε/(m:ℝ):=by
  intro x hx
  change x∈ -z+ᵥ T at hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  have hp:=jl z hz t ht
  simpa[Qy,RV] using hp
 have Lw: -z+ᵥ T⊆S-S:=by
  intro x hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  simpa[Qy,RV] using sub_mem_sub (Ew ht) (Ew hz)
 set F:G→ℂ:=(aC (((aC (mu A) ((indicator B fun _↦(1:_)))))) (mu C))
 refine ⟨T,z,Ew,hz, ?_,Lw, ?_, ?_⟩
 ·simpa[X] using pT
 ·simpa using ch
 ·change(aJ (∞) ((aC ((ep (mu X) m)) F)-F))≤ε
  calc
   _
     = (aJ (∞) (𝔼 a∈(piFinset fun _:Fin m↦X),(τ (∑ i,a i) F-F))):=by
      rw[vJ,expect_sub_distrib,expect_const pT.piFinset_const]
   _≤𝔼 a∈(piFinset fun _:Fin m↦X),(aJ (∞) (τ (∑ i,a i) F-F)):=
    wU le_top
   _≤𝔼 _a∈(piFinset fun _:Fin m↦X),ε:=by
    refine expect_le_expect fun a ha↦ ?_
    calc
     _
       ≤ ∑ i,(aJ (∞) (τ (a i) F-F)):=
        pM le_top _ _ _
     _≤ ∑ _i,ε/(m:ℝ):=by
      gcongr
      simpa[F] using F8 (a _) (Fintype.mem_piFinset.1 ha _)
     _=ε:=by
      simp only[sum_const,card_fin,QS]
      rw[mul_div_cancel₀]
      exact_mod_cast hm
   _=ε:=by rw[expect_const pT.piFinset_const]
end ay
end
section
open AddChar Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
private lemma ub (A:Finset G) (psi:AddChar G ℂ) :
  (∑ x:G,(af A x:ℂ)*psi x) =
   ((A.card:ℂ)⁻¹)*c5.c6 A psi:=by
 classical
 rw[c5.c6,Qj]
 calc
  _ =
    ∑ x:G,if x∈A then ((A.card:ℂ)⁻¹)*psi x else 0:=by
   apply Io rfl
   intro x _
   by_cases hx:x∈A<;>simp[af,hx]
  _= ∑ x∈A,((A.card:ℂ)⁻¹)*psi x:=by
   rw[←QE]
   have eI :
     (Finset.univ.filter fun x:G↦x∈A)=A:=by
    ext x
    simp
   rw[eI]
private lemma pU (A:Finset G)
  (psi:AddChar G ℂ) (t:G) :
  (1-psi t)*(∑ x:G,(af A x:ℂ)*psi x) =
   ∑ x:G,
    ((af A x-af A (x-t):ℝ):ℂ) *
     psi x:=by
 classical
 have kE :
   (∑ x:G,(af A (x-t):ℂ)*psi x) =
    psi t* ∑ x:G,(af A x:ℂ)*psi x:=by
  rw[←(Equiv.addRight t).sum_comp]
  ·change
    (∑ x:G,(af A ((x+t)-t):ℂ)*psi (x+t)) =
     psi t* ∑ x:G,(af A x:ℂ)*psi x
   simp_rw[add_sub_cancel_right,map_add_eq_mul]
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  ·simp
 push_cast
 simp_rw[sub_mul]
 rw[QJ,kE]
 ring
omit [DecidableEq G] in
lemma l8
  {C:aj G} (dF:C.a1) {eta:ℝ} (fC:0<eta)
  {sigma:ℝ≥0}
  (iX:sigma≤1/(100*(max C.rank 1:ℕ):ℝ≥0))
  {psi:AddChar G ℂ} (cT:psi∈c5.cj C.carrier eta)
  {t:G} (ht:t∈(C.ai sigma).carrier) :
  ‖1-psi t‖ ≤
   200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ)/eta:=by
 classical
 let F :=  ∑ x:G,(af C.carrier x:ℂ)*psi x
 have ch:(0:ℝ)<C.carrier.card:=by
  exact_mod_cast C.aE.card_pos
 have JL: ‖F‖ = ‖c5.c6 C.carrier psi‖ /C.carrier.card:=by
  dsimp[F]
  rw[ub,QO]
  simp[Ri]
 have iU:eta≤ ‖F‖:=by
  rw[JL,Qs ch]
  exact c5.gm.mp cT
 have l7 :
   ‖1-psi t‖ * ‖F‖ ≤
    ∑ x:G,
     |af C.carrier (x-t) -
      af C.carrier x|:=by
  rw[←QO,pU C.carrier psi t]
  calc
   _

                                       ≤
     ∑ x:G,
      ‖((af C.carrier x -
        af C.carrier (x-t):ℝ):ℂ)*psi x‖:=
    Rq _ _
   _= ∑ x:G,
     |af C.carrier (x-t) -
      af C.carrier x|:=by
    apply Io rfl
    intro x _
    rw[QO]
    rw[Rf,QK,Su]
    simp
 have AI:=
  aj.cN
   dF iX ht
 have hmul :
   ‖1-psi t‖ *eta ≤
    200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
  calc
   _ ≤ ‖1-psi t‖ * ‖F‖:=
    iO iU (Re _)
   _≤ ∑ x:G,
     |af C.carrier (x-t) -
      af C.carrier x|:=l7
   _≤200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=AI
 exact(Qs fC).2 hmul
omit [DecidableEq G] in
lemma kl
  {C:aj G} (dF:C.a1) {sigma:ℝ≥0}
  (iX:sigma≤1/(100*(max C.rank 1:ℕ):ℝ≥0))
  {psi:AddChar G ℂ} (cT:psi∈c5.cj C.carrier (1/2))
  {t:G} (ht:t∈(C.ai sigma).carrier) :
  ‖1-psi t‖ ≤400*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 have h:=l8 dF (eta:=(1/2:ℝ))
  (by norm_num) iX cT ht
 convert h using 1
 ring
end
end ay
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
def eV (mu:G→ℝ) (K:ℝ)
  (Delta:Finset (AddChar G ℂ)):Prop:=
 ∀ u:AddChar G ℂ→ℂ,
  (∀ psi∈Delta, ‖u psi‖ ≤1) →
   ∑ x:G,mu x *
    ∏ psi∈Delta,(1+(u psi*psi x).re)≤exp K
def fP (mu f:G→ℝ) (eta:ℝ) :
  Finset (AddChar G ℂ):=
  Finset.univ.filter fun psi ↦
  eta*(∑ x:G,f x*mu x) ≤
   ‖∑ x:G,(f x*mu x:ℝ)*psi x‖
@[simp] lemma lQ {mu f:G→ℝ} {eta:ℝ}
  {psi:AddChar G ℂ} :
  psi∈fP mu f eta ↔
   eta*(∑ x:G,f x*mu x) ≤
    ‖∑ x:G,(f x*mu x:ℝ)*psi x‖:=by
 simp[fP]
end ay.aI
end
end
section
noncomputable section
open Finset Real
open scoped BigOperators ComplexConjugate
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
def cy (S Delta:Finset (AddChar G ℂ)):Prop:=
 ∀ t u:Finset (AddChar G ℂ),t⊆Delta→u⊆Delta →
  Disjoint t u→(t∪u).Nonempty →
   (∑ psi∈t,psi)- ∑ psi∈u,psi∉S
omit [Fintype G] in
lemma s0 (S:Finset (AddChar G ℂ)) :
  cy S ∅:=by
 intro t u ht hu x3 vH
 simp only[Finset.subset_empty] at ht hu
 subst t
 subst u
 simp at vH
omit [Fintype G] in
lemma cy.mono {S:Finset (AddChar G ℂ)}
  {Delta Gamma:Finset (AddChar G ℂ)}
  (h:cy S Delta) (l4:Gamma⊆Delta) :
  cy S Gamma:=by
 intro t u ht hu
 exact h t u (ht.trans l4) (hu.trans l4)
omit [Fintype G] in
lemma nT [Finite G]
  (S T:Finset (AddChar G ℂ))
  (hzero:0∈S)
  (hS: ∀ s,s∈S→ -s∈S) :
  ∃ Delta:Finset (AddChar G ℂ),
   Delta⊆T∧cy S Delta ∧
    ∀ psi∈T, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 let candidates:=T.powerset.filter (cy S)
 have BL:candidates.Nonempty:=by
  refine ⟨∅, ?_⟩
  simp[candidates,s0]
 obtain ⟨Delta,C8,C9⟩:=candidates.exists_maximal BL
 have dQ:=Finset.mem_filter.mp C8
 refine ⟨Delta,Finset.mem_powerset.mp dQ.1,dQ.2, ?_⟩
 intro psi Lx
 by_cases zm:psi∈Delta
 ·exact ⟨psi,Finset.subset_addSpan zm,0,hzero,by simp⟩
 ·have y3 :=
   Finset.insert_subset Lx (Finset.mem_powerset.mp dQ.1)
  have hnot: ¬ cy S (insert psi Delta):=by
   intro Ng
   have BM:insert psi Delta∈candidates:=by
    simp[candidates,y3,Ng]
   have l4:=C9 BM (Finset.subset_insert psi Delta)
   exact zm (l4 (Finset.mem_insert_self psi Delta))
  rw[cy] at hnot
  push Not at hnot
  obtain ⟨t,u,ht,hu,x3,vH,Da⟩:=hnot
  have Cl:psi∈t∪u:=by
   by_contra cT
   have rX:t⊆Delta:=by
    intro a ha
    have mS:=ht ha
    rw[Rp] at mS
    exact mS.resolve_left (fun h↦cT (h▸Um u ha))
   have y4:u⊆Delta:=by
    intro a ha
    have mS:=hu ha
    rw[Rp] at mS
    exact mS.resolve_left (fun h↦cT (h▸Ua t ha))
   exact dQ.2 t u rX y4 x3 vH Da
  rw[Finset.mem_union] at Cl
  rcases Cl with Ex | Ey
  ·have Db:psi∉u:=fun h↦Finset.disjoint_left.mp x3 Ex h
   have HM:t.erase psi⊆Delta:=by
    intro a ha
    have mS:=ht (Sm ha)
    rw[Rp] at mS
    exact mS.resolve_left (Sw ha)
   have y4:u⊆Delta:=by
    intro a ha
    have mS:=hu ha
    rw[Rp] at mS
    exact mS.resolve_left (fun h↦Db (h▸ha))
   let z:=(∑ a∈u,a)- ∑ a∈t.erase psi,a
   have hz :=
          Tp y4 HM
   refine ⟨z,hz,(∑ a∈t,a)- ∑ a∈u,a,Da, ?_⟩
   dsimp[z]
   rw[←SO _ _ Ex]
   abel
  ·have Dc:psi∉t:=fun h↦Finset.disjoint_left.mp x3 h Ey
   have HN:u.erase psi⊆Delta:=by
    intro a ha
    have mS:=hu (Sm ha)
    rw[Rp] at mS
    exact mS.resolve_left (Sw ha)
   have rX:t⊆Delta:=by
    intro a ha
    have mS:=ht ha
    rw[Rp] at mS
    exact mS.resolve_left (fun h↦Dc (h▸ha))
   let z:=(∑ a∈t,a)- ∑ a∈u.erase psi,a
   have hz :=
          Tp rX HN
   let s:=-((∑ a∈t,a)- ∑ a∈u,a)
   have hs := hS _ Da
   refine ⟨z,hz,s,hs, ?_⟩
   dsimp[z,s]
   rw[←SO _ _ Ey]
   abel
private def fq (t u:Finset (AddChar G ℂ)):AddChar G ℂ:=
 (∑ psi∈u,psi)- ∑ psi∈t \ u,psi
private def el (v:AddChar G ℂ→ℂ)
  (t u:Finset (AddChar G ℂ)):ℂ:=
 ((∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)) /
  (2:ℂ)^t.card
omit [Fintype G] in
private lemma oi [Finite G]
  (Delta:Finset (AddChar G ℂ)) (v:AddChar G ℂ→ℂ) (x:G) :
  ∏ psi∈Delta,((1+(v psi*psi x).re:ℝ):ℂ) =
   ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    el v t u*fq t u x:=by
 let:=Fintype.ofFinite G
 calc
  ∏ psi∈Delta,((1+(v psi*psi x).re:ℝ):ℂ) =
    ∏ psi∈Delta,
     (((v psi*psi x)+conj (v psi*psi x))/2+1):=by
   apply Finset.prod_congr rfl
   intro psi cT
   rw[RV, ←Complex.re_eq_add_conj]
   push_cast
   rfl
  _= ∑ t∈Delta.powerset,
    ∏ psi∈t,((v psi*psi x)+conj (v psi*psi x))/2:=by
   rw[Finset.prod_add]
   simp
  _= ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    el v t u*fq t u x:=by
   apply Io rfl
   intro t ht
   rw[Finset.prod_div_distrib]
   rw[Finset.prod_add]
   rw[TP]
   apply Io rfl
   intro u hu
   rw[el,fq]
   simp only[AddChar.sum_apply,RO,
    TV]
   simp only[Finset.prod_const]
   simp_rw[RU,TW]
   rw[map_prod]
   ring
private lemma nU
  (w:G→ℝ) (Delta:Finset (AddChar G ℂ))
  (v:AddChar G ℂ→ℂ) :
  ((∑ x:G,w x *
    ∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ) =
   ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    el v t u *
     ay.cG w (fq t u):=by
 simp_rw[Complex.ofReal_prod]
 simp_rw[oi]
 simp_rw[Qj]
 rw[QD]
 apply Io rfl
 intro t ht
 rw[QD]
 apply Io rfl
 intro u hu
 rw[ay.cG,Qj]
 apply Io rfl
 intro x hx
 ring
omit [Fintype G] in
private lemma s3
  {S Delta t u:Finset (AddChar G ℂ)}
  (dQ:cy S Delta)
  (ht:t⊆Delta) (JM:t.Nonempty) (hu:u⊆t) :
  fq t u∉S:=by
 apply dQ u (t \ u)
 ·exact hu.trans ht
 ·exact Finset.sdiff_subset.trans ht
 ·rw[Finset.disjoint_left]
  intro psi Ly JN
  exact(Finset.mem_sdiff.mp JN).2 Ly
 ·simpa[Finset.union_sdiff_of_subset hu] using JM
omit [Fintype G] in
private lemma rF
  {v:AddChar G ℂ→ℂ} {t u:Finset (AddChar G ℂ)}
  (hu:u⊆t) (hv: ∀ psi∈t, ‖v psi‖ ≤1) :
  ‖el v t u‖ ≤((2:ℝ)^t.card)⁻¹:=by
 have OM: ‖∏ psi∈u,v psi‖ ≤1:=by
  rw[norm_prod]
  exact UO (fun psi cT↦Re _)
   (fun psi cT↦hv psi (hu cT))
 have Nh: ‖∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[norm_prod]
  exact UO (fun psi cT↦Re _)
   (fun psi cT↦by
    rw[RCLike.norm_conj]
    exact hv psi (Finset.sdiff_subset cT))
 have kG :
   ‖(∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[QO]
  calc
   _≤1*1:=QW OM Nh (Re _) (by norm_num)
   _=1:=by norm_num
 rw[el,norm_div]
 calc
  _≤1/ ‖(2:ℂ)^t.card‖:=
   Qz kG (Re _)
  _=((2:ℝ)^t.card)⁻¹:=by
   rw[norm_pow]
   norm_num
lemma cy.oj
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ}
  (dQ:cy S Delta)
  (_hw0: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (xZ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (v:AddChar G ℂ→ℂ) (hv: ∀ psi∈Delta, ‖v psi‖ ≤1) :
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re) ≤
   1+q*(2:ℝ)^Delta.card:=by
 classical
 let F:Finset (AddChar G ℂ)→ℂ:=fun t ↦
  ∑ u∈t.powerset,el v t u *
   ay.cG w (fq t u)
 let E :=  ∑ t∈Delta.powerset.erase ∅,F t
 have su:(∅:Finset (AddChar G ℂ))∈Delta.powerset:=by simp
 have Ni: ∑ x:G,(w x:ℂ)=1:=by exact_mod_cast AJ
 have HO:F ∅=1:=by
  simp[F,el,fq,ay.cG,Ni]
 have l9 :
   ((∑ x:G,w x *
     ∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ)=1+E:=by
  rw[nU]
  rw[←SO _ _ su]
  simp only[HO,E,F]
  ring
 have oJ (t:Finset (AddChar G ℂ))
   (ht:t∈Delta.powerset.erase ∅): ‖F t‖ ≤q:=by
  have rX := Finset.mem_powerset.mp (Sm ht)
  have JM := Finset.nonempty_iff_ne_empty.mpr (Sw ht)
  calc
   _ ≤ ∑ u∈t.powerset,
     ‖el v t u *
      ay.cG w (fq t u)‖:=by
    exact Rq _ _
   _≤ ∑ _u∈t.powerset,((2:ℝ)^t.card)⁻¹ *q:=by
    apply QI
    intro u hu
    rw[QO]
    apply QW
    ·exact rF (Finset.mem_powerset.mp hu)
      (fun psi cT↦hv psi (rX cT))
    ·exact hq _ (s3 dQ rX JM
      (Finset.mem_powerset.mp hu))
    ·exact Re _
    ·exact inv_nonneg.mpr (QH (by norm_num) _)
   _=q:=by
    rw[Tq,Ux]
    simp[QS]
 have JO: ‖E‖ ≤q*(2:ℝ)^Delta.card:=by
  calc
   _ ≤ ∑ t∈Delta.powerset.erase ∅, ‖F t‖:=Rq _ _
   _≤ ∑ _t∈Delta.powerset.erase ∅,q:=
          QI fun t ht↦oJ t ht
   _≤ ∑ _t∈Delta.powerset,q:=
          Ry (Finset.erase_subset _ _)
     (fun _ _ _↦xZ)
   _=q*(2:ℝ)^Delta.card:=by
    simp[Ux]
    ring
 let R :=
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re)
 have Lz:(R:ℂ)=1+E:=by
  calc
   _ = ∑ x:G,(w x:ℂ) *
     (↑(∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ):=by
    dsimp[R]
    push_cast
    rfl
   _=1+E:=l9
 have JP:R=1+E.re:=by
  have:=QA Complex.re Lz
  simpa using this
 change R≤1+q*(2:ℝ)^Delta.card
 calc
  R=1+E.re:=JP
  _≤1+ ‖E‖:=Sr (le_refl 1) (Complex.re_le_norm E)
  _≤1+q*(2:ℝ)^Delta.card:=Sr (le_refl 1) JO
lemma cy.uc
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (dQ:cy S Delta)
  (vq: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (xZ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (ch:Delta.card≤k) (ON:q*(2:ℝ)^k≤1) :
  eV w 1 Delta:=by
 intro v hv
 have HP:2^Delta.card≤2^k:=
  QR (by norm_num) ch
 have hpow:(2:ℝ)^Delta.card≤(2:ℝ)^k:=by
  exact_mod_cast HP
 have uX:q*(2:ℝ)^Delta.card≤1:=
  (iO hpow xZ).trans ON
 calc
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re) ≤
    1+q*(2:ℝ)^Delta.card:=
   dQ.oj vq AJ xZ hq v hv
  _≤2:=by linarith
  _≤exp 1:=Real.exp_one_gt_two.le
lemma cy.k4
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (dQ:cy S Delta)
  (vq: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (xZ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (ch:Delta.card≤k) (Dd:q≤(1/4:ℝ)^k) :
  eV w 1 Delta:=by
 apply dQ.uc vq AJ xZ hq ch
 calc
  _ ≤(1/4:ℝ)^k*(2:ℝ)^k:=
   Qi Dd (QH (by norm_num) _)
  _=(1/2:ℝ)^k:=by rw[←QL]; congr 1; norm_num
  _≤1:=Uy (by norm_num) (by norm_num)
lemma nm (A:Finset G) :
  (0:AddChar G ℂ)∈ay.c5.cj A (1/2:ℝ):=by
 rw[ay.c5.gm]
 simp[ay.c5.c6]
 have ch:(0:ℝ)≤A.card:=by exact_mod_cast Nat.zero_le A.card
 nlinarith
lemma ku {A:Finset G} {eta:ℝ}
  {psi:AddChar G ℂ}
  (cT:psi∈ay.c5.cj A eta) :
  -psi∈ay.c5.cj A eta:=by
 rw[ay.c5.gm] at cT ⊢
 have hsum:ay.c5.c6 A (-psi) =
   conj (ay.c5.c6 A psi):=by
  unfold ay.c5.c6
  rw[RK]
  apply Io rfl
  intro x hx
  rw[U2,TV]
 rw[hsum,RCLike.norm_conj]
 exact cT
end ay.aI
end
end
section
open Finset
open scoped BigOperators
namespace ay.jO
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
omit [AddCommGroup G] in
lemma f2
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) :
  ∑ x:G,bs X x*w x=c*X.card:=by
 classical
 calc
  _ = ∑ x∈X,c:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[bs,hx,hw x (ud hx)]
   ·simp
   ·intro x MH He
    simp[bs,He]
  _=c*X.card:=by simp[Qx]
lemma jg
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (psi:AddChar G ℂ) :
  ∑ x:G,((bs X x*w x:ℝ):ℂ)*psi x =
   (c:ℂ)*c5.c6 X psi:=by
 classical
 calc
  _ =
    ∑ x∈X,(c:ℂ)*psi x:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[bs,hx,hw x (ud hx)]
   ·simp
   ·intro x MH He
    simp[bs,He]
  _=(c:ℂ)*c5.c6 X psi:=by
   rw[c5.c6,Qj]
lemma km
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (hc:0<c)
  (eta:ℝ) (psi:AddChar G ℂ) :
  psi∈aI.fP w (bs X) eta ↔
   psi∈c5.cj X eta:=by
 classical
 rw[aI.lQ,c5.gm]
 rw[f2 ud hw]
 rw[jg ud hw]
 rw[QO,Rf,QK,RT hc]
 constructor
 ·intro h
  have hh:c*(eta*(X.card:ℝ)) ≤
    c* ‖c5.c6 X psi‖:=by
   calc
    _ =eta*(c*(X.card:ℝ)):=by ring
    _≤c* ‖c5.c6 X psi‖:=h
  nlinarith
 ·intro h
  calc
   _ =c*(eta*(X.card:ℝ)):=by ring
   _≤c* ‖c5.c6 X psi‖:=
    iO h hc.le
end ay.jO
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
omit [AddCommGroup G] in
lemma j6
  (w:G→ℝ) (hw: ∀ x,0≤w x) (AK: ∑ x:G,w x=1)
  (f:G→ℝ) :
  exp (∑ x:G,w x*f x)≤ ∑ x:G,w x*exp (f x):=by
 have h:=convexOn_exp.map_sum_le (t:=(Finset.univ:Finset G))
  (p:=f) (fun x _↦hw x) (by simpa using AK)
  (fun x _↦Set.mem_univ (f x))
 simpa using h
lemma s4
  (mu:G→ℝ) (K:ℝ) (Delta:Finset (AddChar G ℂ))
  (AL: ∀ x,0≤ mu x)
  (dQ:eV mu K Delta)
  (c:AddChar G ℂ→ℂ) :
  ∑ x:G,mu x*exp ((∑ psi∈Delta,c psi*psi x).re) ≤
   exp (K+(∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
 have l9 (z:ℂ) :
   exp z.re≤cosh ‖z‖ +(z/ ‖z‖).re*sinh ‖z‖:=by
  calc
   _=exp ((z/ ‖z‖).re* ‖z‖):=by
    obtain rfl | hz:=Tf z 0<;>simp[*]
   _≤_:=exp_mul_le_cosh_add_mul_sinh
    (by simpa using z.abs_re_div_norm_le_one) _
 choose u hu OO using fun psi↦Complex.exists_norm_mul_eq_self (c psi)
 have Jw (psi:AddChar G ℂ):u psi≠0:=fun h↦by
  simpa[h] using hu psi
 have gX (x:G) :
   exp ((∑ psi∈Delta,c psi*psi x).re) ≤
    ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
  calc
   exp ((∑ psi∈Delta,c psi*psi x).re) =
     ∏ psi∈Delta,exp ((c psi*psi x).re):=by
      simp_rw[←exp_sum, ←Complex.re_sum]
   _≤ ∏ psi∈Delta,
     (cosh ‖c psi*psi x‖ +
      ((c psi*psi x)/ ‖c psi*psi x‖).re *
       sinh ‖c psi*psi x‖):=by
    gcongr with psi cT
    exact l9 _
   _= ∏ psi∈Delta,
     (cosh ‖c psi‖ +
      (u psi*(c psi*psi x)/(u psi* ↑‖c psi‖)).re *
       sinh ‖c psi‖):=by
    apply prod_congr rfl
    intro psi cT
    rw[QO,Q0,Q3,
     mul_div_mul_left _ _ (Jw psi)]
   _= ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
    apply prod_congr rfl
    intro psi cT
    obtain hc | hc:=Tf (c psi) 0
    ·simp[hc]
    simp only[OO,Q6 (u psi),SH _ hc,
     ←Complex.re_mul_ofReal,QN]
 let q:AddChar G ℂ→ℝ:=fun psi↦sinh ‖c psi‖ /cosh ‖c psi‖
 let v:AddChar G ℂ→ℂ:=fun psi↦(q psi:ℂ)*u psi
 have oc (x:G) :
   (∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re)) =
    (∏ psi∈Delta,cosh ‖c psi‖) *
     (∏ psi∈Delta,
      (1+(v psi*psi x).re)):=by
  rw[←TW]
  apply prod_congr rfl
  intro psi cT
  have PF:cosh ‖c psi‖ ≠0:=Uq (cosh_pos _)
  have F9 :
    (u psi*(sinh ‖c psi‖ :ℂ)*psi x).re =
     sinh ‖c psi‖ *(u psi*psi x).re:=by
   rw[show u psi*(sinh ‖c psi‖ :ℂ)*psi x =
     (sinh ‖c psi‖ :ℂ)*(u psi*psi x) by ring]
   exact Un _ _
  have LA:(v psi*psi x).re=q psi*(u psi*psi x).re:=by
   rw[show v psi*psi x=(q psi:ℂ)*(u psi*psi x) by
    simp[v]; ring]
   exact Un _ _
  rw[F9,LA]
  dsimp[q]
  field_simp
 calc
  ∑ x:G,mu x*exp ((∑ psi∈Delta,c psi*psi x).re) ≤
    ∑ x:G,mu x* ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
   apply sum_le_sum
   intro x hx
   exact iO (gX x) (AL x)
  _=(∏ psi∈Delta,cosh ‖c psi‖) *
    (∑ x:G,mu x *
     ∏ psi∈Delta,
      (1+(v psi*psi x).re)):=by
   rw[Qj]
   apply sum_congr rfl
   intro x hx
   rw[oc]
   ring
  _≤(∏ psi∈Delta,cosh ‖c psi‖)*exp K:=by
   gcongr
   apply dQ v
   intro psi cT
   have hq: |q psi| ≤1:=by
    simpa[q,Real.tanh_eq_sinh_div_cosh] using(Real.abs_tanh_lt_one ‖c psi‖).le
   simpa[v,QO,hu psi,Rf,QK] using hq
  _≤exp ((∑ psi∈Delta, ‖c psi‖ ^2)/2)*exp K:=by
   apply Qi _ (exp_pos _).le
   calc
    ∏ psi∈Delta,cosh ‖c psi‖ ≤
      ∏ psi∈Delta,exp (‖c psi‖ ^2/2):=by
     gcongr with psi cT
     exact cosh_le_exp_half_sq _
    _=exp ((∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
     simp_rw[←exp_sum, ←sum_div]
  _=exp (K+(∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
   rw[←exp_add]
   congr 1
   ring
lemma iQ
  (mu f:G→ℝ) (K eta:ℝ) (Delta:Finset (AddChar G ℂ))
  (AL: ∀ x,0≤ mu x) (OP: ∀ x,0≤f x)
  (Jc: ∀ x,f x≤1)
  (fC:0<eta)
  (dQ:eV mu K Delta)
  (l4:Delta⊆fP mu f eta)
  (ft:0< ∑ x:G,f x*mu x) :
  (Delta.card:ℝ) ≤
   2*(K+log ((∑ x:G,f x*mu x)⁻¹))/eta^2:=by
 let a :=  ∑ x:G,f x*mu x
 have ha:0<a:=by simpa[a] using ft
 let spec:AddChar G ℂ→ℂ:=fun psi ↦
  ∑ x:G,(f x*mu x:ℝ)*psi x
 choose u hu JQ using fun psi:AddChar G ℂ ↦
  Complex.exists_norm_eq_mul_self (spec psi)
 let c:AddChar G ℂ→ℂ:=fun psi↦(eta:ℂ)*u psi
 let P:G→ℝ:=fun x↦(∑ psi∈Delta,c psi*psi x).re
 have HQ (psi:AddChar G ℂ): ‖c psi‖ ^2=eta^2:=by
  simp[c,hu,RT fC]
 have LB: ∑ psi∈Delta, ‖c psi‖ ^2=eta^2*Delta.card:=by
  simp_rw[HQ]
  simp
  ring
 have Ga :
   ∑ x:G,((f x*mu x:ℝ):ℂ) *
     (∑ psi∈Delta,c psi*psi x) =
    (eta:ℂ)* ∑ psi∈Delta,(‖spec psi‖ :ℂ):=by
  calc
   _
                               =
     ∑ psi∈Delta,
      c psi* ∑ x:G,((f x*mu x:ℝ):ℂ)*psi x:=by
    simp_rw[Qj]
    rw[QD]
    apply sum_congr rfl
    intro psi cT
    apply sum_congr rfl
    intro x hx
    ring
   _= ∑ psi∈Delta,(eta:ℂ)*(‖spec psi‖ :ℂ):=by
    apply sum_congr rfl
    intro psi cT
    dsimp[c,spec]
    rw[Qo, ←JQ]
   _=(eta:ℂ)* ∑ psi∈Delta,(‖spec psi‖ :ℂ):=by
    rw[Qj]
 have JR :
   ∑ x:G,f x*mu x*P x =
    eta* ∑ psi∈Delta, ‖spec psi‖:=by
  have JP:=QA Complex.re Ga
  calc
   _ =
     (∑ x:G,((f x*mu x:ℝ):ℂ) *
      (∑ psi∈Delta,c psi*psi x)).re:=by
    simp[P,Complex.re_sum,Complex.mul_re]
   _=((eta:ℂ) *
     ∑ psi∈Delta,(‖spec psi‖ :ℂ)).re:=JP
   _=eta* ∑ psi∈Delta, ‖spec psi‖:=by simp
 have BN :
   eta^2*a*Delta.card≤ ∑ x:G,f x*mu x*P x:=by
  rw[JR]
  calc
   _ =
     ∑ psi∈Delta,eta*(eta*a):=by
    simp
    ring
   _≤ ∑ psi∈Delta,eta* ‖spec psi‖:=by
    gcongr with psi cT
    have hs:=lQ.mp (l4 cT)
    simpa[a,spec] using hs
   _=eta* ∑ psi∈Delta, ‖spec psi‖:=by
    rw[Qj]
 let w:G→ℝ:=fun x↦f x*mu x/a
 have vq: ∀ x,0≤w x:=by
  intro x
  exact RS (Qn (OP x) (AL x)) ha.le
 have AK: ∑ x:G,w x=1:=by
  dsimp[w]
  rw[←TP]
  dsimp[a]
  exact div_self ha.ne'
 have HR:eta^2*Delta.card≤ ∑ x:G,w x*P x:=by
  calc
   _ ≤
     (∑ x:G,f x*mu x*P x)/a:=by
    rw[Qs ha]
    calc
     _ =
       eta^2*a*(Delta.card:ℝ):=by ring
     _≤_:=BN
   _= ∑ x:G,w x*P x:=by
    dsimp[w]
    rw[TP]
    apply sum_congr rfl
    intro x hx
    ring
 have HS :
   exp (eta^2*Delta.card) ≤
    ∑ x:G,w x*exp (P x):=by
  calc
   _ ≤exp (∑ x:G,w x*P x):=
          Real.exp_le_exp.mpr HR
   _≤_:=j6 w vq AK P
 have AM :
   ∑ x:G,w x*exp (P x) ≤
    a⁻¹ * ∑ x:G,mu x*exp (P x):=by
  dsimp[w]
  rw[Qj]
  apply sum_le_sum
  intro x hx
  rw[Ri]
  calc
   _ ≤
     a⁻¹ *(1*mu x)*exp (P x):=by
    apply Qi _ (exp_pos _).le
    apply iO _ (inv_nonneg.mpr ha.le)
    exact Qi (Jc x) (AL x)
   _=a⁻¹ *(mu x*exp (P x)):=by ring
 have JS :
   ∑ x:G,mu x*exp (P x) ≤
    exp (K+eta^2*Delta.card/2):=by
  have hr:=s4 mu K Delta AL dQ c
  simpa[P,LB] using hr
 have ue  :=

  HS.trans (AM.trans
   (iO JS (inv_nonneg.mpr ha.le)))
 have hmul :
   a*exp (eta^2*Delta.card) ≤
    exp (K+eta^2*Delta.card/2):=by
  calc
   _ ≤
     a*(a⁻¹ *exp (K+eta^2*Delta.card/2)):=by
    gcongr
   _=exp (K+eta^2*Delta.card/2):=by
    field_simp
 have Cd :
   log a+eta^2*Delta.card ≤
    K+eta^2*Delta.card/2:=by
  rw[←exp_log ha, ←exp_add] at hmul
  exact Real.exp_le_exp.mp hmul
 have HT := SY fC
 rw[Qs HT]
 rw[log_inv]
 nlinarith
lemma jW
  (B X:Finset G) (ud:X⊆B) (hX:X.Nonempty)
  (w:G→ℝ) (c R eta:ℝ)
  (vq: ∀ x,0≤w x) (hw: ∀ x∈B,w x=c)
  (hc:0<c) (hR:(c*X.card)⁻¹ ≤R)
  (fC:0<eta) (Delta:Finset (AddChar G ℂ))
  (dQ:eV w 1 Delta)
  (l4:Delta⊆c5.cj X eta) :
  (Delta.card:ℝ)≤2*(1+log R)/eta^2:=by
 classical
 have AN  :=

  jO.f2 ud hw
 have ft:0< ∑ x:G,bs X x*w x:=by
  rw[AN]
  have Et:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
  positivity
 have LD:Delta ⊆
   fP w (bs X) eta:=by
  intro psi cT
  exact(jO.km
   ud hw hc eta psi).2 (l4 cT)
 have oQ:=iQ
  w (bs X) 1 eta Delta vq
  (by intro x; unfold bs; split<;>norm_num)
  (by intro x; unfold bs; split<;>norm_num)
  fC dQ LD ft
 have Gb :
   ((∑ x:G,bs X x*w x)⁻¹)≤R:=by
  simpa[AN] using hR
 have ei  :=

  QG (inv_pos.mpr ft) Gb
 calc
  _ ≤
    2*(1+log ((∑ x:G,bs X x*w x)⁻¹)) /
     eta^2:=by simpa using oQ
  _≤2*(1+log R)/eta^2:=by
   gcongr
omit [Fintype G] in
lemma om [Finite G]
  (S T:Finset (AddChar G ℂ)) (hzero:0∈S)
  (eY: ∀ s∈S, -s∈S) (D:ℝ) (k:ℕ)
  (JT:D<k)
  (oQ: ∀ Gamma,Gamma⊆T→cy S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D) :
  ∃ Delta:Finset (AddChar G ℂ),
   Delta⊆T∧(Delta.card:ℝ)≤D ∧
    ∀ psi∈T, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 obtain ⟨Delta,uf,zn,j7⟩:=
  nT S T hzero eY
 have fH:Delta.card≤k:=by
  by_contra hnot
  have HU := Nat.le_of_not_ge hnot
  obtain ⟨Gamma,w6,rG⟩:=
   Finset.exists_subset_card_eq HU
  have zo:= oQ Gamma (w6.trans uf)
   (zn.mono w6) (by simp[rG])
  rw[rG] at zo
  exact(not_le_of_gt JT) zo
 exact ⟨Delta,uf,oQ Delta uf zn fH,j7⟩
def bf (B:aj G) (X:Finset G) (eta:ℝ):ℝ:=
 2*(1+log (2*(B.carrier.card:ℝ)/X.card))/eta^2
def dg (B:aj G) (X:Finset G) (eta:ℝ):ℕ:=
 ⌈bf B X eta⌉₊+1
def cJ (B:aj G) (X:Finset G)
  (eta:ℝ):NNReal:=
 (100*((max B.rank 1:ℕ):NNReal) *
  (((2*dg B X eta+1:ℕ):NNReal)))⁻¹
lemma mY
  (B:aj G) (rH:B.a1)
  (X:Finset G) (hX:X.Nonempty) (ud:X⊆B.carrier)
  (eta:ℝ) (fC:0<eta) :
  ∃ a8:NNReal, ∃ C:aj G,
   ∃ Delta:Finset (AddChar G ℂ),
    1/2≤a8∧a8≤1 ∧
    C=B.ai (a8*cJ B X eta) ∧
    C.a1 ∧
    (Delta.card:ℝ)≤bf B X eta ∧
    Delta⊆c5.cj X eta ∧
    ∀ psi∈c5.cj X eta,
     ∃ z∈Delta.addSpan,
      ∃ s∈c5.cj C.carrier (1/2),psi=z+s:=by
 classical
 let D := bf B X eta
 let k := dg B X eta
 let d := max B.rank 1
 let a := cJ B X eta
 obtain ⟨a8,gJ,lj,xv⟩:=
  (B.ai a).eP
 let tau := a8*a
 let C := B.ai tau
 have td:C.a1:=by
  simpa[C,tau] using xv
 have hd:0<d:=by simp[d]
 have hk:0<k:=by simp[k,dg]
 have ha:a =
   (100*(d:NNReal)*(((2*k+1:ℕ):NNReal)))⁻¹:=by
  simp[a,cJ,d,k]
 have dV:(((2*k:ℕ):NNReal)*tau) ≤
   1/(100*(d:NNReal)):=by
  have LF:(0:NNReal)<(((2*k+1:ℕ):NNReal)):=by positivity
  have Oj:(0:NNReal)<100*(d:NNReal):=by positivity
  calc
   _ =
     ((2*k:ℕ):NNReal)*(a8*a):=rfl
   _≤((2*k:ℕ):NNReal)*(1*a):=by gcongr
   _=(((2*k:ℕ):NNReal) /
     (((2*k+1:ℕ):NNReal))) /
      (100*(d:NNReal)):=by rw[ha]; field_simp
   _≤1/(100*(d:NNReal)):=by
    gcongr
    exact(Q9 LF).2 (by
     exact_mod_cast Nat.le_add_right (2*k) 1)
 let T := c5.cj X eta
 let S :=
  c5.cj C.carrier (1/2)
 let w := ay.ed B tau (2*k)
 let outer:Finset G:=
  (B.ai (1+(((2*k:ℕ):NNReal)*tau))).carrier
 let c:ℝ:=(outer.card:ℝ)⁻¹
 let R:ℝ:=2*(B.carrier.card:ℝ)/X.card
 have vq: ∀ x,0≤w x:=by
  intro x
  exact ay.qz B tau (2*k) x
 have AJ :=
        ay.sn B tau (2*k)
 have HV: ∀ x∈B.carrier,w x=c:=by
  intro x hx
  simpa[w,c,outer] using
   (ay.nh B tau (2*k) hx)
 have De:outer.card≤2*B.carrier.card:=by
  simpa[outer,d] using
   (ay.oM rH (2*k) dV)
 have Ez :=
        outer.card_pos.mpr (by
   simpa[outer] using
    (B.ai (1+(((2*k:ℕ):NNReal)*tau))).aE)
 have hc:0<c:=by
  dsimp[c]
  positivity
 have hR:(c*X.card)⁻¹ ≤R:=by
  have hOr:(0:ℝ)<outer.card:=by exact_mod_cast Ez
  have OQ:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
  have Nj:(outer.card:ℝ)≤2*B.carrier.card:=by
   exact_mod_cast De
  calc
   _ =(outer.card:ℝ)/X.card:=by
    dsimp[c]
    field_simp
   _≤(2*B.carrier.card:ℝ)/X.card:=
    (R9 OQ).2 Nj
   _=R:=by simp[R]
 have hzero :=
        nm C.carrier
 have eY: ∀ s∈S, -s∈S:=by
  intro s hs
  exact ku hs
 have JT:D<(k:ℝ):=by
  calc
   D≤(⌈D⌉₊:ℝ):=Rr D
   _<((⌈D⌉₊+1:ℕ):ℝ):=by
    exact_mod_cast Tr ⌈D⌉₊
   _=(k:ℝ):=by simp[k,dg,D]
 have oQ: ∀ Gamma,Gamma⊆T→cy S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D:=by
  intro Gamma HW EA rG
  have hq: ∀ psi,psi∉S →
    ‖ay.cG w psi‖ ≤(1/2:ℝ)^(2*k):=by
   intro psi cT
   calc
    _ ≤
      ‖ay.cG
       (af (B.ai tau).carrier) psi‖ ^(2*k):=
           ay.ly
      B tau (2*k) psi
    _≤(1/2:ℝ)^(2*k):=by
     gcongr
     exact(ay.fy
      (B.ai tau) psi (by simpa[S,C] using cT)).le
  have qy:eV w 1 Gamma:=by
   apply EA.k4
    vq AJ (by positivity) hq rG
   rw[QU]
   norm_num
  have ch:=jW
   B.carrier X ud hX w c R eta vq HV hc hR fC Gamma
    qy (by simpa[T] using HW)
  simpa[D,bf,R] using ch
 obtain ⟨Delta,uf,fH,j7⟩:=
  om S T hzero eY D k JT oQ
 refine ⟨a8,C,Delta,gJ,lj, ?_,td, ?_, ?_, ?_⟩
 ·simp[C,tau,a]
 ·simpa[D] using fH
 ·simpa[T] using uf
 ·simpa[T,S] using j7
end ay.aI
end
end
section
open Finset Function Real
open scoped BigOperators NNReal
namespace ay.jm
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
noncomputable def aP (psi:AddChar G ℂ):AddCharacter G:=by
  let e:=AddCircle.homeomorphCircle (by norm_num:(1:ℝ)≠0)
  exact
    { toFun:=fun x↦e.symm ((AddChar.circleEquivComplex.symm psi) x)
      map_zero':=by
        apply e.injective
        simp[e,QY]
      map_add':=by
        intro x y
        apply e.injective
        rw[e.apply_symm_apply]
        rw[show e (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) =
            AddCircle.toCircle (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) by
              exact QY _ _]
        rw[Ub]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        exact St _ _ _ }
omit [DecidableEq G] in
lemma qB (psi:AddChar G ℂ) (x:G) :
  AddCircle.toCircle (aP psi x) =
   (AddChar.circleEquivComplex.symm psi) x:=by
 rw[←QY (by norm_num:(1:ℝ)≠0)]
 simp[aP]
omit [DecidableEq G] in
lemma eE (psi:AddChar G ℂ) (x:G) :
  (AddCircle.toCircle (aP psi x):ℂ)=psi x:=by
 classical
 rw[qB]
 exact S6 (AddChar.circleEquivComplex.apply_symm_apply psi) x
omit [DecidableEq G] in
lemma pV :
  Injective (aP (G:=G)):=by
 intro psi fJ h
 ext x
 have hx:=S6 h x
 have hh:=QA (fun z:AddCircle (1:ℝ)↦(AddCircle.toCircle z:ℂ)) hx
 simpa only[eE] using hh
noncomputable def gb :
  AddChar G ℂ→+ AddCharacter G where
 toFun:=aP
 map_zero':=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE]
 map_add' psi fJ:=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE,Ub,
   U3]
noncomputable def nL (Delta:Finset (AddChar G ℂ)) (r:ℝ≥0) :
  aj G where
 eX:=Delta.image aP
 width:=fun _↦r
omit [DecidableEq G] in
@[simp] lemma pH (Delta:Finset (AddChar G ℂ)) (r:ℝ≥0)
  (gamma:AddCharacter G) :
  (nL Delta r).width gamma=r:=rfl
omit [DecidableEq G] in
lemma iC
  {Delta:Finset (AddChar G ℂ)} {r:ℝ≥0} {psi:AddChar G ℂ} {x:G}
  (hx:x∈(nL Delta r).carrier)
  (cT:psi∈Delta.addSpan) :
  ‖aP psi x‖ ≤(Delta.card:ℝ)*(r:ℝ):=by
 classical
 rw[Finset.mem_addSpan] at cT
 obtain ⟨epsilon,eM,hsum⟩:=cT
 have HX :
   ∑ gamma∈Delta,epsilon gamma•aP gamma =
    aP psi:=by
  change ∑ gamma∈Delta,epsilon gamma•gb gamma=gb psi
  calc
   ∑ gamma∈Delta,epsilon gamma•gb gamma =
     ∑ gamma∈Delta,gb (epsilon gamma•gamma):=by
      apply sum_congr rfl
      intro gamma k5
      exact(map_zsmul gb (epsilon gamma) gamma).symm
   _=gb (∑ gamma∈Delta,epsilon gamma•gamma):=by
    exact(RK gb (fun gamma↦epsilon gamma•gamma) Delta).symm
   _=gb psi:=QA gb hsum
 have EB :
   (∑ gamma∈Delta,epsilon gamma•aP gamma) x =
    ∑ gamma∈Delta,(epsilon gamma•aP gamma) x:=by
  induction Delta using Finset.induction_on with
  | empty=>simp
  | @insert gamma Delta k5 ih=>simp[k5]
 rw[←HX,EB]
 calc
  ‖∑ gamma∈Delta,(epsilon gamma•aP gamma) x‖ ≤
    ∑ gamma∈Delta, ‖(epsilon gamma•aP gamma) x‖:=
   Rq _ _
  _≤ ∑ _gamma∈Delta,(r:ℝ):=by
   apply sum_le_sum
   intro gamma k5
   have CK:aP gamma∈(nL Delta r).eX:=by
    exact Finset.mem_image.mpr ⟨gamma,k5,rfl⟩
   have d5:=(aj.mem_carrier _ _).mp hx
    (aP gamma) CK
   have hw: ‖aP gamma x‖ ≤(r:ℝ):=by
    simpa only[pH] using d5
   rcases eM gamma with eY | hzero | JU
   ·simpa[eY] using hw
   ·simp[hzero]
   ·simpa[JU] using hw
  _=(Delta.card:ℝ)*(r:ℝ):=by simp
noncomputable def cD (B:aj G)
    (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0):aj G:=by
  classical
  let Cm:=Delta.image aP
  exact
    { eX:=B.eX∪Cm
      width:=fun gamma ↦
        if gamma∈B.eX then
          if gamma∈Cm then min (aF*B.width gamma) r
          else aF*B.width gamma
        else r }
omit [DecidableEq G] in
lemma vB (B:aj G)
  (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
  (cD B Delta aF r).rank≤B.rank+Delta.card:=by
 classical
 rw[aj.rank,aj.rank,cD]
 exact(Finset.card_union_le _ _).trans_eq (by
  rw[Finset.card_image_iff.mpr pV.injOn])
omit [DecidableEq G] in
lemma fD (B:aj G)
    (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
    (cD B Delta aF r).carrier⊆(B.ai aF).carrier:=by
  classical
  intro x hx
  rw[aj.mem_carrier] at hx ⊢
  intro gamma k5
  have y5:gamma∈B.eX:=by simpa using k5
  have AO:gamma∈B.eX∪Delta.image aP:=
    Um _ y5
  have hbound:=hx gamma (by simpa[cD] using AO)
  by_cases AQ:gamma∈Delta.image aP
  · change ‖gamma x‖ ≤
      (((if gamma∈B.eX then
          if gamma∈Delta.image aP then
            min (aF*B.width gamma) r else aF*B.width gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[RP y5,RP AQ] at hbound
    simpa only[aj.oF,SK] using
      hbound.trans (by exact_mod_cast(Uv (aF*B.width gamma) r))
  · change ‖gamma x‖ ≤
      (((if gamma∈B.eX then
          if gamma∈Delta.image aP then
            min (aF*B.width gamma) r else aF*B.width gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[RP y5,if_neg AQ] at hbound
    simpa only[aj.oF,SK] using hbound
omit [DecidableEq G] in
lemma gd (B:aj G)
  (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
  (cD B Delta aF r).carrier⊆(nL Delta r).carrier:=by
 classical
 intro x hx
 rw[aj.mem_carrier] at hx ⊢
 intro gamma k5
 rw[pH]
 obtain ⟨psi,cT,rfl⟩:=Finset.mem_image.mp k5
 have AQ:aP psi∈Delta.image aP:=
  Finset.mem_image.mpr ⟨psi,cT,rfl⟩
 have AO:aP psi∈B.eX∪Delta.image aP:=
  Ua _ AQ
 have hbound:=hx (aP psi) (by simpa[cD] using AO)
 by_cases hold:aP psi∈B.eX
 ·change ‖aP psi x‖ ≤
   (((if aP psi∈B.eX then
     if aP psi∈Delta.image aP then
      min (aF*B.width (aP psi)) r
     else aF*B.width (aP psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[RP hold,RP AQ] at hbound
  exact hbound.trans (by
   exact_mod_cast(min_le_right (aF*B.width (aP psi)) r))
 ·change ‖aP psi x‖ ≤
   (((if aP psi∈B.eX then
     if aP psi∈Delta.image aP then
      min (aF*B.width (aP psi)) r
     else aF*B.width (aP psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[if_neg hold] at hbound
  exact hbound
omit [DecidableEq G] in
lemma gZ
  (B:aj G) {Delta:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {psi:AddChar G ℂ} {x:G}
  (hx:x∈(cD B Delta aF r).carrier)
  (cT:psi∈Delta.addSpan) :
  ‖aP psi x‖ ≤(Delta.card:ℝ)*(r:ℝ):=
 iC
  (gd B Delta aF r hx) cT
omit [DecidableEq G] in
lemma lV
  (psi:AddChar G ℂ) (x:G)
  (JV: ‖aP psi x‖ ≤(2*pi)⁻¹) :
  ‖1-psi x‖ ≤4*pi* ‖aP psi x‖:=by
 classical
 let a:ℝ:=AddCircle.equivIoc (1:ℝ) (-1/2) (aP psi x)
 have EC:a∈Set.Ioc (-1/2) (-1/2+1):=
  (AddCircle.equivIoc (1:ℝ) (-1/2) (aP psi x)).property
 have JW: |a| ≤1/2:=by
  rw[abs_le]
  constructor<;>linarith[EC.1,EC.2]
 have tw:(a:AddCircle (1:ℝ))=aP psi x:=by
  exact AddCircle.coe_equivIoc
 have Cn: ‖aP psi x‖ = |a|:=by
  rw[←tw]
  exact(Ts (1:ℝ) (by norm_num)).2 (by simpa using JW)
 have vV: ‖(2*pi*a:ℂ)‖ =2*pi* |a|:=by
  simp[QK,QC Real.pi_nonneg]
 have uY: ‖(2*pi*a:ℂ)*Complex.I‖ ≤1:=by
  rw[QO,Complex.norm_I,Q3,vV, ←Cn]
  have Af:0<2*pi:=by positivity
  calc
   2*pi* ‖aP psi x‖ ≤
     2*pi*(2*pi)⁻¹:=
    iO JV Af.le
   _=1:=by field_simp
 have l9:=Complex.norm_exp_sub_one_le uY
 have heval:psi x=Complex.exp ((2*pi*a:ℂ)*Complex.I):=by
  rw[←eE psi x, ←tw]
  simp only[AddCircle.toCircle_apply_mk,Circle.coe_exp]
  congr 1
  push_cast
  field_simp
 rw[heval,norm_sub_rev]
 calc
  ‖Complex.exp ((2*pi*a:ℂ)*Complex.I)-1‖
    ≤ 2* ‖(2*pi*a:ℂ)*Complex.I‖:=l9
  _=4*pi* ‖aP psi x‖:=by
   rw[QO,Complex.norm_I,Q3,vV,Cn]
   ring
omit [DecidableEq G] in
lemma jP
  (B:aj G) {Delta:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {psi:AddChar G ℂ} {x:G}
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (hx:x∈(cD B Delta aF r).carrier)
  (cT:psi∈Delta.addSpan) :
  ‖1-psi x‖ ≤4*pi*((Delta.card:ℝ)*(r:ℝ)):=by
 classical
 have JX:=gZ
  B hx cT
 calc
  _ ≤4*pi* ‖aP psi x‖:=
   lV psi x (JX.trans dV)
  _≤4*pi*((Delta.card:ℝ)*(r:ℝ)):=
   iO JX (by positivity)
omit [DecidableEq G] in
lemma jh
  (B:aj G) {Delta Q S:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {beta:ℝ} {x:G}
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (hx:x∈(cD B Delta aF r).carrier)
  (j7: ∀ psi∈Q, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s)
  (ED: ∀ s∈S, ‖1-s x‖ ≤beta) :
  ∀ psi∈Q,
   ‖1-psi x‖ ≤4*pi*((Delta.card:ℝ)*(r:ℝ))+beta:=by
 classical
 intro psi cT
 obtain ⟨z,hz,s,hs,rfl⟩:=j7 psi cT
 have HY  :=

  jP B dV hx hz
 calc
  _ = ‖(1-z x)+z x*(1-s x)‖:=by
   rw[U3]
   congr 1
   ring
  _≤ ‖1-z x‖ + ‖z x*(1-s x)‖:=norm_add_le _ _
  _= ‖1-z x‖ + ‖1-s x‖:=by
   rw[QO,Q0,QT]
  _≤4*pi*((Delta.card:ℝ)*(r:ℝ))+beta:=
   Sr HY (ED s hs)
omit [DecidableEq G] in
lemma iY
  (C:aj G) (dF:C.a1)
  {Delta Q:Finset (AddChar G ℂ)} {sigma r:ℝ≥0}
  (iX:sigma ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (j7: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈c5.cj C.carrier (1/2),psi=z+s) :
  ∀ x∈(cD C Delta sigma r).carrier, ∀ psi∈Q,
   ‖1-psi x‖ ≤
    4*pi*((Delta.card:ℝ)*(r:ℝ)) +
     400*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 intro x hx
 apply jh
  C dV hx j7
 intro s hs
 exact ay.kl
  dF iX hs (fD C Delta sigma r hx)
end ay.jm
end
section
open Finset
open scoped BigOperators NNReal
namespace ay.qC
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
open aj jm
def rI (m:ℕ) (hm:0< m) (z:AddCircle (1:ℝ)):Fin m:=by
 have ug:0≤(cx z+1/2)*(m:ℝ):=by
  have hz:=(k1 z).1
  have qD:(0:ℝ)≤ m:=by positivity
  exact Qn (by linarith) qD
 refine ⟨⌊(cx z+1/2)*m⌋₊,(Uc ug).2 ?_⟩
 have hz:cx z+1/2<1:=by
  linarith[(k1 z).2]
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 exact(Sk hz qD).trans_eq (QT (m:ℝ))
lemma nV
  {m:ℕ} (hm:0< m) {z w:AddCircle (1:ℝ)}
  (lP:rI m hm z=rI m hm w) :
  ‖z-w‖ ≤1/(m:ℝ):=by
 let rz:=cx z
 let rw:=cx w
 let uz:=(rz+1/2)*(m:ℝ)
 let uw:=(rw+1/2)*(m:ℝ)
 have P8:0≤rz+1/2:=by
  dsimp[rz]
  linarith[(k1 z).1]
 have P9:0≤rw+1/2:=by
  dsimp[rw]
  linarith[(k1 w).1]
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 have OR:0≤uz:=by dsimp[uz]; positivity
 have OS:0≤uw:=by dsimp[uw]; positivity
 have vW:⌊uz⌋₊=⌊uw⌋₊:=by
  have q4:=QA Fin.val lP
  simpa only[rI,uz,uw,rz,rw] using q4
 have uZ := Ti OR
 have u0 := RY uz
 have AR := Ti OS
 have AS := RY uw
 have Df:(rz-rw)*(m:ℝ)<1:=by
  dsimp[uz,uw] at uZ u0 AR AS
  rw[vW] at uZ u0
  nlinarith
 have Dg: -(1/(m:ℝ))<rz-rw:=by
  have hmul:(-1:ℝ)<(rz-rw)*(m:ℝ):=by
   dsimp[uz,uw] at uZ u0 AR AS
   rw[vW] at uZ u0
   nlinarith
  have hdiv:(-1:ℝ)/(m:ℝ)<rz-rw:=
   (Tv qD).2 hmul
  simpa only[neg_div,R6] using hdiv
 have BO:rz-rw<1/(m:ℝ):=
  (SP qD).2 Df
 calc
  _ ≤ |rz-rw|:=gu z w
  _≤1/(m:ℝ):=(abs_lt.2 ⟨Dg,BO⟩).le
def signature (Delta:Finset (AddChar G ℂ))
  (m:ℕ) (hm:0< m) (x:G):Delta→Fin m:=
 fun psi↦rI m hm (aP psi.1 x)
omit [DecidableEq G] in
lemma qE
  (B:aj G) (Delta:Finset (AddChar G ℂ))
  (aF r:NNReal) (x:G) :
  x∈(cD B Delta aF r).carrier ↔
   x∈(B.ai aF).carrier ∧
    ∀ psi∈Delta, ‖aP psi x‖ ≤(r:ℝ):=by
 classical
 constructor
 ·intro hx
  refine ⟨fD B Delta aF r hx, ?_⟩
  intro psi cT
  have JY:=gd B Delta aF r hx
  exact(aj.mem_carrier _ _).mp JY (aP psi)
   (Finset.mem_image.mpr ⟨psi,cT,rfl⟩)
 ·rintro ⟨hB,dQ⟩
  rw[aj.mem_carrier] at hB ⊢
  intro gamma k5
  change gamma∈B.eX∪Delta.image aP at k5
  rw[Finset.mem_union] at k5
  change ‖gamma x‖ ≤
   (((if gamma∈B.eX then
     if gamma∈Delta.image aP then
      min (aF*B.width gamma) r
     else aF*B.width gamma
    else r):NNReal):ℝ)
  rcases k5 with vX | JZ
  ·by_cases Dh:gamma∈Delta.image aP
   ·obtain ⟨psi,cT,EE⟩:=Finset.mem_image.mp Dh
    subst gamma
    rw[RP vX,RP Dh]
    exact le_min (hB _ vX) (dQ psi cT)
   ·rw[RP vX,if_neg Dh]
    exact hB gamma vX
  ·obtain ⟨psi,cT,EE⟩:=Finset.mem_image.mp JZ
   subst gamma
   by_cases vX:aP psi∈B.eX
   ·rw[RP vX,RP JZ]
    exact le_min (hB _ vX) (dQ psi cT)
   ·rw[if_neg vX]
    exact dQ psi cT
omit [DecidableEq G] in
private lemma mB
  (B:aj G) (Delta:Finset (AddChar G ℂ))
  (aF:NNReal) {m:ℕ} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).carrier)
  {x y:↥S} (ni:signature Delta m hm x.1=signature Delta m hm y.1) :
  x.1-y.1 ∈
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier:=by
 classical
 rw[qE]
 constructor
 ·exact aj.j2 (hS x.2) (hS y.2)
 ·intro psi cT
  rw[map_sub]
  have vU:=Uu ni ⟨psi,cT⟩
  have hbound:=nV hm vU
  simpa only[SE,S9,R6] using hbound
omit [DecidableEq G] in
private lemma s5
  (B:aj G) (Delta:Finset (AddChar G ℂ))
  (aF:NNReal) {m:ℕ} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).carrier)
  (a:Delta→Fin m) :
  Fintype.card {x:↥S// signature Delta m hm x.1=a} ≤
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier.card:=by
 classical
 by_cases jv:Nonempty {x:↥S// signature Delta m hm x.1=a}
 ·let x₀ := Classical.choice jv
  let f:{x:↥S// signature Delta m hm x.1=a} →
    ↥(cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier:=
   fun x↦⟨x.1.1-x₀.1.1,mB
    B Delta aF hm S hS (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have q4:=QA Subtype.val ni
   dsimp[f] at q4
   exact S8 q4
  calc
   _ ≤
     Fintype.card ↥(cD B Delta (aF+aF)
      (m:NNReal)⁻¹).carrier:=R1 f hf
   _=(cD B Delta (aF+aF)
      (m:NNReal)⁻¹).carrier.card:=Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma nW
  (B:aj G) (Delta:Finset (AddChar G ℂ))
  (aF:NNReal) {m:ℕ} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).carrier) :
  S.card≤ m^Delta.card *
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier.card:=by
 classical
 let Sigma:=Delta→Fin m
 let q:↥S→ Sigma:=fun x↦signature Delta m hm x.1
 have jv: ∀ a:Sigma,
   Fintype.card {x:↥S// q x=a} ≤
    (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier.card:=by
  intro a
  exact s5 B Delta aF hm S hS a
 have Di:Fintype.card Sigma=m^Delta.card:=by
  dsimp[Sigma]
  rw[TC]
  simp
 rw[←Rx S, ←Di]
 by_contra h
 have xS:Fintype.card Sigma *
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier.card <
    Fintype.card ↥S:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) xS
 have Em: #{x | q x=a} ≤
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Em) ha
omit [DecidableEq G] in
lemma tz
  (B:aj G) (Delta:Finset (AddChar G ℂ))
  (aF:NNReal) {m:ℕ} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).carrier) :
  (cD B Delta (aF+aF) (m:NNReal)⁻¹).rank ≤
    B.rank+Delta.card ∧
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).carrier ⊆
    (B.ai (aF+aF)).carrier ∧
   S.card≤ m^Delta.card *
    (cD B Delta (aF+aF)
     (m:NNReal)⁻¹).carrier.card:=by
 classical
 exact ⟨vB B Delta _ _,
  fD B Delta _ _,
  nW B Delta aF hm S hS⟩
end
end ay.qC
end
section
open scoped BigOperators ENNReal NNReal Pointwise translate
open Finset Function MeasureTheory RCLike
namespace ay.ag
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
omit [DecidableEq G] [Fintype G] in
lemma q8 [Finite G] (psi:AddChar G ℂ) (t:G) :
  ‖psi (-t)-1‖ = ‖1-psi t‖:=by
 rw[psi.map_neg_eq_inv]
 have vH:psi t≠0:=by
  intro h
  have:=Q0 psi t
  simp[h] at this
 calc
  _ = ‖(psi t)⁻¹ *(1-psi t)‖:=by
   congr 1
   field_simp
  _= ‖1-psi t‖:=by
   rw[QO,Up,Q0,inv_one,QT]
lemma oR
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (X:Finset G) (hX:X.Nonempty) (m:ℕ) (F:G→ℂ)
  (eta theta:ℝ) (fC:0≤eta) (OT:0≤theta)
  (t:G)
  (l7: ∀ psi:AddChar G ℂ,
   eta≤ ‖dft ((@mu (ℂ) _ _) X) psi‖ → ‖1-psi t‖ ≤theta) :
  (aJ (∞) (τ t ((aC ((ep (mu X) m)) F))-((aC ((ep (mu X) m)) F)))) ≤
   (theta+2*eta^m)*(c2 1 (dft F)):=by
 rw[dw]
 refine ciSup_le fun x↦ ?_
 let P:G→ℂ:=(aC ((ep (mu X) m)) F)
 have gX :
   (τ t P-P) x =
    𝔼 psi:AddChar G ℂ,
     dft P psi*(psi (x-t)-psi x):=by
  simp only[Rw,QZ]
  rw[←vn P (x-t), ←vn P x,
   ←Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro psi _
  ring
 rw[gX]
 calc
  ‖𝔼 psi:AddChar G ℂ,
    dft P psi*(psi (x-t)-psi x)‖
    ≤ 𝔼 psi:AddChar G ℂ,
      ‖dft P psi*(psi (x-t)-psi x)‖:=
     RCLike.norm_expect_le (K:=ℝ)
  _≤𝔼 psi:AddChar G ℂ,
     (theta+2*eta^m)* ‖dft F psi‖:=by
   refine expect_le_expect fun psi _↦ ?_
   rw[QO]
   have oc :
     ‖psi (x-t)-psi x‖ = ‖1-psi t‖:=by
    have AG:psi (x-t)=psi x*psi (-t):=by
     rw[Qy,psi.map_add_eq_mul]
    rw[AG]
    calc
     ‖psi x*psi (-t)-psi x‖ = ‖psi x*(psi (-t)-1)‖:=by ring_nf
     _= ‖psi (-t)-1‖:=by rw[QO,Q0,QT]
     _= ‖1-psi t‖:=q8 psi t
   rw[oc]
   simp only[P,sb,vP,QO,norm_pow]
   have AL: ‖dft ((@mu (ℂ) _ _) X) psi‖ ≤1:=by
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ≤(aJ 1 (((@mu (ℂ) _ _) X))):=pD _ _
     _=1:=uN hX
   by_cases iU:eta≤ ‖dft ((@mu (ℂ) _ _) X) psi‖
   ·have hpow: ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m≤1:=
     Uy (Re _) AL
    have hp:=l7 psi iU
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m* ‖dft F psi‖ * ‖1-psi t‖ ≤
       1* ‖dft F psi‖ *theta:=by gcongr
     _≤(theta+2*eta^m)* ‖dft F psi‖:=by
      have LG:0≤eta^m:=QH fC m
      have hF:0≤ ‖dft F psi‖:=Re _
      nlinarith
   ·have uX: ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m≤eta^m:=by
     exact Qp (Re _) (le_of_not_ge iU) m
    have OU: ‖1-psi t‖ ≤2:=by
     calc
      ‖1-psi t‖ ≤ ‖(1:ℂ)‖ + ‖psi t‖:=norm_sub_le _ _
      _=2:=by norm_num
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m* ‖dft F psi‖ * ‖1-psi t‖ ≤
       eta^m* ‖dft F psi‖ *2:=by gcongr
     _≤(theta+2*eta^m)* ‖dft F psi‖:=by
      have LG:0≤eta^m:=QH fC m
      have hF:0≤ ‖dft F psi‖:=Re _
      nlinarith
  _=(theta+2*eta^m)*(c2 1 (dft F)):=by
   rw[tq,Finset.mul_expect]
lemma sv
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (A B C:Finset G) (hA:A.Nonempty) (hC:C.Nonempty) :
  (c2 1 (dft ((aC (((aC ((@mu (ℂ) _ _) A) (((indicator B fun _↦(1:_)):G→ℂ))))) (mu C))))) ≤
   Real.sqrt ((B.card:ℝ)/C.card):=by
 calc
  _
    = (c2 1 (dft ((@mu (ℂ) _ _) A) *
      (dft ((indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C)))):=by
     rw[x2,x2]
     congr 1
     funext psi
     ring_nf
  _≤(c2 1 (dft ((indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))):=by
   calc
    _≤(c2 1 (dft ((indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))) *
       (c2 (∞) (dft ((@mu (ℂ) _ _) A))):=by
      simpa[Qx] using
       (tY (f:=dft ((indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))
        (g:=dft ((@mu (ℂ) _ _) A)) 1 ∞)
    _≤(c2 1 (dft ((indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C)))*1:=by
      gcongr
      ·exact yM
      exact(qY _).trans_eq (uN hA)
    _=_:=Q3 _
  _≤(c2 2 (dft ((indicator B fun _↦(1:_)):G→ℂ)))*(c2 2 (dft ((@mu (ℂ) _ _) C))):=
   tY 2 2
  _=Real.sqrt (B.card:ℝ)*(C.card:ℝ)^(-2⁻¹ :ℝ):=by
   rw[w5,tU,w5,CD hC]
  _=Real.sqrt ((B.card:ℝ)/C.card):=by
   rw[Real.sqrt_div (by positivity),U4,
    U4,Qw]
   congr 1
   rw[←TS (by positivity)]
   congr 1
   norm_num
lemma s6 (X:Finset G) (psi:AddChar G ℂ) :
  dft ((@mu (ℂ) _ _) X) psi =
   ay.cG (ay.af X) (-psi):=by
 classical
 rw[dft_apply,wInner_one_eq_sum]
 simp only[inner_apply',ay.cG,
  U2]
 apply Io rfl
 intro x _
 unfold mu ay.af
 by_cases hx:x∈X
 ·simp[hx,Q2, ←Rz,
   ←Ud,Qx]
 ·simp[hx,Q2]
omit [DecidableEq G] in
lemma vY (f:G→ℂ) (a:G) (psi:AddChar G ℂ) :
  ‖dft (τ a f) psi‖ = ‖dft f psi‖:=by
 rw[dft_apply,dft_apply,wInner_one_eq_sum,wInner_one_eq_sum]
 simp only[inner_apply',QZ]
 have hsum :
   (∑ x:G,starRingEnd ℂ (psi x)*f (x-a)) =
    starRingEnd ℂ (psi a)* ∑ x:G,starRingEnd ℂ (psi x)*f x:=by
  rw[Qj]
  refine Qk (Equiv.addRight (-a)) _ _ (fun x↦ ?_)
  simp only[Equiv.coe_addRight,Qy,St,
   Ud,RU,map_inv₀]
  have vH:starRingEnd ℂ (psi a)≠0:=by
   have cT:psi a≠0:=by
    intro h
    have oS:=Q0 psi a
    rw[h,norm_zero] at oS
    norm_num at oS
   simpa using cT
  field_simp
 rw[hsum,QO]
 simp
lemma tA (T:Finset G) (a:G) (psi:AddChar G ℂ) :
  ‖dft ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖ = ‖dft ((@mu (ℂ) _ _) T) psi‖:=by
 rw[←vI (K:=ℂ)]
 exact vY ((@mu (ℂ) _ _) T) a psi
omit [DecidableEq G] in
lemma kH
  (X:Finset G) (hX:X.Nonempty) (psi:AddChar G ℂ)
  (cT:(1/2:ℝ)≤ ‖dft ((@mu (ℂ) _ _) X) psi‖) :
  psi∈ay.c5.cj X (1/2):=by
 classical
 by_contra hnot
 have eY: -psi∉ay.c5.cj X (1/2):=by
  intro hn
  have:=ay.aI.ku hn
  exact hnot (by simpa only[neg_neg] using this)
 have NW  :=

        QV fun h↦eY (ay.c5.gm.mpr h)
 have ch:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
 have xS :
   ‖ay.cG (ay.af X) (-psi)‖ <1/2:=by
  rw[ay.jU,QO,Up,
   Rf,QK,RT ch]
  calc
   _ <
     (X.card:ℝ)⁻¹ *((1/2:ℝ)*X.card):=by gcongr
   _=1/2:=by field_simp
 rw[s6] at cT
 linarith
lemma ib
  (T:Finset G) (hT:T.Nonempty) (a:G) (psi:AddChar G ℂ)
  (cT:(1/2:ℝ)≤ ‖dft ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖) :
  psi∈ay.c5.cj T (1/2):=by
 apply kH T hT psi
 rw[←tA T a psi]
 exact cT
noncomputable def a6 (D:ℝ):ℕ:=
 ⌈2*pi*max D 0⌉₊+1
lemma gf (D:ℝ):0<a6 D:=by
 simp[a6]
lemma jc (D:ℝ) :
  D*((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) ≤
   (2*pi)⁻¹:=by
 let n:=a6 D
 have LH:0<n:=gf D
 have hn:(0:ℝ)<n:=by exact_mod_cast LH
 have Af:(0:ℝ)<2*pi:=by positivity
 have rJ:2*pi*max D 0 ≤
   (Nat.ceil (2*pi*max D 0):ℝ):=Rr _
 have fF:2*pi*D≤(n:ℝ):=by
  calc
   2*pi*D≤2*pi*max D 0:=by
    gcongr
    exact Tu _ _
   _≤(Nat.ceil (2*pi*max D 0):ℝ):=rJ
   _≤(n:ℝ):=by
    dsimp[n,a6]
    exact_mod_cast Nat.le_succ _
 have tw:((((n:ℕ):ℝ≥0)⁻¹ :ℝ))=(n:ℝ)⁻¹:=by
  norm_cast
 rw[tw]
 rw[←Qw,QF hn]
 calc
  D≤(n:ℝ)/(2*pi):=
   (Qs Af).2 (by nlinarith[fF])
  _=(2*pi)⁻¹ *(n:ℝ):=by
   field_simp
lemma sw (D:ℝ) (d q:ℕ)
  (hd:(d:ℝ)≤D) (hq:0<q) :
  4*pi*(d:ℝ) *
    (((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) ≤
   2/(q:ℝ):=by
 have hs := gf D
 have Qa:(0:ℝ)<a6 D:=by exact_mod_cast hs
 have Jd:(0:ℝ)<q:=by exact_mod_cast hq
 have dc:D*((a6 D:ℝ)⁻¹) ≤
   (2*pi)⁻¹:=by
  have h:=jc D
  have tw:((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) =
    (a6 D:ℝ)⁻¹:=by norm_cast
  simpa[tw] using h
 have NX:(d:ℝ)*((a6 D:ℝ)⁻¹) ≤
   (2*pi)⁻¹:=by
  calc
   _ ≤
     D*((a6 D:ℝ)⁻¹):=by gcongr
   _≤_:=dc
 have tw:(((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) =
   ((q:ℝ)*(a6 D:ℝ))⁻¹:=by
  norm_cast
 rw[tw,mul_inv]
 calc
  _
                          =
    (q:ℝ)⁻¹ *
     (4*pi*((d:ℝ)*(a6 D:ℝ)⁻¹)):=by ring
  _≤(q:ℝ)⁻¹ *(4*pi*(2*pi)⁻¹):=by gcongr
  _=2/(q:ℝ):=by
   field_simp
   ring
omit [DecidableEq G] [Fintype G] in
lemma pW [Finite G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (F P:G→ℂ) (t:G) {delta E:ℝ}
  (cu:(aJ (∞) (P-F))≤delta)
  (jl:(aJ (∞) (τ t P-P))≤E) :
  (aJ (∞) (τ t F-F))≤2*delta+E:=by
 have jx :
   (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)):=
  er le_top
 have uh :
   (aJ (∞) (τ t P-F))≤(aJ (∞) (τ t P-P))+(aJ (∞) (P-F)):=
  er le_top
 calc
  (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)):=jx
  _≤(aJ (∞) (τ t F-τ t P)) +
     ((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by gcongr
  _=(aJ (∞) (F-P))+((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by
   have J0:τ t F-τ t P=τ t (F-P):=by rfl
   rw[J0,jY]
  _≤delta+(E+delta):=by
   gcongr
   simpa[r6] using cu
  _=2*delta+E:=by ring
omit [DecidableEq G] in
lemma kn
  (C:ay.aj G) (td:C.a1)
  (Q Delta:Finset (AddChar G ℂ)) (aF:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (hX:X⊆(C.ai aF).carrier)
  (iX:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*pi)⁻¹)
  (j7: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈ay.c5.cj C.carrier (1/2),psi=z+s) :
  let D:=ay.jm.cD C Delta
   (aF+aF) (m:ℝ≥0)⁻¹
  D.rank≤C.rank+Delta.card ∧
   D.carrier⊆(C.ai (aF+aF)).carrier ∧
   X.card≤ m^Delta.card*D.carrier.card ∧
   ∀ t∈D.carrier, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*pi*((Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Delta
  (aF+aF) (m:ℝ≥0)⁻¹
 have tB:=ay.qC.tz
  C Delta aF hm X hX
 refine ⟨tB.1,tB.2.1,tB.2.2, ?_⟩
 intro t ht psi cT
 simpa only[D,SE,S9] using
  (ay.jm.iY
   C td iX dV j7 t ht psi cT)
omit [DecidableEq G] in
lemma kv (D:ay.aj G) :
  ∃ R:ay.aj G,
   R.a1∧R.rank=D.rank∧R.carrier⊆D.carrier ∧
    D.carrier.card≤4^D.rank*R.carrier.card:=by
 classical
 obtain ⟨a8,gJ,lj,dF⟩:=D.eP
 refine ⟨D.ai a8,dF,by simp, ?_, ?_⟩
 ·simpa only[ay.aj.oG] using
   (ay.aj.b5 (B:=D) lj)
 ·have dc:=ay.aj.de D
  have iB:(D.ai (1/2)).carrier.card ≤
    (D.ai a8).carrier.card:=
   Qu (ay.aj.b5 gJ)
  calc
   D.carrier.card=(D.ai 1).carrier.card:=by simp
   _≤4^D.rank*(D.ai (1/2)).carrier.card:=dc
   _≤4^D.rank*(D.ai a8).carrier.card:=
    Qr _ iB
omit [DecidableEq G] in
lemma gK
  (C:ay.aj G) (td:C.a1)
  (Q Delta:Finset (AddChar G ℂ)) (aF:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (hX:X⊆(C.ai aF).carrier)
  (iX:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*pi)⁻¹)
  (j7: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈ay.c5.cj C.carrier (1/2),psi=z+s) :
  ∃ R:ay.aj G,
   R.a1∧R.rank≤C.rank+Delta.card ∧
   R.carrier⊆(C.ai (aF+aF)).carrier ∧
   X.card≤ m^Delta.card*(4^(C.rank+Delta.card)*R.carrier.card) ∧
   ∀ t∈R.carrier, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*pi*((Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Delta
  (aF+aF) (m:ℝ≥0)⁻¹
 have hD:=kn
  C td Q Delta aF m hm X hX iX dV j7
 obtain ⟨R,qk,oT,Hg,ya⟩:=kv D
 refine ⟨R,qk,oT.le.trans hD.1,Hg.trans hD.2.1, ?_, ?_⟩
 ·calc
   X.card≤ m^Delta.card*D.carrier.card:=hD.2.2.1
   _≤ m^Delta.card*(4^D.rank*R.carrier.card):=
    Qr _ ya
   _≤ m^Delta.card*(4^(C.rank+Delta.card)*R.carrier.card):=by
    have hpow:4^D.rank≤4^(C.rank+Delta.card):=
     QR (by omega) hD.1
    exact Qr _ (QQ _ hpow)
 ·intro t ht psi cT
  exact hD.2.2.2 t (Hg ht) psi cT
omit [DecidableEq G] in
lemma iD
  (B:ay.aj G) (rH:B.a1)
  (X:Finset G) (hX:X.Nonempty) (ud:X⊆B.carrier)
  (eta:ℝ) (fC:0<eta) (aF:ℝ≥0) (m:ℕ) (hm:0< m)
  (iX:aF+aF ≤
   1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (dV :
   ay.aI.bf B X eta *
     (((m:ℝ≥0)⁻¹ :ℝ))≤(2*pi)⁻¹) :
  ∃ a8:ℝ≥0, ∃ C:ay.aj G,
   ∃ Delta:Finset (AddChar G ℂ), ∃ R:ay.aj G,
    1/2≤a8∧a8≤1 ∧
    C=B.ai (a8 *
     ay.aI.cJ B X eta) ∧
    C.a1 ∧
    (Delta.card:ℝ) ≤
     ay.aI.bf B X eta ∧
    Delta⊆ay.c5.cj X eta ∧
    R.a1∧R.rank≤B.rank+Delta.card ∧
    R.carrier⊆(C.ai (aF+aF)).carrier ∧
    (C.ai aF).carrier.card ≤
     m^Delta.card*(4^(B.rank+Delta.card)*R.carrier.card) ∧
    ∀ t∈R.carrier,
     ∀ psi∈ay.c5.cj X eta,
      ‖1-psi t‖ ≤
       4*pi *
         (Delta.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) +
        400*((max B.rank 1:ℕ):ℝ) *
         (aF+aF:ℝ≥0):=by
 classical
 obtain ⟨a8,C,Delta,gJ,lj,hC,td,
   fH,u1,j7⟩:=
  ay.aI.mY
   B rH X hX ud eta fC
 have yb:C.rank=B.rank:=by simp[hC]
 have HZ:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0):=by
  simpa[yb] using iX
 have hinv:0≤(((m:ℝ≥0)⁻¹ :ℝ)):=by positivity
 have BP :
   (Delta.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) ≤
    (2*pi)⁻¹:=
  (Qi fH hinv).trans dV
 obtain ⟨R,qk,oT,yc,vZ,l7⟩:=
  gK
   C td (ay.c5.cj X eta) Delta aF m hm
    (C.ai aF).carrier (fun _ hx↦hx) HZ BP j7
 refine ⟨a8,C,Delta,R,gJ,lj,hC,td,
  fH,u1,qk, ?_,yc, ?_, ?_⟩
 ·simpa[yb] using oT
 ·simpa[yb] using vZ
 ·intro t ht psi cT
  simpa only[yb,Qo] using l7 t ht psi cT
lemma fk
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} (hA:A.Nonempty)
  (delta:ℝ) (cu:0<delta) (m:ℕ) (hm:m≠0)
  (M L:Finset G) (hM:M.Nonempty) (hL:L.Nonempty)
  (bl:ay.aj G) (sx:bl.a1)
  (aF:ℝ≥0)
  (dy:aF+aF ≤
   1/(100*(max bl.rank 1:ℕ):ℝ≥0))
  (dh:ℕ) (pX:0<dh) :
  let q:=⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
  let wK:=ay.cQ q
   ((delta/m)/exp 1)
  ∃ (T X:Finset G) (z:G) (a8:ℝ≥0),
   ∃ (fl:ay.aj G)
    (Delta:Finset (AddChar G ℂ)) (R:ay.aj G),
   T⊆bl.carrier∧z∈T∧X= -z+ᵥ T∧X.Nonempty ∧
   (((A.card:ℝ)^wK/2*bl.carrier.card) /
     ((A+bl.carrier).card:ℝ)^wK≤T.card) ∧
   1/2≤a8∧a8≤1 ∧
   fl=bl.ai (a8 *
    ay.aI.cJ bl T (1/2)) ∧
   fl.a1 ∧
   (Delta.card:ℝ) ≤
    ay.aI.bf bl T (1/2) ∧
   Delta⊆ay.c5.cj T (1/2) ∧
   R.a1∧R.rank≤bl.rank+Delta.card ∧
   R.carrier⊆(fl.ai (aF+aF)).carrier ∧
   (fl.ai aF).carrier.card ≤
    (dh*a6
       (ay.aI.bf bl T (1/2))) ^
      Delta.card *
     (4^(bl.rank+Delta.card)*R.carrier.card) ∧
   ∀ t∈R.carrier,
    (aJ (∞) (τ t ((aC (((aC ((@mu (ℂ) _ _) A) (((indicator M fun _↦(1:_)):G→ℂ))))) (mu L))) -
      ((aC (((aC ((@mu (ℂ) _ _) A) (((indicator M fun _↦(1:_)):G→ℂ))))) (mu L))))) ≤
     2*delta +
      (4*pi *
         (Delta.card:ℝ) *
          ((((dh*a6
           (ay.aI.bf
            bl T (1/2)):ℕ):ℝ≥0)⁻¹ :ℝ)) +
        400*((max bl.rank 1:ℕ):ℝ) *
         (aF+aF:ℝ≥0) +
        2*(1/2:ℝ)^m) *
       Real.sqrt ((M.card:ℝ)/L.card):=by
 classical
 let q:=⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
 let wK:=ay.cQ q
  ((delta/m)/exp 1)
 obtain ⟨T,z,ui,ML,pT,_hXdiff,nk,j8⟩:=
  ay.mX
   hA bl.aE delta cu m hm M L hM hL
 let X := -z+ᵥ T
 have uW:T.Nonempty:=⟨z,ML⟩
 let dim:=ay.aI.bf bl T (1/2)
 let n:=dh*a6 dim
 have hn := QP pX (gf dim)
 have dV:dim*(((n:ℝ≥0)⁻¹ :ℝ))≤(2*pi)⁻¹:=by
  have oQ:0≤dim:=by
   have nk:(0:ℝ)<T.card:=by exact_mod_cast uW.card_pos
   have ch:(T.card:ℝ)≤bl.carrier.card:=by
    exact_mod_cast Qu ui
   have eO:(1:ℝ)≤2*(bl.carrier.card:ℝ)/T.card:=by
    rw[Qs nk]
    nlinarith
   have ei :=
    Qv eO
   dsimp[dim,ay.aI.bf]
   positivity
  have dc :=

   jc dim
  have Dj:a6 dim≤n:=by
   dsimp[n]
   exact T9 _ pX
  have hinv:(((n:ℝ≥0)⁻¹ :ℝ)) ≤
    ((((a6 dim:ℕ):ℝ≥0)⁻¹ :ℝ)):=by
   have EG:(0:ℝ≥0) <
     (a6 dim:ℕ):=by
    exact_mod_cast gf dim
   have J1:(0:ℝ≥0)<n:=by exact_mod_cast hn
   have BQ:(a6 dim:ℝ≥0)≤n:=by
    exact_mod_cast Dj
   exact_mod_cast(RJ J1 EG).2 BQ
  exact(iO hinv oQ).trans dc
 obtain ⟨a8,fl,Delta,R,gJ,lj,oU,AT,
   fH,u1,qk,oT,yc,vZ,l7⟩:=
  iD
   bl sx T uW ui (1/2) (by norm_num)
    aF n hn dy (by simpa[dim] using dV)
 let F:G→ℂ:=(aC (((aC (mu A) ((indicator M fun _↦(1:_)))))) (mu L))
 let P:G→ℂ:=(aC ((ep (mu X) m)) F)
 let phase:ℝ:=
  4*pi*(Delta.card:ℝ)*(((n:ℝ≥0)⁻¹ :ℝ)) +
   400*((max bl.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0)
 have H3:0≤phase:=by
  dsimp[phase]
  positivity
 have MM:(c2 1 (dft F))≤Real.sqrt ((M.card:ℝ)/L.card):=by
  simpa[F] using sv A M L hA hL
 have Gc:(aJ (∞) (P-F))≤delta:=by
  simpa[P,F,X] using j8
 have jl: ∀ t∈R.carrier,
   (aJ (∞) (τ t F-F)) ≤
    2*delta+(phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
  intro t ht
  have hP:= oR X (by simpa[X] using pT) m F
   (1/2) phase (by norm_num) H3 t (fun psi cT ↦
    l7 t ht psi
     (ib
      T uW (-z) psi (by simpa[X] using cT)))
  have OV:(aJ (∞) (τ t P-P)) ≤
    (phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
   calc
    _ ≤
      (phase+2*(1/2:ℝ)^m)*(c2 1 (dft F)):=by
       simpa[P] using hP
    _≤(phase+2*(1/2:ℝ)^m) *
      Real.sqrt ((M.card:ℝ)/L.card):=by
       gcongr
  exact pW F P t Gc OV
 refine ⟨T,X,z,a8,fl,Delta,R,ui,ML,rfl,
  by simpa[X] using pT, ?_,gJ,lj, ?_,AT,
  ?_,u1,qk,oT,yc, ?_, ?_⟩
 ·simpa[q,wK] using nk
 ·simpa using oU
 ·simpa[dim] using fH
 ·simpa[n,dim] using vZ
 ·intro t ht
  simpa[F,phase,n,dim,Qo] using jl t ht
noncomputable def aS (A:Finset G) (x:G):ℝ:=
 if x∈A then (A.card:ℝ)⁻¹ else 0
noncomputable def d9 (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (x-y)
noncomputable def a2 (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (y-x)
noncomputable def bC (f g:G→ℝ):ℝ:=
 ∑ x:G,f x*g x
noncomputable def bJ (A:Finset G) (x:G):ℝ:=
 if x∈A then 1 else 0
noncomputable def bW
  (aX a3 S:Finset G) (t:G):ℝ:=
 ∑ a₁:G, ∑ a₂:G,
  bJ aX a₁*bJ a3 a₂*bJ S (t+a₁-a₂)
lemma d7
  {aX a3:Finset G} (fY:aX.Nonempty) (g9:a3.Nonempty)
  (S:Finset G) (t:G) :
  bC
    (fun x↦a2 (aS aX)
     (aS a3) (x-t))
    (bJ S) =
   bW aX a3 S t/(aX.card*a3.card:ℝ):=by
 classical
 simp only[bC,a2,aS,
  bW]
 simp_rw[Qt]
 rw[sum_comm]
 calc
  _

    = ((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ y:G, ∑ x:G,
       bJ aX y*bJ a3 (y-(x-t)) *
        bJ S x:=by
     rw[Qj]
     apply sum_congr rfl
     intro y _
     rw[Qj]
     apply sum_congr rfl
     intro x _
     simp only[bJ]
     split_ifs<;>ring
  _=((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ a₁:G, ∑ a₂:G,
       bJ aX a₁*bJ a3 a₂ *
        bJ S (t+a₁-a₂):=by
     congr 1
     apply sum_congr rfl
     intro a₁ _
     refine(Qk (Equiv.subLeft (t+a₁)) _ _ fun a₂↦ ?_).symm
     simp only[SX]
     congr 2; abel_nf
  _=(∑ a₁:G, ∑ a₂:G,
      bJ aX a₁*bJ a3 a₂ *
       bJ S (t+a₁-a₂)) /
     (aX.card*a3.card:ℝ):=by
     rw[Ri]
     field_simp[fY.card_ne_zero,g9.card_ne_zero]
lemma ja
  {D:Finset G} (_hD:D.Nonempty) (f:G→ℝ) (x:G) :
  d9 (aS D) f x =
   (∑ t∈D,f (x-t))/D.card:=by
 classical
 simp only[d9,aS]
 rw[←sum_subset (s₁:=D) (s₂:=univ)]
 ·rw[Ri,Qj]
  apply sum_congr rfl
  intro t ht
  rw[RP ht]
 ·simp
 ·intro t _ ht
  simp[ht]
lemma mZ
  {D:Finset G} (hD:D.Nonempty)
  (f h:G→ℝ) {eps:ℝ}
  (jl: ∀ t∈D,
   |bC (fun x↦f (x-t)) h-bC f h| ≤eps) :
  |bC (d9 (aS D) f) h -
    bC f h| ≤eps:=by
 classical
 have ch:(0:ℝ)<D.card:=by exact_mod_cast hD.card_pos
 have j8 :
   bC (d9 (aS D) f) h =
    (∑ t∈D,bC (fun x↦f (x-t)) h)/D.card:=by
  simp only[bC]
  simp_rw[ja hD]
  simp_rw[div_mul_eq_mul_div,sum_div,Qt]
  rw[sum_comm]
  simp_rw[←sum_div]
 rw[j8]
 have sy :
   (∑ t∈D,bC (fun x↦f (x-t)) h)/D.card-bC f h =
    (∑ t∈D,
     (bC (fun x↦f (x-t)) h-bC f h))/D.card:=by
  rw[QJ,Tq,QS]
  field_simp[ch.ne']
 rw[sy,TE,RT ch]
 apply(QF ch).2
 calc
  |∑ t∈D,(bC (fun x↦f (x-t)) h-bC f h)|
    ≤ ∑ t∈D,
      |bC (fun x↦f (x-t)) h-bC f h|:=
     abs_sum_le_sum_abs (fun t ↦
      bC (fun x↦f (x-t)) h-bC f h) D
  _≤ ∑ _t∈D,eps:=sum_le_sum fun t ht↦jl t ht
  _=eps*D.card:=by simp[Qx]
lemma ji
  {D:aj G} {aX a3 S:Finset G} {eps:ℝ}
  (fY:aX.Nonempty) (g9:a3.Nonempty)
  (uj: ∀ t∈D.carrier,
   |bW aX a3 S t-bW aX a3 S 0| ≤
    eps*(aX.card:ℝ)*a3.card) :
  |bC
     (d9 (aS D.carrier)
      (a2
       (aS aX) (aS a3)))
     (bJ S) -
    bC
     (a2
      (aS aX) (aS a3))
     (bJ S)| ≤eps:=by
 classical
 apply mZ D.aE
 intro t ht
 have hzero:=d7 fY g9 S (0:G)
 simp only[sub_zero] at hzero
 rw[d7 fY g9,hzero]
 rw[←UT,TE]
 have ch:(0:ℝ)<(aX.card:ℝ)*a3.card:=
  QM (by exact_mod_cast fY.card_pos) (by exact_mod_cast g9.card_pos)
 rw[RT ch]
 apply(QF ch).2
 simpa[Qo] using uj t ht
end ay.ag
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay
namespace aN
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
def dU (D E:Finset G):G→ℝ≥0:=
 (aC ((@mu (ℝ≥0) _ _) D) (mu E))
def bh (D E:Finset G):G→ℝ≥0:=
 (al (dU D E) (dU D E))
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma wY {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty) :
  ∑ x:G,dU D E x=1:=by
 simp[dU,uM,hD,hE]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma i7 {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty) :
  ∑ x:G,bh D E x=1:=by
 simp[bh,jJ,wY hD hE]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma gS (D E:Finset G) :
  0≤bh D E:=by
 simp[bh]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma oo (D E:Finset G) :
  (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E))) =
   (↑) ∘ bh D E:=by
 let b:=dU D E
 calc
  (al (((↑) ∘ b:G→ℂ)) (((↑) ∘ b))) =
    (↑) ∘ ((al (((↑) ∘ b:G→ℝ)) (((↑) ∘ b)))):=by
     exact(Complex.pB ((↑) ∘ b) ((↑) ∘ b)).symm
  _=(↑) ∘ ((al b b)):=by
   rw[←NNReal.gF]
   rfl
  _=(↑) ∘ bh D E:=by
   funext x
   rfl
omit [AddCommGroup G] [DecidableEq G] in
lemma dN (w:G→ℝ≥0) (f:G→ℝ)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) f p=(b0 p w f):=by
 rw[an.dG _ _ hp]
 rw[lu (by exact_mod_cast hp.ne') (by simp)]
 congr 1
 ·apply Io rfl
  intro x _
  simp only[RG,Q2,norm_eq_abs,
   Rh,Ue]
  rw[RN]
 ·simp[R6]
omit [AddCommGroup G] [DecidableEq G] in
lemma gx
  (w:G→ℝ≥0) (f:G→ℝ) (c:ℝ) (hc:0≤c)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) (c•f) p =
   c*an.aM ((↑) ∘ w) f p:=by
 classical
 rw[dN w _ hp,dN w _ hp,
  Ah]
 simp[QK,QC hc]
omit [AddCommGroup G] [DecidableEq G] in
lemma pY
  (w:G→ℝ≥0) (f g:G→ℝ) {p:ℕ} (hp:1≤p) :
  an.aM ((↑) ∘ w) f p ≤
   an.aM ((↑) ∘ w) (f+g) p +
    an.aM ((↑) ∘ w) g p:=by
 classical
 simp_rw[dN w _ (U5 hp)]
 exact qX (by exact_mod_cast hp) w f g
omit [AddCommGroup G] [DecidableEq G] in
lemma qF
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (hC:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x, |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 rw[dN w f hp]
 calc
  _ ≤(b0 p w ((fun _:G↦C))):=by
   apply lpNorm_mono_real .of_discrete
   simpa[QC hC] using hf
  _=C:=by
   rw[lu (by exact_mod_cast hp.ne') (by simp)]
   simp only[Ue]
   have hsum: ∑ x:G,(w x:ℝ)=1:=by exact_mod_cast hw
   have heq: ∑ x:G,(w x:ℝ)* ‖C‖ ^(p:ℝ)=C^p:=by
    rw[norm_eq_abs,QC hC,RN, ←Qt,
     hsum,QT]
   rw[show(∑ x:G,w x• ‖C‖ ^(p:ℝ))=C^p by
    simpa[RG] using heq]
   exact Sc hC hp.ne'
omit [AddCommGroup G] [DecidableEq G] in
lemma lz
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (hC:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x,w x≠0→ |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 let g:G→ℝ:=fun x↦if w x=0 then 0 else f x
 have oS:an.aM ((↑) ∘ w) f p =
   an.aM ((↑) ∘ w) g p:=by
  rw[an.dG _ _ hp,
   an.dG _ _ hp]
  apply QA (fun z:ℝ↦z^(1/(p:ℝ)))
  unfold aK
  apply Io rfl
  intro x _
  by_cases hx:w x=0<;>simp[g,hx]
 rw[oS]
 apply qF hw hC hp
 intro x
 by_cases hx:w x=0
 ·simp[g,hx,hC]
 ·simpa[g,hx] using hf x hx
omit [AddCommGroup G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma eQ (S:Finset G) :
  (@mu (ℝ) _ _) S=af S:=by
 funext x
 by_cases hx:x∈S<;>simp[mu_apply,af,hx]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma eZ
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zq:A⊆B.carrier)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).carrier) :
  |((al ((@mu (ℝ) _ _) A) (mu B.carrier))) t-(B.carrier.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)):=by
 have hB := B.aE
 have dc :
   ∑ x:G,(@mu (ℝ) _ _) A x*mu B.carrier x =
    (B.carrier.card:ℝ)⁻¹:=by
  calc
   _ =
     ∑ x:G,(@mu (ℝ) _ _) A x*(B.carrier.card:ℝ)⁻¹:=by
    apply Io rfl
    intro x _
    by_cases hx:x∈A
    ·rw[mu_apply,mu_apply]
     simp[hx,zq hx]
    ·simp[mu_apply,hx]
   _=(B.carrier.card:ℝ)⁻¹:=by
    rw[←Qt,kW ℝ hA,QT]
 have kE :
   ∑ x:G, |(@mu (ℝ) _ _) B.carrier (x-t)-mu B.carrier x| ≤
    200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ):=by
  simpa only[eQ] using
   B.cN dF dy ht
 rw[eL]
 simp only[Rc,star_trivial]
 rw[←dc]
 rw[←QJ]
 have Dk :
   (∑ x:G,((@mu (ℝ) _ _) A x*mu B.carrier (x-t) -
    mu A x*mu B.carrier x)) =
   ∑ x:G,(@mu (ℝ) _ _) A x *
    (mu B.carrier (x-t)-mu B.carrier x):=by
  apply Io rfl
  intro x _
  ring
 rw[Dk]
 calc
  _
                                         ≤
    ∑ x:G, |(@mu (ℝ) _ _) A x *
     (mu B.carrier (x-t)-mu B.carrier x)|:=
   TQ _ _
  _= ∑ x:G,(@mu (ℝ) _ _) A x *
     |mu B.carrier (x-t)-mu B.carrier x|:=by
   apply Io rfl
   intro x _
   have LI:0≤(@mu (ℝ) _ _) A x:=by
    rw[mu_apply]
    positivity
   rw[SU,QC LI]
  _≤ ∑ x:G,(A.card:ℝ)⁻¹ *
     |(@mu (ℝ) _ _) B.carrier (x-t)-mu B.carrier x|:=by
   apply QI
   intro x _
   apply Qi _ (Q8 _)
   rw[mu_apply]
   split_ifs<;>simp
  _=(A.card:ℝ)⁻¹ *
     ∑ x:G, |(@mu (ℝ) _ _) B.carrier (x-t)-mu B.carrier x|:=by
   rw[Qj]
  _≤(A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)):=
   iO kE (by positivity)
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma ko
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zq:A⊆B.carrier)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).carrier) :
  |((al ((@mu (ℝ) _ _) A) (mu A))) t -
    ((B.carrier.card:ℝ)⁻¹ +
     ((al (((@mu (ℝ) _ _) A-mu B.carrier)) ((mu A-mu B.carrier)))) t)| ≤
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.carrier.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)):=by
 let m:ℝ:=(B.carrier.card:ℝ)⁻¹
 let eA:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))
 let eB:ℝ:=(B.carrier.card:ℝ)⁻¹ *
  (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))
 have PU:=eZ dF hA zq dy ht
 have H4:=eZ dF hA zq dy
  (aj.ec.mpr ht)
 have Nk :
   |((al ((@mu (ℝ) _ _) B.carrier) (mu A))) t-m| ≤eA:=by
  have Nl:((al ((@mu (ℝ) _ _) B.carrier) (mu A))) t =
    ((al (mu A) (mu B.carrier))) (-t):=by
   have h:=wT ((@mu (ℝ) _ _) A) ((@mu (ℝ) _ _) B.carrier) t
   simpa using h.symm
  simpa[m,eA,Nl] using H4
 have PG:=eZ dF
  B.aE (fun _ h↦h) dy ht
 have hsum :
   |(((al ((@mu (ℝ) _ _) A) (mu B.carrier))) t-m) +
    (((al (mu B.carrier) (mu A))) t-m) -
    (((al (mu B.carrier) (mu B.carrier))) t-m)| ≤
     2*eA+eB:=by
  calc
   _

                                                 ≤
     |((al ((@mu (ℝ) _ _) A) (mu B.carrier))) t-m| +
     |((al (mu B.carrier) (mu A))) t-m| +
     |((al (mu B.carrier) (mu B.carrier))) t-m|:=by
      have l4:=abs_sub
       ((((al ((@mu (ℝ) _ _) A) (mu B.carrier))) t-m) +
        (((al (mu B.carrier) (mu A))) t-m))
       (((al (mu B.carrier) (mu B.carrier))) t-m)
      have xt:=UP
       (((al ((@mu (ℝ) _ _) A) (mu B.carrier))) t-m)
       (((al (mu B.carrier) (mu A))) t-m)
      linarith
   _≤eA+eA+eB:=by gcongr
   _=2*eA+eB:=by ring
 have H5 :
   ((al ((@mu (ℝ) _ _) A) (mu A))) t -
     (m+((al ((mu A-mu B.carrier)) ((mu A-mu B.carrier)))) t) =
    (((al (mu A) (mu B.carrier))) t-m) +
    (((al (mu B.carrier) (mu A))) t-m) -
    (((al (mu B.carrier) (mu B.carrier))) t-m):=by
  simp only[BB,BA,Rw]
  ring
 simpa[m,eA,eB,H5] using hsum
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma oq
  (A K:Finset G) :
  (al (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ)))) =
   (↑) ∘ ((K.card:ℝ) •
    ((al (((@mu (ℝ) _ _) A-mu K)) ((mu A-mu K))))):=by
 rw[oB,oC]
 rw[←Complex.pB]
 funext x
 simp only[RD,Rh,Q2]
 rw[show star (↑(Real.sqrt (K.card:ℝ)):ℂ) =
   ↑(Real.sqrt (K.card:ℝ)) by simp]
 rw[←Qo]
 norm_cast
 rw[←TI,Uf (by positivity:(0:ℝ)≤K.card)]
lemma uk
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zq:A⊆B.carrier)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (kI: ∀ t,bh D E t≠0 →
   t∈(B.ai aF).carrier)
  {epsilon:ℝ} (eM:0<epsilon) (oV:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.carrier.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(B.carrier.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (iU :
   epsilon*(B.carrier.card:ℝ)⁻¹ /2 <
    an.aM
     ((↑) ∘ bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.carrier)) ((mu A-mu B.carrier))))
     (an.bS p)) :
  ∃ r:ℕ,0<r∧Even r ∧
   r≤an.cz epsilon p ∧
   (1+epsilon/8)*(B.carrier.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ bh D E) ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
 let K:=B.carrier
 let nu:=bh D E
 let balanced:G→ℝ:=(@mu (ℝ) _ _) A-mu K
 let gH:G→ℝ:=(al balanced balanced)
 let positive:G→ℝ:=(al ((@mu (ℝ) _ _) A) (mu A))
 let main:ℝ:=(K.card:ℝ)⁻¹
 let f:G→ℝ:=(K.card:ℝ)•gH
 let g0 := main•(f+1)
 have hK := B.aE
 have yd:(0:ℝ)<K.card:=by exact_mod_cast hK.card_pos
 have fF:0< main:=by simp[main,yd]
 have ft := i7 hD hE
 have wL:an.cw ((↑) ∘ nu):=
  ⟨fun x↦by exact_mod_cast(show 0≤nu x by exact gS D E x),
   by simpa using QA (fun z:ℝ≥0↦(z:ℝ)) ft⟩
 have LJ :
   (al (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ)))) =
    (↑) ∘ f:=by
  simpa[K,balanced,gH,f] using oq A K
 have J2 :
   (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E)))=(↑) ∘ nu:=by
  simpa[nu] using oo D E
 have Ao: ∀ k:ℕ,0≤ iP ((↑) ∘ nu) f k:=by
  intro k
  have h:=rC LJ J2 k
  simpa[iP,wInner_one_eq_sum,Sb,Qx] using h
 have MN:(K.card:ℝ)*main=1:=by
  simp[main,Uq yd]
 have H6:epsilon/2 <
   an.aM ((↑) ∘ nu) f
    (an.bS p):=by
  rw[show f=(K.card:ℝ)•gH by rfl,
   gx nu gH (K.card:ℝ) (by positivity)
    (by simp[an.bS,hp])]
  have NY:epsilon*main/2 <
    an.aM ((↑) ∘ nu) gH
     (an.bS p):=by
   simpa[K,nu,balanced,gH,main] using iU
  nlinarith
 let sA:=an.cF p
 have LK:0<sA:=by
  have:=an.fK hp
  omega
 have Gd:=an.js
  wL hp (f:=f)
 have EH :=

        H6.trans_le (by simpa[sA] using Gd)
 have AU:(epsilon/2)^sA ≤
   aK ((↑) ∘ nu) f sA:=by
  calc
   _ ≤
     an.aM ((↑) ∘ nu) f sA^sA:=
    Qp (by positivity) EH.le sA
   _=aK ((↑) ∘ nu) f sA:=
    an.jr wL LK
 have c3: ∀ x,g0 x=main*(1+f x):=by
  intro x
  simp[g0,Q2,RV]
  ring
 obtain ⟨r,hr,At,yX,Dl⟩:=
  an.pQ wL
   (f:=f) (fB:=g0) (η:=epsilon/2)
   (bo:=main) (by positivity) (by linarith) fF
   (an.fK hp)
   (an.pP p) Ao AU c3
 have J3:r≤an.cz epsilon p:=by
  simpa[an.cz,sA] using yX
 have BR: ∀ x,nu x≠0→ |positive x-g0 x| ≤epsilon/8*main:=by
  intro x hx
  have hb:=ko dF hA zq dy
   (kI x hx)
  have ye:g0 x=main+gH x:=by
   simp only[smul_add,RM,RD,Q2,Rt,
    Q3,g0,f]
   rw[←Qo,show main*(K.card:ℝ)=1 by nlinarith,QT]
   ring
  simpa[K,balanced,gH,positive,main,ye] using hb.trans d5
 have EI :
   an.aM ((↑) ∘ nu) (positive-g0) r ≤
    epsilon/8*main:=by
  apply lz ft
   (Qn (by positivity) fF.le) hr
  intro x hx
  simpa[Rw] using BR x hx
 have zr:=pY nu g0 (positive-g0)
  (Nat.succ_le_iff.mpr hr)
 have xt:g0+(positive-g0)=positive:=by ext x; simp
 rw[xt] at zr
 refine ⟨r,hr,At,J3, ?_⟩
 simpa[K,nu,positive,main] using(by nlinarith[Dl,zr,EI])
end
end aN
end ay
end
section
open scoped BigOperators
open Finset
namespace ay
namespace cA
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
noncomputable section
def cS (A B:Finset G) {p:ℕ} (s:Fin p→G):Finset G:=
 B.filter fun b↦ ∀ i,b-s i∈A
omit [Fintype G] in
lemma kJ (A B:Finset G) {p:ℕ} (s:Fin p→G) :
  cS A B s⊆B:=by
 intro b hb
 exact(mem_filter.mp hb).1
omit [Fintype G] in
@[simp] lemma jn {A B:Finset G} {p:ℕ} {s:Fin p→G} {b:G} :
  b∈cS A B s↔b∈B∧ ∀ i,b-s i∈A:=by
 simp[cS]
def wM (aX a3:Finset G) (F:G→ℝ):ℝ:=
 ∑ a₁∈aX, ∑ a₂∈a3,F (a₁-a₂)
def ef (A:Finset G) (x:G):ℕ:=
 #(Finset.univ.filter fun t:G↦x-t∈A∧ -t∈A)
private lemma sB (A:Finset G) (ey b₂:G) :
  (∑ s:G,if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0) =
   ef A (ey-b₂):=by
 rw[ef]
 let e := Equiv.subRight b₂
 rw[show((#(Finset.univ.filter fun t:G↦ey-b₂-t∈A∧ -t∈A):ℕ):ℝ) =
   ∑ t:G,if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0 by
  simp]
 refine Qk e
  (fun s:G↦if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0)
  (fun t:G↦if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0)
  (fun t↦ ?_)
 change(if ey-t∈A∧b₂-t∈A then (1:ℝ) else 0) =
  if ey-b₂-(t-b₂)∈A∧ -(t-b₂)∈A then 1 else 0
 have h₁:ey-b₂-(t-b₂)=ey-t:=by abel
 have h₂: -(t-b₂)=b₂-t:=by abel
 rw[h₁,h₂]
private lemma pq (A:Finset G) (ey b₂:G) (p:ℕ) :
  (∑ s:Fin p→G,
    if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0) =
   (ef A (ey-b₂):ℝ)^p:=by
 let D := Finset.univ.filter fun t:G↦ey-t∈A∧b₂-t∈A
 have LL :
   Finset.univ.filter
     (fun s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A) =
    piFinset (fun _:Fin p↦D):=by
  ext s
  simp[D,RX]
 calc
  _
                                                =
    ((Finset.univ.filter
     (fun s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A)).card:ℝ):=by
   simp
  _=((piFinset fun _:Fin p↦D).card:ℝ):=by rw[LL]
  _=(D.card:ℝ)^p:=by simp[Fintype.card_piFinset]
  _=(ef A (ey-b₂):ℝ)^p:=by
   congr 1
   have hsum:=sB A ey b₂
   simpa[D] using hsum
lemma v3 (A aL a0:Finset G) (p:ℕ) (F:G→ℝ) :
  (∑ s:Fin p→G,wM (cS A aL s) (cS A a0 s) F) =
   ∑ ey∈aL, ∑ b₂∈a0,
    (ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
 classical
 simp only[wM,cS,sum_filter]
 rw[QD]
 apply sum_congr rfl
 intro ey PH
 have LN: ∀ s:Fin p→G,
   (if ∀ i,ey-s i∈A then
     ∑ a∈a0,if ∀ i,a-s i∈A then F (ey-a) else 0
    else 0) =
    ∑ a∈a0,if ∀ i,ey-s i∈A then
     if ∀ i,a-s i∈A then F (ey-a) else 0 else 0:=by
  intro s
  by_cases h: ∀ i,ey-s i∈A<;>simp[h]
 simp_rw[LN]
 rw[QD]
 apply sum_congr rfl
 intro b₂ PI
 calc
  _

           =
    (∑ s:Fin p→G,
     (if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0)) *
      F (ey-b₂):=by
       rw[Qt]
       apply sum_congr rfl
       intro s hs
       split_ifs<;>simp_all
  _=(ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
   rw[pq]
section v5
open Function MeasureTheory Real
open scoped ENNReal NNReal Pointwise
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma v7 {A:Finset G} {p:ℕ} {ε δ:ℝ}
  (aL a0:Finset G) (hε:0<ε) (Ak:ε≤1) (Cc:0<δ)
  (hp:Even p) (hp₂:2≤p) (FW:ε⁻¹ *log (2/δ)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∉s p ε aL a0 A) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0 ∧
   1-δ≤ ∑ x∈s p ε aL a0 A,((al (mu aX) (mu a3))) x ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #aX/ #aL ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #a3/ #a0:=
       Hq aL a0 hε Ak Cc hp hp₂ FW hB hA hf
end v5
end
end cA
end ay
end
section
open Finset
open scoped BigOperators NNReal translate
namespace ay.ah
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

open br
structure aA (original:Finset G) where
 restriction:aY G
 shift:G
 eR :
  ∀ x∈restriction.set,x-shift∈original
namespace aA
def e9 {original:Finset G} (s:aA original):Finset G:=
 s.restriction.e9
def density {original:Finset G} (s:aA original):ℝ:=
 s.restriction.density
def rank {original:Finset G} (s:aA original):ℕ:=
 s.restriction.rank
def card {original:Finset G} (s:aA original):ℕ:=
 s.restriction.card
lemma dI {original:Finset G} (s:aA original) :
  0<s.density:=s.restriction.dI
lemma density_le_one {original:Finset G} (s:aA original) :
  s.density≤1:=s.restriction.density_le_one
end aA
inductive cU {original:Finset G}
  (q:ℝ) (aq:ℕ) (aU:ℝ) :
  ℕ→aA original→aA original→Prop
 | nil (s:aA original) :
   cU q aq aU 0 s s
 | cons {n:ℕ} {s t u:aA original}
   (pE:dk q aq aU
    s.restriction t.restriction)
   (x3:cU q aq aU n t u) :
   cU q aq aU (n+1) s u
namespace cU
lemma forget {original:Finset G} {q:ℝ} {aq:ℕ}
  {aU:ℝ} {n:ℕ} {s t:aA original}
  (h:cU q aq aU n s t) :
  eu q aq aU n s.restriction t.restriction:=by
 induction h with
 | nil s=>exact eu.nil s.restriction
 | cons pE _ ih=>exact eu.cons pE ih
lemma qZ {original:Finset G} {q:ℝ} {aq:ℕ}
  {aU:ℝ} (hq:0≤q) {n:ℕ}
  {s t:aA original}
  (h:cU q aq aU n s t) :
  q^n*s.density≤t.density:=
 h.forget.qZ hq
lemma card_bound {original:Finset G} {q:ℝ} {aq:ℕ}
  {aU:ℝ} {n:ℕ} {s t:aA original}
  (h:cU q aq aU n s t) :
  exp (-(n:ℝ)*aU)*(s.card:ℝ)≤(t.card:ℝ):=
 h.forget.card_bound
end cU
def dn (A C:Finset G) (x:G):Finset G:=
 (C.filter fun c=>x-c∈A).image fun c=>-c
omit [Fintype G] in
@[simp] lemma e4 {A C:Finset G} {x z:G} :
  z∈dn A C x↔ -z∈C∧x+z∈A:=by
 classical
 simp only[dn,mem_image,mem_filter]
 constructor
 ·rintro ⟨c,⟨hc,OW⟩,rfl⟩
  exact ⟨by simpa,by simpa[Qy] using OW⟩
 ·rintro ⟨OX,Nm⟩
  refine ⟨-z, ?_,by simp⟩
  exact ⟨OX,by simpa[Qy] using Nm⟩
omit [Fintype G] in
lemma wZ (A C:Finset G) (x:G) :
  (dn A C x).card=(C.filter fun c=>x-c∈A).card:=by
 classical
 unfold dn
 rw[Finset.card_image_of_injective]
 intro a b h
 exact neg_injective h
lemma dz
  {B:aj G} {a8:NNReal} {A C:Finset G} {x:G}
  (hC:C⊆(B.ai a8).carrier) :
  dn A C x⊆(B.ai a8).carrier:=by
 intro z hz
 have OY:=(e4.mp hz).1
 exact aj.ec.mp (hC OY)
lemma bk
  {A C:Finset G} (_hC:C.Nonempty) (x:G) :
  a9 A C x=(dn A C x).card/(C.card:ℝ):=by
 classical
 rw[a9,ao]
 let e := Equiv.subLeft x
 rw[Qk e
  (fun y:G=>bs A y*af C (x-y))
  (fun c:G=>bs A (x-c)*af C c)
  (fun c=>by simp[e])]
 rw[wZ]
 simp only[bs,af,Qw]
 have gX (c:G) :
   (if x-c∈A then (1:ℝ) else 0) *
     (if c∈C then (C.card:ℝ)⁻¹ else 0) =
    if c∈C∧x-c∈A then (C.card:ℝ)⁻¹ else 0:=by
  by_cases hc:c∈C<;>by_cases ha:x-c∈A<;>simp[hc,ha]
 simp_rw[gX]
 rw[←QE]
 have eI :
   (Finset.univ.filter fun c:G=>c∈C∧x-c∈A) =
    C.filter fun c=>x-c∈A:=by
  ext c
  simp
 rw[eI]
 simp
open Function MeasureTheory
open scoped ENNReal Pointwise
omit [AddCommGroup G] [Fintype G] in
lemma hZ (A:Finset G) :
  ag.aS A=(@mu ℝ _ _) A:=by
 funext x
 simp[ag.aS,mu_apply]
lemma eg (aX a3:Finset G) :
  ag.a2
    (ag.aS aX)
    (ag.aS a3) =
   (al ((@mu ℝ _ _) aX) (mu a3)):=by
 funext x
 rw[hZ,hZ,
  ag.a2,eL]
 simp
lemma os
  (aX a3 S:Finset G) (t:G) :
  ((aC (((aC ((@mu (ℂ) _ _) (-aX)) (((indicator S fun _↦(1:_)):G→ℂ))))) (mu a3))) t =
   Complex.ofReal
    (ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S)):=by
 classical
 let a:G→ℝ:=(@mu ℝ _ _) aX
 let b:G→ℝ:=(@mu ℝ _ _) a3
 let kK:G→ℝ:=(indicator S fun _↦(1:_))
 have qG :
   ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S) =
    ⟪τ t ((al a b)),kK⟫_[ℝ]:=by
  rw[eg]
  unfold ag.bC
   ag.bJ
  simp only[Sg,SV,
   R3,QZ,a,b,kK,Qm,
   mem_coe]
 have uO :
   ((aC (((aC ((@mu ℝ _ _) (-aX)) kK))) b)) t =
    ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S):=by
  calc
   _ =
     ((aC (((aC kK b))) ((@mu ℝ _ _) (-aX)))) t:=by
      apply Uu
      calc
       _ =
         (aC kK (((aC ((@mu ℝ _ _) (-aX)) b)))):=by
          rw[fA ((@mu ℝ _ _) (-aX)) kK,
           iS]
       _=(aC kK (((aC b ((@mu ℝ _ _) (-aX)))))):=by
          rw[fA ((@mu ℝ _ _) (-aX)) b]
       _=(aC (((aC kK b))) ((@mu ℝ _ _) (-aX))):=by
          rw[iS]
   _=((al (((aC kK b))) a)) t:=by
    rw[←CB (K:=ℝ) aX,iM]
   _=⟪τ t a,(aC kK b)⟫_[ℝ]:=by
    rw[tV]
    exact RCLike.conj_wInner_symm (𝕜:=ℝ)
     (1:G→ℝ) ((aC kK b)) (τ t a)
   _=⟪(al (τ t a) b),kK⟫_[ℝ]:=
         (kY
     (τ t a) b kK).symm
   _=⟪τ t ((al a b)),kK⟫_[ℝ]:=by rw[rl]
   _=_:=qG.symm
 have LO:((↑) ∘ kK:G→ ℂ)=((indicator S fun _↦(1:_)):G→ ℂ):=by
  ext x
  by_cases hx:x∈S<;>simp[kK,hx]
 rw[←uO]
 change((aC (((aC ((@mu ℂ _ _) (-aX)) (((indicator S fun _↦(1:_)):G→ ℂ))))) (mu a3))) t =
  (Complex.ofReal ∘ ((aC (((aC ((@mu ℝ _ _) (-aX)) kK))) b))) t
 rw[Complex.qo,Complex.qo]
 simp only[Complex.yL,b]
 rw[LO]
lemma ca
  (aX a3 S:Finset G) :
  ag.bC
    (ag.a2
     (ag.aS aX)
     (ag.aS a3))
    (ag.bJ S) =
   ∑ x∈S,((al ((@mu ℝ _ _) aX) (mu a3))) x:=by
 classical
 rw[eg]
 unfold ag.bC
  ag.bJ
 simp only[Td,Q3,mul_zero]
 rw[←QE]
 have eI:Finset.univ.filter (fun x:G=>x∈S)=S:=by ext; simp
 rw[eI]
lemma nn
  {D:aj G} {aX a3 S:Finset G} {epsilon delta:ℝ}
  (fY:aX.Nonempty) (g9:a3.Nonempty)
  (ft:1-delta≤ ∑ x∈S,((al ((@mu ℝ _ _) aX) (mu a3))) x)
  (uj: ∀ t∈D.carrier,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    epsilon*(aX.card:ℝ)*a3.card) :
  1-delta-epsilon ≤
   ag.bC
    (ag.d9
     (ag.aS D.carrier)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S):=by
 have Nn:=
  ag.ji
   fY g9 uj
 have dc :
   1-delta ≤
    ag.bC
     (ag.a2
      (ag.aS aX)
      (ag.aS a3))
     (ag.bJ S):=by
  rwa[ca]
 have ic:=(abs_le.mp Nn).1
 linarith
section zS
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
def bj (A aL a0:Finset G) (p:ℕ):ℝ:=
 (4:ℝ)⁻¹ *
   (b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))^(2*p) /
  (A.card:ℝ)^(2*p)
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kL
  (A:Finset G) (x:G) :
  (cA.ef A x:ℝ) =
   ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))) x:=by
 classical
 rw[cA.ef,eL]
 have qG :
   ((#(Finset.univ.filter fun t:G↦x-t∈A∧ -t∈A):ℕ):ℝ) =
    ∑ t:G,if x-t∈A∧ -t∈A then (1:ℝ) else 0:=by
  simp
 rw[qG]
 refine Qk (Equiv.subLeft x) _ _ (fun y↦ ?_)
 simp only[SX,Qm]
 have eY:x-y-x= -y:=by abel
 rw[eY]
 split_ifs<;>simp_all
lemma gQ
  (A aL a0:Finset G) (p:ℕ) (hp:p≠0)
  (rK:aL.Nonempty) (u2:a0.Nonempty) :
  (∑ u:Fin p→G,
    ((cA.cS A aL u).card:ℝ) *
     (cA.cS A a0 u).card) =
   (aL.card:ℝ)*a0.card *
    (b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))))^p:=by
 classical
 let gH:G→ℝ:=(al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))
 have rL: ∀ x,0≤gH x:=fun x ↦
  dM Set.cY Set.cY x
 have nX:=cA.v3 A aL a0 p (fun _↦(1:ℝ))
 have kB :
   (∑ u:Fin p→G,
     cA.wM (cA.cS A aL u)
      (cA.cS A a0 u) (fun _↦(1:ℝ))) =
    ∑ u:Fin p→G,
     ((cA.cS A aL u).card:ℝ) *
      (cA.cS A a0 u).card:=by
  apply Io rfl
  intro u _
  simp[cA.wM]
 have oO :
   (∑ ey∈aL, ∑ b₂∈a0,
     (cA.ef A (ey-b₂):ℝ)^p) =
    ∑ x:G,((al ((indicator aL fun _↦(1:ℝ))) ((indicator a0 fun _↦(1:_))))) x*gH x^p:=by
  rw[lM]
  simp[Qm,gH,kL]
 have t9 :
   ((al ((indicator aL fun _↦(1:ℝ))) ((indicator a0 fun _↦(1:_))))) =
    fun x↦(aL.card:ℝ)*a0.card *
     ((al ((@mu ℝ _ _) aL) (mu a0))) x:=by
  ext x
  simp only[eL,Qm,mu_apply]
  rw[Qj]
  apply Io rfl
  intro y _
  by_cases hy:y∈aL<;>by_cases Es:y-x∈a0
  ·simp only[mem_coe,RP hy,RP Es,Rc,
    star_trivial,Q3]
   have yf:(aL.card:ℝ)≠0:=by
    exact_mod_cast rK.card_ne_zero
   have yg:(a0.card:ℝ)≠0:=by
    exact_mod_cast u2.card_ne_zero
   field_simp
  ·simp[hy,Es]
  ·simp[hy]
  ·simp[hy]
 have oS:=jd hp
  ((al ((@mu NNReal _ _) aL) (mu a0))) gH
 rw[kB] at nX
 simp only[Q3] at nX
 calc
  _

                          =
    ∑ ey∈aL, ∑ b₂∈a0,
     (cA.ef A (ey-b₂):ℝ)^p:=by
   simpa using nX
  _ =
    ∑ x:G,((al ((indicator aL fun _↦(1:ℝ))) ((indicator a0 fun _↦(1:_))))) x*gH x^p:=
         oO
  _=(aL.card:ℝ)*a0.card *
     ∑ x:G,((al ((@mu ℝ _ _) aL) (mu a0))) x*gH x^p:=by
   rw[t9]
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  _=(aL.card:ℝ)*a0.card *
    (b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))))^p:=by
   congr 1
   rw[oS]
   apply Io rfl
   intro x _
   simp only[RG,Q2,QK,
    QC (rL x),NNReal.lg,
    NNReal.iF,gH]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
theorem qH (A B : Finset G) (p : ℕ) :
    (∑ u : Fin p → G, ((cA.cS A B u).card : ℝ)) =
      (A.card : ℝ) ^ p * B.card:= by
  classical
  have sC :
      ∑ u : Fin p → G, (cA.cS A B u).card =
        A.card ^ p * B.card:= by
    simp only [lN, cA.cS,
      Set.indicator_apply, mem_coe, mem_filter,
      mul_sum, sum_mul, @sum_comm G, Fintype.piFinset_univ,
      sum_pow']
    congr with b
    refine Fintype.sum_equiv (Equiv.subLeft fun _ : Fin p ↦ b) _ _ (fun u ↦ ?_)
    simp only [Equiv.subLeft_apply]
    by_cases hb : b ∈ B
    · simp only [hb, true_and, if_pos, mul_one]
      rw [Fintype.prod_boole]
      simp only [Pi.sub_apply]
      by_cases h : ∀ i : Fin p, b - u i ∈ A <;> simp [h]
    · simp [hb]
  exact_mod_cast sC
lemma pZ
  (A aL a0:Finset G) (p:ℕ) (u3:2≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  ∃ u:Fin p→G,
   (cA.cS A aL u).Nonempty ∧
   (cA.cS A a0 u).Nonempty ∧
   bj A aL a0 p ≤
    ((cA.cS A aL u).card:ℝ)/aL.card ∧
   bj A aL a0 p ≤
    ((cA.cS A a0 u).card:ℝ)/a0.card:=by
 classical
 have hp:p≠0:=by omega
 have rK:aL.Nonempty:=hB.mono inter_subset_left
 have u2:a0.Nonempty:=hB.mono inter_subset_right
 have u4:A.Nonempty:=hA
 let aX:(Fin p→G)→Finset G:=fun u↦cA.cS A aL u
 let a3:(Fin p→G)→Finset G:=fun u↦cA.cS A a0 u
 let N:ℝ:=(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))))
 let g:(Fin p→G)→ℝ:=fun u↦(aX u).card*(a3 u).card
 have hg: ∀ u,0≤g u:=fun u↦by dsimp[g]; positivity
 have Aj: ∑ u,g u=(aL.card:ℝ)*a0.card*N^p:=by
  simpa[g,aX,a3,N] using
   gQ A aL a0 p hp rK u2
 obtain ⟨b,hb⟩:=hB
 obtain ⟨a,ha⟩:=hA
 let sD:Fin p→G:=fun _↦b-a
 have v8:b∈aX sD:=by
  simp only[aX,cA.jn,sD]
  refine ⟨(inter_subset_left hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v9:b∈a3 sD:=by
  simp only[a3,cA.jn,sD]
  refine ⟨(inter_subset_right hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rY:0< ∑ u,g u:=by
  exact Finset.sum_pos' (fun u _↦hg u) ⟨sD,Sz _,by
   dsimp only[g]
   exact QM (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v8⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v9⟩))⟩
 have Hh:0<N^p:=by
  have jt:0<(aL.card:ℝ)*a0.card:=by positivity
  rw[Aj] at rY
  rcases mul_pos_iff.mp rY with gy | eY
  ·exact gy.2
  ·exact(Rd jt.le eY.1).elim
 let M:ℝ:=
  2⁻¹ *N^p*(Real.sqrt aL.card*Real.sqrt a0.card) /
   (A.card:ℝ)^p
 have hM:0<M:=by
  dsimp[M]
  have J4:(0:ℝ)<A.card:=by exact_mod_cast u4.card_pos
  have yf:(0:ℝ)<aL.card:=by exact_mod_cast rK.card_pos
  have yg:(0:ℝ)<a0.card:=by exact_mod_cast u2.card_pos
  exact Rn (QM (QM (by norm_num) Hh)
   (QM (Real.sqrt_pos.2 yf) (Real.sqrt_pos.2 yg)))
   (RF J4 p)
 have H7: ∑ u,((aX u).card:ℝ)=(A.card:ℝ)^p*aL.card:=by
  simpa[aX] using qH A aL p
 have H8: ∑ u,((a3 u).card:ℝ)=(A.card:ℝ)^p*a0.card:=by
  simpa[a3] using qH A a0 p
 have mC: ∃ u,M^2≤g u:=by
  by_cases h: ∀ u,g u≠0→M^2≤g u
  ·have vH: ∃ u,g u≠0:=by
    by_contra hn
    push Not at hn
    have: ∑ u,g u=0:=by simp[hn]
    linarith
   obtain ⟨u,hu⟩:=vH
   exact ⟨u,h u hu⟩
  ·push Not at h
   obtain ⟨u₁,H9,Ge⟩:=h
   have Ap:(2:ℝ)* ∑ u with g u<M^2,g u< ∑ u,g u:=by
    rw[←lt_div_iff₀' (by norm_num:(0:ℝ)<2),Ri]
    calc
     ∑ u with g u<M^2,g u =
       ∑ u with g u<M^2∧g u≠0,
        Real.sqrt (g u)*Real.sqrt (g u):=by
      simp_rw[Ta (hg _), ←Finset.filter_filter,
       Finset.sum_filter_ne_zero]
     _< ∑ u with g u<M^2∧g u≠0,
        M*Real.sqrt (g u):=by
      apply Tt
      ·exact ⟨u₁,Finset.mem_filter.mpr ⟨Sz _,Ge,H9⟩⟩
      ·intro u hu
       have OZ:=(Finset.mem_filter.mp hu).2.1
       have No:=(Finset.mem_filter.mp hu).2.2
       exact Sk ((Real.sqrt_lt' hM).2 OZ)
        (Real.sqrt_pos.2 ((hg u).lt_of_ne' No))
     _≤ ∑ u,M*Real.sqrt (g u):=
      Tj fun u↦by positivity
     _=M*(∑ u,Real.sqrt ((aX u).card) *
        Real.sqrt ((a3 u).card)):=by
      rw[Qj]
      apply Io rfl
      intro u _
      dsimp only[g]
      rw[Real.sqrt_mul (by positivity:(0:ℝ)≤(aX u).card)]
     _≤M*(Real.sqrt (∑ u,((aX u).card:ℝ)) *
        Real.sqrt (∑ u,((a3 u).card:ℝ))):=by
      gcongr
      exact Real.sum_sqrt_mul_sqrt_le _ (fun _↦by positivity)
       (fun _↦by positivity)
     _=(2:ℝ)⁻¹ * ∑ u,g u:=by
      dsimp only[M]
      rw[H7,H8,Real.sqrt_mul' _ (by positivity),
       Real.sqrt_mul' _ (by positivity),
       Q7 (Real.sqrt _),Ta,
       ←Qo,Tz, ←Real.sqrt_mul,
       Qo,Ta,Aj,QN,Qo]
      all_goals positivity
   by_contra z4
   push Not at z4
   have Dn: ∑ u,g u= ∑ u with g u<M^2,g u:=by
    congr 1
    symm
    exact Finset.filter_eq_self.mpr (fun u _↦z4 u)
   rw[Dn] at Ap
   linarith
 obtain ⟨u,hu⟩:=mC
 have te:bj A aL a0 p ≤
   (((aX u).card:ℝ)/aL.card) *
    (((a3 u).card:ℝ)/a0.card):=by
  dsimp[bj,M,N,g] at hu ⊢
  have J4:(A.card:ℝ)≠0:=by exact_mod_cast u4.card_ne_zero
  have yf:(aL.card:ℝ)≠0:=by exact_mod_cast rK.card_ne_zero
  have yg:(a0.card:ℝ)≠0:=by exact_mod_cast u2.card_ne_zero
  rw[div_mul_div_comm,Qs (by positivity)]
  simpa[QL,TY,pow_mul',show(2:ℝ)^2=4 by norm_num,
   Uf (show 0≤(aL.card:ℝ) by positivity),
   Uf (show 0≤(a0.card:ℝ) by positivity),
   J4,yf,yg,S5] using hu
 have J5:0<g u:=(SY hM).trans_le hu
 have EJ:0<((aX u).card:ℝ)*(a3 u).card:=by
  simpa only[g] using J5
 have EK:0<((aX u).card:ℝ)∧0<((a3 u).card:ℝ):=by
  rcases mul_pos_iff.mp EJ with gy | eY
  ·exact gy
  ·exact(Rd (Q5 _) eY.1).elim
 have xB:0<((aX u).card:ℝ):=EK.1
 have Gf:0<((a3 u).card:ℝ):=EK.2
 refine ⟨u,Finset.card_pos.mp (by exact_mod_cast xB),
  Finset.card_pos.mp (by exact_mod_cast Gf), ?_, ?_⟩
 ·have sa:((a3 u).card:ℝ)≤a0.card:=by
   exact_mod_cast Qu (cA.kJ A a0 u)
  exact te.trans (Sq (by positivity)
   ((Q9 (by positivity:(0:ℝ)<a0.card)).2 sa))
 ·have r9:((aX u).card:ℝ)≤aL.card:=by
   exact_mod_cast Qu (cA.kJ A aL u)
  exact te.trans (RQ (by positivity)
   ((Q9 (by positivity:(0:ℝ)<aL.card)).2 r9))
structure aW (A aL a0:Finset G)
  (p:ℕ) (epsilon delta:ℝ) where
 aX:Finset G
 a3:Finset G
 u5:aX⊆aL
 rM:a3⊆a0
 oW:1-delta ≤
  ag.bC
   (ag.a2
    (ag.aS aX)
    (ag.aS a3))
   (ag.bJ (s p epsilon aL a0 A))
 tC:bj A aL a0 p ≤
  (aX.card:ℝ)/aL.card
 tD:bj A aL a0 p ≤
  (a3.card:ℝ)/a0.card
namespace aW
def bg
  (A aL a0:Finset G) (p:ℕ) (epsilon:ℝ):Finset G:=
 s p epsilon aL a0 A∩(aL-a0)
omit [DiscreteMeasurableSpace G] in
lemma oX
  (A aL a0:Finset G) (p:ℕ) (epsilon:ℝ) :
  bg A aL a0 p epsilon⊆aL-a0:=
 Sd
omit [DiscreteMeasurableSpace G] in
lemma lR
  {A aL a0:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (data:aW A aL a0 p epsilon delta)
  (cu:delta<1):data.aX.Nonempty∧data.a3.Nonempty:=by
 have ft:1-delta ≤
   ∑ x∈s p epsilon aL a0 A,((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oW
 constructor
 ·by_contra wa
  have su := not_nonempty_iff_eq_empty.mp wa
  rw[su] at ft
  simp at ft
  linarith
 ·by_contra wa
  have su := not_nonempty_iff_eq_empty.mp wa
  rw[su] at ft
  simp at ft
  linarith
omit [DiscreteMeasurableSpace G] in
lemma np
  {A aL a0:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (data:aW A aL a0 p epsilon delta) :
  1-delta ≤
   ag.bC
    (ag.a2
     (ag.aS data.aX)
     (ag.aS data.a3))
    (ag.bJ
     (bg A aL a0 p epsilon)):=by
 have Ia:1-delta ≤
   ∑ x∈s p epsilon aL a0 A,
    ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oW
 have hsum :
   ∑ x∈bg A aL a0 p epsilon,
     ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x =
    ∑ x∈s p epsilon aL a0 A,
     ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  apply Ro Sh
  intro x xC LP
  rw[←UQ]
  intro Np
  apply LP
  have EL :
    x∈Function.support ((al ((@mu ℝ _ _) data.aX) (mu data.a3))):=Np
  have J6:x∈data.aX-data.a3:=by
   simpa only[f8 cC cC,jo,
    ←coe_sub,mem_coe] using EL
  obtain ⟨a₁,z5,a₂,z6,Hi⟩:=Finset.mem_sub.mp J6
  exact Finset.mem_inter.mpr ⟨xC,
   Finset.mem_sub.mpr ⟨a₁,data.u5 z5,a₂,
    data.rM z6,Hi⟩⟩
 rw[ca,hsum]
 exact Ia
omit [DiscreteMeasurableSpace G] in
lemma gL
  {A aL a0:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (data:aW A aL a0 p epsilon delta)
  (cu:delta<1) :
  (bg A aL a0 p epsilon).Nonempty:=by
 by_contra z4
 have su :=
  not_nonempty_iff_eq_empty.mp z4
 have ft:=data.np
 rw[su] at ft
 simp[ag.bC,
  ag.bJ] at ft
 linarith
end aW
lemma q9
  {A:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (aL a0:Finset G) (eM:0<epsilon) (tE:epsilon≤1)
  (cu:0<delta) (hp:Even p) (u3:2≤p)
  (wb:epsilon⁻¹ *log (2/delta)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (oP: ∃ x,x∈aL-a0∧x∈A-A ∧
   x∉s p epsilon aL a0 A) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 obtain ⟨aX,fY,a3,g9,ft,y6,y7⟩:=
  cA.v7 aL a0 eM tE cu hp u3
   wb hB hA oP
 refine ⟨{
  aX:=aX
  a3:=a3
  u5:=fY
  rM:=g9
  oW:= ?_
  tC:= ?_
  tD:= ?_ }⟩
 ·rwa[ca]
 ·simpa only[bj] using y6
 ·simpa only[bj] using y7
lemma ma
  {A:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (aL a0:Finset G) (cu:0<delta) (u3:2≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (kI: ∀ x,x∈aL-a0→x∈A-A →
   x∈s p epsilon aL a0 A) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 classical
 obtain ⟨u,fY,g9,y6,y7⟩:=
  pZ A aL a0 p u3 hB hA
 let aX:=cA.cS A aL u
 let a3:=cA.cS A a0 u
 have Co:aX⊆aL:=cA.kJ A aL u
 have Cp:a3⊆a0:=cA.kJ A a0 u
 have hp:0<p:=by omega
 let i:Fin p:=⟨0,hp⟩
 have LQ:aX-a3⊆s p epsilon aL a0 A:=by
  intro x hx
  obtain ⟨a₁,z5,a₂,z6,Hi⟩:=Finset.mem_sub.mp hx
  apply kI x
  ·exact Finset.mem_sub.mpr ⟨a₁,Co z5,a₂,Cp z6,Hi⟩
  ·have J7:=(cA.jn.mp z5).2 i
   have J8:=(cA.jn.mp z6).2 i
   refine Finset.mem_sub.mpr ⟨a₁-u i,J7,a₂-u i,J8, ?_⟩
   rw[←Hi]
   abel
 have hsum :
   ∑ x∈s p epsilon aL a0 A,((al ((@mu ℝ _ _) aX) (mu a3))) x=1:=by
  calc
   ∑ x∈s p epsilon aL a0 A,((al ((@mu ℝ _ _) aX) (mu a3))) x =
     ∑ x:G,((al ((@mu ℝ _ _) aX) (mu a3))) x:=by
    apply Ro (S7 _)
    intro x _ LS
    rw[←UQ]
    intro Nq
    apply LS
    apply LQ
    have LU:x∈Function.support ((al ((@mu ℝ _ _) aX) (mu a3))):=Nq
    simpa only[f8 cC cC,jo,
     ←coe_sub,mem_coe] using LU
   _=1:=by
    rw[jJ]
    simp only[Rc,star_trivial]
    rw[kW _ (by simpa[aX] using fY),
     kW _ (by simpa[a3] using g9),QT]
 refine ⟨{
  aX:=aX
  a3:=a3
  u5:=Co
  rM:=Cp
  oW:= ?_
  tC:=by simpa[aX] using y6
  tD:=by simpa[a3] using y7 }⟩
 rw[ca,hsum]
 linarith
lemma kM
  {A:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (aL a0:Finset G) (eM:0<epsilon) (tE:epsilon≤1)
  (cu:0<delta) (hp:Even p) (u3:2≤p)
  (wb:epsilon⁻¹ *log (2/delta)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 classical
 by_cases oP: ∃ x,x∈aL-a0∧x∈A-A ∧
   x∉s p epsilon aL a0 A
 ·exact q9 aL a0 eM tE
   cu hp u3 wb hB hA oP
 ·apply ma aL a0 cu u3 hB hA
  intro x O0 Ek
  by_contra O1
  exact oP ⟨x,O0,Ek,O1⟩
structure cb
  {A aL a0:Finset G} {p:ℕ} {epsilon delta:ℝ}
  (data:aW A aL a0 p epsilon delta)
  (parent:aj G) (dR:NNReal)
  (source:Finset G) (aq bq:ℕ)
  (bm:ℝ) where
 child:aj G
 k6:child.a1
 rN:child.rank≤parent.rank+aq
 tF:child.carrier⊆(parent.ai dR).carrier
 nM:source.card≤bq*child.carrier.card
 oY: ∀ t∈child.carrier,
  |ag.bW
    data.aX data.a3
     (aW.bg A aL a0 p epsilon) t -
   ag.bW
    data.aX data.a3
     (aW.bg A aL a0 p epsilon) 0| ≤
   bm*(data.aX.card:ℝ)*data.a3.card
def cb.mono
  {A aL a0:Finset G} {p:ℕ} {epsilon delta:ℝ}
  {data:aW A aL a0 p epsilon delta}
  {parent:aj G} {dR:NNReal} {source:Finset G}
  {aq bq zs tf:ℕ}
  {bm lA:ℝ}
  (P:cb data parent dR source
   aq bq bm)
  (cK:aq≤zs)
  (ch:bq≤tf)
  (EI:bm≤lA) :
  cb data parent dR source
   zs tf lA where
 child:=P.child
 k6:=P.k6
 rN:=P.rN.trans (Nat.add_le_add_left cK _)
 tF:=P.tF
 nM:=P.nM.trans
  (QQ P.child.carrier.card ch)
 oY:=by
  intro t ht
  calc
   _

     ≤ bm*(data.aX.card:ℝ)*data.a3.card:=
    P.oY t ht
   _≤lA*(data.aX.card:ℝ)*data.a3.card:=by
    gcongr
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kN
  (D aX a3:Finset G) :
  ag.d9
    (ag.aS D)
    (ag.a2
     (ag.aS aX)
     (ag.aS a3)) =
   (aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3))))):=by
 funext x
 rw[hZ,
  eg,
  ag.d9,cR]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma j9
  (D aX a3 S:Finset G) :
  ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S) =
   ∑ x∈S,((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
 classical
 rw[kN]
 unfold ag.bC
  ag.bJ
 simp only[Td,Q3,mul_zero]
 rw[←QE]
 have eI:Finset.univ.filter (fun x:G↦x∈S)=S:=by ext; simp
 rw[eI]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lW
  {D aX a3 S:Finset G} {gH:G→ℝ}
  {mass threshold:ℝ}
  (oZ:0≤threshold)
  (rL: ∀ x,0≤gH x)
  (sE: ∀ x∈S,threshold≤gH x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S)) :
  threshold*mass ≤
   ∑ x:G,((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=by
 classical
 rw[j9] at ft
 have zt: ∀ x:G,
   0≤((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
  intro x
  exact pC cC
   (fun y↦dM cC cC y) x
 calc
  _ ≤
    threshold* ∑ x∈S,
     ((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=
   iO ft oZ
  _= ∑ x∈S,
    threshold*((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
   rw[Qj]
  _≤ ∑ x∈S,
    ((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=by
   apply QI
   intro x hx
   rw[Qx threshold]
   exact iO (sE x hx) (zt x)
  _≤ ∑ x:G,
    ((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=
         Tj fun x ↦
    Qn (zt x) (rL x)
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mD
  {w f:G→ℝ} (hw: ∀ x,0≤w x)
  (u6: ∑ x:G,w x=1) {lower:ℝ}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x:G,lower≤f x:=by
 classical
 obtain ⟨x,_hx,Dp⟩:=
  TX Finset.univ f (Finset.univ_nonempty :
   (Finset.univ:Finset G).Nonempty)
 refine ⟨x,ic.trans ?_⟩
 calc
  _ ≤ ∑ y:G,w y*f x:=by
   apply QI
   intro y _
   exact iO (Dp y (by simp)) (hw y)
  _=f x:=by rw[←Qt,u6,QT]
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lB
  {w f:G→ℝ} {T:Finset G} (hT:T.Nonempty)
  (hw: ∀ x,0≤w x) (wc: ∀ x,x∉T→w x=0)
  (u6: ∑ x:G,w x=1) {lower:ℝ}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x∈T,lower≤f x:=by
 classical
 obtain ⟨x,O2,Dp⟩:=TX T f hT
 refine ⟨x,O2,ic.trans ?_⟩
 calc
  _ ≤ ∑ y:G,w y*f x:=by
   apply QI
   intro y _
   by_cases hy:y∈T
   ·exact iO (Dp y hy) (hw y)
   ·rw[wc y hy,zero_mul,zero_mul]
  _=f x:=by rw[←Qt,u6,QT]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lC
  (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→ℝ) =
   (aC (((al ((@mu ℝ _ _) D) (mu E)))) (((al (mu E) (mu D))))):=by
 unfold aN.bh
  aN.dU
 simp only[NNReal.gF,NNReal.oD,
  NNReal.iF]
 symm
 rw[kr,fA ((@mu ℝ _ _) E) (mu D)]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kp
  (D E:Finset G) (f:G→ℝ) (p:ℕ) :
  aK
    ((↑) ∘ aN.bh D E) f p =
   ∑ z:G,((al ((@mu ℝ _ _) D) (mu E))) z *
    aK
     (fun x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) f p:=by
 rw[lC]
 unfold aK
 simp_rw[cR,Qt]
 rw[QD]
 apply Io rfl
 intro z _
 rw[Qj]
 apply Io rfl
 intro x _
 ring
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lD
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (f:G→ℝ) (p:ℕ) {lower:ℝ}
  (ic:lower≤aK
   ((↑) ∘ aN.bh D E) f p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤aK ((al ((@mu ℝ _ _) (z+ᵥ E)) (mu D))) f p:=by
 let w:G→ℝ:=(al ((@mu ℝ _ _) D) (mu E))
 let F:G→ℝ:=fun z ↦
  aK (fun x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) f p
 have O3:(D-E).Nonempty:=by
  obtain ⟨d,hd⟩:=hD
  obtain ⟨e,he⟩:=hE
  refine ⟨d-e, ?_⟩
  exact Finset.mem_sub.mpr ⟨d,hd,e,he,rfl⟩
 have hw: ∀ z,0≤w z:=by
  intro z
  exact dM cC cC z
 have wc: ∀ z,z∉D-E→w z=0:=by
  intro z hz
  rw[←UQ]
  intro O4
  apply hz
  have EM:z∈Function.support w:= O4
  simpa only[w,f8 cC cC,
   jo, ←coe_sub,mem_coe] using EM
 have u6: ∑ z:G,w z=1:=by
  dsimp only[w]
  rw[jJ]
  simp only[Rc,star_trivial]
  rw[kW _ hD,kW _ hE,QT]
 have Gg:lower≤ ∑ z:G,w z*F z:=by
  rw[←kp]
  exact ic
 obtain ⟨z,hz,y8⟩:=
  lB O3 hw wc u6 Gg
 obtain ⟨d,hd,e,he,O5⟩:=Finset.mem_sub.mp hz
 refine ⟨z,hz, ?_, ?_⟩
 ·refine ⟨d,Finset.mem_inter.mpr ⟨?_,hd⟩⟩
  rw[Ug]
  refine ⟨e,he, ?_⟩
  rw[←O5]
  simp only[Uz]
  exact Rs d e
 ·dsimp only[F] at y8
  have t9 :
    (fun x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) =
     (al ((@mu ℝ _ _) (z+ᵥ E)) (mu D)):=by
   rw[←vI,rl]
   rfl
  rw[t9] at y8
  exact y8
lemma lE
  {D E A:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (_hA:A.Nonempty) {p:ℕ} (hp:0<p) {lower:ℝ}
  (AV:0≤lower)
  (ic:lower ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu ℝ _ _) A) (mu A))) p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤(b0 p ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu ℝ _ _) A) (mu A)))):=by
 let nu:=aN.bh D E
 have rq:an.cw
   ((↑) ∘ nu:G→ℝ):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(aN.gS D E x)
  ·simpa using QA (fun r:NNReal↦(r:ℝ))
    (aN.i7 hD hE)
 have yW:lower^p ≤
   aK ((↑) ∘ nu:G→ℝ)
    ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  calc
   lower^p ≤
     an.aM
       ((↑) ∘ nu:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p^p:=
    Qp AV ic p
   _=aK ((↑) ∘ nu:G→ℝ)
     ((al ((@mu ℝ _ _) A) (mu A))) p:=
    an.jr rq hp
 obtain ⟨z,hz,um,EN⟩:=
  lD hD hE
   ((al ((@mu ℝ _ _) A) (mu A))) p (by simpa[nu] using yW)
 let u7:G→NNReal:=(al ((@mu NNReal _ _) (z+ᵥ E)) (mu D))
 have rK:(z+ᵥ E).Nonempty:=by
  obtain ⟨e,he⟩:=hE
  refine ⟨z+e, ?_⟩
  rw[Ug]
  exact ⟨e,he,rfl⟩
 have Hj:an.cw
   ((↑) ∘ u7:G→ℝ):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(dM cC cC x:0≤u7 x)
  ·dsimp only[u7]
   simp only[NNReal.gF,NNReal.iF]
   rw[jJ]
   simp only[Rc,star_trivial]
   rw[kW _ rK,kW _ hD,QT]
 have Dq:lower^p ≤
   aK ((↑) ∘ u7:G→ℝ)
    ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  simpa only[u7,NNReal.gF,NNReal.iF] using EN
 have EO:lower^p ≤
   an.aM
     ((↑) ∘ u7:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p^p:=by
  rw[an.jr Hj hp]
  exact Dq
 have AW:0 ≤
   an.aM
    ((↑) ∘ u7:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p:=
  an.j3 Hj _ _
 have yh:lower ≤
   an.aM
    ((↑) ∘ u7:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  by_contra hnot
  have xS:=QV hnot
  have LV:=pow_lt_pow_left₀ xS AW hp.ne'
  exact(Rd EO) LV
 refine ⟨z,hz,um, ?_⟩
 rw[aN.dN u7
  ((al ((@mu ℝ _ _) A) (mu A))) hp] at yh
 exact yh
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma m0
  {A D:Finset G} (hA:A.Nonempty) (x:G) :
  (A.card:ℝ)*((aC ((@mu ℝ _ _) D) (mu A))) x=a9 A D x:=by
 classical
 rw[cR,a9,ao,Qj]
 let e := Equiv.subLeft x
 rw[Qk e
  (fun z:G↦(A.card:ℝ)*((@mu ℝ _ _) D z*mu A (x-z)))
  (fun y:G↦(A.card:ℝ)*((@mu ℝ _ _) D (x-y)*mu A y))]
 ·apply Io rfl
  intro y _
  simp only[mu_apply,bs,af]
  have sF:(A.card:ℝ)≠0:=by exact_mod_cast hA.card_ne_zero
  by_cases J9:y∈A
  ·by_cases Ka:x-y∈D
   ·simp only[RP J9,RP Ka,Q3]
    calc
     _ =
       (D.card:ℝ)⁻¹ *((A.card:ℝ)*(A.card:ℝ)⁻¹):=by ring
     _=(D.card:ℝ)⁻¹:=by rw[Tw sF,Q3]
     _=1*(D.card:ℝ)⁻¹:=by rw[QT]
   ·simp[J9,Ka]
  ·simp[J9]
 ·intro y
  simp[e]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma p0
  (d a₁ a₂ a:G→ℝ) :
  ⟪(aC d (((al a₁ a₂)))),(al a a)⟫_[ℝ] =
   ⟪(aC d a),(aC (((al a₂ a₁))) a)⟫_[ℝ]:=by
 rw[ro,ro]
 congr 1
 change(al (((al a a))) (((al a₁ a₂))))=(al (((aC (((al a₂ a₁))) a))) a)
 simp_rw[←iM,pL,conjneg_conjneg]
 calc
  _ =
    (aC (((aC a (conjneg a₁)))) (((aC (conjneg a) a₂)))):=
   ir _ _ _ _
  _=(aC (((aC (conjneg a₁) a))) (((aC a₂ (conjneg a))))):=by
   rw[fA a,fA (conjneg a) a₂]
  _=(aC (((aC (conjneg a₁) a₂))) (((aC a (conjneg a))))):=
   ir _ _ _ _
  _=(aC (((aC (((aC a₂ (conjneg a₁)))) a))) (conjneg a)):=by
   rw[fA (conjneg a₁) a₂]
   exact(iS _ _ _).symm
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma jy
  {D aX a3 A S:Finset G}
  (_hD:D.Nonempty) (fY:aX.Nonempty)
  (g9:a3.Nonempty) (hA:A.Nonempty)
  {threshold mass lower:ℝ} (oZ:0≤threshold)
  (rL: ∀ x,0≤((al ((@mu ℝ _ _) A) (mu A))) x)
  (sE: ∀ x∈S,threshold≤((al ((@mu ℝ _ _) A) (mu A))) x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S))
  (ic:lower≤threshold*mass) :
  ∃ x:G,(A.card:ℝ)*lower≤a9 A D x:=by
 have EP:=lW oZ rL
  sE ft
 have xD:=p0
  ((@mu ℝ _ _) D) (mu aX) (mu a3) (mu A)
 rw[Sg,Sg] at xD
 simp only[SV,R3] at xD
 let w:G→ℝ:=(aC (((al ((@mu ℝ _ _) a3) (mu aX)))) (mu A))
 let f:G→ℝ:=(aC ((@mu ℝ _ _) D) (mu A))
 have hw: ∀ x,0≤w x:=by
  intro x
  exact pC
   (fun y↦dM cC cC y) cC x
 have u6: ∑ x:G,w x=1:=by
  dsimp only[w]
  rw[uM,jJ]
  simp only[Rc,star_trivial]
  rw[kW _ g9,kW _ fY,QT,
   kW _ hA,Q3]
 have Ay:lower≤ ∑ x:G,w x*f x:=by
  calc
   _ ≤threshold*mass:=ic
   _≤ ∑ x:G,
     ((aC ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*((al (mu A) (mu A))) x:=
    EP
   _= ∑ x:G,w x*f x:=by
    rw[xD]
    apply Io rfl
    intro x _
    rw[Qx]
 obtain ⟨x,hx⟩:=mD hw u6 Ay
 refine ⟨x, ?_⟩
 rw[←m0 hA]
 exact iO hx (Q5 _)
end zS
lemma bK
  {A C:Finset G} (hC:C.Nonempty) {x:G}
  (hx:0<a9 A C x) :
  (dn A C x).Nonempty:=by
 by_contra h
 have Gh: ¬ 0<(dn A C x).card:=by
  intro ch
  exact h (Finset.card_pos.mp ch)
 have ch := Nat.eq_zero_of_not_pos Gh
 rw[bk hC,ch] at hx
 norm_num at hx
structure bt where
 ba:aj G
 outer:NNReal
 inner:NNReal
 regular:0< inner∧inner≤outer ∧
  (ba.ai (outer+inner)).carrier.card ≤
   2*(ba.ai (outer-inner)).carrier.card
namespace bt
def carrier (c:bt (G:=G)):Finset G:=
 (c.ba.ai c.outer).carrier
omit [DecidableEq G] in
lemma aE (c:bt (G:=G)):c.carrier.Nonempty:=
 (c.ba.ai c.outer).aE
def eo (c:bt (G:=G))
  (A:Finset G) (hA:A.Nonempty) (ER:A⊆c.carrier) :
  aY G where
 ba:=c.ba
 outer:=c.outer
 inner:=c.inner
 regular:=c.regular
 set:=A
 nonempty:=hA
 mw:=ER
omit [DecidableEq G] in
lemma od (B:aj G) (dF:B.a1) :
    ∃ c:bt (G:=G),
      c.ba=B∧c.outer=1∧c.carrier=B.carrier:=by
  let d:ℕ:=max B.rank 1
  let aF:NNReal:=1/(400*(d:NNReal))
  have hd:0<d:=by simp[d]
  have ES:0<aF:=by
    dsimp[aF]
    positivity
  have zu:aF≤1/(100*(d:NNReal)):=by
    dsimp[aF]
    apply Rb (by positivity) (by positivity)
    exact Qi (by norm_num:(100:NNReal)≤400)
      (by positivity)
  have ET:aF≤1:=by
    apply zu.trans
    rw[Q9]
    · exact_mod_cast(show 1≤100*d by omega)
    · positivity
  have jt:=dF aF (by simpa[d] using zu)
  have Ax:(100:ℝ)*d*(aF:ℝ)≤1/4:=by
    have LW:(aF:ℝ)≤1/(400*(d:ℝ)):=by
      exact_mod_cast(show aF≤1/(400*(d:NNReal)) by rfl)
    have O6:(0:ℝ)<d:=by exact_mod_cast hd
    calc
      (100:ℝ)*d*(aF:ℝ) ≤
          100*d*(1/(400*(d:ℝ))):=by gcongr
      _=1/4:=by field_simp; ring
  have EU :
      ((B.ai (1+aF)).carrier.card:ℝ) ≤
        2*((B.ai (1-aF)).carrier.card:ℝ):=by
    nlinarith[jt.1,jt.2,Ax,
      show(0:ℝ)<B.carrier.card by
        exact_mod_cast B.aE.card_pos]
  have ch :
      (B.ai (1+aF)).carrier.card ≤
        2*(B.ai (1-aF)).carrier.card:=by
    exact_mod_cast EU
  let c:bt (G:=G):=
    { ba:=B
      outer:=1
      inner:=aF
      regular:=⟨ES,ET,ch⟩ }
  refine ⟨c,rfl,rfl, ?_⟩
  simp only[carrier,c,aj.oG]
end bt
def di {original:Finset G} (s:aA original)
  (child:bt (G:=G)) (x:G)
  (gy:0<a9 s.restriction.set child.carrier x) :
  aA original where
 restriction:=child.eo
  (dn s.restriction.set child.carrier x)
  (bK child.aE gy)
  (dz (B:=child.ba) (a8:=child.outer)
   (A:=s.restriction.set) (C:=child.carrier) (x:=x) fun _ h=>h)
 shift:=s.shift-x
 eR:=by
  intro z hz
  have O7:=(e4.mp hz).2
  have gM:=s.eR (x+z) O7
  have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
  rwa[heq]
@[simp] lemma hQ {original:Finset G}
  (s:aA original) (child:bt (G:=G)) (x:G)
  (gy:0<a9 s.restriction.set child.carrier x) :
  (di s child x gy).density =
   a9 s.restriction.set child.carrier x:=by
 change((dn s.restriction.set child.carrier x).card:ℝ) /
   child.carrier.card=a9 s.restriction.set child.carrier x
 exact(bk child.aE x).symm
lemma fb
  {original:Finset G} (s:aA original)
  (child:bt (G:=G)) (x:G)
  {q aU:ℝ} {aq:ℕ}
  (gy:0<a9 s.restriction.set child.carrier x)
  (c8:q*s.density ≤
   a9 s.restriction.set child.carrier x)
  (cK:child.ba.rank≤ s.rank+aq)
  (ch:exp (-aU)*(s.card:ℝ)≤child.carrier.card) :
  dk q aq aU s.restriction
   (di s child x gy).restriction:=by
 refine ⟨?_,cK, ?_⟩
 ·change q*s.density ≤
   ((dn s.restriction.set child.carrier x).card:ℝ) /
    child.carrier.card
  rw[←bk child.aE]
  exact c8
 ·change exp (-aU)*(s.restriction.card:ℝ) ≤
   child.carrier.card
  exact ch
section sG
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma nq
  {D:aj G} {aX a3 S:Finset G} {error:ℝ}
  (fY:aX.Nonempty) (g9:a3.Nonempty)
  (jl: ∀ t∈D.carrier,
   (aJ (∞) (τ t ((aC (((aC ((@mu ℂ _ _) (-aX)) (((indicator S fun _↦(1:_)):G→ ℂ))))) (mu a3))) -
     ((aC (((aC ((@mu ℂ _ _) (-aX)) (((indicator S fun _↦(1:_)):G→ ℂ))))) (mu a3))))) ≤
    error) :
  ∀ t∈D.carrier,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:ℝ)*a3.card:=by
 classical
 let F:G→ ℂ:=
  (aC (((aC ((@mu ℂ _ _) (-aX)) (((indicator S fun _↦(1:_)):G→ ℂ))))) (mu a3))
 have hF (u:G) :
   F u=Complex.ofReal
    (ag.bW aX a3 S u /
     (aX.card*a3.card:ℝ)):=by
  dsimp only[F]
  rw[os]
  congr 1
  exact ag.d7
   fY g9 S u
 intro t ht
 have eY: -t∈D.carrier:=aj.ec.mpr ht
 have gX :
   ‖(τ (-t) F-F) 0‖ ≤error:=by
  calc
   ‖(τ (-t) F-F) 0‖ ≤(aJ (∞) (τ (-t) F-F)):=
    vw
   _≤error:=by simpa only[F] using jl (-t) eY
 have Hk :
   |(ag.bW aX a3 S t -
     ag.bW aX a3 S 0) /
     (aX.card*a3.card:ℝ)| ≤error:=by
  rw[Rw,QZ,sub_neg_eq_add,zero_add,
   hF t,hF 0, ←Complex.ofReal_sub,Rf,QK,
   ←UT] at gX
  exact gX
 have ch:(0:ℝ)<(aX.card:ℝ)*a3.card:=
  QM (by exact_mod_cast fY.card_pos) (by exact_mod_cast g9.card_pos)
 rw[TE,RT ch] at Hk
 have pO:=(QF ch).mp Hk
 nlinarith
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma hU
  (aX a3 S:Finset G) (t:G) :
  ag.bW a3 aX (-S) t =
   ag.bW aX a3 S (-t):=by
 classical
 unfold ag.bW
 rw[QD]
 apply Io rfl
 intro a₁ _
 apply Io rfl
 intro a₂ _
 have F7 (u:G) :
   ag.bJ (-S) u =
    ag.bJ S (-u):=by
  by_cases hu:u∈ -S
  ·have eY: -u∈S:=by simpa using hu
   simp[ag.bJ,hu,eY]
  ·have eY: -u∉S:=by
    intro h
    apply hu
    simpa using h
   simp[ag.bJ,hu,eY]
 rw[F7]
 have uY: -(t+a₂-a₁)= -t+a₁-a₂:=by abel
 rw[uY]
 ring
lemma h4
  {D:aj G} {aX a3 S:Finset G} {error:ℝ}
  (fY:aX.Nonempty) (g9:a3.Nonempty)
  (jl: ∀ t∈D.carrier,
   (aJ (∞) (τ t ((aC (((aC ((@mu ℂ _ _) (-a3)) (((indicator ((-S:Finset G)) fun _↦(1:_)):G→ ℂ))))) (mu aX))) -
     ((aC (((aC ((@mu ℂ _ _) (-a3)) (((indicator ((-S:Finset G)) fun _↦(1:_)):G→ ℂ))))) (mu aX))))) ≤
    error) :
  ∀ t∈D.carrier,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:ℝ)*a3.card:=by
 classical
 have dc:=nq
  (D:=D) (aX:=a3) (a3:=aX) (S:=-S) (error:=error)
  g9 fY jl
 intro t ht
 have eY := aj.ec.mpr ht
 have h:=dc (-t) eY
 rw[hU aX a3 S (-t),
  hU aX a3 S 0] at h
 simpa[Qx,Q6,Qo] using h
noncomputable def mb (M L:Finset G):ℕ:=
 ⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
noncomputable def cm
  (M L:Finset G) (dv:ℝ) (m:ℕ):ℕ:=
 cQ (mb M L)
  ((dv/m)/exp 1)
lemma ej
    {A aL a0:Finset G} {p:ℕ} {sigma delta:ℝ}
    (data:aW A aL a0 p sigma delta)
    (cu:delta<1)
    (dv:ℝ) (sH:0<dv)
    (m:ℕ) (hm:m≠0)
    (bl:aj G) (sx:bl.a1)
    (aF:NNReal)
    (dy:aF+aF ≤
      1/(100*(max bl.rank 1:ℕ):NNReal))
    (dh:ℕ) (pX:0<dh)
    (bm:ℝ)
    (dV: ∀ (T:Finset G) (Delta:Finset (AddChar G ℂ)),
      (Delta.card:ℝ) ≤
        aI.bf bl T (1/2) →
      2*dv +
          (2/(dh:ℝ) +
            400*((max bl.rank 1:ℕ):ℝ) *
              (aF+aF:NNReal) +
            2*(1/2:ℝ)^m) *
          Real.sqrt
            (((aW.bg A aL a0 p sigma).card:ℝ) /
              data.aX.card)≤bm) :
    ∃ (T X:Finset G) (a8:NNReal) (fl:aj G)
      (Delta:Finset (AddChar G ℂ)),
      ((((-data.a3).card:ℝ) ^
            cm
              (-(aW.bg A aL a0 p sigma))
              data.aX dv m/2*bl.carrier.card) /
          ((-data.a3+bl.carrier).card:ℝ) ^
            cm
              (-(aW.bg A aL a0 p sigma))
              data.aX dv m≤T.card) ∧
      T⊆bl.carrier∧X.Nonempty ∧
      (Delta.card:ℝ) ≤
        aI.bf bl T (1/2) ∧
      1/2≤a8∧a8≤1 ∧
      fl=bl.ai (a8 *
        aI.cJ bl T (1/2)) ∧
      Nonempty
        (cb data fl (aF+aF)
          (fl.ai aF).carrier Delta.card
          ((dh*ag.a6
              (aI.bf bl T (1/2))) ^
              Delta.card *
            4^(bl.rank+Delta.card))
          bm):=by
  classical
  let S :=
    aW.bg A aL a0 p sigma
  have gN:=data.lR cu
  have Gi:(-data.a3).Nonempty:=by
    obtain ⟨a,ha⟩:=gN.2
    exact ⟨-a,by simpa using ha⟩
  have hS:S.Nonempty:=by
    simpa[S] using data.gL cu
  have LX:(-S).Nonempty:=by
    obtain ⟨s,hs⟩:=hS
    exact ⟨-s,by simpa using hs⟩
  obtain ⟨T,X,z,a8,fl,Delta,R,ui,_hzT,_hX,
      pT,nk,gJ,lj,oU,AT,
      fH,_hDeltaSpec,qk,oT,yc,vZ,
      jl⟩:=
    ag.fk
      (A:=-data.a3) Gi dv sH m hm
      (-S) data.aX LX gN.1 bl sx aF dy
      dh pX
  let n :=
    dh*ag.a6
      (aI.bf bl T (1/2))
  let p3:ℝ:=
    2*dv +
      (4*pi*(Delta.card:ℝ) *
          ((((n:ℕ):NNReal)⁻¹ :ℝ)) +
        400*((max bl.rank 1:ℕ):ℝ) *
          (aF+aF:NNReal) +
        2*(1/2:ℝ)^m) *
      Real.sqrt ((S.card:ℝ)/data.aX.card)
  have l7 :
      4*pi*(Delta.card:ℝ) *
          ((((n:ℕ):NNReal)⁻¹ :ℝ))≤2/(dh:ℝ):=by
    simpa[n] using
      (ag.sw
        (aI.bf bl T (1/2))
        Delta.card dh fH pX)
  have nX:p3≤bm:=by
    calc
      _ ≤
          2*dv +
            (2/(dh:ℝ) +
              400*((max bl.rank 1:ℕ):ℝ) *
                (aF+aF:NNReal) +
              2*(1/2:ℝ)^m) *
            Real.sqrt ((S.card:ℝ)/data.aX.card):=by
        dsimp only[p3]
        gcongr
      _≤bm:=by simpa[S] using dV T Delta fH
  refine ⟨T,X,a8,fl,Delta, ?_,ui,pT,fH,
    gJ,lj,oU,⟨?_⟩⟩
  · simpa[S,cm,mb] using nk
  refine
    { child:=R
      k6:=qk
      rN:= ?_
      tF:=yc
      nM:= ?_
      oY:= ?_ }
  · simpa[oU] using oT
  · simpa[n,SZ] using vZ
  · have uj:=h4
      gN.1 gN.2 (D:=R) (error:=p3) (by
        intro t ht
        simpa[S,n,p3,Qo] using jl t ht)
    intro t ht
    calc
      _

          ≤ p3*(data.aX.card:ℝ)*data.a3.card:=by
            simpa[S] using uj t ht
      _≤bm*(data.aX.card:ℝ)*data.a3.card:=by
        gcongr
end sG
def bV {original:Finset G} (s:aA original)
  (ak aB:bt (G:=G)) (epsilon:ℝ):Prop:=
 ∃ x∈s.e9,
  (1-epsilon)*s.density ≤
   a9 s.restriction.set ak.carrier x ∧
  (1-epsilon)*s.density ≤
   a9 s.restriction.set aB.carrier x
structure kO {original:Finset G}
  (s:aA original) (epsilon aU:ℝ)
  (aq:ℕ) where
 eta:NNReal
 NZ:s.restriction.ba.vT s.restriction.outer eta
 ak:bt (G:=G)
 aB:bt (G:=G)
 nY:ak.carrier ⊆
  (s.restriction.ba.ai eta).carrier
 p4:aB.carrier ⊆
  (s.restriction.ba.ai eta).carrier
 rankOne:ak.ba.rank≤ s.rank+aq
 p5:aB.ba.rank≤ s.rank+aq
 mE:exp (-aU)*(s.card:ℝ)≤ak.carrier.card
 mF:exp (-aU)*(s.card:ℝ)≤aB.carrier.card
end
end ay.ah
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay.fu
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
lemma ot (f g:G→ℝ) :
  ao f g=(aC f g):=by
 funext x
 rw[ao,cR]
lemma es (f g:G→ℝ) :
  aZ f g=(al f g):=by
 funext x
 rw[aZ,eL]
 simp
lemma k7 (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→ℝ) =
   hJ.c4 D E:=by
 rw[hJ.c4,
  ot,
  es,
  es]
 simp only[aN.bh,
  aN.dU,NNReal.gF,
  NNReal.oD,NNReal.iF,
  aN.eQ]
 exact(kr
  (af D) (af D)
  (af E) (af E)).symm
omit [DecidableEq G] in
private lemma pr
  (a:G→ℝ) (p:ℕ) (x:G) :
  |ao a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=QA norm
  (jw.k2 a a x)
 simp only[Rf,QO,UA] at h
 have h': |ao a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖:=by
  simpa only[QK] using h
 rw[h',QL]
omit [DecidableEq G] in
private lemma k8
  (a:G→ℝ) (p:ℕ) (x:G) :
  |aZ a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=QA norm
  (jw.ga a x)
 simp only[Rf,QO,UA] at h
 have h': |aZ a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖:=by
  simpa only[QK] using h
 rw[h',QL]
omit [DecidableEq G] in
private lemma ka
  (w a:G→ℝ) (p:ℕ) :
  aK w (ao a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold aK
 rw[Qj]
 apply Io rfl
 intro x _
 rw[pr]
 ring
omit [DecidableEq G] in
private lemma h5
  (w a:G→ℝ) (p:ℕ) :
  aK w (aZ a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold aK
 rw[Qj]
 apply Io rfl
 intro x _
 rw[k8]
 ring
lemma ra
  {B:aj G} {eta:ℝ≥0} {D E:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mA:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hD:D.Nonempty) (hE:E.Nonempty)
  (gn:D⊆(B.ai eta).carrier)
  (lk:E⊆(B.ai eta).carrier)
  {p:ℕ} (hp:p≠0) (mx:Even p) (a:G→ℝ) :
  aK (af B.carrier)
    (ao a a) p ≤
   2*aK
    ((↑) ∘ aN.bh D E)
    (aZ a a) p:=by
 have h:=hJ.kF
  dF fC mA hD hE gn lk hp mx ((↑) ∘ a)
 rw[←k7 D E] at h
 have c3:0≤(Fintype.card G:ℝ)^p:=by positivity
 have hmul:=iO h c3
 rw[ka,
  h5]
 nlinarith
lemma tG
  {B:aj G} {eta:ℝ≥0} {D E:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mA:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hD:D.Nonempty) (hE:E.Nonempty)
  (gn:D⊆(B.ai eta).carrier)
  (lk:E⊆(B.ai eta).carrier)
  {p:ℕ} (hp:0<p) (mx:Even p) (a:G→ℝ) :
  an.aM (af B.carrier)
    (ao a a) p ≤
   2*an.aM
    ((↑) ∘ aN.bh D E)
    (aZ a a) p:=by
 have ju:an.cw
   (af B.carrier):=
  ⟨bO B.carrier,
   cf B.aE⟩
 have rq:an.cw
   ((↑) ∘ aN.bh D E):=
  ⟨fun x↦by
   exact_mod_cast(show 0≤aN.bh D E x by
    exact aN.gS D E x),
   by
    simpa using QA (fun z:ℝ≥0↦(z:ℝ))
     (aN.i7 hD hE)⟩
 apply an.lv
  ju rq hp
 exact ra dF fC mA hD hE gn lk
  hp.ne' mx a
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma nr
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zq:A⊆B.carrier)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (kI: ∀ t,aN.bh D E t≠0 →
   t∈(B.ai aF).carrier)
  {epsilon:ℝ} (eM:0<epsilon) (oV:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.carrier.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(B.carrier.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  {tH pI:G→ℝ}
  (ju:an.cw tH)
  (lh :
   an.aM tH pI
     (an.bS p) ≤
    2*an.aM
     ((↑) ∘ aN.bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.carrier)) ((mu A-mu B.carrier))))
     (an.bS p))
  (qv :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz epsilon p) <
    (1+epsilon/8)*(B.carrier.card:ℝ)⁻¹) :
  an.aM tH pI p ≤
   epsilon*(B.carrier.card:ℝ)⁻¹:=by
 let nu:=aN.bh D E
 have ft :=
  aN.i7 hD hE
 have rq:an.cw ((↑) ∘ nu):=
  ⟨fun x↦by
   exact_mod_cast(show 0≤nu x by
    exact aN.gS D E x),
   by simpa using QA (fun z:ℝ≥0↦(z:ℝ)) ft⟩
 have ch:(0:ℝ)<B.carrier.card:=by
  exact_mod_cast B.aE.card_pos
 have fF := inv_pos.mpr ch
 apply an.nP
   ju rq eM fF hp (by simpa[nu] using lh) _
   (by simpa[nu] using qv)
 intro iU
 obtain ⟨r,hr,_hreven,Jh,Ib⟩:=
  aN.uk dF hA zq hD hE dy
   kI eM oV d5 hp (by simpa[nu] using iU)
 exact ⟨r,hr,Jh,by simpa[nu] using Ib⟩
end
end ay.fu
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def rO (m:ℕ) (w r:ℝ):Fin (2*m+1):=
 ⟨min ⌊((r+w)*(m:ℝ))/w⌋₊ (2*m),
  Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩
lemma ou
  {m:ℕ} (hm:0< m) {w r s:ℝ}
  (hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (lP:rO m w r=rO m w s) :
  |r-s| ≤w/(m:ℝ):=by
 by_cases vq:w=0
 ·subst w
  have O8:r=0:=by
   apply abs_eq_zero.mp
   exact SC hr (Q8 r)
  have O9:s=0:=by
   apply abs_eq_zero.mp
   exact SC hs (Q8 s)
  simp[O8,O9]
 have z7 := SM hw (Ne.symm vq)
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 let ur:ℝ:=((r+w)*(m:ℝ))/w
 let us:ℝ:=((s+w)*(m:ℝ))/w
 have MO: -w≤r∧r≤w:=(abs_le.mp hr)
 have MP: -w≤ s∧s≤w:=(abs_le.mp hs)
 have Kb:0≤ur:=by
  dsimp[ur]
  exact RS (Qn (by linarith) qD.le) hw
 have Kc:0≤us:=by
  dsimp[us]
  exact RS (Qn (by linarith) qD.le) hw
 have Kd:ur≤(2*m:ℕ):=by
  dsimp[ur]
  apply(QF z7).2
  push_cast
  nlinarith
 have Ke:us≤(2*m:ℕ):=by
  dsimp[us]
  apply(QF z7).2
  push_cast
  nlinarith
 have KT:⌊ur⌋₊<2*m+1:=by
  apply(Uc Kb).2
  exact lt_of_le_of_lt Kd (by exact_mod_cast(Tr (2*m)))
 have KU:⌊us⌋₊<2*m+1:=by
  apply(Uc Kc).2
  exact lt_of_le_of_lt Ke (by exact_mod_cast(Tr (2*m)))
 have BS:⌊ur⌋₊≤2*m:=by omega
 have BT:⌊us⌋₊≤2*m:=by omega
 have vW:⌊ur⌋₊=⌊us⌋₊:=by
  have q4:=QA Fin.val lP
  simpa only[rO,ur,us,Nat.min_eq_left BS,
   Nat.min_eq_left BT] using q4
 have MQ := Ti Kb
 have EV := RY ur
 have MR := Ti Kc
 have EW := RY us
 have IZ:ur<us+1:=by
  calc
   ur<((⌊ur⌋₊:ℕ):ℝ)+1:=EV
   _=((⌊us⌋₊:ℕ):ℝ)+1:=by rw[vW]
   _≤us+1:=by gcongr
 have I0:us<ur+1:=by
  calc
   us<((⌊us⌋₊:ℕ):ℝ)+1:=EW
   _=((⌊ur⌋₊:ℕ):ℝ)+1:=by rw[←vW]
   _≤ur+1:=by gcongr
 have yi :
   ur-us=((r-s)*(m:ℝ))/w:=by
  dsimp[ur,us]
  field_simp
  ring
 have BU:((r-s)*(m:ℝ))/w<1:=by
  rw[←yi]
  linarith
 have BV:(-1:ℝ)<((r-s)*(m:ℝ))/w:=by
  rw[←yi]
  linarith
 have Dr:(r-s)*(m:ℝ)<w:=by
  have h:=(Tv z7).mp BU
  simpa only[QT] using h
 have Ds: -w<(r-s)*(m:ℝ):=by
  have h:=(SP z7).mp BV
  simpa only[neg_one_mul] using h
 have Kf:r-s<w/(m:ℝ):=
  (SP qD).2 Dr
 have ic: -(w/(m:ℝ))<r-s:=by
  have h:=(Tv qD).2 Ds
  simpa only[neg_div] using h
 exact(abs_lt.2 ⟨ic,Kf⟩).le
def fv (B:aj G) (a8:NNReal) (m:ℕ)
  (x:↥(B.ai a8).carrier):B.eX→Fin (2*m+1):=
 fun γ ↦
  rO m ((a8:ℝ)*(B.width γ.1:ℝ))
   (cx (γ.1 x.1))
omit [DecidableEq G] in
private lemma kP
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m)
  {x y:↥(B.ai a8).carrier}
  (ni:B.fv a8 m x=B.fv a8 m y) :
  x.1-y.1∈(B.ai (a8/(m:NNReal))).carrier:=by
 rw[mem_carrier]
 intro γ oa
 have hx:=(mem_carrier (B.ai a8) x.1).mp x.2 γ oa
 have hy:=(mem_carrier (B.ai a8) y.1).mp y.2 γ oa
 simp only[oF,SK] at hx hy ⊢
 rw[map_sub]
 have CW :
   |cx (γ x.1)| ≤(a8:ℝ)*(B.width γ:ℝ):=by
  rwa[←hH]
 have CX :
   |cx (γ y.1)| ≤(a8:ℝ)*(B.width γ:ℝ):=by
  rwa[←hH]
 have vU:=Uu ni ⟨γ,oa⟩
 have hdiv:= ou hm
  (Qn (by positivity) (by positivity)) CW CX vU
 calc
  _ ≤
    |cx (γ x.1)-cx (γ y.1)|:=
   gu _ _
  _≤((a8:ℝ)*(B.width γ:ℝ))/(m:ℝ):=hdiv
  _=((a8/(m:NNReal):NNReal):ℝ) *
    (B.width γ:ℝ):=by
   push_cast
   field_simp
omit [DecidableEq G] in
private lemma ps
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m)
  (a:B.eX→Fin (2*m+1)) :
  Fintype.card
    {x:↥(B.ai a8).carrier// B.fv a8 m x=a} ≤
   (B.ai (a8/(m:NNReal))).carrier.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai a8).carrier// B.fv a8 m x=a}
 ·let x₀  :=

   Classical.choice jv
  let f :
    {x:↥(B.ai a8).carrier// B.fv a8 m x=a} →
     ↥(B.ai (a8/(m:NNReal))).carrier:=
   fun x ↦
    ⟨x.1.1-x₀.1.1,
     kP B a8 hm
      (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have q4:=QA Subtype.val ni
   dsimp[f] at q4
   exact S8 q4
  calc
   _
                                            ≤
     Fintype.card ↥(B.ai (a8/(m:NNReal))).carrier:=
    R1 f hf
   _=(B.ai (a8/(m:NNReal))).carrier.card:=
    Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma h6
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m) :
  (B.ai a8).carrier.card ≤
   (2*m+1)^B.rank *
    (B.ai (a8/(m:NNReal))).carrier.card:=by
 classical
 let S:=B.eX→Fin (2*m+1)
 let q := B.fv a8 m
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai a8).carrier// q x=a} ≤
    (B.ai (a8/(m:NNReal))).carrier.card:=by
  intro a
  exact ps B a8 hm a
 have AA:Fintype.card S=(2*m+1)^B.rank:=by
  dsimp[S,rank]
  rw[TC]
  simp
 rw[←Rx (B.ai a8).carrier, ←AA]
 by_contra h
 have xS :
   Fintype.card S*(B.ai (a8/(m:NNReal))).carrier.card <
    Fintype.card ↥(B.ai a8).carrier:=by omega
 obtain ⟨a,ha⟩:=
  Rk (f:=q) xS
 have Em: #{x | q x=a} ≤
   (B.ai (a8/(m:NNReal))).carrier.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Em) ha
omit [DecidableEq G] in
lemma cM
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m) :
  (B.ai a8).carrier.card ≤
   (3*m)^B.rank *
    (B.ai (a8/(m:NNReal))).carrier.card:=by
 classical
 calc
  _ ≤
    (2*m+1)^B.rank *
     (B.ai (a8/(m:NNReal))).carrier.card:=
   h6 B a8 hm
  _≤(3*m)^B.rank *
     (B.ai (a8/(m:NNReal))).carrier.card:=by
   apply QQ
   apply R4
   omega
end aj
end
end ay
end
section
open Finset
open scoped NNReal Pointwise
namespace ay
noncomputable section

lemma lX
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (X:Finset G) {beta eta:ℝ}
  (hV:0<beta) (fC:0<eta)
  (hX:X.Nonempty)
  (ch:beta*(B.carrier.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X eta ≤
   2*(1+log (2/beta))/eta^2:=by
 have wN:(0:ℝ)<B.carrier.card:=by
  exact_mod_cast B.aE.card_pos
 have LY:(0:ℝ)<X.card:=by
  exact_mod_cast hX.card_pos
 have eO :
   2*(B.carrier.card:ℝ)/X.card≤2/beta:=by
  rw[Sy LY hV]
  nlinarith
 have Ic:0<2*(B.carrier.card:ℝ)/X.card:=by
  positivity
 have ei  :=

  QG Ic eO
 have Kg := SY fC
 rw[aI.bf]
 apply(R9 Kg).2
 nlinarith
lemma fQ
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (X:Finset G) {beta:ℝ}
  (hV:0<beta) (hX:X.Nonempty)
  (ch:beta*(B.carrier.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X (1/2) ≤
   8*(1+log (2/beta)):=by
 have h:=
  lX B X hV
   (by norm_num:(0:ℝ)<1/2) hX ch
 convert h using 1
 ring
lemma ov
  {α:Type*} (S:Finset α) {D:ℝ}
  (ch:(S.card:ℝ)≤D) :
  S.card≤⌈D⌉₊:=by
 exact_mod_cast ch.trans (Rr D)
end
end ay
end
section
open Finset
open scoped NNReal
namespace ay.ar
noncomputable section
def ax (d aq:ℕ):ℕ:=
 1024*(d+1)*aq
def bn (d aq:ℕ):ℕ:=
 819200*ax d aq*2^d
def bd (d aq:ℕ):ℕ:=
 76800*ax d aq*2^(d+1)
lemma iH {d aq:ℕ} (cE:0<aq) :
  0<ax d aq:=by
 unfold ax
 positivity
lemma y9 {d aq:ℕ} (cE:0<aq) :
  1≤ax d aq:=
 Nat.one_le_iff_ne_zero.mpr (iH cE).ne'
lemma i8 {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  max r 1≤ax d aq:=
       max_le cK (y9 cE)
lemma mc {d aq:ℕ} (cE:0<aq) :
  0<bn d aq:=by
 unfold bn
 exact QP
  (QP (by norm_num) (iH cE))
  (RF (by norm_num) _)
lemma md {d aq:ℕ} (cE:0<aq) :
  0<bd d aq:=by
 unfold bd
 exact QP
  (QP (by norm_num) (iH cE))
  (RF (by norm_num) _)
lemma p6 {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  100*max r 1≤bn d aq:=by
 have lF:=i8 cE cK
 unfold bn
 calc
  _ ≤100*ax d aq:=
   Qr 100 lF
  _≤819200*ax d aq*2^d:=by
   have qI:100≤819200:=by omega
   calc
    _ ≤819200*ax d aq:=
     QQ _ qI
    _≤819200*ax d aq*2^d:=
     Q4 _ (RF (by norm_num) _)
lemma tI {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  ((bn d aq:NNReal)⁻¹) ≤
   1/(100*(max r 1:ℕ):NNReal):=by
 rw[R6]
 have kB:(0:NNReal)<bn d aq:=by
  exact_mod_cast mc cE
 have oO:(0:NNReal)<100*(max r 1:ℕ):=by
  positivity
 apply(RJ kB oO).2
 exact_mod_cast p6 cE cK
lemma wd {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq)
  {density:ℝ}
  (c8:1/(2:ℝ)^d≤density) :
  400*((max r 1:ℕ):ℝ) *
    ((((bn d aq:ℕ):NNReal)⁻¹ :NNReal):ℝ) ≤
   (1/512:ℝ)*density/4:=by
 change 400*((max r 1:ℕ):ℝ) *
   (bn d aq:ℝ)⁻¹ ≤(1/512:ℝ)*density/4
 have lF:=i8 cE cK
 have EX :
   819200*max r 1*2^d≤bn d aq:=by
  unfold bn
  exact QQ (2^d)
   (Qr 819200 lF)
 have hbound :
   (819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d ≤
    (bn d aq:ℝ):=by
  exact_mod_cast EX
 have Hl:(0:ℝ)<bn d aq:=by
  exact_mod_cast mc cE
 have xE :
   (0:ℝ)<(819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d:=by
  positivity
 have hinv :
   (bn d aq:ℝ)⁻¹ ≤
    ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹:=
  (RJ Hl xE).2 hbound
 calc
  _ ≤
    400*((max r 1:ℕ):ℝ) *
     ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹:=by
   gcongr
  _=(1/2048:ℝ)*(1/(2:ℝ)^d):=by
   have tc:(0:ℝ)<(max r 1:ℕ):=by positivity
   have Ie:(0:ℝ)<(2:ℝ)^d:=by positivity
   field_simp
   ring
  _≤(1/2048:ℝ)*density:=by
   gcongr
  _=(1/512:ℝ)*density/4:=by ring
lemma nZ {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  200*max r 1≤bd d aq:=by
 have lF:=i8 cE cK
 unfold bd
 calc
  _ ≤200*ax d aq:=
   Qr 200 lF
  _≤76800*ax d aq*2^(d+1):=by
   have qI:200≤76800:=by omega
   calc
    _ ≤76800*ax d aq:=
     QQ _ qI
    _≤76800*ax d aq*2^(d+1):=
     Q4 _ (RF (by norm_num) _)
lemma rb {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  (bd d aq:NNReal)⁻¹ +(bd d aq:NNReal)⁻¹ ≤
   1/(100*(max r 1:ℕ):NNReal):=by
 have si:=nZ cE cK
 have kB:(0:NNReal)<bd d aq:=by
  exact_mod_cast md cE
 have oO:(0:NNReal)<200*(max r 1:ℕ):=by
  positivity
 have hinv :
   (bd d aq:NNReal)⁻¹ ≤
    (200*(max r 1:ℕ):NNReal)⁻¹:=by
  apply(RJ kB oO).2
  exact_mod_cast si
 calc
  _ ≤
    (200*(max r 1:ℕ):NNReal)⁻¹ +
     (200*(max r 1:ℕ):NNReal)⁻¹:=
   Sr hinv hinv
  _=1/(100*(max r 1:ℕ):NNReal):=by
   have tc:(0:NNReal)<(max r 1:ℕ):=by positivity
   field_simp
   norm_num
end
end ay.ar
end
section
open Filter Finset
open scoped Topology
namespace ay
noncomputable def r3 (N:ℕ):ℕ:=
 addRothNumber (Finset.Icc 1 N)
lemma vC (N:ℕ):r3 N=rothNumberNat N:=by
 rw[r3, ←Finset.Ico_add_one_right_eq_Icc,addRothNumber_Ico]
 simp
lemma nt
  {c beta:ℝ} (hc:0<c) (hV:0<beta) (C:ℝ) :
  Tendsto
   (fun N:ℕ =>
    (log (N:ℝ))^C *
     exp (-c*(log (N:ℝ))^beta))
   atTop (nhds 0):=by
 have ei:Tendsto (fun N:ℕ=>log (N:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp Sa
 have hpow:Tendsto (fun N:ℕ=>(log (N:ℝ))^beta) atTop atTop:=
  (UR hV).comp ei
 have h:=
  (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C/beta) c hc).comp hpow
 refine h.congr' ?_
 filter_upwards[eventually_gt_atTop 1] with N hN
 have ql:0≤log (N:ℝ):=
  Qv (by exact_mod_cast hN.le)
 change
  ((log (N:ℝ))^beta)^(C/beta) *
    exp (-c*(log (N:ℝ))^beta) =
   (log (N:ℝ))^C *
    exp (-c*(log (N:ℝ))^beta)
 congr 1
 rw[←S0 ql]
 congr 1
 field_simp[hV.ne']
lemma m1
  {K c beta:ℝ} (hK:0≤K) (hc:0<c) (hV:0<beta)
  (AX: ∀ᶠ N:ℕ in atTop,
   (r3 N:ℝ) ≤
    K*(N:ℝ)*exp (-c*(log (N:ℝ))^beta))
  (C:ℝ) :
  (fun N:ℕ=>(r3 N:ℝ))=O[atTop]
   (fun N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 have we:=
  nt hc hV C
 have dV: ∀ᶠ N:ℕ in atTop,
   (log (N:ℝ))^C *
     exp (-c*(log (N:ℝ))^beta)≤1:=
  we.eventually (Iic_mem_nhds (by norm_num:(0:ℝ)<1))
 refine Asymptotics.IsBigO.of_bound K ?_
 filter_upwards[AX,dV,eventually_gt_atTop 1] with N hbound Ig hN
 have zv:0≤(N:ℝ):=by positivity
 have Gj:0<log (N:ℝ):=
  Sv (by exact_mod_cast hN)
 have w7:0<(log (N:ℝ))^C:=
  SQ Gj C
 rw[RA (Q5 (r3 N))]
 rw[RA (RS zv w7.le)]
 apply hbound.trans
 have Ih :
   exp (-c*(log (N:ℝ))^beta) ≤
    1/(log (N:ℝ))^C:=by
  rw[Qs w7]
  simpa[Qx] using Ig
 calc
  K*(N:ℝ)*exp (-c*(log (N:ℝ))^beta) ≤
    K*(N:ℝ)*(1/(log (N:ℝ))^C):=
   iO Ih (Qn hK zv)
  _=K*((N:ℝ)/(log (N:ℝ))^C):=by ring
end ay
end
section
open scoped BigOperators
open Finset
namespace ay
namespace aw
variable {G:Type*} [Fintype G] [AddCommGroup G]
noncomputable def uo (f:G→ℝ):ℝ:=
 (∑ x,f x)/Fintype.card G
noncomputable def indicator (C:Finset G) (x:G):ℝ:=
 open scoped Classical in
 if x∈C then 1 else 0
noncomputable def af (C:Finset G) (x:G):ℝ:=
 (Fintype.card G:ℝ)/C.card*indicator C x
noncomputable def aT (B:Finset G) (f:G→ℝ):ℝ:=
 (∑ x∈B,f x)/B.card
noncomputable def bL (C B:Finset G):ℝ:=
 C.card/B.card
noncomputable def cO (B:Finset G) (p:ℕ) (f:G→ℝ):ℝ:=
 aT B fun x↦ |f x| ^p
noncomputable def pairing (f:G→ℝ) (C:Finset G):ℝ:=
 uo fun x↦f x*af C x
lemma mU {C:Finset G} (hC:C.Nonempty) (f:G→ℝ) :
  pairing f C=aT C f:=by
 classical
 unfold pairing aT uo af indicator
 rw[show(∑ x:G,f x *
   ((Fintype.card G:ℝ)/(C.card:ℝ)*if x∈C then 1 else 0)) =
   (Fintype.card G:ℝ)/(C.card:ℝ)* ∑ x∈C,f x by
  simp_rw[Td,Q3,mul_zero]
  simp only[←QE]
  simp only[subset_univ,filter_mem_eq_of_subset]
  rw[←Qt]
  exact Qx _ _]
 have Pa:(C.card:ℝ)≠0:=by exact_mod_cast hC.card_ne_zero
 have yj:(Fintype.card G:ℝ)≠0:=by
  exact_mod_cast(SN:Fintype.card G≠0)
 field_simp
omit [AddCommGroup G] [Fintype G] in
lemma g1 {C:Finset G} (f:G→ℝ) :
  |aT C f| ≤aT C fun x↦ |f x|:=by
 unfold aT
 calc
  _ =
    |(∑ x∈C,f x)| /(C.card:ℝ):=by
   rw[TE]
   congr 1
   exact QC (Q5 C.card)
  _≤(∑ x∈C, |f x|)/(C.card:ℝ):=
   Qz (TQ f C) (by positivity)
omit [AddCommGroup G] [Fintype G] in
lemma mH {C:Finset G} (hC:C.Nonempty)
  (p:ℕ) (f:G→ℝ) :
  (aT C fun x↦ |f x|)^p≤cO C p f:=by
 let w:G→ℝ:=fun _↦(C.card:ℝ)⁻¹
 have hw: ∀ x∈C,0≤w x:=by
  intro x hx
  exact inv_nonneg.mpr (by positivity)
 have Pb: ∑ x∈C,w x=1:=by
  simp[w,hC.card_ne_zero]
 have hz: ∀ x∈C,0≤ |f x|:=by
  intro x hx
  positivity
 have h:=Real.pow_arith_mean_le_arith_mean_pow C w (fun x↦ |f x|)
  hw Pb hz p
 simpa[aT,cO,w,Ri,Qj] using h
lemma s7 {B C:Finset G} (hC:C.Nonempty)
  (w8:C⊆B) (p:ℕ) (f:G→ℝ) :
  bL C B* |pairing f C| ^p≤cO B p f:=by
 have hB := hC.mono w8
 have nN: |pairing f C| ^p≤cO C p f:=by
  rw[mU hC]
  calc
   _
     ≤ (aT C fun x↦ |f x|)^p:=
      Qp (Q8 _) (g1 f) p
   _≤cO C p f:=mH hC p f
 have uS:0≤bL C B:=by
  unfold bL
  positivity
 calc
  _
    ≤ bL C B*cO C p f:=iO nN uS
  _=(∑ x∈C, |f x| ^p)/B.card:=by
   unfold bL cO aT
   field_simp[hC.card_ne_zero,hB.card_ne_zero]
  _≤(∑ x∈B, |f x| ^p)/B.card:=by
   apply Qz _ (by positivity)
   exact Ry w8 fun _ _ _↦by positivity
  _=cO B p f:=rfl
lemma rd {B C:Finset G} (hC:C.Nonempty)
  (w8:C⊆B) (p:ℕ) (_hp:0<p) (f:G→ℝ)
  (dK bo ε:ℝ) (fF:0≤bo) (hε:0≤ε)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-pairing f C| ≤ε*bo/4) :
  |dK-bo| ≤ε*bo ∨
   (ε*bo/2)^p≤cO B p f:=by
 by_cases rE: |dK-bo| ≤ε*bo
 ·exact Or.inl rE
 right
 have JK: |dK-bo| ≤
   |(dK-bo)-pairing f C| + |pairing f C|:=by
  calc
   _ =
     |((dK-bo)-pairing f C)+pairing f C|:=by ring_nf
   _≤ |(dK-bo)-pairing f C| + |pairing f C|:=UP _ _
 have nN:3*(ε*bo)/4< |pairing f C|:=by
  have iU := QV rE
  nlinarith
 have uS:0≤bL C B:=by
  unfold bL
  positivity
 have Gk :=
  Qp (by positivity) nN.le p
 have AY  :=

        QW c8 Gk (by positivity) uS
 calc
  _ =
    (2/3:ℝ)^p*(3*(ε*bo)/4)^p:=by
   rw[←QL]
   congr 1
   ring
  _≤bL C B* |pairing f C| ^p:=AY
  _≤cO B p f:=s7 hC w8 p f
lemma n0 {B C:Finset G} (hC:C.Nonempty)
  (w8:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (dK bo:ℝ) (fF:0<bo)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-pairing f C| ≤bo/8) :
  bo/2≤dK ∨
   (bo/4)^p≤cO B p f:=by
 have An: |(dK-bo)-pairing f C| ≤
   (1/2:ℝ)*bo/4:=by
  convert ew using 1; ring
 have LZ:=rd hC w8 p hp f dK bo
  (1/2:ℝ) fF.le (by norm_num) c8 An
 rcases LZ with rE | oP
 ·left
  have ic:=(abs_le.mp rE).1
  linarith
 ·right
  convert oP using 1; ring
lemma nv {B C:Finset G} (hC:C.Nonempty)
  (w8:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (dK bo:ℝ) (fF:0<bo)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-pairing f C| ≤bo/8)
  (ee:cO B p f≤(bo/8)^p) :
  bo/2≤dK:=by
 rcases n0 hC w8 p hp f dK bo fF
  c8 ew with rE | oP
 ·exact rE
 ·have Nr := Nat.ne_of_gt hp
  have Ii:(bo/8)^p<(bo/4)^p:=by
   apply pow_lt_pow_left₀
   ·nlinarith
   ·positivity
   ·exact Nr
  have:(bo/4)^p≤(bo/8)^p:= oP.trans ee
  exact(Rd this Ii).elim
end aw
end ay
end
section
open Finset
namespace ay
namespace aO
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def a4 (S:Finset G):Finset G:=
 S.image fun x↦x+x
omit [Fintype G] in
@[simp] lemma m2 {S:Finset G} {x:G} :
  x∈a4 S↔ ∃ y∈S,y+y=x:=by
 simp[a4]
omit [Fintype G] in
lemma eJ {S:Finset G} (hS:S.Nonempty) :
  (a4 S).Nonempty:=
       hS.image _
omit [Fintype G] in
lemma qJ {S T:Finset G} (Pc:S⊆T) :
  a4 S⊆a4 T:=by
 intro x hx
 obtain ⟨y,hy,rfl⟩:=m2.mp hx
 exact m2.mpr ⟨y,Pc hy,rfl⟩
omit [Fintype G] in
lemma qK (S:Finset G)
  (eU:Injective (fun x:G↦x+x)) :
  #(a4 S)= #S:=
       card_image_of_injective _ eU
omit [Fintype G] in
lemma pv (S T:Finset G)
  (eU:Injective (fun x:G↦x+x)) :
  aw.bL (a4 S) (a4 T) =
   aw.bL S T:=by
 simp only[aw.bL,qK S eU,
  qK T eU]
omit [DecidableEq G] in
lemma sI
  {H:Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
  (B:aj G) (e:G ≃+ H) :
  B.carrier.image e=(B.map e).carrier:=by
 ext x
 constructor
 ·intro hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  exact(aj.oH B e y).2 hy
 ·intro hx
  refine Finset.mem_image.mpr ⟨e.symm x, ?_,by simp⟩
  have AG:=(aj.oH B e (e.symm x)).1
  exact AG (by simpa using hx)
def hY (M:ℕ) (hM:Odd M) (B:aj (ZMod M)) :
  aj (ZMod M):=
 B.map (aj.eK M hM)
lemma jQ
  {M:ℕ} [NeZero M] (hM:Odd M) (B:aj (ZMod M)) :
  a4 B.carrier=(hY M hM B).carrier:=by
 rw[a4,hY, ←sI]
 apply Finset.image_congr
 intro x _
 exact aj.sV M hM x
@[simp] lemma u8
  (M:ℕ) (hM:Odd M) (B:aj (ZMod M)) :
  (hY M hM B).rank=B.rank:=
       aj.Am B (aj.eK M hM)
@[simp] lemma p7
  (M:ℕ) [NeZero M] (hM:Odd M) (B:aj (ZMod M)) :
  (hY M hM B).carrier.card=B.carrier.card:=
       aj.tZ M hM B
def bb (A' b4:Finset G):ℝ:=
 (Fintype.card G:ℝ) *
  qj
   (ao (af A') (af A'))
   (af (a4 b4))
lemma pw
  (eU:Injective (fun x:G↦x+x))
  (A' b4:Finset G) :
  bb A' b4 =
   (Fintype.card G:ℝ)*(df A' b4:ℝ) *
    (#A':ℝ)⁻¹ ^2*(#b4:ℝ)⁻¹:=by
 rw[bb,
  a4,
  jK eU]
 ring
lemma nw
  (eU:Injective (fun x:G↦x+x))
  {A' b4:Finset G} (qL:A'.Nonempty) (gO:b4.Nonempty) :
  bb A' b4 =
   (Fintype.card G:ℝ)*(df A' b4:ℝ) /
    ((#A':ℝ)^2*(#b4:ℝ)):=by
 rw[pw eU]
 have N0:(#A':ℝ)≠0:=by exact_mod_cast qL.card_ne_zero
 have Ns:(#b4:ℝ)≠0:=by exact_mod_cast gO.card_ne_zero
 field_simp
lemma kb
  {A' b4:Finset G} (gO:b4.Nonempty) :
  bb A' b4 =
   aw.aT (a4 b4) (fun x ↦
    (Fintype.card G:ℝ) *
     ao (af A') (af A') x):=by
 let D:=a4 b4
 let F:=ao (af A') (af A')
 have hD := eJ gO
 have ya:(#D:ℝ)≠0:=by exact_mod_cast hD.card_ne_zero
 unfold bb aw.aT qj
 change(Fintype.card G:ℝ) *
   ∑ x:G,F x*af D x =
  (∑ x∈D,(Fintype.card G:ℝ)*F x)/(#D:ℝ)
 have vS :
   (∑ x:G,F x*af D x) =
    (∑ x∈D,F x)*(#D:ℝ)⁻¹:=by
  change(∑ x:G,F x*(if x∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←QE]
  have eI:univ.filter (fun x:G↦x∈D)=D:=by ext; simp
  rw[eI,Qt]
 rw[vS]
 rw[show(∑ x∈D,(Fintype.card G:ℝ)*F x) =
   (Fintype.card G:ℝ)* ∑ x∈D,F x by
  rw[Qj]]
 field_simp
omit [AddCommGroup G] in
lemma k9 {S:Finset G} (hS:S.Nonempty) :
  an.cw (af S):=by
 refine ⟨bO S, ?_⟩
 exact cf hS
omit [AddCommGroup G] in
lemma h7
  {S:Finset G} (hS:S.Nonempty) (p:ℕ) (f:G→ℝ) :
  aK (af S) f p =
   aw.cO S p f:=by
 have EY:(#S:ℝ)≠0:=by exact_mod_cast hS.card_ne_zero
 unfold aK aw.cO aw.aT
  af
 change(∑ x:G,(if x∈S then (#S:ℝ)⁻¹ else 0)* |f x| ^p) =
  (∑ x∈S, |f x| ^p)/(#S:ℝ)
 simp only[ite_mul,zero_mul]
 rw[←QE]
 have eI:univ.filter (fun x:G↦x∈S)=S:=by ext; simp
 rw[eI]
 rw[←Qj,Qw]
 ring
omit [AddCommGroup G] in
lemma fc
  {S:Finset G} (hS:S.Nonempty) {p:ℕ} (hp:0<p)
  (f:G→ℝ) {C:ℝ} (_hC:0≤C)
  (ee :
   an.aM (af S) f p≤C) :
  aw.cO S p f≤C^p:=by
 have wL:=k9 hS
 rw[←h7 hS p f,
  ←an.jr wL hp]
 exact Qp
  (an.j3 wL f p) ee p
structure eh (original:Finset G) where
 A':Finset G
 b4:Finset G
 B:Finset G
 B':Finset G
 translate:G
 alpha:ℝ
 p:ℕ
 f:G→ℝ
 jR:A'.Nonempty
 iZ:b4.Nonempty
 kQ:B.Nonempty
 h8:b4⊆B'
 fL: ∀ x∈A',x-translate∈original
 fm: ∀ x∈b4,x-translate∈original
 i0:0≤alpha
 kR:alpha*(#B:ℝ)≤(#A':ℝ)
 jS:alpha*(#B':ℝ)≤(#b4:ℝ)
 p_pos:0<p
 gg :
  (2/3:ℝ)^p≤aw.bL b4 B'
 e7 :
  |(bb A' b4 -
    (Fintype.card G:ℝ)/(#B:ℝ)) -
    aw.pairing f (a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#B:ℝ))/8
 gh :
  aw.cO (a4 B') p f ≤
   (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p
noncomputable def cr {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):G:=
 Classical.choose h
lemma c0 {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon) :
  (1-epsilon)*s.density ≤
   a9 s.restriction.set ak.carrier (cr h):=
 (Uo h).2.1
lemma ea {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon) :
  (1-epsilon)*s.density ≤
   a9 s.restriction.set aB.carrier (cr h):=
 (Uo h).2.2

def a5 {original:Finset G}
  (s:ah.aA original) (epsilon:ℝ):ℝ:=
 (1-epsilon)*s.density

lemma lY
  (eU:Injective (fun x:G↦x+x))
  {A' b4:Finset G} (qL:A'.Nonempty) (gO:b4.Nonempty)
  {bo:ℝ}
  (iB:bo/2≤bb A' b4) :
  bo*(#A':ℝ)^2*(#b4:ℝ) /
    (2*(Fintype.card G:ℝ)) ≤
   (df A' b4:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have Kh:(0:ℝ)<(#A':ℝ)^2*(#b4:ℝ):=by
  positivity
 rw[nw eU qL gO] at iB
 have hmul :
   bo/2*((#A':ℝ)^2*(#b4:ℝ)) ≤
    (Fintype.card G:ℝ)*(df A' b4:ℝ):=
  (Qs Kh).mp iB
 rw[QF (QM (by norm_num) hG)]
 nlinarith
lemma m3
  (eU:Injective (fun x:G↦x+x))
  {A A' b4 B':Finset G} (qL:A'.Nonempty) (gO:b4.Nonempty)
  (kc:b4⊆B') (t:G)
  (gP: ∀ x∈A',x-t∈A)
  (fR: ∀ x∈b4,x-t∈A)
  {p:ℕ} (hp:0<p) (f:G→ℝ) {bo:ℝ}
  (fF:0<bo)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4-bo) -
     aw.pairing f (a4 b4)| ≤bo/8)
  (ee :
   aw.cO (a4 B') p f≤(bo/8)^p) :
  bo*(#A':ℝ)^2*(#b4:ℝ) /
    (2*(Fintype.card G:ℝ))≤(dL A:ℝ):=by
 have hC := eJ gO
 have w8 := qJ kc
 have EZ :
   (2/3:ℝ)^p ≤
    aw.bL (a4 b4) (a4 B'):=by
  rwa[pv b4 B' eU]
 have iB  :=

  aw.nv hC w8 p hp f
   (bb A' b4) bo fF EZ ew ee
 have Ki:=
  lY eU qL gO iB
 have E0 :=
  iA t gP fR
 have Dt :
   (df A' b4:ℝ)≤(dL A:ℝ):=by
  exact_mod_cast E0
 exact Ki.trans Dt
lemma kd
  (eU:Injective (fun x:G↦x+x))
  {A A' b4 B B':Finset G}
  (qL:A'.Nonempty) (gO:b4.Nonempty) (hB:B.Nonempty)
  (kc:b4⊆B') (t:G)
  (gP: ∀ x∈A',x-t∈A)
  (fR: ∀ x∈b4,x-t∈A)
  {alpha:ℝ} (b8:0≤alpha)
  (o2:alpha*(#B:ℝ)≤(#A':ℝ))
  (nA:alpha*(#B':ℝ)≤(#b4:ℝ))
  {p:ℕ} (hp:0<p) (f:G→ℝ)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4 -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.pairing f (a4 b4)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.cO (a4 B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p) :
  alpha^3*(#B:ℝ)*(#B':ℝ)/2 ≤
   (dL A:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have yk:(0:ℝ)< #B:=by exact_mod_cast hB.card_pos
 have fF :=
  Rn hG yk
 have ic:=m3 eU qL gO kc t
  gP fR hp f fF c8 ew ee
 have Ij  :=

  Qp (Qn b8 yk.le) o2 2
 have Kj :
   alpha^3*(#B:ℝ)^2*(#B':ℝ) ≤
    (#A':ℝ)^2*(#b4:ℝ):=by
  have hmul:=QW Ij nA
   (Qn b8 (Q5 _)) (sq_nonneg (#A':ℝ))
  nlinarith only[hmul]
 have kB :
   alpha^3*(#B:ℝ)*(#B':ℝ)/2 =
    (alpha^3*(#B:ℝ)^2*(#B':ℝ)) /
     (2*(#B:ℝ)):=by
  field_simp
 have oO :
   ((Fintype.card G:ℝ)/(#B:ℝ))*(#A':ℝ)^2 *
     (#b4:ℝ)/(2*(Fintype.card G:ℝ)) =
    ((#A':ℝ)^2*(#b4:ℝ))/(2*(#B:ℝ)):=by
  field_simp
 rw[oO] at ic
 rw[kB]
 exact(Qz Kj (by positivity)).trans ic

lemma me
  (eU:Injective (fun x:G↦x+x))
  {A A' b4 B B':Finset G}
  (qL:A'.Nonempty) (gO:b4.Nonempty) (hB:B.Nonempty)
  (kc:b4⊆B') (t:G)
  (gP: ∀ x∈A',x-t∈A)
  (fR: ∀ x∈b4,x-t∈A)
  {alpha K:ℝ} {d p:ℕ} (b8:0≤alpha)
  (o2:alpha*(#B:ℝ)≤(#A':ℝ))
  (nA:alpha*(#B':ℝ)≤(#b4:ℝ))
  (hp:0<p) (f:G→ℝ)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4 -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.pairing f (a4 b4)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.cO (a4 B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p)
  (AZ:exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2) :
  exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   (dL A:ℝ):=
       AZ.trans<|
  kd eU qL gO hB kc t
   gP fR b8 o2 nA hp f c8 ew ee
lemma kq
  {M:ℕ} [NeZero M] (hM:Odd M)
  {A A' b4 B B':Finset (ZMod M)}
  (qL:A'.Nonempty) (gO:b4.Nonempty) (hB:B.Nonempty)
  (kc:b4⊆B') (t:ZMod M)
  (gP: ∀ x∈A',x-t∈A)
  (fR: ∀ x∈b4,x-t∈A)
  {alpha K:ℝ} {d p:ℕ} (b8:0≤alpha)
  (o2:alpha*(#B:ℝ)≤(#A':ℝ))
  (nA:alpha*(#B':ℝ)≤(#b4:ℝ))
  (hp:0<p) (f:ZMod M→ℝ)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4 -
     (Fintype.card (ZMod M):ℝ)/(#B:ℝ)) -
     aw.pairing f (a4 b4)| ≤
    ((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)
  (ee :
   aw.cO (a4 B') p f ≤
    (((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)^p)
  (AZ:exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod M):ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2) :
  exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod M):ℝ)^2≤(dL A:ℝ):=by
 apply me
  (aj.eK M hM).injective qL gO hB kc t
  gP fR b8 o2 nA hp f c8 ew ee
  AZ
end
end aO
end ay
end
section
open Filter Finset
open scoped Topology
namespace ay
def dX (K:ℝ) (nO:ℕ):Prop:=
 0<K ∧
  ∀ (N:ℕ),nO≤N →
   ∀ (A:Finset ℕ),A⊆Finset.Icc 1 N→ A.Nonempty →
    ∀ d:ℕ,
     1≤d →
     log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2 →
      exp (-K*(d:ℝ)^12)*(N:ℝ)^2 ≤
       (dL A:ℝ)
lemma jA
  {K:ℝ} {nO:ℕ} (AX:dX K nO) :
  ∀ᶠ N:ℕ in atTop,
   (r3 N:ℝ) ≤
    (N:ℝ)*exp
     (-(log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ)):=by
 have hK:0<K:=AX.1
 have ei:Tendsto (fun N:ℕ=>log (N:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp Sa
 have Gl:Tendsto (fun N:ℕ=>log (N:ℝ)/K) atTop atTop:=
  Tendsto.atTop_div_const hK ei
 have wJ :
   Tendsto
    (fun N:ℕ=>(log (N:ℝ)/K)^(1/12:ℝ))
    atTop atTop:=
  (UR (by norm_num:(0:ℝ)<1/12)).comp Gl
 filter_upwards[eventually_ge_atTop nO,eventually_gt_atTop 3,
   wJ.eventually_ge_atTop 2] with N Kk hN KV
 obtain ⟨A,z8,sF,E1⟩:=UG (Finset.Icc 1 N)
 have wO: #A=r3 N:=by simpa[r3] using sF
 have yl:r3 N≤N:=by
  rw[vC]
  exact rothNumberNat_le N
 have Cq:0<r3 N:=by
  have Du:({1}:Finset ℕ)⊆Finset.Icc 1 N:=by
   simpa using(show 1≤N by omega)
  have ym:=addRothNumber.mono Du
  have Pd:1≤addRothNumber (Finset.Icc 1 N):=by simpa using ym
  have:0<addRothNumber (Finset.Icc 1 N):=by omega
  simpa[r3] using this
 have u4:A.Nonempty:=by
  apply Finset.card_pos.mp
  simpa[wO] using Cq
 have yo:(0:ℝ)<N:=by exact_mod_cast(U5 hN)
 have o3:(0:ℝ)<r3 N:=by exact_mod_cast Cq
 have w9:(r3 N:ℝ)≤N:=by exact_mod_cast yl
 have Dv:(1:ℝ)≤(N:ℝ)/(r3 N:ℝ):=by
  rw[one_le_div o3]
  exact w9
 have Dw:(0:ℝ)<(N:ℝ)/(r3 N:ℝ):=
  Rn yo o3
 let q:ℝ:=log ((N:ℝ)/(r3 N:ℝ))/log 2
 let d:ℕ:=Nat.ceil q
 have sJ:0<log 2:=Sv (by norm_num)
 have E3:0≤q:=by
  exact RS (Qv Dv) sJ.le
 have A0 :
   log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2:=by
  rw[wO]
  rw[←QF sJ]
  simpa[q,d] using Rr q
 have Dx:r3 N<N:=by
  apply SM yl
  intro heq
  have E4: #(Finset.Icc 1 N)=N:=by
   rw[Nat.card_Icc]
   omega
  have Nt:A=Finset.Icc 1 N:=by
   apply Finset.eq_of_subset_of_card_le z8
   rw[E4,wO,heq]
  have E5:ThreeAPFree (Finset.Icc 1 N:Set ℕ):=by
   simpa[Nt] using E1
  have oP:=E5 (a:=1) (b:=2) (c:=3)
   (by simp[show 1≤N by omega]) (by simp[show 2≤N by omega])
   (by simp[show 3≤N by omega]) (by norm_num)
  omega
 have Kl:0<q:=by
  have E9:(1:ℝ)<(N:ℝ)/(r3 N:ℝ):=by
   rw[SP o3]
   norm_num
   exact_mod_cast Dx
  exact Rn (Sv E9) sJ
 have Eo:1≤d:=by
  exact(Nat.ceil_pos.mpr Kl)
 have qG:=AX.2 N Kk A z8 u4 d Eo A0
 rw[uR E1,wO] at qG
 have Ik :
   exp (-K*(d:ℝ)^12)*(N:ℝ)^2≤(N:ℝ):=
  qG.trans w9
 have A1 :
   exp (-K*(d:ℝ)^12)*(N:ℝ)≤1:=by
  have pO :
    (exp (-K*(d:ℝ)^12)*(N:ℝ))*(N:ℝ) ≤
     1*(N:ℝ):=by
   simpa[TI,Qo] using Ik
  exact(TZ pO yo)
 have Dy:log (N:ℝ)≤K*(d:ℝ)^12:=by
  have Fa:=
   QG
    (QM (Q1 _) yo)
    A1
  rw[Ql (Real.exp_ne_zero _) yo.ne',Real.log_exp,
   Real.log_one] at Fa
  linarith
 have ql:0≤log (N:ℝ):=
  Qv (by exact_mod_cast(show 1≤N by omega))
 have BW:0≤log (N:ℝ)/K:=
  RS ql hK.le
 have BX:log (N:ℝ)/K≤(d:ℝ)^12:=by
  rw[QF hK]
  simpa[Qx] using Dy
 have L0 :
   (log (N:ℝ)/K)^(1/12:ℝ)≤(d:ℝ):=by
  calc
   (log (N:ℝ)/K)^(1/12:ℝ) ≤
     ((d:ℝ)^12)^(1/12:ℝ):=
    Sf BW BX (by norm_num)
   _=(d:ℝ):=by
    convert Sc (show(0:ℝ)≤d by positivity)
     (by norm_num:(12:ℕ)≠0) using 1
    all_goals norm_num
 have KW:(d:ℝ)<q+1:=by
  simpa[d] using Nat.ceil_lt_add_one E3
 have yp :
   (log (N:ℝ)/K)^(1/12:ℝ)/2≤q:=by
  linarith
 have xF :
   (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ) ≤
    log ((N:ℝ)/(r3 N:ℝ)):=by
  calc
   (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ) =
     ((log (N:ℝ)/K)^(1/12:ℝ)/2)*log 2:=by ring
   _≤q*log 2:=
    Qi yp sJ.le
   _=log ((N:ℝ)/(r3 N:ℝ)):=by
    simp[q,sJ.ne']
 have Dz:0<K^(1/12:ℝ):=
  SQ hK _
 have A2 :
   (log 2/(2*K^(1/12:ℝ))) *
     (log (N:ℝ))^(1/12:ℝ) =
    (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ):=by
  rw[Real.div_rpow ql hK.le]
  field_simp[Dz.ne']
 have zT :
   exp
     ((log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ)/(r3 N:ℝ):=by
  rw[←Real.le_log_iff_exp_le Dw]
  rw[A2]
  exact xF
 have BY :
   (r3 N:ℝ) *
     exp
      ((log 2/(2*K^(1/12:ℝ))) *
       (log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ):=by
  have:=(Qs o3).mp zT
  simpa[Qx] using this
 calc
  (r3 N:ℝ) ≤
    (N:ℝ) /
     exp
      ((log 2/(2*K^(1/12:ℝ))) *
       (log (N:ℝ))^(1/12:ℝ)):=
   (Qs (Q1 _)).2 BY
  _=(N:ℝ) *
    exp
     (-((log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ))):=by
   rw[Uh,Qw]
  _=(N:ℝ)*exp
    (-(log 2/(2*K^(1/12:ℝ))) *
     (log (N:ℝ))^(1/12:ℝ)):=by
   congr 2
   ring
lemma m4
  {K:ℝ} {nO:ℕ} (AX:dX K nO)
  (C:ℝ) :
  (fun N:ℕ=>(r3 N:ℝ))=O[atTop]
   (fun N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 have hc:0<log 2/(2*K^(1/12:ℝ)):=by
  exact Rn (Sv (by norm_num))
   (QM two_pos (SQ AX.1 _))
 apply m1
   (K:=1) (c:=log 2/(2*K^(1/12:ℝ)))
   (beta:=(1/12:ℝ)) Us hc (by norm_num) _ C
 simpa using jA AX
end ay
end
section
open Finset
open scoped NNReal
namespace ay
def f1 (K:ℝ):Prop:=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*log 2 →
      exp (-K*(d:ℝ)^12) *
        ((aD N:ℕ):ℝ)^2 ≤
       (dL A:ℝ)
noncomputable def gp (G:Type*) [AddCommGroup G]:aj G where
 eX:=∅
 width:=fun _↦0
@[simp] lemma tJ (G:Type*) [AddCommGroup G] :
  aj.rank (gp G)=0:=by
 change(∅:Finset (AddCharacter G)).card=0
 simp
@[simp] lemma fZ (G:Type*) [AddCommGroup G] [Fintype G]
  (a8:ℝ≥0) :
  ((gp G).ai a8).carrier=(Finset.univ:Finset G):=by
 classical
 ext x
 simp[aj.mem_carrier,gp]
@[simp] lemma o4
  (G:Type*) [AddCommGroup G] [Fintype G] :
  (gp G).carrier=(Finset.univ:Finset G):=by
 simpa using fZ G 1
noncomputable def dA (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  br.aY (ZMod (aD N)) where
 ba:=gp (ZMod (aD N))
 outer:=1
 inner:=1
 regular:=by
  refine ⟨by norm_num,by norm_num, ?_⟩
  simp only[fZ]
  omega
 set:=A
 nonempty:=hA
 mw:=by
  intro x hx
  rw[fZ]
  simp
@[simp] lemma n1 (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).density =
   (#A:ℝ)/(aD N:ℕ):=by
 simp[br.aY.density,
  br.aY.e9,dA]
@[simp] lemma px (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).rank=0:=by
 simp[br.aY.rank,dA]
@[simp] lemma py (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).card=aD N:=by
 simp[br.aY.card,
  br.aY.e9,dA]
noncomputable def bQ (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  ah.aA A where
 restriction:=dA N A hA
 shift:=0
 eR:=by
  intro x hx
  simpa[dA] using hx
@[simp] lemma p8 (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).density =
   (#A:ℝ)/(aD N:ℕ):=
       n1 N A hA
@[simp] lemma rP (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).rank=0:=
       px N A hA
@[simp] lemma rQ (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).card=aD N:=
       py N A hA
lemma mf
  {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {original:Finset G} {d:ℕ}
  (s:ah.aA original)
  (c3:br.nK d s.density) :
  1<(1025/1024:ℝ)^(1024*(d+1))*s.density:=by
 have dc:(2:ℝ)≤(1025/1024:ℝ)^1024:=by
  have h:=UM (a:=(1/1024:ℝ)) (by norm_num) 1024
  norm_num at h
  exact h
 have hpow:(2:ℝ)^(d+1) ≤
   (1025/1024:ℝ)^(1024*(d+1)):=by
  calc
   _ ≤((1025/1024:ℝ)^1024)^(d+1):=
    Qp (by positivity) dc (d+1)
   _=(1025/1024:ℝ)^(1024*(d+1)):=by rw[←QU]
 change 1/(2:ℝ)^d≤ s.density at c3
 have hmul:=QW hpow c3 (by positivity) (by positivity)
 have kB:(2:ℝ)^(d+1)*(1/(2:ℝ)^d)=2:=by
  rw[RB]
  field_simp
 rw[kB] at hmul
 exact SI (by norm_num:(1:ℝ)<2) hmul
structure dm (N:ℕ)
  (A:Finset (ZMod (aD N))) (K:ℝ) (d:ℕ) where
 A':Finset (ZMod (aD N))
 b4:Finset (ZMod (aD N))
 B:Finset (ZMod (aD N))
 B':Finset (ZMod (aD N))
 translate:ZMod (aD N)
 alpha:ℝ
 p:ℕ
 f:ZMod (aD N)→ℝ
 jR:A'.Nonempty
 iZ:b4.Nonempty
 kQ:B.Nonempty
 h8:b4⊆B'
 fL: ∀ x∈A',x-translate∈A
 fm: ∀ x∈b4,x-translate∈A
 i0:0≤alpha
 kR:alpha*(#B:ℝ)≤(#A':ℝ)
 jS:alpha*(#B':ℝ)≤(#b4:ℝ)
 p_pos:0<p
 gg :
  (2/3:ℝ)^p≤aw.bL b4 B'
 e7 :
  |(aO.bb A' b4 -
    (Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ)) -
    aw.pairing f (aO.a4 b4)| ≤
   ((Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ))/8
 gh :
  aw.cO (aO.a4 B') p f ≤
   (((Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ))/8)^p
 rr :
  exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (aD N)):ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2
structure dr
  {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {original:Finset G} (t:ah.aA original)
  (K:ℝ) (d:ℕ) where
 ll:aO.eh original
 tK:(3/4:ℝ)*t.density≤ll.alpha
 A3:exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#ll.B:ℝ)
 za:exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#ll.B':ℝ)

namespace dm
private lemma vD:exp (-1)≤(1/2:ℝ):=by
 have he := Real.exp_one_gt_two.le
 have hm:=Qi he (Q1 (-1)).le
 have te:exp 1*exp (-1)=1:=by
  rw[←R7]
  norm_num
 rw[te] at hm
 exact(Qs (by norm_num:(0:ℝ)<2)).2
  (by simpa[Qx] using hm)
lemma p9
  {d:ℕ} (hd:1≤d) {alpha:ℝ}
  (b8:(3/4:ℝ)*(1/(2:ℝ)^d)≤alpha) :
  exp (-(8:ℝ)*(d:ℝ)^12)≤alpha^3/2:=by
 let m:ℕ:=8*d^12
 have l9:exp (-(8:ℝ)*(d:ℝ)^12) =
   exp (-1)^m:=by
  rw[show-(8:ℝ)*(d:ℝ)^12=(m:ℝ)*(-1) by
   simp[m],Real.exp_nat_mul]
 have iB:exp (-1)^m≤(1/2:ℝ)^m:=
  Qp (Q1 _).le vD m
 have PJ:d≤d^12:=Nat.le_pow (by norm_num)
 have hm:3*d+3≤ m:=by
  dsimp[m]
  omega
 have we:(1/2:ℝ)^m≤(1/2:ℝ)^(3*d+3):=
  SJ (by norm_num) (by norm_num) hm
 have qI:(1/2:ℝ)^(3*d+3) ≤
   ((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=by
  rw[RL,QU]
  ring_nf
  rw[show(1/8:ℝ)=(1/2:ℝ)^3 by norm_num, ←QU]
  gcongr
  all_goals norm_num[R8]
 calc
  exp (-(8:ℝ)*(d:ℝ)^12)=exp (-1)^m:=l9
  _≤(1/2:ℝ)^m:=iB
  _≤(1/2:ℝ)^(3*d+3):=we
  _≤((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=qI
  _≤alpha^3/2:=by gcongr
def sK {N:ℕ}
  {A:Finset (ZMod (aD N))} {K:ℝ} {d:ℕ}
  (c:aO.eh A)
  (DA:exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (aD N)):ℝ)^2 ≤
   c.alpha^3*(#c.B:ℝ)*(#c.B':ℝ)/2) :
  dm N A K d where
 A':=c.A'
 b4:=c.b4
 B:=c.B
 B':=c.B'
 translate:=c.translate
 alpha:=c.alpha
 p:=c.p
 f:=c.f
 jR:=c.jR
 iZ:=c.iZ
 kQ:=c.kQ
 h8:=c.h8
 fL:=c.fL
 fm:=c.fm
 i0:=c.i0
 kR:=c.kR
 jS:=c.jS
 p_pos:=c.p_pos
 gg:=c.gg
 e7:=c.e7
 gh:=c.gh
 rr:=DA
lemma nB
  {G:Type*} [Fintype G] {zb zc:ℝ} {d:ℕ} {B B':Finset G}
  (hB:exp (-zb*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B:ℝ))
  (Km:exp (-zc*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B':ℝ)) :
  exp (-(zb+zc)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ):=by
 calc
  _
                          =
    (exp (-zb*(d:ℝ)^12)*(Fintype.card G:ℝ)) *
     (exp (-zc*(d:ℝ)^12)*(Fintype.card G:ℝ)):=by
   rw[show-(zb+zc)*(d:ℝ)^12 =
     -zb*(d:ℝ)^12+ -zc*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤(#B:ℝ)*(#B':ℝ):=
         QW hB Km (by positivity) (by positivity)
lemma lZ
  {G:Type*} [Fintype G] {alpha n2 wP:ℝ} {d:ℕ}
  {B B':Finset G}
  (c8:exp (-n2*(d:ℝ)^12)≤alpha^3/2)
  (DB:exp (-wP*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ)) :
  exp (-(n2+wP)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2:=by
 have Gm:0≤(#B:ℝ)*(#B':ℝ):=by positivity
 calc
  _
                          =
    exp (-n2*(d:ℝ)^12) *
     (exp (-wP*(d:ℝ)^12) *
      (Fintype.card G:ℝ)^2):=by
   rw[show-(n2+wP)*(d:ℝ)^12 =
     -n2*(d:ℝ)^12+ -wP*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤exp (-n2*(d:ℝ)^12) *
     ((#B:ℝ)*(#B':ℝ)):=
   iO DB (Q1 _).le
  _≤(alpha^3/2)*((#B:ℝ)*(#B':ℝ)):=
   Qi c8 Gm
  _=alpha^3*(#B:ℝ)*(#B':ℝ)/2:=by ring
lemma BZ {N:ℕ} {A:Finset (ZMod (aD N))}
  {K:ℝ} {d:ℕ} (c:dm N A K d) :
  exp (-K*(d:ℝ)^12) *
    ((aD N:ℕ):ℝ)^2≤(dL A:ℝ):=by
 let:NeZero (aD N):=⟨by simp[aD]⟩
 have A4:Odd (aD N):=
        ⟨N,by simp[aD,R5]⟩
 simpa using aO.kq A4
  c.jR c.iZ c.kQ c.h8 c.translate
  c.fL c.fm c.i0 c.kR
  c.jS c.p_pos c.f c.gg c.e7
  c.gh c.rr
end dm
def eT (K:ℝ):Prop:=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*log 2 →
      Nonempty (dm N A K d)

lemma nC
  {K:ℝ} (h:eT K) :
  f1 K:=by
 refine ⟨h.1, ?_⟩
 intro N hN A hA d hd ei
 exact(Classical.choice (h.2 N hN A hA d hd ei)).BZ
private lemma uu {d:ℕ} (hd:1≤d) :
  ((d+1:ℕ):ℝ)^12≤(2:ℝ)^12*(d:ℝ)^12:=by
 have Pe:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+1:ℕ):ℝ)≤2*(d:ℝ):=by
  push_cast
  linarith
 calc
  _ ≤(2*(d:ℝ))^12:=
   Qp (by positivity) dc 12
  _=(2:ℝ)^12*(d:ℝ)^12:=by rw[QL]
namespace dm
lemma iJ
  {G:Type*} [Fintype G] {K:ℝ} (hK:0≤K)
  {d n mg:ℕ} (hd:1≤d) (hn:n≤1024*(d+1))
  {B:Finset G}
  (ue:exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11))*(Fintype.card G:ℝ) ≤
    (mg:ℝ))
  (A5:exp (-(K*((d+1:ℕ):ℝ)^11)) *
    (mg:ℝ)≤(#B:ℝ)) :
  exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)≤(#B:ℝ):=by
 let step := K*((d+1:ℕ):ℝ)^11
 have Kn:n+1≤1025*(d+1):=by omega
 have Ko:(n:ℝ)+1≤1025*((d+1:ℕ):ℝ):=by
  exact_mod_cast Kn
 have yq:0≤ step:=by
  dsimp[step]
  positivity
 have Gn:((n:ℝ)+1)*step ≤
   1025*K*((d+1:ℕ):ℝ)^12:=by
  calc
   _ ≤
     (1025*((d+1:ℕ):ℝ))*step:=
    Qi Ko yq
   _=1025*K*((d+1:ℕ):ℝ)^12:=by
    simp only[step]
    ring
 have hpow:=uu hd
 have yr:((n:ℝ)+1)*step ≤
   (1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by
  calc
   _ ≤
     1025*K*((d+1:ℕ):ℝ)^12:=Gn
   _≤1025*K*((2:ℝ)^12*(d:ℝ)^12):=
    iO hpow (Qn (by norm_num) hK)
   _=(1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by ring
 have Fb:exp (-((n:ℝ)+1)*step) *
   (Fintype.card G:ℝ)≤(#B:ℝ):=by
  calc
   _ =
     exp (-step) *
      (exp (-(n:ℝ)*step)*(Fintype.card G:ℝ)):=by
    rw[show-((n:ℝ)+1)*step =
      -step+(-(n:ℝ)*step) by ring,R7]
    ring
   _≤exp (-step)*(mg:ℝ):=
    iO (by simpa[step] using ue)
     (Q1 _).le
   _≤(#B:ℝ):=by simpa[step] using A5
 have l9:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) ≤
   exp (-((n:ℝ)+1)*step):=by
  apply Real.exp_le_exp.mpr
  nlinarith
 exact(Qi l9 (by positivity)).trans Fb
noncomputable def tL
  {N d n:ℕ} (hd:1≤d)
  {A:Finset (ZMod (aD N))} (hA:A.Nonempty)
  {K:ℝ} (hK:0≤K)
  {t:ah.aA A}
  (hn:n≤1024*(d+1))
  (uv:br.nK d
   (bQ N A hA).density)
  (c8:(1025/1024:ℝ)^n *
    (bQ N A hA).density≤t.density)
  (ch:exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11)) *
    ((bQ N A hA).card:ℝ)≤(t.card:ℝ))
  (terminal:dr t K d) :
  dm N A
   (8+2050*(2:ℝ)^12*K) d:=by
 letI:NeZero (aD N):=⟨by simp[aD]⟩
 let c:=terminal.ll
 have B0:0≤(bQ N A hA).density:=
  (bQ N A hA).dI.le
 have uP:(1:ℝ)≤(1025/1024:ℝ)^n:=
  RH (by norm_num)
 have Go:(bQ N A hA).density≤t.density:=by
  calc
   (bQ N A hA).density =
     1*(bQ N A hA).density:=by ring
   _≤(1025/1024:ℝ)^n*(bQ N A hA).density:=
    Qi uP B0
   _≤t.density:=c8
 have c3:(1/(2:ℝ)^d) ≤
   (bQ N A hA).density:=uv
 have b8:(3/4:ℝ)*(1/(2:ℝ)^d)≤c.alpha:=by
  calc
   (3/4:ℝ)*(1/(2:ℝ)^d) ≤
     (3/4:ℝ)*(bQ N A hA).density:=
    iO c3 (by norm_num)
   _≤(3/4:ℝ)*t.density:=
    iO Go (by norm_num)
   _≤c.alpha:=terminal.tK
 have A6:exp (-(8:ℝ)*(d:ℝ)^12) ≤
   c.alpha^3/2:=p9 hd b8
 have ys:exp (-(n:ℝ) *
    (K*((d+1:ℕ):ℝ)^11)) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(t.card:ℝ):=by
  simpa only[rQ,ZMod.card] using ch
 have hB:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(#c.B:ℝ):=by
  exact iJ
   (G:=ZMod (aD N)) (K:=K) hK
   (d:=d) (n:=n) (mg:=t.card) hd hn ys terminal.A3
 have Km:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(#c.B':ℝ):=by
  exact iJ
   (G:=ZMod (aD N)) (K:=K) hK
   (d:=d) (n:=n) (mg:=t.card) hd hn ys terminal.za
 have DB:=nB hB Km
 have DA:=lZ A6 DB
 exact sK c (by
  convert DA using 1; ring_nf)
end dm
private lemma n3 {N:ℕ} (hN:1≤N) :
  (((aD N:ℕ):ℝ))≤4*(N:ℝ):=by
 push_cast
 have Qb:(1:ℝ)≤N:=by exact_mod_cast hN
 linarith
private lemma ow
  {N d:ℕ} {A:Finset ℕ} (hN:1≤N) (hA:A.Nonempty)
  (ei:log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2) :
  log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
   ((d+2:ℕ):ℝ)*log 2:=by
 have Kp:(0:ℝ)<N:=by exact_mod_cast hN
 have Fc:(0:ℝ)< #A:=by exact_mod_cast hA.card_pos
 have Il := Rn Kp Fc
 have wh :
   (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
    4*((N:ℝ)/(#A:ℝ)):=by
  calc
   _ ≤
     (4*(N:ℝ))/(#A:ℝ):=
    Qz (n3 hN) Fc.le
   _=4*((N:ℝ)/(#A:ℝ)):=by ring
 calc
  _ ≤
    log (4*((N:ℝ)/(#A:ℝ))):=
   QG (by positivity) wh
  _=2*log 2+log ((N:ℝ)/(#A:ℝ)):=by
   rw[Ql (by norm_num:(4:ℝ)≠0) Il.ne',
    show(4:ℝ)=2*2 by norm_num,
    Ql (by norm_num:(2:ℝ)≠0) (by norm_num:(2:ℝ)≠0)]
   ring
  _≤2*log 2+(d:ℝ)*log 2:=by linarith
  _=((d+2:ℕ):ℝ)*log 2:=by
   push_cast
   ring
private lemma ux {d:ℕ} (hd:1≤d) :
  ((d+2:ℕ):ℝ)^12≤(3:ℝ)^12*(d:ℝ)^12:=by
 have Pe:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+2:ℕ):ℝ)≤3*(d:ℝ):=by
  push_cast
  linarith
 calc
  _ ≤(3*(d:ℝ))^12:=
   Qp (by positivity) dc 12
  _=(3:ℝ)^12*(d:ℝ)^12:=by rw[QL]
lemma tM
  {K:ℝ} (zd:f1 K) :
  dX ((3:ℝ)^12*K) 1:=by
 refine ⟨QM (RF (by norm_num) _) zd.1, ?_⟩
 intro N hN A z8 hA d hd ei
 have Kq: ∀ a∈A,a≤N:=by
  intro a ha
  exact(Finset.mem_Icc.mp (z8 ha)).2
 have ze:(cZ N A).Nonempty:=by
  obtain ⟨a,ha⟩:=hA
  exact ⟨cn N a,fi.mpr ⟨a,ha,rfl⟩⟩
 have DC := vR Kq
 have Fd :
   log (((aD N:ℕ):ℝ) /
     (#(cZ N A):ℝ)) ≤
    ((d+2:ℕ):ℝ)*log 2:=by
  rw[DC]
  exact ow hN hA ei
 have Kr:=zd.2 N hN (cZ N A) ze
  (d+2) (by omega) Fd
 have hpow:=ux hd
 have l9 :
   exp (-((3:ℝ)^12*K)*(d:ℝ)^12) ≤
    exp (-K*((d+2:ℕ):ℝ)^12):=by
  apply Real.exp_le_exp.mpr
  have hK:=zd.1.le
  nlinarith[iO hpow hK]
 have Ks:(N:ℝ)^2≤(((aD N:ℕ):ℝ))^2:=by
  apply Qp (by positivity) _ 2
  push_cast
  have MS:(0:ℝ)≤N:=by positivity
  linarith
 calc
  _ ≤
    exp (-K*((d+2:ℕ):ℝ)^12) *
     (((aD N:ℕ):ℝ))^2:=
   QW l9 Ks (sq_nonneg _) (Q1 _).le
  _≤(dL (cZ N A):ℝ):=Kr
  _=(dL A:ℝ):=by rw[q1 Kq]
lemma mh
  (h: ∃ K:ℝ,f1 K) :
  ∃ K:ℝ, ∃ nO:ℕ,dX K nO:=by
 obtain ⟨K,hK⟩:=h
 exact ⟨(3:ℝ)^12*K,1,tM hK⟩
lemma i2
  (h: ∃ K:ℝ,eT K) :
  ∃ K:ℝ, ∃ nO:ℕ,dX K nO:=by
 obtain ⟨K,hK⟩:=h
 exact mh
  ⟨K,nC hK⟩
end ay
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.bu
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
def et (K:aj G) (A:Finset G):G→ℝ:=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.carrier) (mu A-mu K.carrier)
lemma l0
  {K W:aj G} (L3:K.a1)
  (u9:W.a1)
  {A:Finset G} (hA:A.Nonempty) (lO:A⊆K.carrier)
  {eta:ℝ≥0} (fC:0<eta)
  (mA:4*eta ≤
   1/(400*(max W.rank 1:ℕ):ℝ≥0))
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (gn:D⊆(W.ai eta).carrier)
  (lk:E⊆(W.ai eta).carrier)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  (kI: ∀ t,aN.bh D E t≠0 →
   t∈(K.ai aF).carrier)
  {epsilon:ℝ} (eM:0<epsilon) (oV:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (K.carrier.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(K.carrier.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (qv :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz epsilon p) <
    (1+epsilon/8)*(K.carrier.card:ℝ)⁻¹) :
  an.aM (af W.carrier)
    (ao
     ((@mu (ℝ) _ _) A-mu K.carrier) (mu A-mu K.carrier)) p ≤
   epsilon*(K.carrier.card:ℝ)⁻¹:=by
 let a:G→ℝ:=(@mu (ℝ) _ _) A-mu K.carrier
 have hq:0<an.bS p:=
  QP (by norm_num) hp
 have lh:=
  fu.tG u9 fC mA
   hD hE gn lk hq
   (an.sX p) a
 rw[fu.es]
  at lh
 apply fu.nr
   L3 hA lO hD hE dy kI eM oV d5 hp
   ⟨bO W.carrier,
    cf W.aE⟩
 ·simpa[a] using lh
 ·exact qv
structure aG (original:Finset G) where
 aV:ah.aA original
 fS:aV.restriction.outer=1
 iK:aV.restriction.ba.a1
namespace aG
def density {original:Finset G} (s:aG original) :
  ℝ:=s.aV.density
def rank {original:Finset G} (s:aG original) :
  ℕ:=s.aV.rank
def card {original:Finset G} (s:aG original) :
  ℕ:=s.aV.card
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma dI {original:Finset G} (s:aG original) :
  0<s.density:=s.aV.dI
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma density_nonneg {original:Finset G} (s:aG original) :
  0≤ s.density:=s.dI.le
end aG
structure dB
  {original:Finset G} (s:aG original)
  (epsilon aU:ℝ) (aq:ℕ) where
 aF:ℝ≥0
 xb :
  aF ≤
   1/(100*(max s.aV.restriction.ba.rank 1:ℕ):ℝ≥0)
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 fT:ak.outer=1
 g3:aB.outer=1
 ez:ak.ba.a1
 fe:aB.ba.a1
 nY:ak.carrier ⊆
  (s.aV.restriction.ba.ai aF).carrier
 p4:aB.carrier ⊆
  (s.aV.restriction.ba.ai aF).carrier
 tg :
  400*((max s.aV.restriction.ba.rank 1:ℕ):ℝ)*(aF:ℝ) ≤
   epsilon *
    cp s.aV.restriction.set
     s.aV.restriction.ba.carrier/4
 rankOne:ak.ba.rank≤ s.rank+aq
 p5:aB.ba.rank≤ s.rank+aq
 mE:exp (-aU)*(s.card:ℝ)≤ak.carrier.card
 mF:exp (-aU)*(s.card:ℝ)≤aB.carrier.card
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma m5
  {original:Finset G} (s:aG original)
  {epsilon aU:ℝ} {aq:ℕ}
  (eM:0<epsilon)
  (P:dB s epsilon aU aq) :
  ah.bV s.aV P.ak P.aB epsilon ∨
   ∃ t:aG original,
    br.dk (1+epsilon/2) aq aU
     s.aV.restriction t.aV.restriction:=by
 have hA:=s.aV.restriction.nonempty
 have lO :
   s.aV.restriction.set⊆s.aV.restriction.ba.carrier:=by
  simpa[br.aY.e9,s.fS] using
   s.aV.restriction.mw
 have o5 :
   cp s.aV.restriction.set
     s.aV.restriction.ba.carrier=s.aV.density:=by
  unfold ah.aA.density br.aY.density
   cp br.aY.e9
  simp[s.fS]
 rcases kk
   s.iK P.xb hA lO
   P.ak.aE P.aB.aE
   P.nY P.p4 eM P.tg with
  aQ | Im | In
 ·left
  rw[o5] at aQ
  simpa[ah.bV,ah.aA.e9,
   ah.aA.density,
   br.aY.density,
   br.aY.e9,s.fS] using aQ
 ·right
  obtain ⟨x,hx⟩:=Im
  rw[o5] at hx
  have gy:0<a9 s.aV.restriction.set
    P.ak.carrier x:=by
   have hs := s.aV.dI
   have hq:0<(1+epsilon/2:ℝ):=by nlinarith
   exact(QM hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.ak x gy
  refine ⟨{ aV:=u,fS:= ?_,iK:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.eo]
    using P.fT
  ·simpa[u,ah.di,ah.bt.eo]
    using P.ez
  ·apply ah.fb
    s.aV P.ak x gy
   ·simpa[ah.aA.density,
     br.aY.density,
     br.aY.e9] using hx
   ·exact P.rankOne
   ·exact P.mE
 ·right
  obtain ⟨x,hx⟩:=In
  rw[o5] at hx
  have gy:0<a9 s.aV.restriction.set
    P.aB.carrier x:=by
   have hs := s.aV.dI
   have hq:0<(1+epsilon/2:ℝ):=by nlinarith
   exact(QM hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.aB x gy
  refine ⟨{ aV:=u,fS:= ?_,iK:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.eo]
    using P.g3
  ·simpa[u,ah.di,ah.bt.eo]
    using P.fe
  ·apply ah.fb
    s.aV P.aB x gy
   ·simpa[ah.aA.density,
     br.aY.density,
     br.aY.e9] using hx
   ·exact P.p5
   ·exact P.mF
def a7
  {original:Finset G} {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):Finset G:=
 ah.dn s.restriction.set ak.carrier
  (aO.cr h)
def d3
  {original:Finset G} {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):Finset G:=
 ah.dn s.restriction.set aB.carrier
  (aO.cr h)
noncomputable def mi
    {original:Finset G} (s:ah.aA original)
    {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
    (aQ:ah.bV s ak aB epsilon)
    (_hepsilon_nonneg:0≤epsilon) (b2:epsilon<1)
    {p:ℕ} (hp:0<p) (f:G→ℝ)
    (jz:(2/3:ℝ)^p≤aO.a5 s epsilon)
    (ew :
      |(aO.bb
            (a7 aQ) (d3 aQ) -
          (Fintype.card G:ℝ)/(#ak.carrier:ℝ)) -
          aw.pairing f
            (aO.a4 (d3 aQ))| ≤
        ((Fintype.card G:ℝ)/(#ak.carrier:ℝ))/8)
    (ee :
      an.aM
          (af (aO.a4 aB.carrier)) f p ≤
        ((Fintype.card G:ℝ)/(#ak.carrier:ℝ))/8) :
    aO.eh original:=by
  let x := aO.cr aQ
  let A' := a7 aQ
  let b4 := d3 aQ
  let B := ak.carrier
  let B' := aB.carrier
  let alpha := aO.a5 s epsilon
  have lG:alpha≤a9 s.restriction.set B x:=by
    simpa[alpha,x,B,aO.a5] using
      aO.c0 aQ
  have o0:alpha≤a9 s.restriction.set B' x:=by
    simpa[alpha,x,B',aO.a5] using
      aO.ea aQ
  have b8 :=
    QM (sub_pos.mpr b2) s.dI
  have qL:A'.Nonempty:=by
    apply ah.bK ak.aE
    exact b8.trans_le lG
  have gO:b4.Nonempty:=by
    apply ah.bK aB.aE
    exact b8.trans_le o0
  have kc :=
          ah.dz
      (B:=aB.ba) (a8:=aB.outer)
      (A:=s.restriction.set) (C:=aB.carrier)
      (x:=x) (fun _ hz↦hz)
  have gP: ∀ z∈A',z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set:=
      (ah.e4.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have fR: ∀ z∈b4,z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set:=
      (ah.e4.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have nx:alpha*(#B:ℝ)≤(#A':ℝ):=by
    have wN:(0:ℝ)< #B:=by exact_mod_cast ak.aE.card_pos
    rw[ah.bk
      ak.aE x] at lG
    exact(Qs wN).mp lG
  have ny:alpha*(#B':ℝ)≤(#b4:ℝ):=by
    have wg:(0:ℝ)< #B':=by exact_mod_cast aB.aE.card_pos
    rw[ah.bk
      aB.aE x] at o0
    exact(Qs wg).mp o0
  have qM :
      (2/3:ℝ)^p≤aw.bL b4 B':=by
    calc
      _ ≤alpha:=jz
      _≤a9 s.restriction.set B' x:= o0
      _=aw.bL b4 B':=by
        rw[ah.bk
          aB.aE x]
        rfl
  have o1 :=
    aO.eJ aB.aE
  have uq :
      aw.cO (aO.a4 B') p f ≤
        (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p:=by
    apply aO.fc o1 hp f (by positivity)
    simpa[B,B'] using ee
  exact
    { A':=A'
      b4:=b4
      B:=B
      B':=B'
      translate:=s.shift-x
      alpha:=alpha
      p:=p
      f:=f
      jR:=qL
      iZ:=gO
      kQ:=ak.aE
      h8:=kc
      fL:=gP
      fm:=fR
      i0:=b8.le
      kR:=nx
      jS:=ny
      p_pos:=hp
      gg:=qM
      e7:=by simpa[A',b4,B] using ew
      gh:=uq }
structure eS
  {original:Finset G} (s:aG original)
  {epsilon aU:ℝ} {aq p:ℕ}
  (P:dB s epsilon aU aq)
  (aQ:ah.bV s.aV P.ak P.aB epsilon) where
 base:aj G
 weight:aj G
 wj:base.a1
 uy:weight.a1
 wk:base.carrier=P.ak.carrier
 uA :
  weight.carrier=aO.a4 P.aB.carrier
 rt:(a7 aQ).Nonempty
 th:a7 aQ⊆base.carrier
 eta:ℝ≥0
 uB:0<eta
 mI:4*eta ≤
  1/(400*(max weight.rank 1:ℕ):ℝ≥0)
 D:Finset G
 E:Finset G
 yt:D.Nonempty
 yu:E.Nonempty
 rZ:D⊆(weight.ai eta).carrier
 r0:E⊆(weight.ai eta).carrier
 aF:ℝ≥0
 yv:aF≤1/(100*(max base.rank 1:ℕ):ℝ≥0)
 ru :
  ∀ t,aN.bh D E t≠0 →
   t∈(base.ai aF).carrier
 uC :
  2*(((a7 aQ).card:ℝ)⁻¹ *
    (200*((max base.rank 1:ℕ):ℝ)*(aF:ℝ))) +
   (base.carrier.card:ℝ)⁻¹ *
    (200*((max base.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
   (1/8:ℝ)/8*(base.carrier.card:ℝ)⁻¹
 vr :
  (2/3:ℝ)^p≤aO.a5 s.aV epsilon
 e7 :
  |(aO.bb
     (a7 aQ) (d3 aQ) -
    (Fintype.card G:ℝ)/(#P.ak.carrier:ℝ)) -
    aw.pairing
     (et base (a7 aQ))
     (aO.a4 (d3 aQ))| ≤
   ((Fintype.card G:ℝ)/(#P.ak.carrier:ℝ))/8
 qN :
  (1+(1/8:ℝ)/8)*(base.carrier.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) (a7 aQ)) (mu (a7 aQ))))
     (an.cz (1/8:ℝ) p) →
   ∃ t:aG original,
    (257/256:ℝ) *
      aO.a5 s.aV epsilon≤t.density ∧
    t.rank≤ s.rank+aq ∧
    exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)
noncomputable def ox
    {original:Finset G} (s:aG original)
    {K:ℝ} {d aq p:ℕ}
    (P:dB s (1/512:ℝ)
      (K*((d+1:ℕ):ℝ)^11) aq)
    (aQ:ah.bV s.aV P.ak P.aB
      (1/512:ℝ))
    (hp:0<p)
    (Q:eS (p:=p) s P aQ)
    (nX :
      an.aM (af Q.weight.carrier)
          (ao
            ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.carrier)
            (mu (a7 aQ)-mu Q.base.carrier)) p ≤
        (1/8:ℝ)*(Q.base.carrier.card:ℝ)⁻¹) :
    dr s.aV K d:=by
  let c:=mi s.aV aQ
    (by norm_num) (by norm_num) hp
    (et Q.base (a7 aQ))
    Q.vr Q.e7 (by
      let w:G→ℝ≥0:=mu Q.weight.carrier
      have c3:=
        aN.gx w
          (ao
            ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.carrier)
            (mu (a7 aQ)-mu Q.base.carrier))
          (Fintype.card G:ℝ) (by positivity) hp
      have uD :
          an.aM
              (af Q.weight.carrier)
              (et Q.base (a7 aQ)) p =
            (Fintype.card G:ℝ) *
              an.aM
                (af Q.weight.carrier)
                (ao
                  ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.carrier)
                  (mu (a7 aQ)-mu Q.base.carrier)) p:=by
        simpa only[w,NNReal.iF,
          aN.eQ,
          et] using c3
      have pO :
          an.aM
              (af Q.weight.carrier)
              (et Q.base (a7 aQ)) p ≤
            (Fintype.card G:ℝ) *
              ((1/8:ℝ)*(Q.base.carrier.card:ℝ)⁻¹):=by
        rw[uD]
        exact iO nX (by positivity)
      rw[Q.uA] at pO
      simpa[Q.wk,Qw,Qo,Q6,
        Qx] using pO)
  refine
    { ll:=c
      tK:= ?_
      A3:= ?_
      za:= ?_ }
  · change(3/4:ℝ)*s.aV.density ≤
      aO.a5 s.aV (1/512:ℝ)
    simp only[aO.a5]
    nlinarith[s.aV.dI.le]
  · change exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.ak.carrier:ℝ)
    exact P.mE
  · change exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.aB.carrier:ℝ)
    exact P.mF
lemma l1
  {original:Finset G} (s:aG original)
  {K:ℝ} {d aq p:ℕ}
  (P:dB s (1/512:ℝ)
   (K*((d+1:ℕ):ℝ)^11) aq)
  (hp:0<p)
  (mj :
   ∀ aQ:ah.bV s.aV P.ak P.aB
     (1/512:ℝ),
    Nonempty (eS (p:=p) s P aQ)) :
  Nonempty (dr s.aV K d) ∨
   ∃ t:aG original,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.restriction t.aV.restriction:=by
 rcases m5 s
   (by norm_num:(0:ℝ)<1/512) P with nN | DD
 ·obtain ⟨Q⟩:=mj nN
  by_cases mC :
    (1+(1/8:ℝ)/8)*(Q.base.carrier.card:ℝ)⁻¹ ≤
     an.aM
      ((↑) ∘ aN.bh Q.D Q.E)
      ((al ((@mu (ℝ) _ _) (a7 nN)) (mu (a7 nN))))
      (an.cz (1/8:ℝ) p)
  ·right
   obtain ⟨u,c8,Kt,Ku⟩:=Q.qN mC
   refine ⟨u, ?_,Kt,Ku⟩
   calc
    (1025/1024:ℝ)*s.aV.density ≤
      (257/256:ℝ) *
       aO.a5 s.aV (1/512:ℝ):=by
     simp only[aO.a5]
     nlinarith[s.aV.dI.le]
    _≤u.density:=c8
  ·left
   have L4 :
     an.aM
       ((↑) ∘ aN.bh Q.D Q.E)
       ((al ((@mu (ℝ) _ _) (a7 nN)) (mu (a7 nN))))
       (an.cz (1/8:ℝ) p) <
      (1+(1/8:ℝ)/8)*(Q.base.carrier.card:ℝ)⁻¹:=
    QV mC
   have nX:=l0 Q.wj
    Q.uy Q.rt Q.th Q.uB
    Q.mI Q.yt Q.yu Q.rZ Q.r0
    Q.yv Q.ru (by norm_num) (by norm_num)
    Q.uC hp L4
   exact ⟨ox s P nN hp Q nX⟩
 ·right
  obtain ⟨u,hu⟩:=DD
  refine ⟨u, ?_⟩
  simpa only[show(1+(1/512:ℝ)/2) =
    (1025/1024:ℝ) by norm_num] using hu
inductive c1 {original:Finset G}
  (q:ℝ) (aq:ℕ) (aU:ℝ) :
  ℕ→aG original →
   aG original→Prop
 | nil (s:aG original) :
   c1 q aq aU 0 s s
 | cons {n:ℕ} {s t u:aG original}
   (pE:br.dk q aq aU
    s.aV.restriction t.aV.restriction)
   (x3:c1 q aq aU n t u) :
   c1 q aq aU (n+1) s u
namespace c1
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma forget {original:Finset G} {q aU:ℝ} {aq n:ℕ}
  {s t:aG original}
  (h:c1 q aq aU n s t) :
  ah.cU q aq aU n s.aV t.aV:=by
 induction h with
 | nil s=>exact ah.cU.nil s.aV
 | cons pE _ ih=>exact ah.cU.cons pE ih
end c1
lemma pz
  (G:Type*) [AddCommGroup G] [Fintype G] :
  (gp G).a1:=by
 intro aF _hkappa
 simp only[tJ,show max 0 1=1 by omega,
  Nat.cast_one]
 rw[o4]
 simp only[fZ]
 have ch:(0:ℝ)≤Fintype.card G:=by positivity
 constructor<;>nlinarith[show(0:ℝ)≤aF by positivity]
noncomputable def eF (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  aG A where
 aV:=bQ N A hA
 fS:=rfl
 iK:=pz (ZMod (aD N))
@[simp] lemma la (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (eF N A hA).density =
   (#A:ℝ)/(aD N:ℕ):=
       p8 N A hA
@[simp] lemma wm (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (eF N A hA).rank=0:=
       rP N A hA
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma jB
  {original:Finset G}
  {Terminal:aG original→Prop}
  {q lower aU:ℝ} {aq total used remaining:ℕ}
  (hq:1≤q)
  (oe:used+remaining≤total)
  (yq: ∀ n<total, ∀ s:aG original,
   lower≤ s.density →
   s.rank≤n*aq →
   Terminal s∨ ∃ t:aG original,
    br.dk q aq aU
     s.aV.restriction t.aV.restriction)
  (initial:aG original)
  (c3:lower≤ initial.density)
  (cK:initial.rank≤used*aq)
  (rW:1<q^remaining*initial.density) :
  ∃ n≤remaining, ∃ t:aG original,
   c1 q aq aU n initial t ∧
   Terminal t:=by
 induction remaining generalizing initial used with
 | zero =>
   have hs:=initial.aV.density_le_one
   simp only[pow_zero,QT] at rW
   exact(Rd hs rW).elim
 | succ remaining ih =>
   have L5:used<total:=by omega
   rcases yq used L5 initial c3 cK with wq | ⟨t,pE⟩
   ·exact ⟨0,by omega,initial,
     c1.nil initial,wq⟩
   ·have L6:initial.density≤t.density:=by
     calc
      initial.density=1*initial.density:=by ring
      _≤q*initial.density:=
       Qi hq initial.density_nonneg
      _≤t.density:=pE.1
    have uD:lower≤t.density:=c3.trans L6
    have A7:t.rank≤(used+1)*aq:=by
     calc
      t.rank≤ initial.rank+aq:=pE.2.1
      _≤used*aq+aq:=
       RZ cK aq
      _=(used+1)*aq:=by
       rw[Nat.add_mul]
       simp
    have xG:used+1+remaining≤total:=by omega
    have uP:0≤q^remaining:=QH (zero_le_one.trans hq) _
    have Gp:1<q^remaining*t.density:=by
     calc
      1<q^(remaining+1)*initial.density:=by simpa using rW
      _=q^remaining*(q*initial.density):=by
       rw[RB]
       ring
      _≤q^remaining*t.density:=
       iO pE.1 uP
    obtain ⟨n,hn,u,ue,hu⟩:=
     ih xG t uD A7 Gp
    exact ⟨n+1,by omega,u,
     c1.cons pE ue,hu⟩
lemma lH
  {N d:ℕ} (_hN:1≤N)
  {A:Finset (ZMod (aD N))} (hA:A.Nonempty)
  (ei:log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
   (d:ℝ)*log 2) :
  br.nK d
   (eF N A hA).density:=by
 have Ip:0<aD N:=by simp[aD]
 have yY:(0:ℝ)<aD N:=by exact_mod_cast Ip
 have ch:(0:ℝ)< #A:=by exact_mod_cast hA.card_pos
 have eO:(0:ℝ) <
   ((aD N:ℕ):ℝ)/(#A:ℝ):=Rn yY ch
 have hpow:(0:ℝ)<(2:ℝ)^d:=RF (by norm_num) _
 have L7 :
   log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
    log ((2:ℝ)^d):=by
  simpa[QB] using ei
 have wh :
   (((aD N:ℕ):ℝ)/(#A:ℝ))≤(2:ℝ)^d:=
  (SW eO hpow).mp L7
 have hmul:(((aD N:ℕ):ℝ)) ≤
   (2:ℝ)^d*(#A:ℝ):=(QF ch).mp wh
 rw[br.nK]
 simp only[la]
 apply(Sy hpow yY).2
 simpa[Qx] using hmul
def jZ (K:ℝ):Prop:=
 ∀ (N:ℕ),
  ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
   ∀ d:ℕ,1≤d →
    ∃ aq p:ℕ,0<p ∧
     ∀ n<1024*(d+1),
      ∀ s:aG A,
       (1/(2:ℝ)^d)≤ s.density →
       s.rank≤n*aq →
       ∃ P:dB s (1/512:ℝ)
        (K*((d+1:ℕ):ℝ)^11) aq,
        ∀ aQ:ah.bV s.aV
          P.ak P.aB (1/512:ℝ),
         Nonempty (eS (p:=p) s P aQ)
lemma lb
  {K:ℝ} (hK:0<K) (Iq:jZ K) :
  eT
   (8+2050*(2:ℝ)^12*K):=by
 refine ⟨by positivity, ?_⟩
 intro N hN A hA d hd ei
 obtain ⟨aq,p,hp,yh⟩:=Iq N A hA d hd
 let fuel:ℕ:=1024*(d+1)
 let initial:=eF N A hA
 let Terminal:aG A→Prop:=
  fun s=>Nonempty (dr s.aV K d)
 have yq: ∀ n<fuel, ∀ s:aG A,
   (1/(2:ℝ)^d)≤ s.density →
   s.rank≤n*aq →
   Terminal s∨ ∃ t:aG A,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.restriction t.aV.restriction:=by
  intro n hn s c3 cK
  obtain ⟨P,mj⟩:=yh n (by simpa[fuel] using hn) s c3 cK
  exact l1 s P hp mj
 have uv:=lH hN hA ei
 have zU :
   (1/(2:ℝ)^d)≤ initial.density:=by
  change(1/(2:ℝ)^d)≤(bQ N A hA).density
  exact uv
 have rW :
   1<(1025/1024:ℝ)^fuel*initial.density:=by
  simpa[fuel,initial] using
   mf
    (bQ N A hA) uv
 obtain ⟨n,hn,t,ue,wq⟩:=
  jB
   (Terminal:=Terminal) (q:=(1025/1024:ℝ))
   (lower:=1/(2:ℝ)^d)
   (aU:=K*((d+1:ℕ):ℝ)^11)
   (aq:=aq) (total:=fuel) (used:=0)
   (remaining:=fuel) (by norm_num) (by omega) yq initial
   zU (by simp[initial]) rW
 let data:=Classical.choice wq
 have Cr:=ue.forget
 have zw:=
  Cr.qZ (by norm_num)
 change(1025/1024:ℝ)^n *
   (bQ N A hA).density≤t.aV.density at zw
 have c8  :=

        zw
 have Fe:=Cr.card_bound
 change exp (-(n:ℝ)*(K*((d+1:ℕ):ℝ)^11)) *
   ((bQ N A hA).card:ℝ)≤t.aV.card at Fe
 have ch  :=

        Fe
 exact ⟨dm.tL hd hA hK.le hn
  uv c8 ch data⟩
end
end ay.bu
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.pJ
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
private lemma rf (K:aj G) (x:G) :
  af K.carrier (-x)=af K.carrier x:=by
 by_cases hx:x∈K.carrier
 ·have Kv := aj.ec.mpr hx
  simp[dj hx,dj Kv]
 ·have Kv: -x∉K.carrier:=by
   intro h
   exact hx (aj.ec.mp h)
  simp[dO hx,
   dO Kv]
lemma ie
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A:Finset G} (hA:A.Nonempty) (lO:A⊆K.carrier)
  {t:G} (ht:t∈(K.ai κ).carrier) :
  |ao (af A)
    (af K.carrier) t-(K.carrier.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)):=by
 let E:ℝ:=200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)
 have sF:(A.card:ℝ)≠0:=by exact_mod_cast hA.card_ne_zero
 have L8 :=
  cf hA
 have dc :
   ∑ x:G,af A x*(K.carrier.card:ℝ)⁻¹ =
    (K.carrier.card:ℝ)⁻¹:=by
  rw[←Qt,L8,QT]
 have Gq :
   ∑ x:G,
     |af K.carrier (t-x) -
      af K.carrier (-x)| ≤E:=by
  have eY :=
   aj.ec.mpr ht
  have kE:=
   aj.cN
    dF qx eY
  calc
   _

                         =
     ∑ x:G,
      |af K.carrier (x- -t) -
       af K.carrier x|:=by
    refine Qk (Equiv.neg G) _ _ ?_
    intro x
    simp only[Equiv.neg_apply]
    congr 2; abel_nf
   _≤E:=kE
 have qy :
   ∑ x:G,af A x *
     |af K.carrier (t-x) -
      af K.carrier (-x)| ≤
    (A.card:ℝ)⁻¹ *E:=by
  calc
   _

                         =
     (A.card:ℝ)⁻¹ * ∑ x∈A,
      |af K.carrier (t-x) -
       af K.carrier (-x)|:=by
    change(∑ x:G,(if x∈A then (A.card:ℝ)⁻¹ else 0) *
      |af K.carrier (t-x) -
       af K.carrier (-x)|)=_
    simp only[ite_mul,zero_mul]
    rw[←QE]
    have eI:(Finset.univ:Finset G).filter (fun x↦x∈A)=A:=by
     ext x
     simp
    rw[eI,Qj]
   _≤(A.card:ℝ)⁻¹ * ∑ x:G,
      |af K.carrier (t-x) -
       af K.carrier (-x)|:=by
    apply iO
    ·exact Ry (S7 A)
      (fun _ _ _↦Q8 _)
    ·positivity
   _≤(A.card:ℝ)⁻¹ *E:=
    iO Gq (by positivity)
 rw[ao, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  _

                            =
    |∑ x:G,af A x *
     (af K.carrier (t-x) -
      af K.carrier (-x))|:=by
   apply QA abs
   apply Io rfl
   intro x _
   by_cases hx:x∈A
   ·rw[rf K x,
     dj (lO hx)]
   ·simp[dO hx]
  _≤ ∑ x:G, |af A x *
     (af K.carrier (t-x) -
      af K.carrier (-x))|:=
   abs_sum_le_sum_abs _ _
  _= ∑ x:G,af A x *
     |af K.carrier (t-x) -
      af K.carrier (-x)|:=by
   apply Io rfl
   intro x _
   rw[SU,QC (bO A x)]
  _≤(A.card:ℝ)⁻¹ *E:=qy
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma tN
  {C:Finset G} (hC:C.Nonempty) (f:G→ℝ) (c:ℝ) :
  aw.aT C f-c =
   aw.aT C (fun x↦f x-c):=by
 unfold aw.aT
 rw[QJ]
 simp only[Tq,QS]
 have Pf:(C.card:ℝ)≠0:=by exact_mod_cast hC.card_ne_zero
 field_simp
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma wt
  {C:Finset G} (hC:C.Nonempty) (c:ℝ) :
  aw.aT C (fun _↦c)=c:=by
 unfold aw.aT
 simp[hC.card_ne_zero]
lemma dY
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A C:Finset G} (hA:A.Nonempty) (lO:A⊆K.carrier)
  (hC:C.Nonempty) (fN:C⊆(K.ai κ).carrier) :
  |aw.aT C
    (ao (af A)
     (af K.carrier))-(K.carrier.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)):=by
 let M:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))
 rw[tN hC]
 calc
  _

                                             ≤
   aw.aT C (fun x ↦
    |ao (af A)
     (af K.carrier) x-(K.carrier.card:ℝ)⁻¹|):=
   aw.g1 _
  _≤aw.aT C (fun _↦M):=by
   unfold aw.aT
   apply Qz
   ·apply QI
    intro x hx
    exact ie
     dF qx hA lO (fN hx)
   ·positivity
  _=M:=wt hC M
omit [DecidableEq G] in
private lemma mJ
  (a k:G→ℝ) (x:G) :
  ao (a-k) (a-k) x =
   ao a a x-ao a k x -
    ao k a x+ao k k x:=by
 unfold ao
 simp only[Rw,UY,sub_mul,QJ]
 ring
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma xH
  {C:Finset G} (f g:G→ℝ) :
  aw.aT C (fun x↦f x+g x) =
   aw.aT C f+aw.aT C g:=by
 unfold aw.aT
 rw[T7,add_div]
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma sL
  {C:Finset G} (f g:G→ℝ) :
  aw.aT C (fun x↦f x-g x) =
   aw.aT C f-aw.aT C g:=by
 unfold aw.aT
 rw[QJ,UT]
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma kx
  {C:Finset G} (c:ℝ) (f:G→ℝ) :
  aw.aT C (fun x↦c*f x) =
   c*aw.aT C f:=by
 unfold aw.aT
 rw[←Qj]
 ring
lemma gT
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A b4:Finset G} (hA:A.Nonempty) (lO:A⊆K.carrier)
  (gO:b4.Nonempty)
  (fN:aO.a4 b4⊆(K.ai κ).carrier)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.carrier.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.carrier.card:ℝ)⁻¹)/8) :
  |(aO.bb A b4 -
    (Fintype.card G:ℝ)/(#K.carrier:ℝ)) -
    aw.pairing
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.carrier)
       (af A-af K.carrier))
     (aO.a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#K.carrier:ℝ))/8:=by
 let C:=aO.a4 b4
 let yw:=ao (af A) (af A)
 let qO:=ao (af A) (af K.carrier)
 let rv:=ao (af K.carrier) (af A)
 let sM:=ao (af K.carrier) (af K.carrier)
 let eC:ℝ:=(K.carrier.card:ℝ)⁻¹
 let E:ℝ:=200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)
 have hC := aO.eJ gO
 have Kw: |aw.aT C qO-eC| ≤
   (A.card:ℝ)⁻¹ *E:=by
  simpa[C,qO,eC,E] using
   dY
    dF qx hA lO hC fN
 have Pg: |aw.aT C rv-eC| ≤
   (A.card:ℝ)⁻¹ *E:=by
  rw[show rv=qO by
   dsimp[rv,qO]
   exact fG _ _]
  exact Kw
 have Ph: |aw.aT C sM-eC| ≤eC*E:=by
  simpa[C,sM,eC,E] using
   dY
    dF qx K.aE (Finset.Subset.rfl) hC fN
 have hsum :
   |(aw.aT C qO-eC) +
     (aw.aT C rv-eC) -
     (aw.aT C sM-eC)| ≤
    2*((A.card:ℝ)⁻¹ *E)+eC*E:=by
  calc
   _

                      ≤
    |aw.aT C qO-eC| +
     |aw.aT C rv-eC| +
     |aw.aT C sM-eC|:=by
    calc
     _ ≤ |(aw.aT C qO-eC) +
       (aw.aT C rv-eC)| +
       |aw.aT C sM-eC|:=by
      simpa[Su] using(abs_sub_le
       ((aw.aT C qO-eC) +
        (aw.aT C rv-eC))
       (0:ℝ) (aw.aT C sM-eC))
     _≤(|aw.aT C qO-eC| +
       |aw.aT C rv-eC|) +
       |aw.aT C sM-eC|:=by
      gcongr
      exact UP _ _
   _≤2*((A.card:ℝ)⁻¹ *E)+eC*E:=by
    nlinarith
 have fF:(Fintype.card G:ℝ)/(#K.carrier:ℝ) =
   (Fintype.card G:ℝ)*eC:=by
  simp[eC,Qw]
 have L9:aO.bb A b4 =
   (Fintype.card G:ℝ)*aw.aT C yw:=by
  rw[aO.kb gO]
  change aw.aT C
    (fun x↦(Fintype.card G:ℝ)*yw x)=_
  rw[kx]
 have nN :
   aw.pairing
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.carrier)
       (af A-af K.carrier)) C =
    (Fintype.card G:ℝ) *
     (aw.aT C yw-aw.aT C qO -
      aw.aT C rv+aw.aT C sM):=by
  rw[aw.mU hC]
  change aw.aT C (fun x↦(Fintype.card G:ℝ) *
   ao
    (af A-af K.carrier)
    (af A-af K.carrier) x)=_
  rw[kx]
  congr 1
  rw[show ao
    (af A-af K.carrier)
    (af A-af K.carrier) =
    (fun x↦yw x-qO x-rv x+sM x) by
   funext x
   simpa[yw,qO,rv,sM] using
    mJ (af A)
     (af K.carrier) x]
  rw[xH,sL,sL]
 rw[L9,fF,nN]
 have yj:0≤(Fintype.card G:ℝ):=by positivity
 calc
  _

                              =
   (Fintype.card G:ℝ) *
    |(aw.aT C qO-eC) +
     (aw.aT C rv-eC) -
     (aw.aT C sM-eC)|:=by
   have heq :
     (Fintype.card G:ℝ)*aw.aT C yw -
       (Fintype.card G:ℝ)*eC -
       (Fintype.card G:ℝ) *
        (aw.aT C yw-aw.aT C qO -
         aw.aT C rv+aw.aT C sM) =
      (Fintype.card G:ℝ) *
       ((aw.aT C qO-eC) +
        (aw.aT C rv-eC) -
        (aw.aT C sM-eC)):=by ring
   rw[heq,SU,QC yj]
  _≤(Fintype.card G:ℝ) *
    (2*((A.card:ℝ)⁻¹ *E)+eC*E):=
   iO hsum yj
  _≤(Fintype.card G:ℝ)*(eC/8):=by
   apply iO
   ·simpa[E,eC] using d5
   ·exact yj
  _=((Fintype.card G:ℝ)/(#K.carrier:ℝ))/8:=by
   rw[fF]
   ring
lemma e5
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A b4:Finset G} (hA:A.Nonempty) (lO:A⊆K.carrier)
  (gO:b4.Nonempty)
  (fN:aO.a4 b4⊆(K.ai κ).carrier)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.carrier.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    (1/8:ℝ)/8*(K.carrier.card:ℝ)⁻¹) :
  |(aO.bb A b4 -
    (Fintype.card G:ℝ)/(#K.carrier:ℝ)) -
    aw.pairing
     ((Fintype.card G:ℝ) •
      ao
       ((@mu (ℝ) _ _) A-mu K.carrier)
       (mu A-mu K.carrier))
     (aO.a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#K.carrier:ℝ))/8:=by
 have Ma:0≤(K.carrier.card:ℝ)⁻¹:=by positivity
 have Cs :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.carrier.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.carrier.card:ℝ)⁻¹)/8:=by
  apply d5.trans
  nlinarith
 have Nu :=
  aN.eQ A
 have Nv :=
  aN.eQ K.carrier
 simpa only[Nu,Nv] using
  gT dF qx hA lO
   gO fN Cs
end
end ay.pJ
end
section
open Finset
open scoped NNReal
namespace ay.aa
noncomputable section
def cH:ℝ:=1/8192
def dh (alpha:ℝ):ℕ:=⌈8192/alpha⌉₊
def dq (alpha:ℝ):ℕ:=Nat.clog 2 (dh alpha)
def g4 (alpha:ℝ):ℕ:=
 ⌈1+log (2/alpha)⌉₊
def fE (alpha:ℝ):ℕ:=
 ay.cQ (g4 alpha)
  ((cH/dq alpha)/exp 1)
def gs (alpha:ℝ) (k:ℕ):ℝ:=
 (alpha/2)^k/2
def rg (alpha:ℝ) (k:ℕ):ℕ:=
 ⌈8*(1+log (2/gs alpha k))⌉₊
def dt (d:ℕ):ℕ:=4*(d+1)
def bH (d:ℕ):ℕ:=
 an.cz (1/8:ℝ) (dt d)
def av (d:ℕ):ℕ:=
 2+2*d*bH d
def aR (d:ℕ):ℝ:=
 1/(2:ℝ)^av d
def au (d:ℕ):ℕ:=
 max 1 (rg (aR d)
  (fE (aR d)))
def bE (d:ℕ):ℕ:=dh (aR d)
def b1 (d:ℕ):ℕ:=
 dq (aR d)
def dC (d:ℕ):ℕ:=
 fE (aR d)
def nD (d:ℕ):ℕ:=
 2^38*(av d+13)^3
def o6 (d:ℕ):ℕ:=
 2^42*(av d+13)^4
def aH:ℕ:=
 2^42*1720335^4
lemma nE:0<cH:=by
 norm_num[cH]
lemma ml (d:ℕ):0<dt d:=by
 unfold dt
 positivity
lemma fU (d:ℕ):0<bH d:=by
 unfold bH
 exact an.uQ (by norm_num) (ml d)
lemma nF (d:ℕ):Even (bH d):=by
 unfold bH
 exact an.t4 _ _
lemma va (d:ℕ) :
  bH d≤860160*(d+1):=by
 have h:=
  an.po
   (ε:=(1/8:ℝ)) (p:=dt d) (ml d)
 norm_num[bH,dt,cP] at h ⊢
 omega
lemma gU (d:ℕ) :
  av d≤1720322*(d+1)^2:=by
 unfold av
 have h:=va d
 nlinarith[show d≤d+1 by omega]
lemma bP (d:ℕ):0<aR d:=by
 unfold aR
 positivity
lemma dZ (d:ℕ):aR d≤1:=by
 unfold aR
 have hpow:(1:ℝ)≤(2:ℝ)^av d:=by
  exact RH (by norm_num)
 exact(QF (by positivity)).2
  (by simpa only[av,QT] using hpow)
lemma i3 (d:ℕ):aR d≤2:=
 (dZ d).trans (by norm_num)
lemma bX (d:ℕ):0<au d:=by
 unfold au
 exact SI (by norm_num) (Tu _ _)
lemma ti (d:ℕ) :
  bE d=8192*2^av d:=by
 unfold bE dh aR
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 rw[show(8192:ℝ)/(1/(2:ℝ)^av d) =
   ((8192*2^av d:ℕ):ℝ) by
    push_cast
    field_simp]
 exact Nat.ceil_natCast _
lemma uE (d:ℕ) :
  b1 d=13+av d:=by
 unfold b1 dq
 change Nat.clog 2 (bE d)=13+av d
 rw[ti]
 rw[show(8192:ℕ)=2^13 by norm_num, ←RL,
  Nat.clog_pow 2 (13+av d) (by norm_num)]
lemma tO (d:ℕ) :
  g4 (aR d)≤av d+2:=by
 unfold g4 aR
 apply Nat.ceil_le.mpr
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 have uY :
   2/(1/(2:ℝ)^av d) =
    (2:ℝ)^(av d+1):=by
  field_simp
  rw[RB]
  ring
 rw[uY,QB]
 have ei:log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 push_cast
 nlinarith[iO ei
  (show(0:ℝ)≤av d+1 by positivity)]
lemma n4 (d:ℕ) :
  dC d≤nD d:=by
 unfold dC fE nD
 unfold ay.cQ
 apply Nat.ceil_le.mpr
 have hq:=tO d
 have uX:=uE d
 have Jd:(g4 (aR d):ℝ) ≤
   av d+2:=by exact_mod_cast hq
 have Kx:(dq (aR d):ℝ) =
   av d+13:=by
  change(b1 d:ℝ) =
   av d+13
  exact_mod_cast(by simpa[Nat.add_comm] using uX)
 have l9:exp 1≤3:=Real.exp_one_lt_three.le
 have hE:(0:ℝ)≤av d:=by positivity
 rw[Kx]
 unfold cH
 have si :
   (0:ℝ) <
    (((1/8192:ℝ)/(av d+13)) /
     exp 1/2)^2:=by positivity
 apply(QF si).2
 have Gr:(0:ℝ)<av d+13:=by positivity
 have PK:(g4 (aR d):ℝ) ≤
   av d+13:=by linarith
 have PL:exp 1^2≤(9:ℝ):=by
  nlinarith[Q1 (1:ℝ)]
 field_simp
 push_cast
 calc
  64*(g4 (aR d):ℝ)*8192^2 *
    (av d+13)^2*exp 1^2*2^2 ≤
   64*(av d+13)*8192^2 *
    (av d+13)^2*9*2^2:=by
     gcongr
  _=(64*8192^2*9*2^2:ℝ) *
    (av d+13)^3:=by ring
  _≤(2^38:ℝ)*(av d+13)^3:=by
   gcongr
   norm_num
  _=(274877906944:ℝ) *
    (av d+13)^3:=by norm_num
lemma gV {alpha:ℝ} (b8:0<alpha) :
  0<dh alpha:=by
 unfold dh
 apply Nat.ceil_pos.2
 positivity
lemma m6 {alpha:ℝ} (_halpha:0<alpha) :
  8192/alpha≤(dh alpha:ℝ):=
       Rr _
lemma s8 {alpha ratio:ℝ}
  (b8:0<alpha) (yx:alpha≤2)
  (eO:alpha/2≤ratio) :
  ⌈1+log (min 1 ratio)⁻¹⌉₊≤g4 alpha:=by
 have yy:0<alpha/2:=by positivity
 have Gs:alpha/2≤(1:ℝ):=by linarith
 have Ky := le_min Gs eO
 have Ir := yy.trans_le Ky
 have hinv:(min 1 ratio)⁻¹ ≤(alpha/2)⁻¹:=
  (RJ Ir yy).2 Ky
 have ei:log (min 1 ratio)⁻¹ ≤log (2/alpha):=by
  have sy:(alpha/2)⁻¹ =2/alpha:=by
   field_simp
  rw[←sy]
  exact QG (by positivity) hinv
 unfold g4
 apply S3
 linarith
lemma qa {q Q:ℕ} {epsilon:ℝ}
  (hq:q≤Q) (eM:0<epsilon) :
  ay.cQ q epsilon ≤
   ay.cQ Q epsilon:=by
 unfold ay.cQ
 apply S3
 have si:0<(epsilon/2)^2:=by positivity
 exact Qz
  (by exact_mod_cast Qr 64 hq) si.le
lemma ig
  {G:Type*} [AddCommGroup G]
  (M L:Finset G) {alpha:ℝ}
  (b8:0<alpha) (yx:alpha≤2)
  (eO:alpha/2≤(L.card:ℝ)/M.card)
  (hm:0<dq alpha) :
  ah.cm M L cH
    (dq alpha)≤fE alpha:=by
 classical
 unfold ah.cm fE
 apply qa
 ·unfold ah.mb
  exact s8 b8 yx eO
 ·have uX:(0:ℝ)<dq alpha:=by exact_mod_cast hm
  exact Rn (Rn nE uX) (Q1 _)
lemma sN {alpha:ℝ} (b8:0<alpha)
  (o7:alpha≤1) :
  0<dq alpha:=by
 unfold dq
 have hq:1<dh alpha:=by
  have iU:(1:ℝ)<8192/alpha:=by
   have:alpha<8192:=by
    nlinarith
   exact(SP b8).2 (by nlinarith)
  have rJ := m6 b8
  exact_mod_cast iU.trans_le rJ
 exact Nat.clog_pos (by norm_num) hq
lemma o8 {alpha:ℝ} (_halpha:0<alpha) :
  dh alpha≤2^dq alpha:=by
 unfold dq
 exact Nat.le_pow_clog (by norm_num) _
lemma qP {alpha:ℝ} (b8:0<alpha) :
  (1/2:ℝ)^dq alpha≤alpha/8192:=by
 have hq:(0:ℝ)<dh alpha:=by
  exact_mod_cast gV b8
 have hpow:(0:ℝ)<(2:ℝ)^dq alpha:=by positivity
 have uP:(dh alpha:ℝ)≤(2:ℝ)^dq alpha:=by
  exact_mod_cast o8 b8
 have rJ :=
  m6 b8
 calc
  _ =
    ((2:ℝ)^dq alpha)⁻¹:=by
     rw[R6,Te]
  _≤(dh alpha:ℝ)⁻¹:=
   (RJ hpow hq).2 uP
  _≤(8192/alpha)⁻¹:=by
   have dc:(0:ℝ)<8192/alpha:=by positivity
   exact(RJ hq dc).2 rJ
  _=alpha/8192:=by
   field_simp
lemma jj {alpha:ℝ}
  (b8:0<alpha) (o7:alpha≤1) :
  Real.sqrt (2/alpha)≤2/alpha:=by
 have JU:(1:ℝ)≤2/alpha:=by
  apply(Qs b8).2
  nlinarith
 have ug:0≤2/alpha:=by positivity
 rw[Real.sqrt_le_iff]
 constructor
 ·exact ug
 ·nlinarith
lemma qQ
  {alpha:ℝ} (b8:0<alpha) (o7:alpha≤1) :
  (2/(dh alpha:ℝ))*Real.sqrt (2/alpha)≤1/2048:=by
 have hq:(0:ℝ)<dh alpha:=by
  exact_mod_cast gV b8
 have rJ:=m6 b8
 have DE:=jj b8 o7
 calc
  (2/(dh alpha:ℝ))*Real.sqrt (2/alpha) ≤
    (2/(dh alpha:ℝ))*(2/alpha):=by
   gcongr
  _≤(2/(8192/alpha))*(2/alpha):=by
   have dc:(0:ℝ)<8192/alpha:=by positivity
   have hdiv:2/(dh alpha:ℝ)≤2/(8192/alpha):=by
    exact Rb (by norm_num) dc rJ
   exact Qi hdiv (by positivity)
  _=1/2048:=by
   field_simp
   norm_num
lemma s9
  {alpha:ℝ} (b8:0<alpha) (o7:alpha≤1) :
  (2*(1/2:ℝ)^dq alpha) *
    Real.sqrt (2/alpha)≤1/2048:=by
 have uX:=qP b8
 have DE:=jj b8 o7
 calc
  _
                        ≤
   (2*(alpha/8192))*(2/alpha):=by
    gcongr
  _=1/2048:=by
   field_simp
   norm_num
lemma zV {alpha:ℝ} {k:ℕ} (b8:0<alpha) :
  0<gs alpha k:=by
 unfold gs
 positivity
lemma sO
  {alpha:ℝ} {k:ℕ} (b8:0<alpha) :
  log (2/gs alpha k) =
   log 4+(k:ℝ)*log (2/alpha):=by
 have iB:(0:ℝ)<alpha/2:=by positivity
 have uY :
   2/gs alpha k=4/(alpha/2)^k:=by
  unfold gs
  field_simp
  ring
 rw[uY,Ui (by norm_num) (Rg _ iB.ne'),
  QB,Ui (by norm_num) b8.ne',
  Ui b8.ne' (by norm_num)]
 ring
lemma ke (d:ℕ) :
  au d≤o6 d:=by
 unfold au o6
 apply max_le
 ·have gy:0<2^42*(av d+13)^4:=by
   positivity
  omega
 ·unfold rg
  apply Nat.ceil_le.mpr
  rw[sO (bP d)]
  have hk:=n4 d
  have MT:(fE (aR d):ℝ) ≤
    (2^38*(av d+13)^3:ℕ):=by
   exact_mod_cast hk
  have Ct:log (2:ℝ)≤1:=by
   convert QX (show(0:ℝ)<2 by norm_num) using 1
   norm_num
  have A8:log (4:ℝ)≤2:=by
   rw[show(4:ℝ)=2^2 by norm_num,QB]
   have hmul:=iO Ct
    (show(0:ℝ)≤2 by norm_num)
   norm_num at hmul ⊢
   exact hmul
  have Ff :
    log (2/aR d) ≤
     (av d+1:ℝ):=by
   unfold aR
   have uY :
     2/(1/(2:ℝ)^av d) =
      (2:ℝ)^(av d+1):=by
    field_simp
    rw[RB]
    ring
   rw[uY,QB]
   push_cast
   nlinarith[iO Ct
    (show(0:ℝ)≤(av d+1:ℕ) by positivity)]
  have Pj :
    (av d+1:ℝ) ≤
     av d+13:=by norm_num
  have F0 :
    (1:ℝ)≤(av d+13)^4:=by
   have Pk:(0:ℝ)≤av d:=by positivity
   have:(1:ℝ)≤av d+13:=by nlinarith
   exact RH this
  have DF :
    0≤log (2/aR d):=by
   apply Qv
   apply(Qs (bP d)).2
   nlinarith[i3 d]
  have Nw :
    (fE (aR d):ℝ) ≤
     (2^38:ℝ)*(av d+13)^3:=by
   norm_num at MT ⊢
   exact MT
  have DG  :=

              Ff.trans Pj
  have hmul  :=

         QW Nw DG DF (by positivity)
  push_cast at ⊢
  calc
   _

                          ≤
    8*(1+(2 +
     (2^38*(av d+13)^3:ℝ) *
      (av d+13))):=by
       have oJ :
         log 4 +
           (fE (aR d):ℝ) *
            log (2/aR d) ≤
          2+(2^38:ℝ) *
           (av d+13)^3 *
            (av d+13):=by
        linarith
       nlinarith
   _=8*(3 +
     (2^38:ℝ)*(av d+13)^4):=by ring
   _≤(2^42:ℝ)*(av d+13)^4:=by
    norm_num at ⊢
    nlinarith
   _=(4398046511104:ℝ) *
     (av d+13)^4:=by norm_num
lemma jC (d:ℕ) :
  au d ≤
   aH*(d+1)^8:=by
 have hE:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Gr :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  au d ≤
    2^42*(av d+13)^4:=
   ke d
  _≤2^42*(1720335*(d+1)^2)^4:=by
   gcongr
  _=aH*(d+1)^8:=by
   unfold aH
   ring
lemma ff (d:ℕ) :
  ar.ax d (au d) ≤
   (1024*aH)*(d+1)^9:=by
 unfold ar.ax
 calc
  _ ≤
    1024*(d+1) *
     (aH*(d+1)^8):=by
   gcongr
   exact jC d
  _=(1024*aH)*(d+1)^9:=by
   ring
lemma fh:log (2:ℝ)≤1:=by
 have h:=
  QX (show(0:ℝ)<2 by norm_num)
 norm_num at h ⊢
 exact h
lemma cV {n:ℕ} (hn:0<n) :
  log (n:ℝ)≤n:=by
 have h:=QX
  (show(0:ℝ)<n by exact_mod_cast hn)
 nlinarith
lemma qb (d:ℕ) :
  log (bE d:ℝ) ≤
   (av d+13:ℝ):=by
 rw[ti]
 push_cast
 rw[show(8192:ℝ)=2^13 by norm_num, ←RL,
  QB]
 push_cast
 have ug:(0:ℝ)≤13+av d:=by positivity
 nlinarith[iO fh ug]
lemma o9 (d:ℕ) :
  log (bE d:ℝ) ≤
   1720335*((d+1:ℕ):ℝ)^2:=by
 have hE:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Gr :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  log (bE d:ℝ) ≤
    (av d+13:ℝ):=
   qb d
  _≤1720335*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Gr
lemma pa (d:ℕ) :
  log (au d:ℝ) ≤
   42+4*(av d+13:ℝ):=by
 have yr:=ke d
 have Kz :
   (au d:ℝ) ≤
    ((2^42*(av d+13)^4:ℕ):ℝ):=by
  exact_mod_cast yr
 have wu:(0:ℝ)<au d:=by
  exact_mod_cast bX d
 have ei  :=

  QG wu Kz
 have Gt :
   log ((2^42*(av d+13)^4:ℕ):ℝ) =
    42*log 2 +
     4*log ((av d+13:ℕ):ℝ):=by
  push_cast
  rw[show(4398046511104:ℝ)=(2:ℝ)^42 by norm_num]
  rw[Ql (Rg _ (by norm_num))
   (Rg _ (by positivity)),
   QB,QB]
  push_cast
  ring
 have It:0<av d+13:=by positivity
 have Iu  :=

  cV It
 rw[Gt] at ei
 have MV:42*log (2:ℝ)≤42:=by
  nlinarith[iO fh
   (show(0:ℝ)≤42 by norm_num)]
 have Gu:=iO Iu
  (show(0:ℝ)≤4 by norm_num)
 push_cast at ei Gu
 nlinarith
lemma fM (d:ℕ) :
  log (au d:ℝ) ≤
   6881382*((d+1:ℕ):ℝ)^2:=by
 have hE:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Iv :
   42+4*(av d+13) ≤
    6881382*(d+1)^2:=by
  nlinarith
 calc
  log (au d:ℝ) ≤
    42+4*(av d+13:ℝ):=
   pa d
  _≤6881382*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Iv
lemma qc
  {R:ℕ} (hR:0<R) :
  log ((8*R+1:ℕ):ℝ) ≤
   9+log (R:ℝ):=by
 have Mb:1≤R:=Nat.one_le_iff_ne_zero.mpr hR.ne'
 have sC:8*R+1≤9*R:=by omega
 have zf:(0:ℝ)<((8*R+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<8*R+1 by positivity)
 have kT:(0:ℝ)<R:=by exact_mod_cast hR
 have ei :
   log ((8*R+1:ℕ):ℝ) ≤
    log ((9*R:ℕ):ℝ):=
  QG zf (by exact_mod_cast sC)
 have te :
   log ((9*R:ℕ):ℝ) =
    log 9+log (R:ℝ):=by
  push_cast
  rw[Ql (by norm_num) kT.ne']
 rw[te] at ei
 have h9:log (9:ℝ)≤9:=
  cV (by norm_num)
 nlinarith
lemma m7 (d:ℕ) :
  log
    ((bE d*(8*au d+1:ℕ):ℕ):ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
 have Hm:0<bE d:=by
  unfold bE
  exact gV (bP d)
 have kT:=bX d
 have KA:(0:ℝ)<bE d:=by exact_mod_cast Hm
 have Fh:(0:ℝ)<8*au d+1:=by positivity
 have Mc:= o9 d
 have Gv:=qc kT
 have wR:=fM d
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 push_cast
 rw[Ql KA.ne' Fh.ne']
 push_cast at Mc wR pb Gv
 nlinarith
lemma eG (d:ℕ) :
  log
    (ar.ax d (au d):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
 have Gw:=bX d
 have wu:(0:ℝ)<au d:=by
  exact_mod_cast Gw
 have hdPos:0<d+1:=by omega
 have Fi:(0:ℝ)<d+1:=by exact_mod_cast hdPos
 have Md :=
  cV hdPos
 have Gx:=fM d
 have Nx:((d+1:ℕ):ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 unfold ar.ax
 push_cast
 rw[Ql
   (Rl (by norm_num) Fi.ne') wu.ne',
  Ql (by norm_num) Fi.ne']
 have Ny:log (1024:ℝ)≤10:=by
  rw[show(1024:ℝ)=2^10 by norm_num,QB]
  push_cast
  nlinarith[iO fh
   (show(0:ℝ)≤10 by norm_num)]
 push_cast at Md Gx Nx ⊢
 have pb:(1:ℝ)≤(↑d+1)^2:=by
  nlinarith
 nlinarith
lemma qd (d:ℕ) :
  log
    (ar.bn d (au d):ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
 have hR:=eG d
 have hconst:log (819200:ℝ)≤819200:=
  cV (by norm_num)
 have hpow:(d:ℝ)*log 2≤d:=by
  nlinarith[iO fh
   (show(0:ℝ)≤d by positivity)]
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gy:(d:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have hd:(d:ℝ)≤d+1:=by norm_num
  push_cast at pb ⊢
  nlinarith
 have kT:0<ar.ax d (au d):=
  ar.iH (bX d)
 have wv:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast kT
 unfold ar.bn
 push_cast
 rw[Ql (Rl (by norm_num) wv.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) wv.ne',QB]
 push_cast at hR hpow Gy ⊢
 nlinarith
lemma qe (d:ℕ) :
  log
    (ar.bd d (au d):ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
 have hR:=eG d
 have hconst:log (76800:ℝ)≤76800:=
  cV (by norm_num)
 have hpow:((d+1:ℕ):ℝ)*log 2≤d+1:=by
  have hmul:=iO fh
   (show(0:ℝ)≤((d+1:ℕ):ℝ) by positivity)
  norm_num at hmul ⊢
  exact hmul
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gy:((d+1:ℕ):ℝ) ≤
   ((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have kT:0<ar.ax d (au d):=
  ar.iH (bX d)
 have wv:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast kT
 unfold ar.bd
 push_cast
 rw[Ql (Rl (by norm_num) wv.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) wv.ne',QB]
 push_cast at hR hpow Gy ⊢
 nlinarith
lemma kU
  (d ax:ℕ) (vb:0<ax) {LR:ℝ}
  (KY:log (ax:ℝ)≤LR) :
  log
    ((8388608*max ax 1 *
     2^av d:ℕ):ℝ) ≤
   23+LR+av d:=by
 have lF :=
  max_eq_left (Nat.one_le_iff_ne_zero.mpr vb.ne')
 rw[lF]
 have zx:(0:ℝ)<ax:=by exact_mod_cast vb
 have MW:log (8388608:ℝ)≤23:=by
  rw[show(8388608:ℝ)=2^23 by norm_num,QB]
  push_cast
  nlinarith[iO fh
   (show(0:ℝ)≤23 by norm_num)]
 have N1 :
   (av d:ℝ)*log 2 ≤
    av d:=by
  nlinarith[iO fh
   (show(0:ℝ)≤av d by positivity)]
 push_cast
 rw[Ql
   (Rl (by norm_num) zx.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) zx.ne',QB]
 nlinarith
lemma m8 (d:ℕ) :
  (2/(bE d:ℝ)) *
    Real.sqrt (2/aR d)≤1/2048:=by
 unfold bE
 exact qQ
  (bP d) (dZ d)
lemma pA (d:ℕ) :
  (2*(1/2:ℝ)^b1 d) *
    Real.sqrt (2/aR d)≤1/2048:=by
 unfold b1
 exact s9
  (bP d) (dZ d)
def dH (rank delta n:ℕ):ℕ:=
 n^delta*4^(rank+delta)
def cL (d:ℕ):ℕ:=
 dH
  (ar.ax d (au d))
  (au d)
  (bE d*(8*au d+1))
def eW:ℕ:=
 aH*8601726 +
  2*(1024*aH +
   aH)
def bG (rank m:ℕ):ℕ:=
 (3*m)^rank*4^rank
def bT (rank bn bd:ℕ):ℕ:=
 bG rank bn*bG rank bd
def bR (rank:ℕ):ℕ:=
 bG rank (1600*max rank 1) *
  bG rank (200*max rank 1) *
   bG rank (200*max rank 1)
def cd (d ax:ℕ):ℕ:=
 8388608*max ax 1*2^av d
lemma vE
  {rank delta n R D N:ℕ}
  (hn:0<n) (Hn:n≤N)
  (cK:rank≤R) (cu:delta≤D) :
  dH rank delta n≤dH R D N:=by
 unfold dH
 have hN := hn.trans_le Hn
 have jx:n^delta≤N^D:=by
  calc
   _ ≤N^delta:=R4 Hn _
   _≤N^D:=QR hN cu
 have uh:4^(rank+delta)≤4^(R+D):=by
  apply QR (by norm_num)
  exact Nat.add_le_add cK cu
 exact Ra jx uh
lemma pc (R:ℕ) :
  ⌈8*(R:ℝ)⌉₊+1=8*R+1:=by
 rw[show 8*(R:ℝ)=((8*R:ℕ):ℝ) by
  push_cast
  ring]
 rw[Nat.ceil_natCast]
def bA (rank d4 m:ℕ):ℕ:=
 200*max rank 1*(2*d4+1)*m
lemma kg {rank d4 m:ℕ} (hm:0< m) :
  0<bA rank d4 m:=by
 unfold bA
 positivity
lemma uF {rank d4 m:ℕ} (hm:0< m) :
  log (bA rank d4 m:ℝ) =
   log 200+log ((max rank 1:ℕ):ℝ) +
    log ((2*d4+1:ℕ):ℝ)+log (m:ℝ):=by
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 unfold bA
 push_cast
 rw[Ql (by positivity) qD.ne',
  Ql (by positivity) (by positivity),
  Ql (by norm_num) (by positivity)]
lemma m9
  {rank d4 m:ℕ} {LR LC LM:ℝ} (hm:0< m)
  (PM:log ((max rank 1:ℕ):ℝ)≤LR)
  (PV:log ((2*d4+1:ℕ):ℝ)≤LC)
  (hM:log (m:ℝ)≤LM) :
  log (bA rank d4 m:ℝ) ≤
   200+LR+LC+LM:=by
 rw[uF hm]
 have DH:log (200:ℝ)≤200:=
  cV (by norm_num)
 nlinarith
lemma ky
  {rank ax:ℕ} (vb:0<ax) (cK:rank≤ax) :
  log ((max rank 1:ℕ):ℝ)≤log (ax:ℝ):=by
 have lF :=
  max_le cK (Nat.one_le_iff_ne_zero.mpr vb.ne')
 have wS:(0:ℝ)< max rank 1:=by positivity
 exact QG wS (by exact_mod_cast lF)
lemma kh
  {d4 R:ℕ} (hR:0<R) (pd:d4≤8*R) :
  log ((2*d4+1:ℕ):ℝ) ≤
   17+log (R:ℝ):=by
 have Mb:1≤R:=Nat.one_le_iff_ne_zero.mpr hR.ne'
 have sC:2*d4+1≤17*R:=by
  nlinarith
 have zf:(0:ℝ)<((2*d4+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<2*d4+1 by positivity)
 have kT:(0:ℝ)<R:=by exact_mod_cast hR
 have ei :
   log ((2*d4+1:ℕ):ℝ) ≤
    log ((17*R:ℕ):ℝ):=
  QG zf (by exact_mod_cast sC)
 have te :
   log ((17*R:ℕ):ℝ) =
    log 17+log (R:ℝ):=by
  push_cast
  rw[Ql (by norm_num) kT.ne']
 rw[te] at ei
 have Qc:log (17:ℝ)≤17:=
  cV (by norm_num)
 nlinarith
lemma iR
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (pd:d4≤8*au d) :
  log
    (bA rank d4
     (8388608 *
      max (ar.ax d (au d)) 1 *
       2^av d):ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
 let R:=ar.ax d (au d)
 let m:=8388608*max R 1*2^av d
 have kT:0<R:=by
  unfold R
  exact ar.iH (bX d)
 have hm:0< m:=by
  unfold m
  positivity
 have wR:log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have Gz:log ((max rank 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=
  (ky kT (by simpa[R] using cK)).trans wR
 have Iw:log ((2*d4+1:ℕ):ℝ) ≤
   17+6881382*((d+1:ℕ):ℝ)^2:=by
  calc
   _ ≤
     17+log (au d:ℝ):=
    kh
     (bX d) pd
   _≤17+6881382*((d+1:ℕ):ℝ)^2:=by
    gcongr
    exact fM d
 have Me:log (m:ℝ) ≤
   23+8601715*((d+1:ℕ):ℝ)^2:=by
  have nX:=kU d R kT wR
  have hE:=gU d
  have Qd:(av d:ℝ) ≤
    1720322*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast hE
  unfold m
  nlinarith
 have gM:=m9
  (rank:=rank) (d4:=d4) (m:=m) hm Gz Iw Me
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 simpa[m,R] using(by nlinarith :
  log (bA rank d4 m:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2)
lemma jT
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (pd:d4≤8*au d) :
  log
    (((3*bA rank d4
     (cd d
      (ar.ax d (au d))))^rank:ℕ):ℝ) ≤
   (1024*aH*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 let m:=cd d R
 let P:=bA rank d4 m
 have hm:0< m:=by
  unfold m cd
  positivity
 have hP:0<P:=by
  unfold P
  exact kg hm
 have PN:log (P:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
  simpa[P,m,R,cd] using
   iR d rank d4 cK pd
 have Pl:log ((3*P:ℕ):ℝ) ≤
   3+22364730*((d+1:ℕ):ℝ)^2:=by
  have Pm:(0:ℝ)<P:=by exact_mod_cast hP
  have h3:log (3:ℝ)≤3:=
   cV (by norm_num)
  rw[show((3*P:ℕ):ℝ)=(3:ℝ)*(P:ℝ) by norm_num]
  rw[Ql (by norm_num) Pm.ne']
  nlinarith
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have oc:log ((3*P:ℕ):ℝ) ≤
   22364733*((d+1:ℕ):ℝ)^2:=by
  nlinarith
 have sP:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (rank:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using cK)
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*aH:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast ff d)
 have zW:0≤log ((3*P:ℕ):ℝ):=by
  apply Qv
  exact_mod_cast(show 1≤3*P by omega)
 have hmul:=QW sP oc zW (by positivity)
 push_cast
 rw[QB]
 push_cast at hmul ⊢
 nlinarith
lemma i4
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (T:Finset G) (eta:ℝ) (m:ℕ)
  (hm:0< m) (a8:NNReal) (jM:1/2≤a8) :
  ((bA B.rank
    (aI.dg B T eta) m:NNReal)⁻¹) ≤
   a8*aI.cJ B T eta *
    (m:NNReal)⁻¹:=by
 classical
 unfold bA aI.cJ
 have cK:(0:NNReal)< max B.rank 1:=by positivity
 have pd:(0:NNReal) <
   (2*aI.dg B T eta+1:ℕ):=by
  positivity
 have w4:(0:NNReal)< m:=by exact_mod_cast hm
 have hmul :
   (200*(max B.rank 1:NNReal) *
     (2*aI.dg B T eta+1:ℕ) *
     (m:NNReal))*(1/2) ≤
    (200*(max B.rank 1:NNReal) *
     (2*aI.dg B T eta+1:ℕ) *
     (m:NNReal))*a8:=by
  exact iO jM (by positivity)
 field_simp
 norm_num at hmul ⊢
 convert hmul using 1; ring
lemma f5
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (P:ℕ) (hP:0<P) {a8:NNReal}
  (jM:((P:NNReal)⁻¹)≤a8) :
  B.carrier.card ≤
   (3*P)^B.rank*(B.ai a8).carrier.card:=by
 classical
 have dc:=
  aj.cM B 1 hP
 have ym :
   (B.ai ((P:NNReal)⁻¹)).carrier.card ≤
    (B.ai a8).carrier.card:=
  Qu (aj.b5 jM)
 calc
  B.carrier.card=(B.ai 1).carrier.card:=by simp
  _≤(3*P)^B.rank *
    (B.ai ((P:NNReal)⁻¹)).carrier.card:=by
     simpa[Qw] using dc
  _≤(3*P)^B.rank*(B.ai a8).carrier.card:=
   Qr _ ym
lemma wx
  {rank delta n:ℕ} (hn:0<n) :
  log (dH rank delta n:ℝ) =
   (delta:ℝ)*log (n:ℝ) +
    (rank+delta:ℝ)*log 4:=by
 have Ko:(0:ℝ)<n:=by exact_mod_cast hn
 unfold dH
 push_cast
 rw[Ql (Rg _ Ko.ne') (Rg _ (by norm_num)),
  QB,QB]
 push_cast
 ring
lemma ck {rank m:ℕ} (hm:0< m) :
  0<bG rank m:=by
 unfold bG
 positivity
lemma f0 {rank m:ℕ} (hm:0< m) :
  log (bG rank m:ℝ) =
   (rank:ℝ) *
    (log ((3*m:ℕ):ℝ)+log 4):=by
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 unfold bG
 push_cast
 rw[Ql (Rg _ (Rl (by norm_num) qD.ne'))
   (Rg _ (by norm_num)),QB,QB]
 ring
lemma qf {rank bn bd:ℕ}
  (eH:0<bn) (fw:0<bd) :
  log (bT rank bn bd:ℝ) =
   (rank:ℝ) *
    (log ((3*bn:ℕ):ℝ)+log 4) +
   (rank:ℝ) *
    (log ((3*bd:ℕ):ℝ)+log 4):=by
 unfold bT
 push_cast
 rw[Ql
   (by exact_mod_cast(ck eH).ne')
   (by exact_mod_cast(ck fw).ne'),
  f0 eH,f0 fw]
 push_cast
 ring
lemma nG (rank:ℕ) :
  log (bR rank:ℝ) =
   (rank:ℝ) *
     (log ((3*(1600*max rank 1):ℕ):ℝ) +
      log 4) +
    (rank:ℝ) *
     (log ((3*(200*max rank 1):ℕ):ℝ) +
      log 4) +
    (rank:ℝ) *
     (log ((3*(200*max rank 1):ℕ):ℝ) +
      log 4):=by
 have lF:0< max rank 1:=by positivity
 have DI:0<1600*max rank 1:=by positivity
 have DH:0<200*max rank 1:=by positivity
 have u4 :
   ((bG rank (1600*max rank 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DI).ne'
 have GA :
   ((bG rank (200*max rank 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DH).ne'
 unfold bR
 push_cast
 rw[Ql
   (Rl u4 GA) GA,
  Ql u4 GA,
  f0 DI,
  f0 DH]
 push_cast
 ring
lemma fI
  {m:ℕ} {L:ℝ} (hm:0< m)
  (ei:log (m:ℝ)≤L) :
  log ((3*m:ℕ):ℝ)≤3+L:=by
 have qD:(0:ℝ)< m:=by exact_mod_cast hm
 have h3:log (3:ℝ)≤3:=
  cV (by norm_num)
 push_cast
 rw[Ql (by norm_num) qD.ne']
 nlinarith
lemma lS:log (4:ℝ)≤2:=by
 rw[show(4:ℝ)=2^2 by norm_num,QB]
 have hmul:=iO fh
  (show(0:ℝ)≤2 by norm_num)
 norm_num at hmul ⊢
 exact hmul
lemma ia
  (d rank:ℕ)
  (cK:rank ≤
   ar.ax d (au d)) :
  log
    (bT rank
     (ar.bn d (au d))
     (ar.bd d (au d)):ℝ) ≤
   (1024*aH*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let bn:=ar.bn d (au d)
 let bd:=ar.bd d (au d)
 have eH:0<bn:=by
  unfold bn
  exact ar.mc (bX d)
 have fw:0<bd:=by
  unfold bd
  exact ar.md (bX d)
 have GB:log (bn:ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
  simpa[bn] using qd d
 have GC:log (bd:ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
  simpa[bd] using qe d
 have Nz:=fI eH GB
 have NA:=fI fw GC
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have DJ :
   log ((3*bn:ℕ):ℝ)+log 4 ≤
    7700599*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have DK :
   log ((3*bd:ℕ):ℝ)+log 4 ≤
    6958199*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have sP:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   _ ≤
     (ar.ax d (au d):ℝ):=by
    exact_mod_cast cK
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    exact_mod_cast ff d
 have xI :
   0≤log ((3*bn:ℕ):ℝ)+log 4:=by
  have h3:(1:ℝ)≤(3*bn:ℕ):=by
   exact_mod_cast(show 1≤3*bn by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 have xJ :
   0≤log ((3*bd:ℕ):ℝ)+log 4:=by
  have h3:(1:ℝ)≤(3*bd:ℕ):=by
   exact_mod_cast(show 1≤3*bd by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 rw[qf eH fw]
 have GD:=QW sP DJ xI (by positivity)
 have GF:=QW sP DK xJ (by positivity)
 push_cast at GD GF ⊢
 nlinarith
lemma gD
  (d rank:ℕ)
  (cK:rank ≤
   ar.ax d (au d)) :
  log (bR rank:ℝ) ≤
   (1024*aH*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 have kT:0<R:=by
  unfold R
  exact ar.iH (bX d)
 have wR:log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have N2:log ((max rank 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=
  (ky kT (by simpa[R] using cK)).trans wR
 have wS:0< max rank 1:=by positivity
 have A9:(0:ℝ)< max rank 1:=by exact_mod_cast wS
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Ix :
   log ((1600*max rank 1:ℕ):ℝ) ≤
    1600+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((1600*max rank 1:ℕ):ℝ) =
    (1600:ℝ)*((max rank 1:ℕ):ℝ) by norm_num]
  rw[Ql (by norm_num) A9.ne']
  have DI:log (1600:ℝ)≤1600:=
   cV (by norm_num)
  nlinarith
 have Fj :
   log ((200*max rank 1:ℕ):ℝ) ≤
    200+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((200*max rank 1:ℕ):ℝ) =
    (200:ℝ)*((max rank 1:ℕ):ℝ) by norm_num]
  rw[Ql (by norm_num) A9.ne']
  have DH:log (200:ℝ)≤200:=
   cV (by norm_num)
  nlinarith
 have Iy:0<1600*max rank 1:=by positivity
 have Fk:0<200*max rank 1:=by positivity
 have NB:=fI Iy Ix
 have Mf:=fI Fk Fj
 have DL :
   log ((3*(1600*max rank 1):ℕ):ℝ)+log 4 ≤
    6882998*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have Ba :
   log ((3*(200*max rank 1):ℕ):ℝ)+log 4 ≤
    6881598*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have sP:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (rank:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using cK)
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*aH:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast ff d)
 have xK :
   0≤log ((3*(1600*max rank 1):ℕ):ℝ)+log 4:=by
  have h3:(1:ℝ)≤(3*(1600*max rank 1):ℕ):=by
   exact_mod_cast(show 1≤3*(1600*max rank 1) by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 have wy :
   0≤log ((3*(200*max rank 1):ℕ):ℝ)+log 4:=by
  have h3:(1:ℝ)≤(3*(200*max rank 1):ℕ):=by
   exact_mod_cast(show 1≤3*(200*max rank 1) by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 rw[nG]
 have GG:=QW sP DL xK (by positivity)
 have DM:=QW sP Ba wy (by positivity)
 push_cast at GG DM ⊢
 nlinarith
def cv (d rank d4:ℕ):ℕ:=
 bT rank
   (ar.bn d (au d))
   (ar.bd d (au d)) *
  bR rank *
   (3*bA rank d4
    (cd d
     (ar.ax d (au d))))^rank *
    cL d
def cW:ℕ:=
 1024*aH*57669725 +
  eW
lemma lI (d:ℕ) :
  log (cL d:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
 let R:=ar.ax d (au d)
 let delta:=au d
 let n:=bE d*(8*au d+1)
 have Hm:0<bE d:=by
  unfold bE
  exact gV (bP d)
 have MX:0<delta:=by
  simpa[delta] using bX d
 have hn:0<n:=by
  unfold n
  positivity
 have Mg:log (n:ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
  simpa[n] using m7 d
 have B1:0≤log (n:ℝ):=by
  apply Qv
  exact_mod_cast(show 1≤n by exact Nat.one_le_iff_ne_zero.mpr hn.ne')
 have cu:(delta:ℝ) ≤
   (aH:ℝ) *
    ((d+1:ℕ):ℝ)^8:=by
  unfold delta
  exact_mod_cast jC d
 have hR:(R:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  unfold R
  exact_mod_cast ff d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have PO:((d+1:ℕ):ℝ)^8 ≤
   ((d+1:ℕ):ℝ)^10:=
  Se hx (by omega)
 have PQ:((d+1:ℕ):ℝ)^9 ≤
   ((d+1:ℕ):ℝ)^10:=
  Se hx (by omega)
 have jx :
   (delta:ℝ)*log (n:ℝ) ≤
    ((aH:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (delta:ℝ)*log (n:ℝ) ≤
     ((aH:ℝ) *
      ((d+1:ℕ):ℝ)^8) *
      (8601726*((d+1:ℕ):ℝ)^2):=
    QW cu Mg B1 (by positivity)
   _=((aH:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by ring
 have KB:(R+delta:ℝ) ≤
   (1024*aH +
    aH:ℕ) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R:ℝ)+delta ≤
     ((1024*aH:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^9 +
      aH *
       ((d+1:ℕ):ℝ)^8:=Sr hR cu
   _≤((1024*aH:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^10 +
      aH *
       ((d+1:ℕ):ℝ)^10:=by
    gcongr
   _=((1024*aH +
      aH:ℕ):ℝ) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 have A8:log (4:ℝ)≤2:=by
  rw[show(4:ℝ)=2^2 by norm_num,QB]
  have hmul:=iO fh
   (show(0:ℝ)≤2 by norm_num)
  norm_num at hmul ⊢
  exact hmul
 have zg:0≤log (4:ℝ):=
  Qv (by norm_num)
 have uh :
   (R+delta:ℝ)*log 4 ≤
    (2:ℝ) *
     (1024*aH +
      aH) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R+delta:ℝ)*log 4 ≤
     ((1024*aH +
      aH:ℕ):ℝ) *
      ((d+1:ℕ):ℝ)^10*2:=
    QW KB A8 zg (by positivity)
   _=(2:ℝ) *
     (1024*aH +
      aH) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 unfold cL
 change log (dH R delta n:ℝ)≤_
 rw[wx hn]
 unfold eW
 push_cast at jx uh ⊢
 nlinarith
lemma jX
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (pd:d4≤8*au d) :
  log (cv d rank d4:ℝ) ≤
   (cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let two:=bT rank
  (ar.bn d (au d))
  (ar.bd d (au d))
 let smooth:=bR rank
 let source:=
  (3*bA rank d4
   (cd d
    (ar.ax d (au d))))^rank
 let cell:=cL d
 have vc:log (two:ℝ) ≤
   (1024*aH*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[two] using
   ia d rank cK
 have j8:log (smooth:ℝ) ≤
   (1024*aH*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[smooth] using
   gD d rank cK
 have gM:log (source:ℝ) ≤
   (1024*aH*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[source] using
   jT d rank d4 cK pd
 have lP:log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
  simpa[cell] using lI d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have KC:((d+1:ℕ):ℝ)^10 ≤
   ((d+1:ℕ):ℝ)^11:=
  Se hx (by omega)
 have Iz:log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=
  lP.trans (iO KC (by positivity))
 have uG:(0:ℝ)<two:=by
  have eH:=ar.mc (d:=d)
   (aq:=au d) (bX d)
  have fw:=ar.md (d:=d)
   (aq:=au d) (bX d)
  unfold two bT
  exact_mod_cast QP
   (ck eH) (ck fw)
 have vd:(0:ℝ)<smooth:=by
  unfold smooth bR bG
  positivity
 have yA:(0:ℝ)<source:=by
  unfold source bA cd
  positivity
 have GH:(0:ℝ)<cell:=by
  have hq:0<bE d:=by
   unfold bE
   exact gV (bP d)
  unfold cell cL dH
  positivity
 change log ((two*smooth*source*cell:ℕ):ℝ)≤_
 push_cast
 rw[Ql
   (Rl
    (Rl uG.ne' vd.ne') yA.ne')
   GH.ne',
  Ql (Rl uG.ne' vd.ne') yA.ne',
  Ql uG.ne' vd.ne']
 unfold cW
 push_cast at vc j8 gM Iz ⊢
 nlinarith
end
end ay.aa
end
section
open Finset Fintype Function
open scoped BigOperators NNReal Pointwise translate
namespace ay.uH
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
omit [DecidableEq G] [Fintype G] in
lemma vs
    {H:Type*} [AddCommGroup H]
    (B:aj G) (e:G ≃+ H) (a8:NNReal) :
    (B.map e).ai a8=(B.ai a8).map e:=by
  classical
  rfl
omit [DecidableEq G] in
lemma w0
  {H:Type*} [AddCommGroup H] [Fintype H]
  (B:aj G) (e:G ≃+ H) (hB:B.a1) :
  (B.map e).a1:=by
 classical
 unfold aj.a1 at hB ⊢
 simp only[aj.Am]
 intro aF dy
 have h:=hB aF dy
 rw[vs,vs,
  aj.kA,aj.kA,
  aj.kA]
 exact h
lemma qR
  {M:ℕ} [NeZero M] (hM:Odd M) (B:aj (ZMod M))
  (hB:B.a1) :
  (aO.hY M hM B).a1:=
       w0 B (aj.eK M hM) hB
omit [DecidableEq G] in
lemma fW
  (B:aj G) (m:ℕ) (hm:0< m) :
  ∃ c:ah.bt (G:=G),
   c.ba.a1 ∧
   c.ba.rank=B.rank ∧
   c.outer=1 ∧
   c.carrier=c.ba.carrier ∧
   c.carrier⊆(B.ai ((m:NNReal)⁻¹)).carrier ∧
   B.carrier.card ≤
    ((3*m)^B.rank*4^B.rank)*c.carrier.card:=by
 classical
 let D:=B.ai ((m:NNReal)⁻¹)
 obtain ⟨R,qk,oT,Hg,ya⟩:=
  ag.kv D
 obtain ⟨c,Bb,_hcouter,wz⟩:=
  ah.bt.od R qk
 refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
 ·simpa[Bb] using qk
 ·simpa[Bb,D] using oT
 ·exact _hcouter
 ·simpa[Bb] using wz
 ·simpa[wz,D] using Hg
 ·have c3:=
   aj.cM
    B 1 hm
  have uD :
    B.carrier.card ≤
     (3*m)^B.rank *
      (B.ai ((m:NNReal)⁻¹)).carrier.card:=by
   simpa[Qw] using c3
  calc
   _ ≤
     (3*m)^B.rank *
      (B.ai ((m:NNReal)⁻¹)).carrier.card:=uD
   _≤(3*m)^B.rank*(4^B.rank*R.carrier.card):=
          Qr _ (by simpa[D] using ya)
   _=((3*m)^B.rank*4^B.rank)*c.carrier.card:=by
    rw[wz]
    ring
def b9 (B:aj G) (m:ℕ):ℕ:=
 (3*m)^B.rank*4^B.rank
def bI (B:aj G) (bn bd:ℕ):ℕ:=
 b9 B bn*b9 B bd
structure c7 (B:aj G) (bn bd:ℕ) where
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 ez:ak.ba.a1
 fe:aB.ba.a1
 rankOne:ak.ba.rank=B.rank
 p5:aB.ba.rank=B.rank
 fT:ak.outer=1
 g3:aB.outer=1
 eD:ak.carrier=ak.ba.carrier
 n5:aB.carrier=aB.ba.carrier
 nY:ak.carrier⊆(B.ai ((bn:NNReal)⁻¹)).carrier
 p4:aB.carrier⊆(B.ai ((bn:NNReal)⁻¹)).carrier
 Bc :
  aB.carrier ⊆
   (ak.ba.ai ((bd:NNReal)⁻¹)).carrier
 kV :
  aO.a4 aB.carrier ⊆
   (ak.ba.ai
    ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).carrier
 mE :
  B.carrier.card ≤
   b9 B bn*ak.carrier.card
 mF :
  B.carrier.card ≤
   bI B bn bd*aB.carrier.card
lemma rR (B:aj G)
  (bn bd:ℕ) (eH:0<bn) (fw:0<bd)
  (xL:((bd:NNReal)⁻¹)≤1) :
  Nonempty (c7 B bn bd):=by
 obtain ⟨Bd,IA,xM,Fl,tP,zy,ve⟩:=
  fW B bn eH
 obtain ⟨xN,IB,Fm,Fn,B2,r2,B3⟩:=
  fW Bd.ba bd fw
 have Fo:xN.carrier ⊆
   (B.ai ((bn:NNReal)⁻¹)).carrier:=by
  intro x hx
  apply zy
  rw[tP]
  simpa using aj.b5 xL (r2 hx)
 have GI :
   aO.a4 xN.carrier ⊆
    (Bd.ba.ai
     ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).carrier:=by
  intro x hx
  obtain ⟨y,hy,rfl⟩:=aO.m2.mp hx
  exact aj.e8 (r2 hy) (r2 hy)
 have GJ := Fm.trans xM
 have xO :
   B.carrier.card ≤
    bI B bn bd*xN.carrier.card:=by
  calc
   _ ≤
     b9 B bn*Bd.carrier.card:=
    ve
   _≤b9 B bn *
     (b9 Bd.ba bd *
      xN.carrier.card):=
    Qr _
     (by simpa[tP,b9] using B3)
   _=bI B bn bd*xN.carrier.card:=by
    simp[b9,bI,xM]
    ring
 exact ⟨{
  ak:=Bd
  aB:=xN
  ez:=IA
  fe:=IB
  rankOne:=xM
  p5:=GJ
  fT:=Fl
  g3:=Fn
  eD:=tP
  n5:=B2
  nY:=zy
  p4:=Fo
  Bc:=r2
  kV:=GI
  mE:=ve
  mF:=xO }⟩
structure gj {original:Finset G}
  (s:ah.aA original) (bn bd:ℕ)
  (epsilon aU:ℝ) where
 Be:s.restriction.outer=1
 iK:s.restriction.ba.a1
 yB :
  ((bn:NNReal)⁻¹) ≤
   1/(100*(max s.restriction.ba.rank 1:ℕ):NNReal)
 vt :
  400*((max s.restriction.ba.rank 1:ℕ):ℝ) *
    (((bn:NNReal)⁻¹ :NNReal):ℝ)≤epsilon*s.density/4
 tk :
  exp (-aU)*(s.card:ℝ) ≤
   ((b9 s.restriction.ba bn:ℕ):ℝ)⁻¹ *
    (s.restriction.ba.carrier.card:ℝ)
 tl :
  exp (-aU)*(s.card:ℝ) ≤
   ((bI s.restriction.ba bn bd:ℕ):ℝ)⁻¹ *
    (s.restriction.ba.carrier.card:ℝ)
lemma mm
  {original:Finset G} (s:ah.aA original)
  {g5:ℕ} {aU:ℝ} {child:Finset G}
  (mK:(0:ℝ)<(g5:ℝ))
  (oe :
   exp (-aU)*(s.card:ℝ) ≤
    (g5:ℝ)⁻¹ *(s.restriction.ba.carrier.card:ℝ))
  (GK :
   (s.restriction.ba.carrier.card:ℝ) ≤
    (g5:ℝ)*(child.card:ℝ)) :
  exp (-aU)*(s.card:ℝ)≤child.card:=by
 calc
  _ ≤
    (g5:ℝ)⁻¹ *(s.restriction.ba.carrier.card:ℝ):= oe
  _≤(g5:ℝ)⁻¹ *((g5:ℝ)*(child.card:ℝ)):=
         iO GK (by positivity)
  _=child.card:=by
   field_simp
lemma jk
  {original:Finset G} (s:ah.aA original)
  (ju:s.restriction.outer=1)
  {g5:ℕ} {aU:ℝ}
  (mK:(0:ℝ)<(g5:ℝ))
  (ei:log (g5:ℝ)≤aU) :
  exp (-aU)*(s.card:ℝ) ≤
   (g5:ℝ)⁻¹ *(s.restriction.ba.carrier.card:ℝ):=by
 have l9 :
   exp (-aU)≤(g5:ℝ)⁻¹:=by
  have eY := TO ei
  have h:=Real.exp_le_exp.mpr eY
  calc
   _ ≤exp (-log (g5:ℝ)):=h
   _=(g5:ℝ)⁻¹:=by
    rw[Uh,Real.exp_log mK]
 have ch :
   (s.card:ℝ)=(s.restriction.ba.carrier.card:ℝ):=by
  unfold ah.aA.card br.aY.card
   br.aY.e9
  simp[ju]
 rw[ch]
 exact Qi l9 (by positivity)
lemma oy
  {g5:ℕ} {aU:ℝ} (mK:0<g5)
  (ei:log (g5:ℝ)≤aU) :
  exp (-aU)*(g5:ℝ)≤1:=by
 have l9:exp (-aU)≤(g5:ℝ)⁻¹:=by
  have eY := TO ei
  calc
   _ ≤exp (-log (g5:ℝ)):=
    Real.exp_le_exp.mpr eY
   _=(g5:ℝ)⁻¹:=by
    rw[Uh,Real.exp_log (by exact_mod_cast mK)]
 calc
  _ ≤(g5:ℝ)⁻¹ *g5:=by gcongr
  _=1:=by
   have Pn:(0:ℝ)<g5:=by exact_mod_cast mK
   field_simp
omit [Fintype G] in
lemma lJ
  {A S T D:Finset G} (k:ℕ) {alpha C:ℝ}
  (b8:0≤alpha) (hC:0<C)
  (hA:A.Nonempty) (hS:S.Nonempty)
  (Cu:alpha*(D.card:ℝ)≤(A.card:ℝ))
  (hsum:((A+S).card:ℝ)≤C*(D.card:ℝ))
  (hT :
   (((A.card:ℝ)^k/2*S.card) /
     ((A+S).card:ℝ)^k≤(T.card:ℝ))) :
  (((alpha/C)^k/2)*(S.card:ℝ))≤(T.card:ℝ):=by
 have rY:(0:ℝ)<(A+S).card:=by
  exact_mod_cast(hA.add hS).card_pos
 have IC:(0:ℝ)<((A+S).card:ℝ)^k:=by
  positivity
 apply Sj ?_ hT
 apply(Qs IC).2
 calc
  _
                     ≤
   ((alpha/C)^k/2)*(S.card:ℝ) *
    (C*(D.card:ℝ))^k:=by
     gcongr
  _=(alpha*(D.card:ℝ))^k/2*S.card:=by
     have PW := hC.ne'
     rw[QL]
     field_simp
     have ID:alpha/C*C=alpha:=by field_simp
     rw[←QL (alpha/C) C,ID, ←QL]
  _≤(A.card:ℝ)^k/2*S.card:=by
     gcongr
lemma nH
  (B:aj G) (A S:Finset G) {a8:NNReal}
  (hA:A⊆B.carrier)
  (hS:S⊆(B.ai a8).carrier) :
  (-A)+S⊆(B.ai (1+a8)).carrier:=by
 intro x hx
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp hx
 obtain ⟨a,ha,rfl⟩:=Finset.mem_neg.mp hu
 exact aj.e8
  (by simpa using(aj.ec.mpr (hA ha))) (hS hv)
lemma ij
  (B:aj G) (rH:B.a1)
  (A S:Finset G) {a8:NNReal}
  (hA:A⊆B.carrier)
  (hS:S⊆(B.ai a8).carrier)
  (jM :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal)) :
  (-A+S).card≤2*B.carrier.card:=by
 have l4:=nH B A S hA hS
 have ch :
   ((B.ai (1+a8)).carrier.card:ℝ) ≤
    (1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)) *
     (B.carrier.card:ℝ):=
  (rH a8 jM).2
 have qI :
   1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)≤2:=by
  have NC :
    (a8:ℝ) ≤
     1/(100*((max B.rank 1:ℕ):ℝ)):=by
   exact_mod_cast jM
  have ND:(0:ℝ)<(max B.rank 1:ℕ):=by positivity
  have hmul :
    100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)≤1:=by
   calc
    _ ≤
      100*((max B.rank 1:ℕ):ℝ) *
       (1/(100*((max B.rank 1:ℕ):ℝ))):=by
        gcongr
    _=1:=by field_simp
  nlinarith
 have KD :
   ((B.ai (1+a8)).carrier.card:ℝ) ≤
    2*(B.carrier.card:ℝ):=by
  calc
   _ ≤
     (1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)) *
      (B.carrier.card:ℝ):=ch
   _≤2*(B.carrier.card:ℝ):=by
    gcongr
 have GM :
   ((-A+S).card:ℝ) ≤
    ((B.ai (1+a8)).carrier.card:ℝ):=by
  exact_mod_cast Qu l4
 exact_mod_cast GM.trans KD
lemma pe
  (B:aj G) (rH:B.a1)
  (S:Finset G) {a8:NNReal}
  (hS:S⊆(B.ai a8).carrier)
  (jM :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal)) :
  (B.carrier-S).card≤2*B.carrier.card:=by
 have h:=
  ij B rH B.carrier S
   (fun _ hx↦hx) hS jM
 have eY :
   (B.carrier-S).card=(-B.carrier+S).card:=by
  rw[←Finset.card_neg]
  simp[Qy,RV]
 rw[eY]
 exact h
lemma mL
  (B:aj G) (rH:B.a1)
  (S:Finset G) {a8:NNReal}
  (hS:S⊆(B.ai a8).carrier)
  (jM :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal))
  (z:G) :
  ((z+ᵥ B.carrier)-S).card≤2*B.carrier.card:=by
 have dc:=pe B rH S hS jM
 have heq :
   (z+ᵥ B.carrier)-S=z+ᵥ (B.carrier-S):=by
  ext x
  constructor
  ·intro hx
   obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp hx
   obtain ⟨b,hb,rfl⟩:=Finset.mem_vadd_finset.mp hu
   apply Finset.mem_vadd_finset.mpr
   exact ⟨b-v,Finset.mem_sub.mpr ⟨b,hb,v,hv,rfl⟩,by
    simp only[Uz]
    abel⟩
  ·intro hx
   obtain ⟨u,hu,rfl⟩:=Finset.mem_vadd_finset.mp hx
   obtain ⟨b,hb,v,hv,rfl⟩:=Finset.mem_sub.mp hu
   apply Finset.mem_sub.mpr
   exact ⟨z+b,Finset.mem_vadd_finset.mpr ⟨b,hb,rfl⟩,
    v,hv,by
     simp only[Uz]
     abel⟩
 rw[heq,Finset.card_vadd_finset]
 exact dc
structure bU (W:aj G) where
 eta:NNReal
 b6:aj G
 vf:NNReal
 theta:NNReal
 bx:aj G
 vg:NNReal
 phi:NNReal
 bl:aj G
 pg:NNReal
 Fp:eta=1/(1600*(max W.rank 1:ℕ):NNReal)
 uB:0<eta
 mI :
  4*eta≤1/(400*(max W.rank 1:ℕ):NNReal)
 GN:b6=(W.ai eta).ai vf
 zz:1/2≤vf
 GO:vf≤1
 zA:b6.a1
 Bf:theta=1/(200*(max b6.rank 1:ℕ):NNReal)
 theta_pos:0<theta
 xc :
  theta≤1/(100*(max b6.rank 1:ℕ):NNReal)
 GQ:bx=(b6.ai theta).ai vg
 zB:1/2≤vg
 GR:vg≤1
 zC:bx.a1
 Fq:phi=1/(200*(max bx.rank 1:ℕ):NNReal)
 IE:0<phi
 zD :
  phi≤1/(100*(max bx.rank 1:ℕ):NNReal)
 zh:bl=(bx.ai phi).ai pg
 xd:1/2≤pg
 DN:pg≤1
 wA:bl.a1
 rZ:b6.carrier⊆(W.ai eta).carrier
 r0:bx.carrier⊆(W.ai eta).carrier
 xe:bx.carrier⊆(b6.ai theta).carrier
 DO:bl.carrier⊆(W.ai eta).carrier
 wB:bl.carrier⊆(bx.ai phi).carrier
omit [DecidableEq G] in
lemma rS (W:aj G) :
  Nonempty (bU W):=by
 classical
 let dW := max W.rank 1
 let eta:NNReal:=1/(1600*(dW:NNReal))
 have Qe:0<dW:=by simp[dW]
 have IF:0<eta:=by
  dsimp[eta]
  positivity
 have vh :
   4*eta≤1/(400*(max W.rank 1:ℕ):NNReal):=by
  dsimp[eta,dW]
  have hd:(0:NNReal)<(max W.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vf,Fr,Bg,Mh⟩:=
  (W.ai eta).eP
 let b6:aj G:=(W.ai eta).ai vf
 let dD := max b6.rank 1
 let theta:NNReal:=1/(200*(dD:NNReal))
 have Qf:0<dD:=by simp[dD]
 have Fs:0<theta:=by
  dsimp[theta]
  positivity
 have xf :
   theta≤1/(100*(max b6.rank 1:ℕ):NNReal):=by
  dsimp[theta,dD]
  have hd:(0:NNReal)<(max b6.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vg,Ft,Bh,Mi⟩:=
  (b6.ai theta).eP
 let bx:aj G:=(b6.ai theta).ai vg
 let dE := max bx.rank 1
 let phi:NNReal:=1/(200*(dE:NNReal))
 have Qg:0<dE:=by simp[dE]
 have IG:0<phi:=by
  dsimp[phi]
  positivity
 have zE :
   phi≤1/(100*(max bx.rank 1:ℕ):NNReal):=by
  dsimp[phi,dE]
  have hd:(0:NNReal)<(max bx.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨pg,B4,yC,sx⟩:=
  (bx.ai phi).eP
 let bl:aj G:=(bx.ai phi).ai pg
 have gn:b6.carrier⊆(W.ai eta).carrier:=by
  dsimp[b6]
  simpa using
   (aj.b5 Bg :
    ((W.ai eta).ai vf).carrier ⊆
     ((W.ai eta).ai 1).carrier)
 have Cv :
   bx.carrier⊆(b6.ai theta).carrier:=by
  dsimp[bx]
  simpa using
   (aj.b5 Bh :
    ((b6.ai theta).ai vg).carrier ⊆
     ((b6.ai theta).ai 1).carrier)
 have Fu:theta≤1:=by
  calc
   _ ≤1/(100*(max b6.rank 1:ℕ):NNReal):=
    xf
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤100*max b6.rank 1 by omega)
    ·positivity
 have lk:bx.carrier⊆(W.ai eta).carrier:=by
  apply Cv.trans
  apply(aj.b5 Fu).trans
  simpa using gn
 have Bi :
   bl.carrier⊆(bx.ai phi).carrier:=by
  dsimp[bl]
  simpa using
   (aj.b5 yC :
    ((bx.ai phi).ai pg).carrier ⊆
     ((bx.ai phi).ai 1).carrier)
 have IH:phi≤1:=by
  calc
   _ ≤1/(100*(max bx.rank 1:ℕ):NNReal):=
    zE
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤100*max bx.rank 1 by omega)
    ·positivity
 have DP:bl.carrier⊆(W.ai eta).carrier:=by
  apply Bi.trans
  apply(aj.b5 IH).trans
  simpa using lk
 exact ⟨{
  eta:=eta
  b6:=b6
  vf:=vf
  theta:=theta
  bx:=bx
  vg:=vg
  phi:=phi
  bl:=bl
  pg:=pg
  Fp:=rfl
  uB:=IF
  mI:=vh
  GN:=rfl
  zz:=Fr
  GO:=Bg
  zA:=by simpa[b6] using Mh
  Bf:=rfl
  theta_pos:=Fs
  xc:=xf
  GQ:=rfl
  zB:=Ft
  GR:=Bh
  zC:=by simpa[bx] using Mi
  Fq:=rfl
  IE:=IG
  zD:=zE
  zh:=rfl
  xd:=B4
  DN:=yC
  wA:=by simpa[bl] using sx
  rZ:=gn
  r0:=lk
  xe:=Cv
  DO:=DP
  wB:=Bi }⟩
omit [DecidableEq G] in
lemma d0
  (B:aj G) (a8:NNReal) (jM:1/2≤a8) :
  B.carrier.card≤4^B.rank*(B.ai a8).carrier.card:=by
 classical
 have iB:=B.de
 have ym :
   (B.ai (1/2)).carrier.card≤(B.ai a8).carrier.card:=
  Qu (aj.b5 jM)
 calc
  B.carrier.card≤4^B.rank*(B.ai (1/2)).carrier.card:=
   by simpa using iB
  _≤4^B.rank*(B.ai a8).carrier.card:=
   Qr _ ym
omit [DecidableEq G] in
lemma mn (W:aj G) (H:bU W) :
  H.b6.rank=W.rank∧H.bx.rank=W.rank∧H.bl.rank=W.rank:=by
 have hD:H.b6.rank=W.rank:=by
  rw[H.GN,aj.f6,aj.f6]
 have hE:H.bx.rank=W.rank:=by
  rw[H.GQ,aj.f6,aj.f6]
  exact hD
 have hB:H.bl.rank=W.rank:=by
  rw[H.zh,aj.f6,aj.f6]
  exact hE
 constructor
 ·exact hD
 constructor
 ·exact hE
 ·exact hB
def b7 (W:aj G):ℕ:=
 ((3*(1600*max W.rank 1))^W.rank*4^W.rank) *
  ((3*(200*max W.rank 1))^W.rank*4^W.rank) *
  ((3*(200*max W.rank 1))^W.rank*4^W.rank)
omit [DecidableEq G] in
lemma qg
  (W:aj G) (H:bU W) :
  W.carrier.card≤b7 W*H.bl.carrier.card:=by
 classical
 let qh:ℕ:=1600*max W.rank 1
 let jD:ℕ:=200*max W.rank 1
 have Mj:0<qh:=by dsimp[qh]; positivity
 have Cw:0<jD:=by dsimp[jD]; positivity
 have uI:=mn W H
 have Mk :
   W.carrier.card≤(3*qh)^W.rank *
    (W.ai H.eta).carrier.card:=by
  have c3:=
   aj.cM W 1 Mj
  rw[H.Fp]
  simpa[qh,Qw] using c3
 have Ml :
   (W.ai H.eta).carrier.card≤4^W.rank*H.b6.carrier.card:=by
  rw[H.GN]
  simpa only[aj.f6] using
   d0
    (W.ai H.eta) H.vf H.zz
 have IJ :
   H.b6.carrier.card≤(3*jD)^W.rank *
    (H.b6.ai H.theta).carrier.card:=by
  have c3:=
   aj.cM H.b6 1 Cw
  rw[H.Bf]
  simpa[jD,uI.1,Qw] using c3
 have Po :
   (H.b6.ai H.theta).carrier.card ≤
    4^W.rank*H.bx.carrier.card:=by
  rw[H.GQ]
  simpa[uI.1] using
   d0
    (H.b6.ai H.theta) H.vg H.zB
 have IK :
   H.bx.carrier.card≤(3*jD)^W.rank *
    (H.bx.ai H.phi).carrier.card:=by
  have c3:=
   aj.cM H.bx 1 Cw
  rw[H.Fq]
  simpa[jD,uI.2.1,Qw] using c3
 have Pp :
   (H.bx.ai H.phi).carrier.card ≤
    4^W.rank*H.bl.carrier.card:=by
  rw[H.zh]
  simpa[uI.2.1] using
   d0
    (H.bx.ai H.phi) H.pg H.xd
 unfold b7
 calc
  _ ≤(3*qh)^W.rank *
    (W.ai H.eta).carrier.card:=Mk
  _≤(3*qh)^W.rank*(4^W.rank*H.b6.carrier.card):=
   Qr _ Ml
  _≤((3*qh)^W.rank*4^W.rank) *
    ((3*jD)^W.rank *
     (H.b6.ai H.theta).carrier.card):=by
   have h:=Qr
    ((3*qh)^W.rank*4^W.rank) IJ
   simpa[SZ,R8,U6] using h
  _≤((3*qh)^W.rank*4^W.rank) *
    ((3*jD)^W.rank*(4^W.rank*H.bx.carrier.card)):=by
   gcongr
  _≤((3*qh)^W.rank*4^W.rank) *
    (((3*jD)^W.rank*4^W.rank) *
     ((3*jD)^W.rank *
      (H.bx.ai H.phi).carrier.card)):=by
   have h:=Qr
    (((3*qh)^W.rank*4^W.rank) *
     ((3*jD)^W.rank*4^W.rank)) IK
   simpa[SZ,R8,U6] using h
  _≤((3*qh)^W.rank*4^W.rank) *
    (((3*jD)^W.rank*4^W.rank) *
     ((3*jD)^W.rank*(4^W.rank*H.bl.carrier.card))):=by
   gcongr
  _=(((3*(1600*max W.rank 1))^W.rank*4^W.rank) *
    ((3*(200*max W.rank 1))^W.rank*4^W.rank) *
    ((3*(200*max W.rank 1))^W.rank*4^W.rank)) *
    H.bl.carrier.card:=by
   simp[qh,jD]
   ring
lemma ki
  (W:aj G) {D E:Finset G} {eta:NNReal}
  (hD:D⊆(W.ai eta).carrier)
  (hE:E⊆(W.ai eta).carrier) :
  ∀ t,aN.bh D E t≠0 →
   t∈(W.ai (4*eta)).carrier:=by
 intro t ht
 have zF :
   t∈Function.support (aN.bh D E):=ht
 have qm :
   0≤aN.dU D E:=by
  simp[aN.dU]
 have KE:t∈(D+E)-(D+E):=by
  rw[aN.bh,
   f8 qm qm,
   aN.dU,
   tW cC cC,
   jo,jo] at zF
  simpa only[←coe_add, ←coe_sub,mem_coe] using zF
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp KE
 obtain ⟨d₁,Mm,KF,Mn,rfl⟩:=Finset.mem_add.mp hu
 obtain ⟨d₂,Mo,KG,Mp,rfl⟩:=Finset.mem_add.mp hv
 have Pq :
   d₁+KF∈(W.ai (eta+eta)).carrier:=
  aj.e8 (hD Mm) (hE Mn)
 have Pr :
   d₂+KG∈(W.ai (eta+eta)).carrier:=
  aj.e8 (hD Mo) (hE Mp)
 have l4 :
   (d₁+KF)-(d₂+KG) ∈
    (W.ai ((eta+eta)+(eta+eta))).carrier:=
  aj.j2 Pq Pr
 simpa[show(eta+eta)+(eta+eta)=4*eta by ring] using l4
lemma ld
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ}
  (C:c7 s.restriction.ba bn bd)
  (W:aj G) (H:bU W)
  (kz:W.carrier=aO.a4 C.aB.carrier) :
  ∀ t,
   aN.bh H.bx.carrier H.b6.carrier t≠0 →
   t∈(C.ak.ba.ai
    ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).carrier:=by
 intro t ht
 have KH  :=

  ki W H.r0 H.rZ t ht
 have GS:4*H.eta≤(1:NNReal):=by
  calc
   _ ≤
     1/(400*(max W.rank 1:ℕ):NNReal):=H.mI
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤400*max W.rank 1 by omega)
    ·positivity
 have MY:t∈W.carrier:=by
  simpa only[aj.oG] using
   (aj.b5 GS KH)
 rw[kz] at MY
 exact C.kV MY
def gk
  (W:aj G) (H:bU W) (a3:Finset G):Finset G:=
 (-a3)+H.bl.carrier
def cI
  (W:aj G) (H:bU W) (a3:Finset G):ℝ:=
 (gk W H a3).card
def cq
  (W:aj G) (H:bU W):ℝ:=
 H.bl.carrier.card
def du (a3:Finset G):ℝ:=
 (-a3).card
section wC
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
def b3
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (_data:ah.aW A aL H.bx.carrier p sigma delta)
  (k:ℕ):ℝ:=
 ((ah.bj A aL H.bx.carrier p/2)^k)/2
omit [DiscreteMeasurableSpace G] in
lemma mo
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  ((((ah.bj A aL H.bx.carrier p/2)^k) /
    2)*cq W H)≤(T.card:ℝ):=by
 have gN:=data.lR cu
 have Fv:(0:ℝ)<H.bx.carrier.card:=by
  exact_mod_cast H.bx.aE.card_pos
 have Cu :
   ah.bj A aL H.bx.carrier p *
     (H.bx.carrier.card:ℝ)≤(data.a3.card:ℝ):=
       (Qs Fv).mp data.tD
 have DQ :
   ah.bj A aL H.bx.carrier p *
     (H.bx.carrier.card:ℝ)≤((-data.a3).card:ℝ):=by
  simpa using Cu
 have yZ :
   (gk W H data.a3).card ≤
    2*H.bx.carrier.card:=by
  unfold gk
  apply ij H.bx H.zC
   data.a3 (H.bl).carrier data.rM H.wB H.zD
 have hsum :
   cI W H data.a3 ≤
    2*(H.bx.carrier.card:ℝ):=by
  unfold cI
  exact_mod_cast yZ
 have b8 :
   0≤ah.bj A aL H.bx.carrier p:=by
  unfold ah.bj
  exact RS (Qn (by norm_num) (QH tX _))
   (by positivity)
 have Mq:(-data.a3).Nonempty:=by
  obtain ⟨a,ha⟩:=gN.2
  exact ⟨-a,by simpa using ha⟩
 simpa only[du,cq,cI,
  gk,show(2:ℝ)=2 by rfl] using
  (lJ
   (A:=-data.a3) (S:=(H.bl).carrier) (T:=T)
   (D:=H.bx.carrier) k b8 (by norm_num:(0:ℝ)<2)
   Mq (H.bl).aE DQ hsum hT)
omit [DiscreteMeasurableSpace G] in
lemma i5
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G) (Delta:Finset (AddChar G ℂ))
  (hV:0 <
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)))
  (dQ:(Delta.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  Delta.card ≤
   ⌈8*(1+log (2 /
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k))⌉₊:=by
 have wD :
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.carrier.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[b3,cq] using
   mo W H data cu k T hT
 have oQ :
   aI.bf H.bl T (1/2) ≤
    8*(1+log (2 /
     b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k)):=
  fQ H.bl T hV
   (by
    have gy:(0:ℝ) <
      b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
       (delta:=delta) W H data k *
      (H.bl.carrier.card:ℝ):=
     QM hV (by exact_mod_cast H.bl.aE.card_pos)
    have DR:(0:ℝ)<T.card:=gy.trans_le wD
    exact Finset.card_pos.mp (by exact_mod_cast DR))
   wD
 exact ov Delta (dQ.trans oQ)
omit [DiscreteMeasurableSpace G] in
lemma oz
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (hV:0 <
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   8*(1+log (2 /
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k)):=by
 have wD :
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.carrier.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[b3,cq] using
   mo W H data cu k T hT
 apply fQ H.bl T hV
 ·have gy:(0:ℝ) <
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k *
     (H.bl.carrier.card:ℝ):=
   QM hV (by exact_mod_cast H.bl.aE.card_pos)
  have DR:(0:ℝ)<T.card:=gy.trans_le wD
  exact Finset.card_pos.mp (by exact_mod_cast DR)
 ·exact wD
end wC
lemma n6
  {original:Finset G} (s:ah.aA original)
  {d:ℕ}
  (c3:(1/(2:ℝ)^d)≤ s.density) :
  (2/3:ℝ)^(4*(d+1)) ≤
   (1-(1/512:ℝ))*s.density:=by
 have dc:(2/3:ℝ)^4≤1/2:=by norm_num
 have hpow :
   (2/3:ℝ)^(4*(d+1))≤(1/2:ℝ)^(d+1):=by
  calc
   _ =
     ((2/3:ℝ)^4)^(d+1):=by rw[QU]
   _≤(1/2:ℝ)^(d+1):=
    Qp (by positivity) dc (d+1)
 have we :
   (1/2:ℝ)^(d+1) ≤
    (511/512:ℝ)*(1/(2:ℝ)^d):=by
  have DS:0≤(1/2:ℝ)^d:=by positivity
  rw[RB]
  calc
   _ ≤
     (1/2:ℝ)^d*(511/512):=
    iO (by norm_num) DS
   _=(511/512:ℝ)*(1/(2:ℝ)^d):=by
    simp[R6,Te,Qx]
 calc
  _ ≤(1/2:ℝ)^(d+1):=hpow
  _≤(511/512:ℝ)*(1/(2:ℝ)^d):=we
  _≤(511/512:ℝ)*s.density:=
   iO c3 (by norm_num)
  _=(1-(1/512:ℝ))*s.density:=by ring
noncomputable def bF
    {original:Finset G}
    (s:bu.aG original)
    {bn bd:ℕ} (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {epsilon aU:ℝ} {aq:ℕ}
    (kG:gj s.aV bn bd epsilon aU) :
    bu.dB s epsilon aU aq:=by
  have zX :
      (0:ℝ)<(b9 s.aV.restriction.ba bn:ℝ):=by
    unfold b9
    positivity
  have zY :
      (0:ℝ) <
        (bI s.aV.restriction.ba bn bd:ℝ):=by
    unfold bI b9
    positivity
  have IL :
      (s.aV.restriction.ba.carrier.card:ℝ) ≤
        (b9 s.aV.restriction.ba bn:ℝ) *
          (C.ak.carrier.card:ℝ):=by
    exact_mod_cast C.mE
  have IM :
      (s.aV.restriction.ba.carrier.card:ℝ) ≤
        (bI s.aV.restriction.ba bn bd:ℝ) *
          (C.aB.carrier.card:ℝ):=by
    exact_mod_cast C.mF
  have ve :
      exp (-aU)*(s.card:ℝ)≤C.ak.carrier.card:=by
    simpa[bu.aG.card] using
      mm s.aV zX kG.tk IL
  have xO :
      exp (-aU)*(s.card:ℝ)≤C.aB.carrier.card:=by
    simpa[bu.aG.card] using
      mm s.aV zY kG.tl IM
  have o5 :
      cp s.aV.restriction.set
          s.aV.restriction.ba.carrier=s.aV.density:=by
    unfold ah.aA.density
      br.aY.density cp
      br.aY.e9
    simp[s.fS]
  refine
    { aF:=(bn:NNReal)⁻¹
      xb:=kG.yB
      ak:=C.ak
      aB:=C.aB
      fT:=C.fT
      g3:=C.g3
      ez:=C.ez
      fe:=C.fe
      nY:=C.nY
      p4:=C.p4
      tg:= ?_
      rankOne:= ?_
      p5:= ?_
      mE:=ve
      mF:=xO }
  · simpa only[o5] using kG.vt
  · rw[C.rankOne]
    simp[bu.aG.rank,
      ah.aA.rank,br.aY.rank]
  · rw[C.p5]
    simp[bu.aG.rank,
      ah.aA.rank,br.aY.rank]
def cX {original:Finset G}
  (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon):Finset G:=
 ah.dn s.restriction.set ak.carrier
  (aO.cr aQ)
def jE {original:Finset G}
  (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon):Finset G:=
 ah.dn s.restriction.set aB.carrier
  (aO.cr aQ)
def a5 {original:Finset G}
  (s:ah.aA original) (epsilon:ℝ):ℝ:=
 (1-epsilon)*s.density
lemma ph
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  (cX s ak aB aQ).Nonempty:=by
 let alpha:=a5 s epsilon
 have b8 :=
  QM (sub_pos.mpr b2) s.dI
 have lG:alpha ≤
   a9 s.restriction.set ak.carrier
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.c0 aQ
 apply ah.bK
  ak.aE
 exact b8.trans_le lG
lemma qS
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon) :
  cX s ak aB aQ⊆ak.carrier:=
       ah.dz
  (B:=ak.ba) (a8:=ak.outer)
  (A:=s.restriction.set) (C:=ak.carrier)
  (x:=aO.cr aQ) (fun _ hz↦hz)

noncomputable def bB
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  ah.aA original:=by
 let x:=aO.cr aQ
 have oc :=
  QM (sub_pos.mpr b2) s.dI
 have hx:a5 s epsilon ≤
   a9 s.restriction.set ak.carrier x:=by
  simpa[x,a5] using
   aO.c0 aQ
 exact ah.di s ak x (oc.trans_le hx)
@[simp] lemma D1
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  (bB s ak aB aQ b2).restriction.set =
   cX s ak aB aQ:=by
 rfl
lemma na
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (eH:0<bn)
  (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (ju:s.restriction.outer=1) :
  (bB s C.ak C.aB aQ b2).card≤ s.card:=by
 have GU:((bn:NNReal)⁻¹)≤1:=by
  apply(inv_le_one₀ (by exact_mod_cast eH)).2
  exact_mod_cast(show 1≤bn by omega)
 have A5:C.ak.carrier.card≤ s.restriction.ba.carrier.card:=by
  calc
   _ ≤
     (s.restriction.ba.ai ((bn:NNReal)⁻¹)).carrier.card:=
    Qu C.nY
   _≤(s.restriction.ba.ai 1).carrier.card:=
    Qu (aj.b5 GU)
   _=s.restriction.ba.carrier.card:=by simp
 calc
  _ =
    C.ak.carrier.card:=by
   simp[bB,ah.di,
    ah.bt.eo,
    ah.aA.card,br.aY.card,
    br.aY.e9,C.fT,
    C.eD]
  _≤ s.restriction.ba.carrier.card:=A5
  _=s.card:=by
   unfold ah.aA.card br.aY.card
    br.aY.e9
   simp[ju]
lemma mq
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (eH:0<bn)
  (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (ju:s.restriction.outer=1)
  (W:aj G) (H:bU W)
  (wE:W.carrier.card=C.aB.carrier.card) :
  ((bB s C.ak C.aB aQ b2).card:ℝ) ≤
   ((bI s.restriction.ba bn bd *
     b7 W:ℕ):ℝ)*(H.bl.carrier.card:ℝ):=by
 have mj  :=

  na s eH C aQ b2 ju
 have KI :
   s.card≤bI s.restriction.ba bn bd*W.carrier.card:=by
  have hC:=C.mF
  unfold ah.aA.card br.aY.card
   br.aY.e9
  rw[wE]
  simpa[ju] using hC
 have Mr:=qg W H
 have sC :
   (bB s C.ak C.aB aQ b2).card ≤
    (bI s.restriction.ba bn bd *
     b7 W)*H.bl.carrier.card:=by
  calc
   _ ≤
     s.card:=mj
   _≤bI s.restriction.ba bn bd*W.carrier.card:=KI
   _≤bI s.restriction.ba bn bd *
     (b7 W*H.bl.carrier.card):=
    Qr _ Mr
   _=(bI s.restriction.ba bn bd *
     b7 W)*H.bl.carrier.card:=by ring
 exact_mod_cast sC
section xP
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma mM
  (A aL a0:Finset G) {p:ℕ} (hp:0<p) :
  ah.bj A aL a0 p =
   (4:ℝ)⁻¹ *
    ((A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) p)^(2*p):=by
 let w:G→ℝ≥0:=(al (mu aL) (mu a0))
 have rL :
   ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_))))) =
    ((A.card:ℝ)^2)•((al ((@mu (ℝ) _ _) A) (mu A))):=by
  rw[←l5 ℝ A,oB,oC]
  funext x
  simp[RD,Q2,TI]
  ring
 have c3:=
  aN.gx w
   ((al ((@mu (ℝ) _ _) A) (mu A))) ((A.card:ℝ)^2) (by positivity) hp
 have oS :
   (b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:ℝ))) ((indicator A fun _↦(1:_)))))) =
    (A.card:ℝ)^2 *
     an.aM
      ((↑) ∘ w)
      ((al ((@mu (ℝ) _ _) A) (mu A))) p:=by
  rw[rL]
  simpa only[aN.dN w
   ((A.card:ℝ)^2•((al ((@mu (ℝ) _ _) A) (mu A)))) hp] using c3
 dsimp[w,Function.comp_def] at oS
 rw[ah.bj,oS]
 by_cases MZ:(A.card:ℝ)=0
 ·have vc:2*p≠0:=by omega
  simp[MZ,vc]
 have hpow:(A.card:ℝ)^(2*p)≠0:=Rg _ MZ
 field_simp[hpow]
 ring
lemma mN
  (A aL a0:Finset G) {p:ℕ} (hp:0<p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  0<ah.bj A aL a0 p:=by
 classical
 have xY := hp.ne'
 have rK := hB.mono Sh
 have u2 := hB.mono Sd
 let N:ℝ:=(b0 p ((al (mu aL) (mu a0))) ((al ((indicator A fun _↦(1:(ℝ)))) ((indicator A fun _↦(1:_))))))
 have KJ:=
  ah.gQ A aL a0 p xY rK u2
 obtain ⟨b,hb⟩:=hB
 obtain ⟨a,ha⟩:=hA
 let sD:Fin p→G:=fun _↦b-a
 have v8:b∈cA.cS A aL sD:=by
  simp only[cA.jn,sD]
  refine ⟨Sh hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v9:b∈cA.cS A a0 sD:=by
  simp only[cA.jn,sD]
  refine ⟨Sd hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rY :
   0< ∑ u:Fin p→G,
    ((cA.cS A aL u).card:ℝ) *
     (cA.cS A a0 u).card:=by
  apply Finset.sum_pos'
  ·intro u hu
   positivity
  ·refine ⟨sD,Sz _, ?_⟩
   exact QM
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v8⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v9⟩))
 have Hh:0<N^p:=by
  rw[KJ] at rY
  have jt:0<(aL.card:ℝ)*a0.card:=by positivity
  rcases mul_pos_iff.mp rY with gy | eY
  ·simpa[N] using gy.2
  ·exact(Rd jt.le eY.1).elim
 have GV:0≤N:=by
  dsimp[N]
  exact tX
 have NH:N≠0:=by
  intro MS
  rw[MS] at Hh
  simp[xY] at Hh
 have Ms := SM GV (Ne.symm NH)
 unfold ah.bj
 have sF:(0:ℝ)<A.card:=by
  exact_mod_cast(Finset.card_pos.mpr ⟨a,ha⟩)
 dsimp[N] at Ms
 positivity
omit [DiscreteMeasurableSpace G] in
lemma ik
  (H:bU W)
  {A:Finset G} {p:ℕ} {sigma delta alpha:ℝ} (z:G)
  (data:ah.aW A
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma delta)
  (cu:delta<1)
  (b8:0≤alpha)
  (dS :
   alpha≤ah.bj A
    (z+ᵥ H.b6.carrier) H.bx.carrier p) :
  alpha/2 ≤
   (data.aX.card:ℝ) /
    (ah.aW.bg A
     (z+ᵥ H.b6.carrier) H.bx.carrier p sigma).card:=by
 let S :=
  ah.aW.bg A
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma
 have vi:S.Nonempty:=by
  simpa[S] using data.gL cu
 have DT:(0:ℝ)<S.card:=by exact_mod_cast vi.card_pos
 have yk :
   ((z+ᵥ H.b6.carrier).card:ℝ) =
    (H.b6.carrier.card:ℝ):=by
  simp
 have Mt :
   alpha*(H.b6.carrier.card:ℝ)≤(data.aX.card:ℝ):=by
  have aQ  :=

   dS.trans data.tC
  rw[yk] at aQ
  have Mu:(0:ℝ)<H.b6.carrier.card:=by
   exact_mod_cast H.b6.aE.card_pos
  exact(Qs Mu).mp aQ
 have Fw :
   S.card≤2*H.b6.carrier.card:=by
  calc
   _ ≤((z+ᵥ H.b6.carrier)-H.bx.carrier).card:=
          Qu
     (ah.aW.oX
      A (z+ᵥ H.b6.carrier) H.bx.carrier p sigma)
   _≤2*H.b6.carrier.card:=
    mL H.b6 H.zA
     H.bx.carrier H.xe H.xc z
 have EY:(S.card:ℝ)≤2*(H.b6.carrier.card:ℝ):=by
  exact_mod_cast Fw
 apply(Qs DT).2
 calc
  _ ≤
    alpha/2*(2*(H.b6.carrier.card:ℝ)):=
         iO EY (by positivity)
  _=alpha*(H.b6.carrier.card:ℝ):=by ring
  _≤(data.aX.card:ℝ):=Mt
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma oA
  {aX S:Finset G} {alpha:ℝ}
  (b8:0<alpha) (fY:aX.Nonempty) (hS:S.Nonempty)
  (eO:alpha/2≤(aX.card:ℝ)/S.card) :
  Real.sqrt ((S.card:ℝ)/aX.card)≤Real.sqrt (2/alpha):=by
 have xB:(0:ℝ)<aX.card:=by exact_mod_cast fY.card_pos
 have DT:(0:ℝ)<S.card:=by exact_mod_cast hS.card_pos
 have hmul:alpha/2*(S.card:ℝ)≤(aX.card:ℝ):=
  (Qs DT).mp eO
 have hdiv:(S.card:ℝ)/aX.card≤2/alpha:=by
  apply(Sy xB b8).2
  nlinarith
 exact Real.sqrt_le_sqrt hdiv
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma tQ
  (d:ℕ) {rank:ℕ} {aF:NNReal}
  {aX S:Finset G}
  (fY:aX.Nonempty) (hS:S.Nonempty)
  (eO :
   aa.aR d/2 ≤
    (aX.card:ℝ)/S.card)
  (d5 :
   (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
    1/2048) :
  2*aa.cH +
    (2/(aa.bE d:ℝ) +
     400*((max rank 1:ℕ):ℝ) *
      (aF+aF:NNReal) +
     2*(1/2:ℝ)^aa.b1 d) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤(1/512:ℝ):=by
 classical
 have fX:=aa.bP d
 have DE  :=

  oA fX fY hS eO
 have l7 :
   (2/(aa.bE d:ℝ)) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _
                                    ≤
    (2/(aa.bE d:ℝ)) *
     Real.sqrt (2/aa.aR d):=by
      gcongr
   _≤1/2048:=aa.m8 d
 have Cs :
   (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _

                                   ≤
    (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d):=by
     gcongr
   _≤1/2048:=d5
 have uX :
   (2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _
                                    ≤
    (2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt (2/aa.aR d):=by
      gcongr
   _≤1/2048:=aa.pA d
 unfold aa.cH
 nlinarith
def bD (d ax:ℕ):ℕ:=
 8388608*max ax 1 *
  2^(2+2*d*aa.bH d)
def ct (d ax:ℕ):NNReal:=
 ((bD d ax:ℕ):NNReal)⁻¹
lemma jF (d ax:ℕ) :
  0<bD d ax:=by
 unfold bD
 positivity
lemma rh
  (d ax rank:ℕ) (cK:rank≤ax) :
  (400*((max rank 1:ℕ):ℝ) *
    (ct d ax +
     ct d ax:NNReal)) *
   Real.sqrt (2/aa.aR d) ≤
   1/2048:=by
 let e:ℕ:=2+2*d*aa.bH d
 let P := bD d ax
 have Mv:(0:ℝ)<P:=by
  dsimp[P,bD,e]
  positivity
 have lF :=
  Sn 1 cK
 have DE  :=

  aa.jj
   (aa.bP d)
   (aa.dZ d)
 have hbound :
   (400*((max rank 1:ℕ):ℝ) *
     (ct d ax +
      ct d ax:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
   (400*((max rank 1:ℕ):ℝ) *
     (ct d ax +
      ct d ax:NNReal)) *
    (2/aa.aR d):=by
  gcongr
 apply hbound.trans
 unfold ct bD
  aa.aR
 change
  (400*((max rank 1:ℕ):ℝ) *
    (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
   (2/(1/(2:ℝ)^e))≤1/2048
 have NI:((max rank 1:ℕ):ℝ)≤ max ax 1:=by
  exact_mod_cast lF
 have Ie:(0:ℝ)<(2:ℝ)^e:=by positivity
 have Mw :
   (400*((max rank 1:ℕ):ℝ) *
     (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
    (2/(1/(2:ℝ)^e)) =
   1600*((max rank 1:ℕ):ℝ)*(2:ℝ)^e/P:=by
  field_simp
  ring
 rw[Mw]
 have hP :
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e =
    (P:ℝ):=by
  dsimp[P,bD]
  norm_cast
 rw[←hP]
 have si:(0:ℝ) <
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e:=by
  positivity
 apply(QF si).2
 calc
  _ ≤
    1600*((max ax 1:ℕ):ℝ)*(2:ℝ)^e:=by
   gcongr
  _≤(1/2048:ℝ) *
    ((8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e):=by
   have wS:(0:ℝ)<(max ax 1:ℕ):=by positivity
   nlinarith
lemma lK
  (d ax rank:ℕ) (cK:rank≤ax) :
  ct d ax+ct d ax ≤
   1/(100*(max rank 1:ℕ):NNReal):=by
 let e:ℕ:=2+2*d*aa.bH d
 let P:ℕ:=bD d ax
 have Mv:(0:ℝ)<P:=by
  dsimp[P,bD,e]
  positivity
 have tc:(0:ℝ)<100*(max rank 1:ℕ):=by positivity
 have lF:max rank 1≤ max ax 1:=
  Sn 1 cK
 have sC:2*(100*max rank 1)≤P:=by
  dsimp[P,bD]
  have hpow:1≤2^e:=Nat.one_le_pow _ _ (by omega)
  calc
   2*(100*max rank 1)≤200*max ax 1:=by
    omega
   _≤8388608*max ax 1*2^e:=by
    have qI:200≤8388608:=by norm_num
    calc
     200*max ax 1≤8388608*max ax 1:=
      QQ _ qI
     _≤8388608*max ax 1*2^e:=
      Q4 _ (by positivity)
 have uO :
   (2:ℝ)*(P:ℝ)⁻¹ ≤
    1/(100*(max rank 1:ℕ):ℝ):=by
  have NJ:(2:ℝ)*(100*(max rank 1:ℕ))≤P:=by
   exact_mod_cast sC
  field_simp
  linarith
 unfold ct
 change
  ((P:ℕ):NNReal)⁻¹ +((P:ℕ):NNReal)⁻¹ ≤
   1/(100*(max rank 1:ℕ):NNReal)
 have Ps :
   (2:NNReal)*((P:ℕ):NNReal)⁻¹ ≤
    1/(100*(max rank 1:ℕ):NNReal):=by
  exact_mod_cast uO
 simpa[R5] using Ps
omit [DiscreteMeasurableSpace G] in
lemma e6
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bx.carrier p)
  (hk:k≤aa.dC d) :
  ⌈8*(1+log (2 /
   b3 W H data k))⌉₊ ≤
   aa.au d:=by
 let alpha:=aa.aR d
 let K:=aa.dC d
 let DU:=ah.bj A aL H.bx.carrier p
 have fX:0<alpha:=by
  simpa[alpha] using aa.bP d
 have wF:alpha≤1:=by
  simpa[alpha] using aa.dZ d
 have xQ:0<DU:=fX.trans_le (by simpa[DU,alpha] using dS)
 have qm:0≤alpha/2:=by positivity
 have xR:alpha/2≤1:=by linarith
 have IN:(alpha/2)^K≤(alpha/2)^k:=by
  have hK:k+(K-k)=K:=Nat.add_sub_of_le hk
  calc
   (alpha/2)^K=(alpha/2)^(k+(K-k)):=by rw[hK]
   _=(alpha/2)^k*(alpha/2)^(K-k):=by rw[RL]
   _≤(alpha/2)^k*1:=by
    exact iO
     (Uy qm xR) (by positivity)
   _=(alpha/2)^k:=by ring
 have GW:(alpha/2)^k≤(DU/2)^k:=by
  apply Qp
  ·positivity
  ·simpa[DU,alpha] using(Qz dS (by norm_num))
 have DV :
   aa.gs alpha K≤b3 W H data k:=by
  unfold aa.gs b3
  exact Qz (IN.trans GW) (by norm_num)
 have NK:0<b3 W H data k:=by
  unfold b3
  positivity
 have Fx:0<aa.gs alpha K:=
  aa.zV fX
 have hdiv :
   2/b3 W H data k ≤
    2/aa.gs alpha K:=by
  exact Rb (by norm_num) Fx DV
 have ei :
   log (2/b3 W H data k) ≤
    log (2/aa.gs alpha K):=
  QG (by positivity) hdiv
 have y2 :
   8*(1+log (2/b3 W H data k)) ≤
    8*(1+log (2/aa.gs alpha K)):=by
  nlinarith
 apply Sj (S3 y2)
 unfold aa.au aa.rg
 exact le_max_right _ _
omit [DiscreteMeasurableSpace G] in
lemma gR
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bx.carrier p)
  (hk:k≤aa.dC d)
  (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   aa.au d:=by
 have xQ :
   0<ah.bj A aL H.bx.carrier p:=
  (aa.bP d).trans_le dS
 have hV:0<b3 W H data k:=by
  unfold b3
  positivity
 have oQ:= oz W H data cu k T hV hT
 have rJ :
   8*(1+log (2/b3 W H data k)) ≤
    (⌈8*(1+log (2/b3 W H data k))⌉₊:ℝ):=
  Rr _
 have cK:=e6 W H data d k dS hk
 have Fy :
   (⌈8*(1+log (2/b3 W H data k))⌉₊:ℝ) ≤
    aa.au d:=by
  exact_mod_cast cK
 exact oQ.trans (rJ.trans Fy)
omit [DiscreteMeasurableSpace G] in
lemma nb
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (d k ax:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bx.carrier p)
  (hk:k≤aa.dC d)
  (g6:H.bl.rank≤ax)
  (T:Finset G) (Delta:Finset (AddChar G ℂ))
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)))
  (dQ:(Delta.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  (aa.bE d *
    ag.a6
     (aI.bf H.bl T (1/2))) ^
    Delta.card*4^(H.bl.rank+Delta.card) ≤
   aa.dH ax
    (aa.au d)
    (aa.bE d *
     (⌈8*(aa.au d:ℝ)⌉₊+1)):=by
 let dim:=aI.bf H.bl T (1/2)
 have oQ:dim≤aa.au d:=by
  simpa[dim] using gR W H data cu d k
   dS hk T hT
 have Fz :
   ag.a6 dim ≤
    ⌈8*(aa.au d:ℝ)⌉₊+1:=by
  unfold ag.a6
  apply RZ
  apply S3
  have lF:max dim 0≤(aa.au d:ℝ):=
   max_le oQ (by positivity)
  have Af:2*pi≤(8:ℝ):=by
   nlinarith[Real.pi_lt_four]
  calc
   2*pi*max dim 0 ≤
     2*pi*aa.au d:=by
    gcongr
   _≤8*(aa.au d:ℝ):=by
    gcongr
 have hq:0<aa.bE d:=by
  unfold aa.bE
  exact aa.gV (aa.bP d)
 have GX :
   0<ag.a6 dim:=by
  unfold ag.a6
  positivity
 have hn :
   0<aa.bE d *
    ag.a6 dim:=
  QP hq GX
 have Hn :
   aa.bE d *
     ag.a6 dim ≤
    aa.bE d *
     (⌈8*(aa.au d:ℝ)⌉₊+1):=
  Qr _ Fz
 have xQ :
   0<ah.bj A aL H.bx.carrier p:=
  (aa.bP d).trans_le dS
 have hV:0<b3 W H data k:=by
  unfold b3
  positivity
 have DW:Delta.card≤aa.au d:=by
  apply(i5 W H data cu k T Delta
   hV hT dQ).trans
  exact e6 W H data d k dS hk
 simpa[aa.dH,dim] using
  aa.vE hn Hn g6 DW
lemma i6
  (A aL a0 K:Finset G) (d:ℕ)
  (hK:K.Nonempty)
  (c8:1/(2:ℝ)^d≤(A.card:ℝ)/K.card)
  (oS :
   (65/64:ℝ)*(K.card:ℝ)⁻¹ ≤
    an.aM
     (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
     ((al ((@mu (ℝ) _ _) A) (mu A)))
     (aa.bH d)) :
  aa.aR d ≤
   ah.bj A aL a0
    (aa.bH d):=by
 let r:=aa.bH d
 have hr:0<r:=by
  simpa[r] using aa.fU d
 have x6:(0:ℝ)<K.card:=by exact_mod_cast hK.card_pos
 have Bj:(0:ℝ)≤A.card:=by positivity
 have KK:0≤(A.card:ℝ)/K.card:=by positivity
 have AY :
   1/(2:ℝ)^d ≤
    (A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
  calc
   _ ≤(A.card:ℝ)/K.card:=c8
   _≤(65/64:ℝ)*((A.card:ℝ)/K.card):=by
    nlinarith
   _=(A.card:ℝ)*((65/64:ℝ)*(K.card:ℝ)⁻¹):=by
    field_simp
   _≤(A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r:=
    iO (by simpa[r] using oS) Bj
 have sy :
   aa.aR d =
    (4:ℝ)⁻¹ *(1/(2:ℝ)^d)^(2*r):=by
  unfold aa.aR
  unfold aa.av
  dsimp[r]
  simp only[R6, ←Te,RL,QU]
  field_simp
  have hpow :
    (1/2:ℝ) ^
      (d*aa.bH d*2) *
     (4:ℝ)^(d*aa.bH d)=1:=by
   rw[show d*aa.bH d*2 =
     2*(d*aa.bH d) by omega]
   rw[show(4:ℝ)=(2:ℝ)^2 by norm_num, ←QU]
   rw[R6,Te]
   field_simp
  norm_num[QU,RL] at hpow ⊢
  have Mx :
    (((1/2:ℝ)^d)^aa.bH d)^2 =
     (((1/2:ℝ)^d)^2) ^
      aa.bH d:=by
   conv_lhs =>
    rw[←QU, ←QU]
   conv_rhs =>
    rw[←QU, ←QU]
   congr 1
   simp[R8]
  rw[Mx] at hpow
  nlinarith
 rw[sy,mM A aL a0 hr]
 gcongr
lemma qT (d:ℕ) :
  ((1/8192:ℝ)⁻¹)*log (2/(1/8192:ℝ)) ≤
   aa.bH d:=by
 have My:log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 have ei:log (2/(1/8192:ℝ))≤14:=by
  rw[show(2/(1/8192:ℝ))=(2:ℝ)^14 by norm_num,
   QB]
  norm_num at My ⊢
  nlinarith
 have kB :
   ((1/8192:ℝ)⁻¹)*log (2/(1/8192:ℝ)) ≤
    (114688:ℝ):=by
  norm_num
  nlinarith
 apply kB.trans
 unfold aa.bH aa.dt
 rw[an.pF]
 norm_num[cP]
 have hd:1≤d+1:=by omega
 norm_num at hd ⊢
 nlinarith
lemma sQ :
  (1+(1/8:ℝ)/32) ≤
   (65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512):=by
 norm_num
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma rT
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (bZ:d1<1) :
  (1+(1/8:ℝ)/32) *
    (bB s C.ak C.aB aQ
     bZ).density ≤
   ((bB s C.ak C.aB aQ
     bZ).restriction.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.carrier.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
 let u:=bB s C.ak C.aB aQ bZ
 have x6:(0:ℝ)<C.ak.ba.carrier.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have c8 :
   u.density=(u.restriction.set.card:ℝ) /
    C.ak.ba.carrier.card:=by
  simp only[u,bB,ah.hQ]
  rw[ah.bk
   C.ak.aE]
  simp[ah.di,ah.bt.eo,
   C.eD]
 rw[show(bB s C.ak C.aB aQ
   bZ).density=u.density by rfl,
  show(bB s C.ak C.aB aQ
   bZ).restriction.set=u.restriction.set by rfl,
  c8]
 have kG:=sQ
 have hA:(0:ℝ)≤u.restriction.set.card:=by positivity
 calc
  _
                                                      ≤
   ((65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512)) *
     ((u.restriction.set.card:ℝ)/C.ak.ba.carrier.card):=by
   gcongr
  _=(u.restriction.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.carrier.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
   field_simp
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma nc
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (zZ:d1=(1/512:ℝ))
  (bZ:d1<1)
  {d:ℕ} (c3:1/(2:ℝ)^d≤ s.density) :
  1/(2:ℝ)^(d+1) ≤
   (bB s C.ak C.aB aQ
    bZ).density:=by
 let u:=bB s C.ak C.aB aQ bZ
 have wG:a5 s d1≤u.density:=by
  let x:=aO.cr aQ
  have hx:a5 s d1 ≤
    a9 s.restriction.set C.ak.carrier x:=by
   simpa[x,a5] using
    aO.c0 aQ
  simpa[u,bB,ah.hQ] using hx
 have iB :
   1/(2:ℝ)^(d+1) ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=by
  rw[RB]
  have hpow:(0:ℝ)≤(2:ℝ)^d:=by positivity
  field_simp
  nlinarith
 calc
  _ ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=iB
  _≤(1-(1/512:ℝ))*s.density:=by gcongr
  _=a5 s d1:=by simp[a5,zZ]
  _≤u.density:=wG
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma l2
  {original:Finset G} (s:ah.aA original)
  {d:ℕ} (c3:1/(2:ℝ)^d≤ s.density) :
  (2/3:ℝ)^aa.dt (d+1) ≤
   a5 s (1/512:ℝ):=by
 have dc:0≤(2/3:ℝ):=by norm_num
 have xR:(2/3:ℝ)≤1:=by norm_num
 have l9:aa.dt d ≤
   aa.dt (d+1):=by
  unfold aa.dt
  omega
 calc
  _ ≤
    (2/3:ℝ)^aa.dt d:=
         SJ dc xR l9
  _≤(1-(1/512:ℝ))*s.density:=by
   simpa[aa.dt] using
    n6 s c3
  _=a5 s (1/512:ℝ):=by
   simp[a5]
lemma nd
  {vj i9 alpha width:ℝ}
  (sF:0<vj) (yd:0< i9)
  (b8:0<alpha) (wF:alpha≤1)
  (lO:alpha*i9≤vj)
  (d5:width≤alpha/384) (wH:0≤width) :
  2*(vj⁻¹ *width)+i9⁻¹ *width ≤
   (1/64:ℝ)*i9⁻¹:=by
 have IP := QM b8 yd
 have PR:vj⁻¹ ≤(alpha*i9)⁻¹:=
  (RJ sF IP).2 lO
 have jx:vj⁻¹ *width≤ i9⁻¹ /384:=by
  calc
   _ ≤(alpha*i9)⁻¹ *width:=by gcongr
   _≤(alpha*i9)⁻¹ *(alpha/384):=by gcongr
   _=i9⁻¹ /384:=by
    field_simp
 have FA:width≤1/384:=by
  calc
   _ ≤alpha/384:=d5
   _≤1/384:=by gcongr
 have uh:i9⁻¹ *width≤ i9⁻¹ /384:=by
  simpa[Qw] using
   iO FA (by positivity:0≤ i9⁻¹)
 calc
  _ ≤
    2*(i9⁻¹ /384)+i9⁻¹ /384:=by gcongr
  _≤(1/64:ℝ)*i9⁻¹:=by
   have Ma:0≤ i9⁻¹:=by positivity
   nlinarith
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma uJ
  {original:Finset G} (s:ah.aA original)
  {d aq bn:ℕ}
  (C:c7 s.restriction.ba bn
   (ar.bd (d+1) aq))
  (aQ:ah.bV s C.ak C.aB (1/512:ℝ))
  (c3:1/(2:ℝ)^d≤ s.density)
  (cK:s.rank≤ar.ax (d+1) aq)
  (cE:0<aq) :
  2*(((cX s C.ak C.aB aQ).card:ℝ)⁻¹ *
    (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:NNReal)⁻¹ +
      (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ))) +
   (C.ak.ba.carrier.card:ℝ)⁻¹ *
    (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:NNReal)⁻¹ +
      (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ)) ≤
   (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹:=by
 let alpha:ℝ:=(1-(1/512:ℝ))*(1/(2:ℝ)^d)
 let width:ℝ:=
  200*((max C.ak.ba.rank 1:ℕ):ℝ) *
   (((ar.bd (d+1) aq:NNReal)⁻¹ +
    (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ)
 have u4:(cX s C.ak C.aB aQ).Nonempty:=
  ph s C.ak C.aB aQ (by norm_num)
 have Mz:(0:ℝ)<(cX s C.ak C.aB aQ).card:=by
  exact_mod_cast u4.card_pos
 have x6:(0:ℝ)<C.ak.ba.carrier.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have fX:0<alpha:=by unfold alpha; positivity
 have wF:alpha≤1:=by
  unfold alpha
  have c8:1/(2:ℝ)^d≤1:=by
   have hpow:(1:ℝ)≤(2:ℝ)^d:=RH (by norm_num)
   exact(QF (by positivity)).2 (by simpa using hpow)
  nlinarith
 have lG:alpha ≤
   a9 s.restriction.set C.ak.carrier
    (aO.cr aQ):=by
  calc
   alpha≤(1-(1/512:ℝ))*s.density:=by
    unfold alpha
    gcongr
   _=a5 s (1/512:ℝ):=by simp[a5]
   _≤a9 s.restriction.set C.ak.carrier
     (aO.cr aQ):=by
    simpa[a5] using aO.c0 aQ
 have lO:alpha*(C.ak.ba.carrier.card:ℝ) ≤
   (cX s C.ak C.aB aQ).card:=by
  rw[ah.bk
   C.ak.aE] at lG
  have MA:(0:ℝ)<C.ak.carrier.card:=by
   exact_mod_cast C.ak.aE.card_pos
  simpa[cX,C.eD] using
   (Qs MA).mp lG
 have wH:0≤width:=by unfold width; positivity
 have d5:width≤alpha/384:=by
  have lF:max C.ak.ba.rank 1 ≤
    ar.ax (d+1) aq:=by
   rw[C.rankOne]
   exact ar.i8 cE cK
  have Hl:(0:ℝ)<ar.bd (d+1) aq:=by
   exact_mod_cast ar.md cE
  have kT:(0:ℝ)<ar.ax (d+1) aq:=by
   exact_mod_cast ar.iH cE
  have MB:((max C.ak.ba.rank 1:ℕ):ℝ) ≤
    ar.ax (d+1) aq:=by exact_mod_cast lF
  have Pt:max (C.ak.ba.rank:ℝ) 1 ≤
    ar.ax (d+1) aq:=by
   simpa[Nat.cast_max] using MB
  unfold width alpha ar.bd
  simp only[NNReal.coe_add,SE,S9]
  push_cast
  change 200*max (C.ak.ba.rank:ℝ) 1 *
    ((76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹ +
     (76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹) ≤
   ((1-1/512)*(1/(2:ℝ)^d))/384
  field_simp
  have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
  have MC:(2:ℝ)^(d+1+1)=4*(2:ℝ)^d:=by
   rw[show d+1+1=d+2 by omega,RL]
   norm_num
   ring
  rw[MC]
  nlinarith
 convert nd Mz x6 fX wF
   lO d5 wH using 1
 norm_num
open ah in
lemma lL
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set aL
   H.bx.carrier p sigma delta)
  (hp:0<p)
  (hB:(aL∩H.bx.carrier).Nonempty)
  (cu:delta<1)
  (dv:ℝ) (sH:0<dv)
  (m:ℕ) (hm:m≠0)
  (aF:NNReal)
  (dy:aF+aF ≤
   1/(100*(max H.bl.rank 1:ℕ):NNReal))
  (dh:ℕ) (pX:0<dh)
  (bm aU:ℝ)
  (dV: ∀ (T:Finset G) (Delta:Finset (AddChar G ℂ)),
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*dv +
     (2/(dh:ℝ) +
      400*((max H.bl.rank 1:ℕ):ℝ) *
       (aF+aF:NNReal) +
      2*(1/2:ℝ)^m) *
     Real.sqrt
      (((ah.aW.bg
        s.restriction.set aL H.bx.carrier p sigma).card:ℝ) /
       data.aX.card)≤bm)
  {aq bq:ℕ}
  (g6:H.bl.rank≤ s.rank)
  (B5 :
   ⌈8*(1+log (2 /
    b3 W H data
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bx.carrier p sigma))
      data.aX dv m)))⌉₊≤aq)
  (DX: ∀ (T:Finset G) (Delta:Finset (AddChar G ℂ)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bx.carrier p sigma))
      data.aX dv m)/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set aL H.bx.carrier p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (dh*ag.a6
     (aI.bf H.bl T (1/2))) ^
     Delta.card *
    4^(H.bl.rank+Delta.card)≤bq)
  (pj:0<bq)
  (gM: ∀ (T:Finset G) (a8:NNReal) (fl:aj G)
    (_Delta:Finset (AddChar G ℂ)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bx.carrier p sigma))
      data.aX dv m)/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set aL H.bx.carrier p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   1/2≤a8 →
   fl=H.bl.ai (a8 *
    aI.cJ H.bl T (1/2)) →
   exp (-aU)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fl.ai aF).carrier.card:ℝ)) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    dR source aq pk bm,
    P.child.rank≤ s.rank+aq ∧
    exp (-aU)*(s.card:ℝ)≤P.child.carrier.card:=by
 obtain ⟨T,X,a8,fl,Delta,nk,ui,pT,dQ,
   gJ,lj,oU,GY⟩:=
  ej
   data cu dv sH m hm H.bl H.wA
   aF dy dh pX bm dV
 obtain ⟨GY⟩:=GY
 let vu:ℕ:=
  (dh*ag.a6
    (aI.bf H.bl T (1/2))) ^
    Delta.card *
   4^(H.bl.rank+Delta.card)
 let k :=
  ah.cm
   (-(ah.aW.bg
    s.restriction.set aL H.bx.carrier p sigma))
   data.aX dv m
 have zi :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)):=by
  simpa[k,du,cq,
   cI,gk] using nk
 have xQ  :=

  mN s.restriction.set aL
   H.bx.carrier hp hB s.restriction.nonempty
 have hV :
   0<b3 W H data k:=by
  unfold b3
  positivity
 have A7:Delta.card≤aq:=by
  apply(i5 W H data cu k T Delta
   hV zi dQ).trans
  simpa[k] using B5
 have KL:vu≤bq:=by
  simpa[vu] using DX T Delta zi dQ
 let P:=GY.mono A7 KL (le_refl bm)
 have Bk:P.child.rank≤ s.rank+aq:=by
  have nX:=P.rN
  calc
   _ ≤H.bl.rank+aq:=by
    simpa[P,oU,aj.f6] using nX
   _≤ s.rank+aq:=RZ g6 aq
 have GZ  :=

  gM T a8 fl Delta zi gJ oU
 have FB :
   ((fl.ai aF).carrier.card:ℝ) ≤
    (bq:ℝ)*(P.child.carrier.card:ℝ):=by
  have sC  :=

         P.nM
  exact_mod_cast sC
 have FC :
   (bq:ℝ) *
     (exp (-aU)*(s.card:ℝ)) ≤
    (bq:ℝ)*(P.child.carrier.card:ℝ):=by
  calc
   _
                                 =
     exp (-aU)*(s.card:ℝ)*bq:=by ring
   _≤((fl.ai aF).carrier.card:ℝ):=GZ
   _≤(bq:ℝ)*(P.child.carrier.card:ℝ):=FB
 have G0:(0:ℝ)<bq:=by exact_mod_cast pj
 have Bl  :=

  Uj FC G0
 exact ⟨fl,aF+aF,(fl.ai aF).carrier,
  bq,P,Bk,Bl⟩
lemma jG
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma delta)
  (hp:0<p)
  (hB:((z+ᵥ H.b6.carrier)∩H.bx.carrier).Nonempty)
  (cu:delta<1)
  (dS :
   aa.aR d ≤
    ah.bj s.restriction.set
     (z+ᵥ H.b6.carrier) H.bx.carrier p)
  (aF:NNReal)
  (dy:aF+aF ≤
   1/(100*(max H.bl.rank 1:ℕ):NNReal))
  (bm aU:ℝ)
  (vF:(1/512:ℝ)≤bm)
  (d5 :
   (400*((max H.bl.rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
     1/2048)
  {bq:ℕ}
  (g6:H.bl.rank≤ s.rank)
  (DX: ∀ (T:Finset G) (Delta:Finset (AddChar G ℂ)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set (z+ᵥ H.b6.carrier)
        H.bx.carrier p sigma))
      data.aX aa.cH
       (aa.b1 d))/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.carrier)
         H.bx.carrier p sigma))
       data.aX aa.cH
        (aa.b1 d))≤(T.card:ℝ)) →
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (aa.bE d *
     ag.a6
      (aI.bf H.bl T (1/2))) ^
     Delta.card *
    4^(H.bl.rank+Delta.card)≤bq)
  (pj:0<bq)
  (gM: ∀ (T:Finset G) (a8:NNReal) (fl:aj G)
    (_Delta:Finset (AddChar G ℂ)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set (z+ᵥ H.b6.carrier)
        H.bx.carrier p sigma))
      data.aX aa.cH
       (aa.b1 d))/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.carrier)
         H.bx.carrier p sigma))
       data.aX aa.cH
        (aa.b1 d))≤(T.card:ℝ)) →
   1/2≤a8 →
   fl=H.bl.ai (a8 *
    aI.cJ H.bl T (1/2)) →
   exp (-aU)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fl.ai aF).carrier.card:ℝ)) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    dR source (aa.au d)
     pk bm,
    P.child.rank≤ s.rank+aa.au d ∧
    exp (-aU)*(s.card:ℝ)≤P.child.carrier.card:=by
 let S :=
  ah.aW.bg s.restriction.set
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma
 let k :=
  ah.cm (-S) data.aX
   aa.cH
   (aa.b1 d)
 have fX:=aa.bP d
 have eO :
   aa.aR d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using
   ik H z data cu
    (aa.bP d).le dS
 have vk :
   0<aa.b1 d:=by
  unfold aa.b1
  exact aa.sN
   (aa.bP d)
   (aa.dZ d)
 have hk :
   k≤aa.dC d:=by
  dsimp[k]
  unfold aa.dC
  exact aa.ig
   (-S) data.aX fX
   (aa.i3 d) eO vk
 have dV :
   ∀ (T:Finset G) (Delta:Finset (AddChar G ℂ)),
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*aa.cH +
     (2/(aa.bE d:ℝ) +
      400*((max H.bl.rank 1:ℕ):ℝ) *
       (aF+aF:NNReal) +
      2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt
      (((ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.carrier)
        H.bx.carrier p sigma).card:ℝ) /
       data.aX.card)≤bm:=by
  intro T Delta dQ
  have gN:=data.lR cu
  have vi:S.Nonempty:=by
   simpa[S] using data.gL cu
  apply(tQ d gN.1 vi
   (by simpa[S] using eO) d5).trans
  exact vF
 apply lL s W H data hp hB cu
  aa.cH
  aa.nE
  (aa.b1 d) vk.ne'
  aF dy (aa.bE d)
  (by
   unfold aa.bE
   exact aa.gV fX)
  bm aU dV g6
 ·simpa[k,S] using
   e6 W H data d k dS hk
 ·exact DX
 ·exact pj
 ·exact gM
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mO
  (B:aj G) (source:Finset G) {a8:NNReal}
  (P:ℕ) (hP:0<P)
  (jM:((P:NNReal)⁻¹)≤a8)
  {mr d2 aU:ℝ} {bq:ℕ}
  (nI:0≤d2)
  (dc:mr≤d2*(B.carrier.card:ℝ))
  (gM:source=(B.ai a8).carrier)
  (oe :
   exp (-aU)*d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(bq:ℝ)≤1) :
  exp (-aU)*mr*(bq:ℝ) ≤
   (source.card:ℝ):=by
 classical
 have B6 :
   B.carrier.card≤(3*P)^B.rank*source.card:=by
  rw[gM]
  exact aa.f5
   B P hP jM
 have G1 :
   (B.carrier.card:ℝ) ≤
    (((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ):=by
  exact_mod_cast B6
 have KZ :
   mr≤d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ):=by
  calc
   mr≤d2*(B.carrier.card:ℝ):=dc
   _≤d2 *
     ((((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ)):=
    iO G1 nI
   _=d2*(((3*P)^B.rank:ℕ):ℝ) *
     (source.card:ℝ):=by ring
 calc
  _ ≤
    exp (-aU) *
     (d2*(((3*P)^B.rank:ℕ):ℝ) *
      (source.card:ℝ))*(bq:ℝ):=by
       gcongr
  _=(exp (-aU)*d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(bq:ℝ)) *
     (source.card:ℝ):=by ring
  _≤1*(source.card:ℝ):=
   Qi oe (by positivity)
  _=(source.card:ℝ):=by ring
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mP
  (H:bU W) (d ax:ℕ)
  (T:Finset G) (a8:NNReal) (fl:aj G)
  (jM:1/2≤a8)
  (oU:fl=H.bl.ai (a8 *
   aI.cJ H.bl T (1/2)))
  {mr d2 aU:ℝ} {bq:ℕ}
  (nI:0≤d2)
  (dc:mr≤d2*(H.bl.carrier.card:ℝ))
  (oe :
   exp (-aU)*d2 *
     (((3*aa.bA H.bl.rank
       (aI.dg H.bl T (1/2))
       (bD d ax))^H.bl.rank:ℕ):ℝ) *
      (bq:ℝ)≤1) :
  exp (-aU)*mr*(bq:ℝ) ≤
   ((fl.ai (ct d ax)).carrier.card:ℝ):=by
 classical
 let m:=bD d ax
 let P:=aa.bA H.bl.rank
  (aI.dg H.bl T (1/2)) m
 have hm:0< m:=by
  simpa[m] using jF d ax
 have hP:0<P:=by
  exact aa.kg hm
 have c3 :
   ((P:NNReal)⁻¹) ≤
    a8*aI.cJ H.bl T (1/2) *
     (m:NNReal)⁻¹:=by
  simpa[P] using
   aa.i4
    H.bl T (1/2) m hm a8 jM
 have G3 :
   (fl.ai (ct d ax)).carrier =
    (H.bl.ai
     (a8*aI.cJ H.bl T (1/2) *
      (m:NNReal)⁻¹)).carrier:=by
  rw[oU]
  simp[ct,m,aj.vo,
   Qx,Q6]
 apply mO
  (a8:=a8*aI.cJ H.bl T (1/2) *
  (m:NNReal)⁻¹)
  H.bl (fl.ai (ct d ax)).carrier P hP
 ·exact c3
 ·exact nI
 ·exact dc
 ·exact G3
 ·simpa[P,m] using oe
def jH (d:ℕ):ℕ:=
 aa.bE d *
  (⌈8*(aa.au d:ℝ)⌉₊+1)
def cB (d ax:ℕ):ℕ:=
 aa.dH ax
  (aa.au d) (jH d)
def bY (d ax:ℕ):ℕ:=
 aa.bA ax
  (aa.au d+1)
  (bD d ax)
lemma vG (d:ℕ):0<jH d:=by
 unfold jH
 have hq:0<aa.bE d:=by
  unfold aa.bE
  exact aa.gV (aa.bP d)
 positivity
lemma sR (d ax:ℕ) :
  0<cB d ax:=by
 unfold cB aa.dH
 have hn:=vG d
 positivity
omit [DiscreteMeasurableSpace G] in
lemma nJ
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bx.carrier p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bx.carrier p)
  (hk:k≤aa.dC d)
  (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.dg H.bl T (1/2) ≤
   aa.au d+1:=by
 unfold aI.dg
 apply RZ
 apply Nat.ceil_le.mpr
 exact gR W H data cu d k
  dS hk T hT
lemma il
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma delta)
  (hp:0<p)
  (hB:((z+ᵥ H.b6.carrier)∩H.bx.carrier).Nonempty)
  (cu:delta<1)
  (dS :
   aa.aR d ≤
    ah.bj s.restriction.set
     (z+ᵥ H.b6.carrier) H.bx.carrier p)
  (ax:ℕ)
  (B7:H.bl.rank≤ s.rank)
  (g6:H.bl.rank≤ax)
  {d2 c9:ℝ}
  (nI:0≤d2)
  (dc:(s.card:ℝ)≤d2*(H.bl.carrier.card:ℝ))
  (oe :
   exp (-c9)*d2 *
     (((3*bY d ax)^ax:ℕ):ℝ) *
      (cB d ax:ℝ)≤1) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    dR source (aa.au d)
     pk (1/512:ℝ),
    P.child.rank≤ s.rank+aa.au d ∧
    exp (-c9)*(s.card:ℝ)≤P.child.carrier.card:=by
 let S :=
  ah.aW.bg s.restriction.set
   (z+ᵥ H.b6.carrier) H.bx.carrier p sigma
 let k := ah.cm (-S) data.aX
  aa.cH (aa.b1 d)
 have fX:=aa.bP d
 have eO :
   aa.aR d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using ik H z data cu
   fX.le dS
 have vk:0<aa.b1 d:=by
  unfold aa.b1
  exact aa.sN fX
   (aa.dZ d)
 have hk:k≤aa.dC d:=by
  dsimp[k]
  unfold aa.dC
  exact aa.ig
   (-S) data.aX fX (aa.i3 d)
   eO vk
 apply jG s W H z data hp hB cu
  dS (ct d ax)
  (lK d ax H.bl.rank g6)
  (1/512:ℝ) c9 (SF)
  (rh d ax H.bl.rank g6)
  B7
 ·intro T Delta hT dQ
  simpa[cB,jH,k,S] using
   nb W H data cu d k ax
    dS hk g6 T Delta (by simpa[k,S] using hT) dQ
 ·exact sR d ax
 ·intro T a8 fl Delta hT gJ oU
  have pd  :=

   nJ W H data cu d k dS hk T
    (by simpa[k,S] using hT)
  have hP :
    aa.bA H.bl.rank
      (aI.dg H.bl T (1/2))
      (bD d ax) ≤
     bY d ax:=by
   unfold bY aa.bA
   have lF :=
    Sn 1 g6
   gcongr
  have hpow :
    (3*aa.bA H.bl.rank
      (aI.dg H.bl T (1/2))
      (bD d ax))^H.bl.rank ≤
     (3*bY d ax)^ax:=by
   calc
    _

                           ≤
     (3*bY d ax)^H.bl.rank:=by
      apply R4
      gcongr
    _≤(3*bY d ax)^ax:=by
     apply QR
     ·have IQ:0<bY d ax:=by
       unfold bY
       exact aa.kg
        (jF d ax)
      exact QP (by norm_num) IQ
     ·exact g6
  have xG :
    exp (-c9)*d2 *
     (((3*aa.bA H.bl.rank
       (aI.dg H.bl T (1/2))
       (bD d ax))^H.bl.rank:ℕ):ℝ) *
      (cB d ax:ℝ)≤1:=by
   apply Sj ?_ oe
   gcongr
  exact mP H d ax T a8 fl
   gJ oU nI dc xG
theorem gW
    {original : Finset G} (s : ah.aA original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta bm fx aU : ℝ}
    {aq r : ℕ}
    (eM : 0 < epsilon)
    (iX : 0 < sigma) (qU : sigma ≤ 1)
    (cu : 0 < delta) (wI : delta < 1)
    (hr : 0 < r) (Bm : Even r) (DY : 2 ≤ r)
    (Bn : sigma⁻¹ * log (2 / delta) ≤ r)
    (rU : 0 ≤ fx)
    (mC : fx ≤
      an.aM
        ((↑) ∘ aN.bh D E)
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) r)
    (DZ :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : ℝ) *
          (((1 - sigma) * fx) *
            (1 - delta - bm)))
    (pl :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        fx ≤
          (_root_.b0 r ((_root_.al (_root_.mu (z +ᵥ E)) (_root_.mu D))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set)))) →
        ∀ data : ah.aW s.restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : aj G) (dR : NNReal)
            (source : Finset G) (bq : ℕ),
            ∃ P : ah.cb data parent
              dR source aq bq bm,
              P.child.rank ≤ s.rank + aq ∧
              exp (-aU) * (s.card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : bu.aG original,
      br.dk (1 + epsilon / 32) aq aU
        s.restriction t.aV.restriction:= by
  obtain ⟨z, hz, um, rV⟩:=
    ah.lE hD hE
      s.restriction.nonempty hr rU mC
  let aL  :=  z +ᵥ E
  let a0  :=  D
  have hB : (aL ∩ a0).Nonempty:= by
    simpa [aL, a0] using um
  obtain ⟨data⟩:=
    ah.kM
      (A:= s.restriction.set) (p:= r) (epsilon:= sigma) (delta:= delta)
      aL a0 iX qU cu Bm DY Bn hB
      s.restriction.nonempty
  obtain ⟨parent, dR, source, bq, P, Bk, Bl⟩:=
    pl z hz (by simpa [aL, a0] using um)
      (by simpa [aL, a0] using rV)
      (by simpa [aL, a0] using data)
  have gN:= data.lR wI
  let S  :=
    ah.aW.bg
      s.restriction.set aL a0 r sigma
  have ft  :=

          ah.nn gN.1 gN.2
      (by
        simpa only [ah.ca]
          using data.np)
      (by simpa [S] using P.oY)
  have oZ  :=
    mul_nonneg (sub_nonneg.mpr qU) rU
  have sE : ∀ x ∈ S,
      (1 - sigma) * fx ≤
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x:= by
    intro x hx
    have xC : x ∈ _root_.s r sigma aL a0 s.restriction.set:= by
      have FD:= hx
      change x ∈ _root_.s r sigma aL a0 s.restriction.set ∩ (aL - a0) at FD
      exact (Finset.mem_inter.mp FD).1
    have FE :
        (1 - sigma) *
            (_root_.b0 r ((_root_.al (_root_.mu aL) (_root_.mu a0))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set)))) <
          ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x:=
      (I6.mp xC)
    exact (mul_le_mul_of_nonneg_left rV
      (sub_nonneg.mpr qU)).trans FE.le
  have rL : ∀ x, 0 ≤
      ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x:= by
    intro x
    exact dM cC cC x
  obtain ⟨x, hx⟩:=
    ah.jy
      P.child.aE gN.1 gN.2 s.restriction.nonempty
      oZ rL sE ft
      (show ((1 - sigma) * fx) * (1 - delta - bm) ≤
          ((1 - sigma) * fx) * (1 - delta - bm) from le_rfl)
  obtain ⟨child, yD, B8, vv⟩:=
    ah.bt.od P.child P.k6
  have FD :
      (1 + epsilon / 32) * s.density ≤
        a9 s.restriction.set child.carrier x:= by
    rw [vv]
    exact DZ.trans hx
  have gy : 0 < a9 s.restriction.set child.carrier x:=
    (mul_pos (by nlinarith [eM]) s.dI).trans_le FD
  let t:= ah.di s child x gy
  refine ⟨{ aV:= t, fS:= ?_, iK:= ?_ }, ?_⟩
  · simpa [t, ah.di, ah.bt.eo]
      using B8
  · simpa [t, ah.di, ah.bt.eo,
      yD] using P.k6
  · apply ah.fb s child x gy FD
    · simpa [yD] using Bk
    · simpa [vv] using Bl
lemma gq
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (bZ:d1<1)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {epsilon sigma delta bm fx eb
   c9:ℝ} {aq r:ℕ}
  (eM:0<epsilon)
  (iX:0<sigma) (qU:sigma≤1)
  (cu:0<delta) (wI:delta<1)
  (hr:0<r) (Bm:Even r) (DY:2≤r)
  (Bn:sigma⁻¹ *log (2/delta)≤r)
  (rU:0≤fx)
  (jx :
   exp (-eb)*(s.card:ℝ)≤C.ak.carrier.card)
  (mC:fx ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu ℝ _ _)
     (bB s C.ak C.aB aQ bZ).restriction.set) (mu (bB s C.ak C.aB aQ bZ).restriction.set)))
    r)
  (DZ :
   (1+epsilon/32) *
     (bB s C.ak C.aB aQ
      bZ).density ≤
    ((bB s C.ak C.aB aQ
      bZ).restriction.set.card:ℝ) *
     (((1-sigma)*fx) *
      (1-delta-bm)))
  (pl :
   ∀ (z:G),z∈D-E→((z+ᵥ E)∩D).Nonempty →
    fx ≤
     (b0 r ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu (ℝ) _ _)
       (bB s C.ak C.aB aQ
        bZ).restriction.set) (mu (bB s C.ak C.aB aQ
        bZ).restriction.set)))) →
    ∀ data:ah.aW
      (bB s C.ak C.aB aQ
       bZ).restriction.set
      (z+ᵥ E) D r sigma delta,
     ∃ (parent:aj G) (dR:NNReal)
      (source:Finset G) (bq:ℕ),
      ∃ P:ah.cb data parent
       dR source aq bq bm,
       P.child.rank ≤
        (bB s C.ak C.aB aQ
         bZ).rank+aq ∧
       exp (-c9) *
         ((bB s C.ak C.aB aQ
          bZ).card:ℝ)≤P.child.carrier.card) :
  ∃ t:bu.aG original,
   (1+epsilon/32)*a5 s d1≤t.density ∧
   t.rank≤ s.rank+aq ∧
   exp (-(eb+c9))*(s.card:ℝ) ≤
    (t.card:ℝ):=by
 let u:=bB s C.ak C.aB aQ bZ
 obtain ⟨t,ht⟩:=
  gW u hD hE eM
   iX qU cu wI hr Bm DY Bn rU
   (by simpa[u] using mC) (by simpa[u] using DZ)
   (by simpa[u] using pl)
 have wG:a5 s d1≤u.density:=by
  let x:=aO.cr aQ
  have hx:a5 s d1 ≤
    a9 s.restriction.set C.ak.carrier x:=by
   simpa[x,a5] using
    aO.c0 aQ
  simpa[u,bB,ah.hQ] using hx
 have IS :
   exp (-eb)*(s.card:ℝ)≤(u.card:ℝ):=by
  change exp (-eb)*(s.card:ℝ) ≤
   (C.ak.carrier.card:ℝ)
  exact jx
 refine ⟨t, ?_, ?_, ?_⟩
 ·exact(iO wG (by nlinarith)).trans ht.1
 ·have Bo:u.rank=s.rank:=by
   simpa[u,bB,ah.aA.rank,
    br.aY.rank,
    ah.di,ah.bt.eo]
    using C.rankOne
  rw[←Bo]
  exact ht.2.1
 ·calc
   _ =
     exp (-c9) *
      (exp (-eb)*(s.card:ℝ)):=by
    rw[show-(eb+c9) =
      -c9+ -eb by ring,R7]
    ring
   _≤exp (-c9)*(u.card:ℝ):=
    iO IS (Q1 _).le
   _≤(t.card:ℝ):=ht.2.2
end xP
section IT
def et (K:aj G) (A:Finset G):G→ℝ:=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.carrier) (mu A-mu K.carrier)
lemma nf
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (dy :
   (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
    1/(100*(max C.ak.ba.rank 1:ℕ):NNReal))
  (d5 :
   2*(((cX s C.ak C.aB aQ).card:ℝ)⁻¹ *
     (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
      (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
    (C.ak.ba.carrier.card:ℝ)⁻¹ *
     (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
      (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
    (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹) :
  |(aO.bb
     (cX s C.ak C.aB aQ)
     (jE s C.ak C.aB aQ) -
    (Fintype.card G:ℝ)/(#C.ak.carrier:ℝ)) -
    aw.pairing
     (et C.ak.ba
      (cX s C.ak C.aB aQ))
     (aO.a4
      (jE s C.ak C.aB aQ))| ≤
   ((Fintype.card G:ℝ)/(#C.ak.carrier:ℝ))/8:=by
 let alpha:=a5 s epsilon
 have b8 :=
  QM (sub_pos.mpr b2) s.dI
 have lG:alpha ≤
   a9 s.restriction.set C.ak.carrier
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.c0 aQ
 have o0:alpha ≤
   a9 s.restriction.set C.aB.carrier
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.ea aQ
 have hA :
   (cX s C.ak C.aB aQ).Nonempty:=by
  apply ah.bK
   C.ak.aE
  exact b8.trans_le lG
 have gO :
   (jE s C.ak C.aB aQ).Nonempty:=by
  apply ah.bK
   C.aB.aE
  exact b8.trans_le o0
 have lO :
   cX s C.ak C.aB aQ ⊆
    C.ak.ba.carrier:=by
  rw[←C.eD]
  exact ah.dz
   (B:=C.ak.ba) (a8:=C.ak.outer)
   (A:=s.restriction.set) (C:=C.ak.carrier)
   (x:=aO.cr aQ) (fun _ hz↦hz)
 have r2  :=

        ah.dz
   (B:=C.aB.ba) (a8:=C.aB.outer)
   (A:=s.restriction.set) (C:=C.aB.carrier)
   (x:=aO.cr aQ) (fun _ hz↦hz)
 have dV :
   aO.a4
     (jE s C.ak C.aB aQ) ⊆
    (C.ak.ba.ai
     ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).carrier:=
  (aO.qJ r2).trans C.kV
 have h:=
  pJ.e5
   C.ez dy hA lO gO dV d5
 simpa[et,C.eD] using h
lemma kj
    {original:Finset G}
    (s:bu.aG original)
    {bn bd:ℕ} (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {epsilon aU:ℝ} {aq p:ℕ}
    (kG:gj s.aV bn bd epsilon aU)
    (aQ:ah.bV s.aV
      (bF
        (aq:=aq) s eH fw C kG).ak
      (bF
        (aq:=aq) s eH fw C kG).aB epsilon)
    (b2:epsilon<1)
    (W:aj G) (u9:W.a1)
    (kz :
      W.carrier=aO.a4 C.aB.carrier)
    {eta:ℝ≥0} (fC:0<eta)
    (vh :
      4*eta≤1/(400*(max W.rank 1:ℕ):ℝ≥0))
    {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
    (gn:D⊆(W.ai eta).carrier)
    (lk:E⊆(W.ai eta).carrier)
    {aF:ℝ≥0}
    (Bp :
      aF=(bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)
    (dy :
      aF ≤
        1/(100*(max C.ak.ba.rank 1:ℕ):ℝ≥0))
    (kI :
      ∀ t,aN.bh D E t≠0 →
        t∈(C.ak.ba.ai aF).carrier)
    (d5 :
      2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (aF:ℝ))) +
        (C.ak.ba.carrier.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (aF:ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹)
    (jz :
      (2/3:ℝ)^p ≤
        aO.a5 s.aV epsilon)
    (mC :
      (1+(1/8:ℝ)/8) *
          (C.ak.ba.carrier.card:ℝ)⁻¹ ≤
          an.aM
            ((↑) ∘ aN.bh D E)
            ((al ((@mu (ℝ) _ _) (bu.a7 aQ)) (mu (bu.a7 aQ))))
            (an.cz (1/8:ℝ) p) →
        ∃ t:bu.aG original,
          (257/256:ℝ) *
              aO.a5 s.aV epsilon≤t.density ∧
          t.rank≤ s.rank+aq ∧
          exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)) :
    Nonempty
      (bu.eS (p:=p) s
        (bF
          (aq:=aq) s eH fw C kG) aQ):=by
  let P:=bF
    (aq:=aq) s eH fw C kG
  change ah.bV s.aV C.ak C.aB epsilon at aQ
  have mj :
      (bu.a7 aQ).Nonempty:=by
    simpa[bu.a7,cX] using
      ph s.aV C.ak C.aB aQ b2
  have IU :
      bu.a7 aQ⊆C.ak.ba.carrier:=by
    rw[←C.eD]
    simpa[bu.a7,cX] using
      qS s.aV C.ak C.aB aQ
  have ew :
      |(aO.bb
            (bu.a7 aQ)
            (bu.d3 aQ) -
          (Fintype.card G:ℝ)/(#C.ak.carrier:ℝ)) -
          aw.pairing
            (bu.et C.ak.ba
              (bu.a7 aQ))
            (aO.a4
              (bu.d3 aQ))| ≤
        ((Fintype.card G:ℝ)/(#C.ak.carrier:ℝ))/8:=by
    have IV :
        (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
          1/(100*(max C.ak.ba.rank 1:ℕ):NNReal):=by
      simpa[Bp] using dy
    have Bq :
        2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
            (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
              (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
          (C.ak.ba.carrier.card:ℝ)⁻¹ *
            (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
              (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
          (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹:=by
      simpa[Bp] using d5
    simpa[bu.a7,
      bu.d3,cX,jE,
      bu.et,et] using
      nf s.aV C aQ b2
        IV Bq
  exact ⟨{
    base:=C.ak.ba
    weight:=W
    wj:=C.ez
    uy:=u9
    wk:=by
      change C.ak.ba.carrier=C.ak.carrier
      exact C.eD.symm
    uA:=kz
    rt:=mj
    th:=IU
    eta:=eta
    uB:=fC
    mI:=vh
    D:=D
    E:=E
    yt:=hD
    yu:=hE
    rZ:=gn
    r0:=lk
    aF:=aF
    yv:=dy
    ru:=kI
    uC:=d5
    vr:=jz
    e7:=ew
    qN:=mC }⟩
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma iE
    {original:Finset G}
    (s:bu.aG original)
    {d ax bn bd:ℕ}
    (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {eb c9:ℝ}
    (kG:gj s.aV bn bd (1/512:ℝ)
      (eb+c9))
    (jx :
      exp (-eb)*(s.card:ℝ)≤C.ak.carrier.card)
    (aQ:ah.bV s.aV
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kG).ak
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kG).aB (1/512:ℝ))
    (c3:1/(2:ℝ)^d≤ s.density)
    (W:aj G) (u9:W.a1)
    (kz:W.carrier=aO.a4 C.aB.carrier)
    (wE:W.carrier.card=C.aB.carrier.card)
    (yE:W.rank=s.rank)
    (H:bU W)
    (jI:s.rank≤ax)
    (dy :
      (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
        1/(100*(max C.ak.ba.rank 1:ℕ):NNReal))
    (d5 :
      2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
        (C.ak.ba.carrier.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹)
    (sS :
      exp (-c9) *
          ((bI s.aV.restriction.ba bn bd *
            b7 W:ℕ):ℝ) *
          (((3*bY (d+1) ax)^ax:ℕ):ℝ) *
            (cB (d+1) ax:ℝ)≤1) :
    Nonempty (bu.eS
      (p:=aa.dt (d+1)) s
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kG) aQ):=by
  change ah.bV s.aV C.ak C.aB
    (1/512:ℝ) at aQ
  let u:=bB s.aV C.ak C.aB aQ (by norm_num)
  have uI:=mn W H
  have xg := uI.2.2.trans yE
  have Br:H.bl.rank≤ax:=by rw[xg]; exact jI
  have Bo:u.rank=s.rank:=by
    simpa[u,bB,ah.aA.rank,
      bu.aG.rank,
      br.aY.rank,
      ah.di,ah.bt.eo]
      using C.rankOne
  have D0:H.bl.rank≤u.rank:=by
    rw[xg,Bo]
  have N3:1/(2:ℝ)^(d+1)≤u.density:=by
    simpa[u] using nc s.aV C aQ rfl
      (by norm_num) c3
  have dc:(u.card:ℝ) ≤
      ((bI s.aV.restriction.ba bn bd *
          b7 W:ℕ):ℝ)*(H.bl.carrier.card:ℝ):=by
    simpa[u] using mq s.aV eH C aQ
      (by norm_num) s.fS W H wE
  have pl :
      ∀ (z:G),z∈H.bx.carrier-H.b6.carrier →
        ((z+ᵥ H.b6.carrier)∩H.bx.carrier).Nonempty →
        (65/64:ℝ)*(C.ak.ba.carrier.card:ℝ)⁻¹ ≤
          (b0 (aa.bH (d+1)) ((al (mu (z+ᵥ H.b6.carrier)) (mu H.bx.carrier))) ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))) →
        ∀ data:ah.aW u.restriction.set
            (z+ᵥ H.b6.carrier) H.bx.carrier
            (aa.bH (d+1))
            (1/8192:ℝ) (1/8192:ℝ),
          ∃ (parent:aj G) (dR:NNReal)
            (source:Finset G) (bq:ℕ),
            ∃ P:ah.cb data parent
              dR source (aa.au (d+1))
              bq (1/512:ℝ),
              P.child.rank≤u.rank+aa.au (d+1) ∧
              exp (-c9)*(u.card:ℝ)≤P.child.carrier.card:=by
    intro z hz um rV data
    have B9 :
        (65/64:ℝ)*(C.ak.ba.carrier.card:ℝ)⁻¹ ≤
          an.aM
            ((NNReal.toReal ∘ ((al (mu (z+ᵥ H.b6.carrier)) (mu H.bx.carrier)))):G→ℝ)
            ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))
            (aa.bH (d+1)):=by
      rw[aN.dN
        ((al (mu (z+ᵥ H.b6.carrier)) (mu H.bx.carrier)))
        ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))
        (aa.fU (d+1))]
      exact rV
    have b8  :=

      i6
        u.restriction.set (z+ᵥ H.b6.carrier) H.bx.carrier
        C.ak.ba.carrier (d+1)
        C.ak.ba.aE
        (by
          have c8 :
              u.density=(u.restriction.set.card:ℝ) /
                C.ak.ba.carrier.card:=by
            simp only[u,bB,ah.hQ]
            rw[ah.bk
              C.ak.aE]
            simp[ah.di,ah.bt.eo,
              C.eD]
          rwa[←c8]) B9
    exact il u W H z data
      (aa.fU (d+1)) um (by norm_num)
      b8 ax D0 Br (by positivity) dc sS
  apply kj s eH fw C kG aQ
    (by norm_num) W u9 kz H.uB H.mI
    H.bx.aE H.b6.aE H.r0 H.rZ
    (show(bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ =
      (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ from rfl)
    dy
    (ld s.aV C W H kz)
    d5 (l2 s.aV c3)
  intro mC
  obtain ⟨t,zG,KM,KN⟩:=
    gq
      s.aV C aQ (by norm_num) H.bx.aE
      H.b6.aE (epsilon:=(1/8:ℝ))
      (sigma:=(1/8192:ℝ)) (delta:=(1/8192:ℝ))
      (bm:=(1/512:ℝ))
      (fx:=(65/64:ℝ) *
        (C.ak.ba.carrier.card:ℝ)⁻¹)
      (eb:=eb) (c9:=c9)
      (aq:=aa.au (d+1))
      (r:=aa.bH (d+1))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (aa.fU (d+1))
      (aa.nF (d+1))
      (by
        have gy:=aa.fU (d+1)
        have mx:=aa.nF (d+1)
        rcases mx with ⟨k,hk⟩
        omega)
      (qT (d+1)) (by positivity) jx
      (by
        norm_num at mC ⊢
        simpa[u,aa.bH,
          bu.a7,cX,
          bF] using mC)
      (rT s.aV C aQ (by norm_num))
      (by simpa[u] using pl)
  exact ⟨t,by norm_num at zG ⊢; exact zG,KM,by
    simpa[bu.aG.card,
      RV,add_left_comm,add_assoc] using KN⟩
def fo:ℝ:=
 4096*(aa.cW:ℝ)
lemma iL
  (d rank d4:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1)))
  (pd:d4≤8*aa.au (d+1)) :
  log (aa.cv (d+1) rank d4:ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have ei:=aa.jX
  (d+1) rank d4 cK pd
 have dc:((d+1+1:ℕ):ℝ)≤2*((d+1:ℕ):ℝ):=by
  push_cast
  nlinarith
 have hpow:((d+1+1:ℕ):ℝ)^11 ≤
   (2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by
  calc
   _ ≤
     (2*((d+1:ℕ):ℝ))^11:=
    Qp (by positivity) dc 11
   _=(2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by rw[QL]
 calc
  _ ≤
    (aa.cW:ℝ) *
     ((d+1+1:ℕ):ℝ)^11:=by simpa using ei
  _≤(aa.cW:ℝ) *
    ((2:ℝ)^11*((d+1:ℕ):ℝ)^11):=by gcongr
  _=2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by norm_num; ring
lemma f3
  (d rank:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1))) :
  log (aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let d4:=aa.au (d+1)+1
 have pd:d4≤8*aa.au (d+1):=by
  dsimp[d4]
  have gy:=aa.bX (d+1)
  omega
 have KO:=iL d rank d4 cK pd
 have uG:(0:ℝ)<aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):=by
  exact_mod_cast QP
   (aa.ck
    (ar.mc (aa.bX (d+1))))
   (aa.ck
    (ar.md (aa.bX (d+1))))
 have hle:aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))) ≤
   aa.cv (d+1) rank d4:=by
  unfold aa.cv
  rw[show
   aa.bT rank
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     aa.bR rank *
     (3*aa.bA rank d4
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^rank *
     aa.cL (d+1) =
    aa.bT rank
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     (aa.bR rank *
     (3*aa.bA rank d4
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^rank *
     aa.cL (d+1)) by ring]
  apply Q4
  have j8:0<aa.bR rank:=by
   unfold aa.bR
    aa.bG
   positivity
  have gM:0 <
    (3*aa.bA rank d4
     (aa.cd (d+1)
      (ar.ax (d+1)
       (aa.au (d+1)))))^rank:=by
   unfold aa.bA aa.cd
   positivity
  have lP:0<aa.cL (d+1):=by
   unfold aa.cL aa.dH
   have hq:0<aa.bE (d+1):=by
    unfold aa.bE
    exact aa.gV
     (aa.bP (d+1))
   positivity
  exact QP (QP j8 gM) lP
 exact(QG uG (by exact_mod_cast hle)).trans KO
lemma gE
  (d rank:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1))) :
  log (aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have vc:=f3 d rank cK
 have IW:(0:ℝ)<aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))):=by
  exact_mod_cast aa.ck
   (ar.mc (aa.bX (d+1)))
 have hle:aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))) ≤
   aa.bT rank
    (ar.bn (d+1) (aa.au (d+1)))
    (ar.bd (d+1) (aa.au (d+1))):=by
  unfold aa.bT
  apply Q4
  exact aa.ck
   (ar.md (aa.bX (d+1)))
 exact(QG IW (by exact_mod_cast hle)).trans vc
lemma sT :
    ∃ K:ℝ,0<K∧bu.jZ K:=by
  refine ⟨fo, ?_, ?_⟩
  · unfold fo
    unfold aa.cW
      aa.aH
      aa.eW
    positivity
  · intro N A hA d hd
    let e:ℕ:=d+1
    let aq:ℕ:=aa.au e
    let p:ℕ:=aa.dt e
    refine ⟨aq,p, ?_, ?_⟩
    · dsimp[p]
      exact aa.ml e
    · intro n hn s c3 cK
      let ax:ℕ:=ar.ax e aq
      let bn:ℕ:=ar.bn e aq
      let bd:ℕ:=ar.bd e aq
      let eN:ℝ:=
        2048*(aa.cW:ℝ) *
          ((d+1:ℕ):ℝ)^11
      have cE:0<aq:=by
        dsimp[aq]
        exact aa.bX e
      have jI:s.rank≤ax:=by
        dsimp[ax,e,aq]
        unfold ar.ax
        have Kn:n≤1024*(d+1+1):=by omega
        exact Sj cK (QQ _ Kn)
      have eH:0<bn:=by
        dsimp[bn]
        exact ar.mc cE
      have fw:0<bd:=by
        dsimp[bd]
        exact ar.md cE
      have IX:1/(2:ℝ)^e≤ s.density:=by
        calc
          1/(2:ℝ)^e≤1/(2:ℝ)^d:=by
            dsimp[e]
            rw[RB]
            have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
            field_simp
            nlinarith
          _≤ s.density:=c3
      have kG:gj s.aV bn bd (1/512:ℝ)
          (fo*((d+1:ℕ):ℝ)^11):=by
        refine
          { Be:=s.fS
            iK:=s.iK
            yB:= ?_
            vt:= ?_
            tk:= ?_
            tl:= ?_ }
        · dsimp[bn]
          exact ar.tI cE jI
        · dsimp[bn]
          exact ar.wd cE jI IX
        · have mK :
              (0:ℝ) <
                (b9 s.aV.restriction.ba bn:ℕ):=by
            unfold b9
            positivity
          apply jk s.aV s.fS mK
          have ei:=gE d s.rank jI
          apply ei.trans
          unfold fo
          gcongr
          norm_num
        · have mK :
              (0:ℝ) <
                (bI s.aV.restriction.ba bn bd:ℕ):=by
            unfold bI b9
            positivity
          apply jk s.aV s.fS mK
          have ei:=f3 d s.rank jI
          apply ei.trans
          unfold fo
          gcongr
          norm_num
      have xL:((bd:NNReal)⁻¹)≤1:=by
        apply(inv_le_one₀ (by exact_mod_cast fw)).2
        exact_mod_cast(show 1≤bd by omega)
      let C:c7 s.aV.restriction.ba bn bd:=
        Classical.choice (rR s.aV.restriction.ba
          bn bd eH fw xL)
      have yr :
          eN+eN =
            fo*((d+1:ℕ):ℝ)^11:=by
        dsimp[eN,fo]
        ring
      have Bs :
          gj s.aV bn bd (1/512:ℝ)
            (eN+eN):=by
        rw[yr]
        exact kG
      rw[←yr]
      let P:bu.dB s (1/512:ℝ)
          (eN+eN) aq:=
        bF
          (aq:=aq) s eH fw C Bs
      refine ⟨P, ?_⟩
      intro aQ
      have Bt :
          exp (-eN)*(s.aV.card:ℝ) ≤
            ((b9 s.aV.restriction.ba bn:ℕ):ℝ)⁻¹ *
              (s.aV.restriction.ba.carrier.card:ℝ):=by
        have mK :
            (0:ℝ) <
              (b9 s.aV.restriction.ba bn:ℕ):=by
          unfold b9
          positivity
        apply jk s.aV s.fS mK
        simpa[eN,b9,
          aa.bG,bn,e,aq,
          bu.aG.rank,
          ah.aA.rank,
          br.aY.rank] using
          (gE d s.rank jI)
      have jx :
          exp (-eN)*(s.card:ℝ)≤C.ak.carrier.card:=by
        have mK :
            (0:ℝ) <
              (b9 s.aV.restriction.ba bn:ℕ):=by
          unfold b9
          positivity
        have GK :
            (s.aV.restriction.ba.carrier.card:ℝ) ≤
              (b9 s.aV.restriction.ba bn:ℝ) *
                (C.ak.carrier.card:ℝ):=by
          exact_mod_cast C.mE
        simpa[bu.aG.card] using
          mm s.aV mK Bt GK
      let:NeZero (aD N):=⟨by simp[aD]⟩
      have A4:Odd (aD N):=by
        exact ⟨N,by simp[aD,R5]⟩
      let W:aj (ZMod (aD N)):=
        aO.hY (aD N) A4 C.aB.ba
      have u9:W.a1:=by
        dsimp[W]
        exact qR A4 C.aB.ba
          C.fe
      have kz :
          W.carrier=aO.a4 C.aB.carrier:=by
        rw[C.n5]
        dsimp[W]
        exact
          (aO.jQ
            A4 C.aB.ba).symm
      have wE:W.carrier.card=C.aB.carrier.card:=by
        dsimp[W]
        rw[aO.p7]
        exact QA Finset.card C.n5.symm
      have yE:W.rank=s.rank:=by
        dsimp[W]
        rw[aO.u8,C.p5]
        rfl
      let H:bU W:=
        Classical.choice (rS W)
      have dy :
          (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
            1/(100*(max C.ak.ba.rank 1:ℕ):NNReal):=by
        rw[C.rankOne]
        simpa[bd,e,aq,
          bu.aG.rank,
          ah.aA.rank,
          br.aY.rank] using
          (ar.rb cE jI)
      have d5 :
          2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
              (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
                (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
            (C.ak.ba.carrier.card:ℝ)⁻¹ *
              (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
                (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
            (1/8:ℝ)/8*(C.ak.ba.carrier.card:ℝ)⁻¹:=by
        simpa[bd,e,aq] using
          (uJ s.aV C aQ c3 jI cE)
      let d4:ℕ:=aq+1
      have pd:d4≤8*aa.au e:=by
        dsimp[d4,aq]
        have gy:=aa.bX e
        omega
      have FF :
          0<aa.cv e ax d4:=by
        have KP:0<ar.bn e
            (aa.au e):=
          ar.mc (aa.bX e)
        have KQ:0<ar.bd e
            (aa.au e):=
          ar.md (aa.bX e)
        have hq:0<aa.bE e:=by
          unfold aa.bE
          exact aa.gV
            (aa.bP e)
        have vc:0<aa.bT ax
            (ar.bn e (aa.au e))
            (ar.bd e (aa.au e)):=by
          unfold aa.bT
          exact QP
            (aa.ck KP)
            (aa.ck KQ)
        have j8 :
            0<aa.bR ax:=by
          unfold aa.bR
            aa.bG
          positivity
        have gM :
            0<(3*aa.bA ax d4
              (aa.cd e
                (ar.ax e
                  (aa.au e))))^ax:=by
          unfold aa.bA
            aa.cd
          positivity
        have lP:0<aa.cL e:=by
          unfold aa.cL
            aa.dH
          positivity
        unfold aa.cv
        exact QP (QP (QP vc j8) gM) lP
      have Bu :
          exp (-eN) *
              (aa.cv e ax d4:ℝ) ≤
            1:=by
        apply oy FF
        simpa[eN,e] using
          (iL d ax d4 (SF) pd)
      have FH :
          (bI s.aV.restriction.ba bn bd *
              b7 W) *
              (3*bY e ax)^ax *
              cB e ax ≤
            aa.cv e ax d4:=by
        have zH :
            s.aV.restriction.ba.rank≤ax:=by
          simpa[bu.aG.rank,
            ah.aA.rank,
            br.aY.rank] using jI
        have xh {m:ℕ} (hm:0< m) :
            b9 s.aV.restriction.ba m ≤
              aa.bG ax m:=by
          unfold b9 aa.bG
          exact Ra
            (QR (by omega) zH)
            (QR (by norm_num) zH)
        have vc :
            bI s.aV.restriction.ba bn bd ≤
              aa.bT ax bn bd:=by
          unfold bI aa.bT
          exact Ra (xh eH) (xh fw)
        have lF:max s.rank 1≤ max ax 1:=
          Sn 1 jI
        have ri (c:ℕ) (hc:0<c) :
            (3*(c*max s.rank 1))^s.rank*4^s.rank ≤
              aa.bG ax
                (c*max ax 1):=by
          unfold aa.bG
          have dc :
              3*(c*max s.rank 1)≤3*(c*max ax 1):=by
            gcongr
          have xE:0<3*(c*max ax 1):=by positivity
          have jx :
              (3*(c*max s.rank 1))^s.rank ≤
                (3*(c*max ax 1))^ax:=by
            calc
              (3*(c*max s.rank 1))^s.rank ≤
                  (3*(c*max ax 1))^s.rank:=
                R4 dc _
              _≤(3*(c*max ax 1))^ax:=
                QR xE jI
          exact Ra jx
            (QR (by norm_num) jI)
        have j8 :
            b7 W ≤
              aa.bR ax:=by
          unfold b7
            aa.bR
          rw[yE]
          exact Ra
            (Ra (ri 1600 (by norm_num))
              (ri 200 (by norm_num)))
            (ri 200 (by norm_num))
        have gM :
            (3*bY e ax)^ax =
              (3*aa.bA ax d4
                (aa.cd e
                  (ar.ax e
                    (aa.au e))))^ax:=by
          unfold bY bD
            aa.bA
            aa.cd
            aa.av
          dsimp[ax,aq,d4]
        have lP :
            cB e ax =
              aa.cL e:=by
          unfold cB jH
            aa.cL
          rw[aa.pc]
        unfold aa.cv
        rw[←gM, ←lP]
        dsimp[bn,bd,aq]
        exact Ra
          (Ra (Ra vc j8) (SF))
          (SF)
      have sS :
          exp (-eN) *
              ((bI s.aV.restriction.ba bn bd *
                b7 W:ℕ):ℝ) *
              (((3*bY e ax)^ax:ℕ):ℝ) *
                (cB e ax:ℝ)≤1:=by
        calc
          exp (-eN) *
              ((bI s.aV.restriction.ba bn bd *
                b7 W:ℕ):ℝ) *
              (((3*bY e ax)^ax:ℕ):ℝ) *
                (cB e ax:ℝ) ≤
              exp (-eN) *
                (aa.cv e ax d4:ℝ):=by
                  have yF :
                      ((bI s.aV.restriction.ba bn bd *
                        b7 W) *
                        (3*bY e ax)^ax *
                        cB e ax:ℝ) ≤
                        (aa.cv
                          e ax d4:ℝ):=by
                    exact_mod_cast FH
                  push_cast at yF ⊢
                  calc
                    exp (-eN) *
                        ((bI s.aV.restriction.ba bn bd:ℝ) *
                          b7 W) *
                        (3*bY e ax:ℝ)^ax *
                          cB e ax =
                        exp (-eN) *
                          (((bI s.aV.restriction.ba bn bd:ℝ) *
                            b7 W) *
                            (3*bY e ax:ℝ)^ax *
                              cB e ax):=by ring
                    _≤exp (-eN) *
                        (aa.cv e ax d4:ℝ):=
                      iO yF (Q1 _).le
          _≤1:=Bu
      simpa[p,e] using
        (iE
          (d:=d) (ax:=ax) (bn:=bn) (bd:=bd)
          s eH fw C Bs jx aQ c3 W u9
          kz wE yE H jI dy d5 sS)
end IT
end
end ay.uH
end
section
open Filter
open scoped Topology
namespace ay
lemma lf
  {K:ℝ} (hK:0<K) (nX:bu.jZ K)
  (C:ℝ) :
  (fun N:ℕ=>(r3 N:ℝ))=O[atTop]
   (fun N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 obtain ⟨K',nO,qG⟩:=
  i2
   ⟨8+2050*(2:ℝ)^12*K,
    bu.lb hK nX⟩
 exact m4 qG C
lemma l3
  (nX: ∃ K:ℝ,0<K∧bu.jZ K)
  (C:ℝ) (_hC:0<C) :
  (fun N:ℕ=>(r3 N:ℝ))=O[atTop]
   (fun N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 obtain ⟨K,hK,MD⟩:=nX
 exact lf hK MD C
lemma FI (C:ℝ) (hC:0<C) :
  (fun N:ℕ=>(r3 N:ℝ))=O[atTop]
   (fun N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=
       l3
  uH.sT C hC
end ay
end
section
open Filter Real Asymptotics
namespace Erdos142KM
lemma z0 (N:ℕ):Erdos142.r 3 N=ay.r3 N:=
 w1.r4 N
lemma logSquare : ∀ᶠ N:ℕ in atTop,
  (Erdos142.r 3 N:ℝ)≤(N:ℝ)/log (N:ℝ)^((1:ℝ)+1):=by
 obtain ⟨K,hK⟩:=(ay.FI 3 (by norm_num)).bound
 have ei:Tendsto (fun N:ℕ=>log (N:ℝ)) atTop atTop:=
  tendsto_log_atTop.comp Sa
 filter_upwards[hK,ei.eventually (eventually_ge_atTop (max K 1))] with N hN hL
 have Pu:(1:ℝ)≤log (N:ℝ):=Sj (le_max_right _ _) hL
 have Pv:K≤log (N:ℝ):=Sj (Tu _ _) hL
 have ME:0<log (N:ℝ):=SI U1 Pu
 have PX:(0:ℝ)≤N:=Q5 N
 have hq:0≤(N:ℝ)/log (N:ℝ)^(3:ℝ):=by positivity
 rw[RA (Q5 _),RA hq] at hN
 rw[z0]
 have e3:log (N:ℝ)^(3:ℝ)=log (N:ℝ)^((1:ℝ)+1)*log (N:ℝ):=by
  rw[←Real.rpow_add_one ME.ne']
  norm_num
 calc (ay.r3 N:ℝ)≤K*((N:ℝ)/log (N:ℝ)^(3:ℝ)):=hN
  _≤log (N:ℝ)*((N:ℝ)/log (N:ℝ)^(3:ℝ)):=
    Qi Pv hq
  _=(N:ℝ)/log (N:ℝ)^((1:ℝ)+1):=by
    rw[e3]
    have:0<log (N:ℝ)^((1:ℝ)+1):=by positivity
    field_simp
end Erdos142KM
end

open Erdos142 Filter Real
open OMA.R_Erdos142_erdos_142_variants_lower_R3

namespace WindowEstimate

lemma reciprocal_window_le {k n : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hw : ∀ x ∈ S, ∃ j ∈ Finset.Ico n (2*n), 4*4^j < x ∧ x ≤ 5*4^j)
    (hf : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ n * ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
  let B (j : ℕ) := (Finset.Icc 1 (4^j)).filter (fun b => 4*4^j+b ∈ S)
  have sub j : B j ⊆ Finset.Icc 1 (4^j) := Finset.filter_subset _ _
  let block j := (B j).map (addLeftEmbedding (4*4^j))
  have cover : S ⊆ (Finset.Ico n (2*n)).biUnion block := by
    intro x hx
    obtain ⟨j, hj, hl, hu⟩ := hw x hx
    refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_map.mpr ⟨x-4*4^j, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa [Nat.add_sub_of_le hl.le] using hx⟩
    · change 4*4^j+(x-4*4^j) = x
      omega
  have size j : (B j).card ≤ r k (4^j) := by
    apply card_le_r (sub j) ((apFree_iff hk).mpr ?_)
    rintro ⟨a, d, hd, h⟩
    exact hf ⟨4*4^j+a, d, hd, fun i hi => by simpa [Nat.add_assoc] using (Finset.mem_filter.mp (h i hi)).2⟩
  calc
    _ ≤ ∑ x ∈ (Finset.Ico n (2*n)).biUnion block, (x : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg cover (by intros; positivity)
    _ = _ := Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint _ B sub)
    _ ≤ ∑ _j ∈ Finset.Ico n (2*n), ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _x ∈ block j, (4 * (4:ℝ)^j)⁻¹ := by
          apply Finset.sum_le_sum
          intro x hx
          apply inv_anti₀ (by positivity)
          exact_mod_cast (mem_shiftBlock_bounds (sub j) hx).1.le
        _ = (B j).card / (4:ℝ)^j / 4 := by simp [block, div_eq_mul_inv]; ring
        _ ≤ (r k (4^j) : ℝ) / (4:ℝ)^j / 4 := by gcongr; exact_mod_cast size j
        _ ≤ _ := div_le_div_of_nonneg_right (blockDensity_antitone hk (Finset.mem_Ico.mp hj).1) (by norm_num)
    _ = _ := by simp [show 2 * n - n = n by omega, mul_div_assoc]

end WindowEstimate

open Erdos142 Filter Real WindowEstimate

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R3.H1 := by
  intro ε hε
  have L : 0 < log 4 := log_pos (by norm_num)
  have tend : Tendsto (fun n : ℕ => (4:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [tend.eventually Erdos142KM.logSquare,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (1/(4*ε*(log 4)^2))),
    eventually_gt_atTop (0:ℕ)] with n hN hn hn0 S hw hf
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn0
  have bound := reciprocal_window_le (by decide : 1 < 3) S hw hf
  apply bound.trans
  push_cast at hN
  rw [Real.log_pow] at hN
  norm_num at hN
  have hp : 0 < (4:ℝ)^n := by positivity
  calc
    _ ≤ n * (((4:ℝ)^n / ((n:ℝ)*log 4)^2) / (4:ℝ)^n) / 4 := by gcongr
    _ = 1/(4*(n:ℝ)*(log 4)^2) := by field_simp
    _ ≤ ε := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := (div_le_iff₀ (by positivity : 0 < 4*ε*(log 4)^2)).mp hn
      linarith only [show (n:ℝ) * (4 * ε * (log 4)^2) = ε * (4 * n * (log 4)^2) by ring, hh]
