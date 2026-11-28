import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1
import Mathlib
open scoped BigOperators Matrix
namespace GSR
abbrev Aa:=Matrix.GeneralLinearGroup
abbrev Ab:=rootsOfUnity
alias Ac:=Matrix.mulVec_mulVec
alias Ad:=mul_assoc
alias Ae:=Subtype.ext
alias Af:=Matrix.mul_assoc
alias Ag:=Finset.sum_congr
alias Ah:=congrArg
alias Ai:=Finset.mem_univ
alias Aj:=Matrix.toLin'_apply
alias Ak:=Matrix.of_apply
alias Al:=Matrix.mulVec_smul
alias Am:=smul_eq_mul
alias An:=congrFun
alias Ao:=Matrix.mul_smul
alias Ap:=LinearMap.ext
alias Aq:=Matrix.map_mul
alias Ar:=Matrix.smul_mul
alias As:=Matrix.mul_one
alias At:=ZMod.natCast_eq_zero_iff
alias Au:=Nat.card_eq_fintype_card
alias Av:=Matrix.mul_apply
alias Aw:=if_neg
alias Ax:=Subgroup.Normal.conj_mem
alias Ay:=Finset.sum_eq_single
alias Az:=if_pos
alias AA:=one_mul
alias AB:=Matrix.dotProduct_mulVec
alias AC:=Matrix.one_mul
alias AD:=Function.update_self
alias AE:=Bool.false_eq_true
alias AF:=map_mul
alias AG:=Pi.single_apply
alias AH:=Matrix.one_apply_ne
alias AI:=Matrix.vecMul_transpose
alias AJ:=Matrix.mulVec_sum
alias AK:=mul_one
alias AL:=Finset.mem_filter
alias AM:=Matrix.transpose_apply
alias AN:=Matrix.one_mulVec
alias AO:=Fintype.sum_equiv
alias AP:=Nat.le_of_dvd
alias AQ:=Finset.sum_apply
alias AR:=smul_smul
alias AS:=mul_zero
alias AT:=Matrix.transpose_mul
alias AU:=LinearMap.smul_apply
alias AV:=Equiv.apply_symm_apply
alias AW:=Fintype.card_fin
alias AX:=Pi.smul_apply
alias AY:=Finset.sum_comm
alias AZ:=Matrix.map_apply
alias A1:=Finset.sum_eq_zero
alias A2:=Matrix.smul_apply
alias A3:=Matrix.mulVec_add
alias A4:=Fin.ext
alias A6:=Finset.mul_sum
alias A7:=Units.ext
alias A8:=Finset.sum_ite_eq'
alias A9:=Nat.mod_eq_of_lt
alias Ba:=map_sum
alias Bb:=mul_comm
alias Bc:=Nat.card_congr
alias Bd:=map_smul
alias Be:=ite_true
alias Bf:=LinearMap.mem_ker
alias Bg:=eq_self_iff_true
alias Bh:=Matrix.neg_apply
alias Bi:=QuotientGroup.mk'_surjective
alias Bj:=ite_false
alias Bk:=Subgroup.mem_center_iff
alias Bl:=orderOf_dvd_of_pow_eq_one
alias Bm:=zero_mul
alias Bn:=map_zero
alias Bo:=Finset.sum_mul
alias Bp:=Submodule.coe_smul_of_tower
alias Bq:=Finset.sum_ite_eq
alias Br:=LinearMap.id_apply
alias Bs:=QuotientGroup.eq_one_iff
alias Bt:=Finset.sum_add_distrib
alias Bu:=Function.update_of_ne
alias Bv:=Matrix.smul_mulVec
alias Bw:=MonoidHom.mem_ker
alias Bx:=one_smul
alias By:=mul_inv_cancel
alias Bz:=Bool.false_ne_true
alias BA:=pow_succ'
alias BB:=Subgroup.coe_mul
alias BC:=Finset.smul_sum
alias BD:=Matrix.mul_sum
alias BE:=pow_orderOf_eq_one
alias BF:=Matrix.zero_mulVec
alias BG:=Matrix.one_apply
alias BH:=Matrix.mul_add
alias BI:=map_one
alias BJ:=Matrix.neg_mulVec
alias BL:=Fin.snoc_castSucc
alias BM:=Matrix.transpose_one
alias BN:=Finset.card_union_of_disjoint
alias BO:=Matrix.mulVec_diagonal
alias BP:=Matrix.sum_mul
alias BQ:=Matrix.add_mul
alias BR:=Matrix.sum_apply
alias BS:=Finset.card_univ
alias BT:=Matrix.one_apply_eq
alias BU:=LinearMap.sub_apply
alias BV:=LinearMap.congr_fun
alias BW:=Submodule.mem_top
alias BX:=Subgroup.card_mul_index
alias BY:=Submodule.eq_bot_iff
alias BZ:=LinearMap.comp_apply
alias B0:=Matrix.mul_nonsing_inv
alias B3:=true_and
alias B4:=Submodule.coe_sum
alias B5:=Nat.exists_prime_and_dvd
alias B6:=Bool.eq_true_of_not_eq_false
alias B7:=Nat.dvd_iff_mod_eq_zero
alias B8:=one_pow
alias B9:=Bool.xor_self
alias Ca:=mul_ite
alias Cb:=Nat.coprime_iff_gcd_eq_one
alias Cc:=Matrix.transpose_transpose
alias Cd:=Nat.div_add_mod
alias Ce:=Matrix.zero_mul
alias Cf:=Subgroup.card_subgroup_dvd_card
alias Cg:=Submodule.eq_top_iff'
alias Ch:=Matrix.transpose_smul
alias Ci:=Fintype.bijective_iff_injective_and_card
alias Cj:=mul_right_cancel
alias Ck:=mul_left_cancel₀
alias Cl:=Fintype.card_fun
alias Cm:=Finset.sum_const
alias Cn:=Units.val_one
alias Co:=Subgroup.mem_zpowers
alias Cp:=Matrix.neg_mul
alias Cq:=Matrix.det_mul
alias Cr:=Submodule.mem_bot
alias Cs:=Nat.gcd_dvd_right
alias Ct:=LinearMap.toMatrix_comp
alias Cu:=Finset.mem_insert
alias Cv:=Subgroup.mem_centralizer_iff
alias Cw:=Fintype.card_le_of_injective
alias Cx:=sub_self
alias Cy:=Matrix.diagonal_mul
alias Cz:=pow_mul
alias CC:=mul_pow
alias CD:=Nat.card_pos
alias CE:=sub_eq_zero
alias CF:=Submodule.projectionOnto_apply_left
alias CG:=Subgroup.mem_bot
alias CH:=Subgroup.coe_one
alias CI:=Nat.gcd_dvd_left
alias CJ:=Fin.succ_ne_zero
alias CK:=inv_mul_cancel
alias CL:=Nat.prime_dvd_prime_iff_eq
alias CM:=Nat.pos_of_ne_zero
alias CN:=Matrix.mul_neg
alias CO:=LinearMap.toMatrix'_mulVec
alias CP:=ZMod.natCast_zmod_val
alias CQ:=Module.finrank_pi
alias CR:=Fin.eq_zero
alias CS:=Fin.snoc_last
alias CT:=pow_add
alias CU:=Matrix.mul_diagonal
alias CV:=LinearMap.sum_apply
alias CW:=Subgroup.nontrivial_iff_ne_bot
alias CX:=zero_ne_one
alias CY:=Finset.sum_sub_distrib
alias CZ:=Matrix.mul_zero
alias C0:=Matrix.diagonal_mul_diagonal
alias C1:=Finset.card_insert_of_notMem
alias C2:=map_ofNat
alias C3:=Bool.not_true
alias C4:=Fintype.sum_prod_type
alias C5:=map_inv
alias C6:=Fintype.card_bool
alias C7:=Finset.sum_insert
alias C8:=Nat.finite_of_card_ne_zero
alias C9:=Matrix.map_injective
alias Da:=Finset.mem_singleton
alias Db:=Bool.not_false
alias Dc:=map_pow
alias Dd:=orderOf_dvd_natCard
alias De:=Units.val_mul
alias Df:=Matrix.diagonal_apply_ne
alias Dg:=LinearMap.toMatrix_apply
alias Dh:=LinearMap.toMatrix'_comp
alias Di:=Matrix.det_zero
alias Dj:=Subgroup.commutator_mem_commutator
alias Dk:=Nat.sub_add_cancel
alias Dl:=zero_smul
alias Dm:=mul_inv_rev
alias Dn:=Polynomial.degree_X_pow
alias Do:=zpow_add
alias Dp:=neg_neg
alias Dq:=Subgroup.range_subtype
alias Dr:=Prod.ext
alias Ds:=Nat.mod_self
alias Dt:=MonoidHom.range_eq_map
alias Du:=Matrix.nonsing_inv_mul
alias Dv:=Matrix.det_one
alias Dw:=LinearMap.toMatrix'_id
alias Dx:=IsPGroup.iff_card
alias Dy:=Finset.sum_neg_distrib
alias Dz:=Bool.false_xor
alias DA:=Subgroup.one_lt_card_iff_ne_bot
alias DB:=LinearMap.toMatrix_id
alias DC:=Fintype.sum_bijective
alias DD:=exists_prime_orderOf_dvd_card'
alias DE:=RingHom.id_apply
alias DF:=Nat.mod_lt
alias DG:=Units.val_mk0
alias DH:=Units.ne_zero
alias DI:=Nat.prime_two
alias DJ:=sub_smul
alias DK:=pow_succ
alias DL:=one_ne_zero
alias DM:=mul_ne_zero
alias DN:=mul_inv_cancel_right
alias DO:=map_natCast
alias DP:=le_antisymm
alias DQ:=add_comm
alias DR:=Nat.dvd_gcd
alias DS:=Finsupp.single_apply
alias DT:=RingHom.map_det
alias DU:=Finset.sum_smul
alias DV:=Equiv.congr_fun
alias DW:=Polynomial.eval_pow
alias DX:=Module.finrank_self
alias DY:=Subgroup.commutator_normal
alias DZ:=Matrix.mulVec_zero
alias D0:=Fin.succ_injective
alias D1:=Nat.eq_of_mul_eq_mul_left
alias D2:=decide_eq_true_eq
alias D3:=Polynomial.eval_X
alias D4:=Matrix.diag_apply
alias D5:=Fintype.card_perm
alias D6:=Finset.sum_subset
alias D7:=pow_zero
alias D8:=add_zero
alias D9:=Subgroup.mem_top
alias Ea:=Fintype.sum_bool
alias Eb:=Finset.mem_image
alias Ec:=Equiv.ext
alias Ed:=Algebra.smul_def
alias Ee:=zpow_natCast
alias Ef:=Polynomial.degree_sub_eq_left_of_degree_lt
alias Eg:=Nat.dvd_of_mod_eq_zero
alias Eh:=MvPolynomial.coeff_sum
alias Ei:=LinearMap.single_apply
alias Ej:=Finset.dvd_prod_of_mem
alias Ek:=Equiv.symm_apply_apply
alias El:=Nat.two_pow_pos
alias Em:=LinearEquiv.ext
alias En:=QuotientGroup.ker_mk'
alias Eo:=Nat.Coprime.pow_right
alias Ep:=Module.finrank_matrix
alias Eq:=smul_add
alias Er:=Nat.chineseRemainder
alias Es:=MvPolynomial.aeval_C
alias Et:=MonoidHom.comp_apply
alias Eu:=Matrix.det_transpose
alias Ev:=Fintype.card_subtype
alias Ew:=Finset.disjoint_left
alias Ex:=Bool.xor_false
alias Ey:=ZMod.card
alias Ez:=Fin.elim0
alias EA:=Polynomial.eval_sub
alias EB:=MvPolynomial.eval_C
alias EC:=Function.comp_apply
alias ED:=Finset.card_le_card
alias EE:=Pi.zero_apply
alias EF:=Nat.find_spec
alias EG:=Nat.card_prod
alias EH:=Submodule.smul_mem
alias EI:=Submodule.map_iSup
alias EJ:=Nat.div_mul_cancel
alias EK:=MvPolynomial.isHomogeneous_C_mul_X
alias EL:=two_mul
alias EM:=mul_add
alias EN:=map_add
alias EO:=dvd_refl
alias EP:=Units.val_mk
alias EQ:=Submodule.eq_of_le_of_finrank_le
alias ER:=Module.nontrivial_of_finrank_pos
alias ES:=Matrix.zero_apply
alias ET:=Subgroup.card_quotient_dvd_card
alias EU:=LinearMap.trace_eq_matrix_trace
alias EV:=Submodule.eq_top_of_finrank_eq
alias EW:=Subgroup.coe_inv
alias EX:=Nat.card_zpowers
alias EY:=Matrix.add_apply
alias EZ:=LinearMap.toMatrix_mulVec_repr
alias E0:=Finset.card_image_of_injective
alias E1:=Nat.Prime.coprime_iff_not_dvd
alias E3:=mul_left_cancel
alias E4:=Subgroup.eq_of_le_of_card_ge
alias E5:=Subgroup.commutator_le_right
alias E6:=pow_two
alias E7:=inv_pow
alias E8:=ZMod.natCast_eq_natCast_iff
alias E9:=QuotientGroup.mk_surjective
alias Fa:=top_ne_bot
alias Fb:=isConj_iff
alias Fc:=add_smul
alias Fd:=MvPolynomial.eval_monomial
alias Fe:=Matrix.mul_sub
alias Ff:=Matrix.ext
alias Fg:=LinearEquiv.finrank_map_eq
alias Fh:=Finsupp.lapply
alias Fi:=Finset.sum_bij
alias Fk:=Fin.sum_univ_eq_sum_range
section RationalAndRealMinus
lemma WH {G H:Type*} [Group G] [Group H] (f:G→*H) {x y:G} (h:IsConj x y) : IsConj (f x) (f y):=by
 obtain ⟨c,hc⟩:=isConj_iff.mp h;exact isConj_iff.mpr ⟨f c,by rw[<-C5,<-AF,<-AF,hc]⟩
lemma QC {G:Type*} [Group G] [Finite G] (g:G):g ^ Nat.card G=1:=by
 have:Fintype G:=Fintype.ofFinite G;rw[Au];exact pow_card_eq_one
def Qw (G:Type*) [Group G]:Prop:=
 ∀ (x:G) (n:ℕ),(Nat.card G).Coprime n->IsConj x (x ^ n)
lemma QT {G H:Type*} [Group G] [Group H] (e:G≃*H) (hG:Qw G):Qw H:=by
 intro y n hn;have zc:Nat.card G=Nat.card H:=Bc e.toEquiv;rw[<-zc] at hn;have za:=hG (e.symm y) n hn;have zb:=WH e.toMonoidHom za;simpa[Dc] using zb
lemma Wo {G:Type*} [Group G] [Finite G] (N:Subgroup G) [N.Normal] (hG:Qw G):Qw (G ⧸ N):=by
 classical
 intro x m hm;obtain ⟨g,rfl⟩:=E9 x;set M:=Nat.card (G ⧸ N) with hM_def
 set D:=Nat.card G with hD_def
 have zn:0 < M:=CD;have zh:0 < D:=CD;set S:=D.primeFactors.filter (fun q=>¬ q∣M);set B:=∏ q∈S,q;have zo:M.Coprime B:=(by rw[Cb];by_contra hne;obtain ⟨q,za,zb⟩:=B5 hne;have ze:q∣M:=zb.trans (CI M B);have zg:q∣B:=zb.trans (Cs M B);rw[Prime.dvd_finsetProd_iff za.prime] at zg;obtain ⟨r,zl,zt⟩:=zg;have zf:r.Prime:=(Nat.mem_primeFactors.mp (Finset.mem_filter.mp zl).1).1;have zi:q=r:=(CL za zf).mp zt;exact (Finset.mem_filter.mp zl).2 (zi ▸ ze));obtain ⟨n,zm,zu⟩:=Er zo m 1;have zp:D.Coprime n:=by
  rw[Cb];by_contra hne;obtain ⟨q,za,zb⟩:=B5 hne;have zq:q∣D:=zb.trans (CI D n);have zk:q∣n:=zb.trans (Cs D n);by_cases ze:q∣M
  . have zr:q∣m:=(by have h1:n % q=m % q:=(zm.of_dvd ze);rw[B7] at zk ⊢;omega);exact za.not_dvd_one (hm.gcd_eq_one ▸ DR ze zr)
  . have zs:q∈S:=Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨za,zq,zh.ne'⟩,ze⟩;have zg:q∣B:=Ej _ zs;have h1:n % q=1 % q:=zu.of_dvd zg;rw[B7] at zk;have zv:1 % q=1:=A9 za.one_lt;omega
 have zj:=WH (QuotientGroup.mk' N) (hG g n zp);have zd:(QuotientGroup.mk g:G ⧸ N) ^ n=(QuotientGroup.mk g:G ⧸ N) ^ m:=by
  have h1:(QuotientGroup.mk g:G ⧸ N) ^ M=1:=QC _;have zc:∀ k:ℕ,(QuotientGroup.mk g:G ⧸ N) ^ k=(QuotientGroup.mk g:G ⧸ N) ^ (k % M):=by
   intro k
   conv_lhs=>rw[<-Cd k M]
   rw[CT,Cz,h1,B8,AA]
  rw[zc n,zc m,zm]
 simpa[Dc,zd] using zj
lemma WX {G:Type*} [Group G] [Finite G] (hG:Qw G) : Qw (G×Multiplicative (ZMod 2)):=by
 intro ⟨g,a⟩ n hn;have za:Nat.card (G×Multiplicative (ZMod 2))=Nat.card G*2:=by rw[EG,Au (α:=Multiplicative (ZMod 2))];simp
 rw[za] at hn;have zc:(Nat.card G).Coprime n:=(Nat.coprime_mul_iff_left.mp hn).1;have zd:Nat.Coprime 2 n:=(Nat.coprime_mul_iff_left.mp hn).2;obtain ⟨c,hc⟩:=isConj_iff.mp (hG g n zc);rw[Fb];refine ⟨(c,1),?_⟩;ext
 . simpa using hc
 .
  change 1*a*1⁻¹=a ^ n;simp only[AA,inv_one,AK];have ze:a ^ 2=1:=by
   change Multiplicative.ofAdd ((2:ℕ)•Multiplicative.toAdd a)=1;have zf:(2:ℕ)•Multiplicative.toAdd a=0:=by
    rw[nsmul_eq_mul];have:((2:ℕ):ZMod 2)=0:=by decide
    rw[this,Bm]
   rw[zf];rfl
  have zb:n % 2=1:=by
   have zg:¬ 2∣n:=fun h=>by
    have:=DR (EO 2) h
    rw[zd.gcd_eq_one] at this;omega
   omega
  conv_rhs=>rw[<-Cd n 2,zb,CT,Cz,ze,B8,AA,pow_one]
def QQ {G:Type*} [Group G] (z:G):Prop:=
 ∀ g:G,IsConj g g⁻¹\/IsConj g (z*g)
lemma WS {G:Type*} [Group G] [Finite G] (z:G) (hG:Qw G) : QQ z:=by
 intro g;left;have za:0 < Nat.card G:=CD;have zb:(Nat.card G).Coprime (Nat.card G - 1):=by
  rcases Nat.eq_or_lt_of_le za with h1 | hgt
  . rw[<-h1];simp
  .
   have:Nat.card G=(Nat.card G - 1)+1:=by omega
   conv_lhs=>rw[this]
   simp
 have zc:g ^ (Nat.card G - 1)=g⁻¹:=(by apply eq_inv_of_mul_eq_one_left;rw[<-DK,Dk za,QC]);simpa[zc] using hG g (Nat.card G - 1) zb
lemma W6 {L L_U:Type*} [Group L] [Fintype L] [Group L_U]
  {z:L} (zd:z∈Subgroup.center L) (zk:z*z=1) (zl:z≠1) (zm:QQ z) (A:Subgroup L) [A.Normal] (zn:∀ a∈A,a*a=1) (zh:z∈A) (za:A→*ℤˣ) (zi:za ⟨z,zh⟩=-1) (I:Subgroup L) (zc:∀ g:L,g∈I↔∀ a:A,za ⟨g*a.1*g⁻¹,Ax ‹_› a.1 a.2 g⟩=za a) (π:I→*L_U) (ze:Function.Surjective π) (zj:L_U) (zb:A<=I) (zf:∀ a:A,za a=1->π ⟨a.1,zb a.2⟩=1) (zg:∀ a:A,za a=-1->π ⟨a.1,zb a.2⟩=zj) : QQ zj:=by
 classical
 have zr:∀ a:A,za a=1\/za a=-1:=fun a=>Int.units_eq_one_or (za a);have zz:∀ a:A,a.1⁻¹=a.1:=fun a=>inv_eq_of_mul_eq_one_right (zn a.1 a.2);have zQ:z⁻¹=z:=inv_eq_of_mul_eq_one_right zk;have zD:∀ g:L,z*g=g*z:=fun g=>(Subgroup.mem_center_iff.mp zd g).symm;intro va;obtain ⟨y,rfl⟩:=ze va;by_cases zK:∃ a:A,za a=-1/\IsConj y (⟨a.1,zb a.2⟩*y)
 . right;obtain ⟨a,zW,zq⟩:=zK;have zF:=WH π zq;rw[AF,zg a zW] at zF;exact zF
 .
  left;push Not at zK;let P (ε:ℤˣ) (u:I):Prop:=∃ a:A,za a=ε/\IsConj u (⟨a.1,zb a.2⟩*y);let f:I->ℚ:=fun u=>if P 1 u then 1 else if P (-1) u then -1 else 0;have zM:∀ u:I,¬ (P 1 u/\P (-1) u):=by
   rintro u ⟨⟨a,zX,hca⟩,⟨b,hb1,hcb⟩⟩;have vb:IsConj (⟨a.1,zb a.2⟩*y) (⟨b.1,zb b.2⟩*y):=hca.symm.trans hcb;obtain ⟨h,hh⟩:=isConj_iff.mp vb;let a':A:=⟨h.1*a.1⁻¹*h.1⁻¹*b.1,A.mul_mem (Ax ‹_› a.1⁻¹ (A.inv_mem a.2) h.1) b.2⟩;have zN:za a'=-1:=by
    have h1:za ⟨h.1*a.1*h.1⁻¹,Ax ‹_› a.1 a.2 h.1⟩=za a:=
     (zc h.1).mp h.2 a
    have zR:a'=⟨h.1*a.1*h.1⁻¹,Ax ‹_› a.1 a.2 h.1⟩*b:=(by ext;simp[a',zz a]);rw[zR,AF,h1,zX,hb1,AA]
   have zO:IsConj y (⟨a'.1,zb a'.2⟩*y):=by
    rw[Fb];refine ⟨h,Ae ?_⟩;change h.1*y.1*h.1⁻¹=a'.1*y.1;have zG:h.1*(a.1*y.1)*h.1⁻¹=b.1*y.1:=Ah Subtype.val hh;have zp:h.1*y.1*h.1⁻¹=(h.1*a.1⁻¹*h.1⁻¹)*(h.1*(a.1*y.1)*h.1⁻¹):=by group
    rw[zp,zG];simp[a',Ad]
   exact zK a' zN zO
  have zE:∀ h u:I,f (h*u*h⁻¹)=f u:=by
   intro h u;have zA:∀ ε:ℤˣ,P ε (h*u*h⁻¹)↔P ε u:=by intro ε;refine exists_congr fun a=>and_congr_right fun _=>?_;have hu:IsConj u (h*u*h⁻¹):=isConj_iff.mpr ⟨h,rfl⟩;exact ⟨fun hc=>hu.trans hc,fun hc=>hu.symm.trans hc⟩
   simp only[f,zA]
  have z7:f y=1:=by
   have hy:P 1 y:=⟨1,BI za,by
    have h1:(⟨(1:A).1,zb (1:A).2⟩:I)=1:=Ae rfl
    rw[h1,AA]⟩
   dsimp only[f];rw[Az hy]
  have zu:∀ (b:A) (u:I),f (⟨b.1,zb b.2⟩*u)=((za b:ℤ):ℚ)*f u:=by
   intro b u;have zA:∀ ε:ℤˣ,P ε (⟨b.1,zb b.2⟩*u)↔P (za b*ε) u:=by
    intro ε;constructor
    .
     rintro ⟨a,haε,hc⟩;obtain ⟨h,hh⟩:=isConj_iff.mp hc;let hb:A:=⟨h.1*b.1*h.1⁻¹,Ax ‹_› b.1 b.2 h.1⟩;refine ⟨hb*a,?_,?_⟩
     . rw[AF,(zc h.1).mp h.2 b,haε]
     .
      rw[Fb];refine ⟨h,Ae ?_⟩;change h.1*u.1*h.1⁻¹=(hb*a).1*y.1;have zG:h.1*(b.1*u.1)*h.1⁻¹=a.1*y.1:=Ah Subtype.val hh;have zp:h.1*u.1*h.1⁻¹=(h.1*b.1⁻¹*h.1⁻¹)*(h.1*(b.1*u.1)*h.1⁻¹):=by group
      rw[zp,zG,zz b];simp[hb,Ad]
    .
     rintro ⟨a',ha'ε,hc⟩;obtain ⟨h,hh⟩:=isConj_iff.mp hc;let hb:A:=⟨h.1*b.1*h.1⁻¹,Ax ‹_› b.1 b.2 h.1⟩;refine ⟨hb*a',?_,?_⟩
     . rw[AF,(zc h.1).mp h.2 b,ha'ε,<-Ad];rcases zr b with h1 | h1 <;> simp[h1]
     .
      rw[Fb];refine ⟨h,Ae ?_⟩;change h.1*(b.1*u.1)*h.1⁻¹=(hb*a').1*y.1;have zG:h.1*u.1*h.1⁻¹=a'.1*y.1:=Ah Subtype.val hh;have zp:h.1*(b.1*u.1)*h.1⁻¹=(h.1*b.1*h.1⁻¹)*(h.1*u.1*h.1⁻¹):=by group
      rw[zp,zG];simp[hb,Ad]
   rcases zr b with hb1 | hb1
   . dsimp only[f];simp only[zA,hb1,AA,Cn,Int.cast_one]
   .
    dsimp only[f];simp only[zA 1,zA (-1),hb1,AK,mul_neg,Dp,Units.val_neg,Cn,Int.cast_neg,Int.cast_one,neg_one_mul];by_cases h1:P 1 u
    . have h2:¬ P (-1) u:=fun h2=>zM u ⟨h1,h2⟩;rw[Aw h2,Az h1,Az h1]
    .
     by_cases h2:P (-1) u
     . rw[Az h2,Aw h1,Az h2,Dp]
     . rw[Aw h2,Aw h1,Aw h1,Aw h2,neg_zero]
  let F:L->ℚ:=fun g=>
   ∑ t:L,if h:t*g*t⁻¹∈I then f ⟨t*g*t⁻¹,h⟩ else 0
  have zy:∀ k g:L,F (k*g*k⁻¹)=F g:=by
   intro k g;simp only[F];refine DC (fun t:L=>t*k) (Group.mulRight_bijective k) _ _ ?_;intro t;have zw:t*(k*g*k⁻¹)*t⁻¹=(t*k)*g*(t*k)⁻¹:=by group
   simp[zw]
  have zS:∀ g:L,F (z*g)=-F g:=by
   intro g;simp only[F,<-Dy];refine Ag rfl fun t _=>?_;have zw:t*(z*g)*t⁻¹=z*(t*g*t⁻¹):=by
    calc t*(z*g)*t⁻¹=(t*z)*g*t⁻¹:=by group
    _ = (z*t)*g*t⁻¹:=by rw[<-zD t]
    _ = z*(t*g*t⁻¹):=by group
   have zs:z*(t*g*t⁻¹)∈I↔t*g*t⁻¹∈I:=
    I.mul_mem_cancel_left (zb zh)
   rw[zw];by_cases h:t*g*t⁻¹∈I
   . have h':z*(t*g*t⁻¹)∈I:=zs.mpr h;rw[dif_pos h',dif_pos h];have zx:=zu ⟨z,zh⟩ ⟨t*g*t⁻¹,h⟩;rw[zi] at zx;simpa using zx
   . have h':z*(t*g*t⁻¹)∉I:=mt zs.mp h;rw[dif_neg h',dif_neg h,neg_zero]
  have zT:∀ g:L,F g⁻¹=F g:=by
   intro g;rcases zm g with h1 | h2
   . obtain ⟨k,hk⟩:=isConj_iff.mp h1;rw[<-hk,zy]
   .
    have zU:F g=0:=by
     obtain ⟨k,hk⟩:=isConj_iff.mp h2;have h1:F (z*g)=F g:=by rw[<-hk,zy]
     rw[zS] at h1;linarith
    have z8:F g⁻¹=0:=by
     obtain ⟨k,hk⟩:=isConj_iff.mp h2;have vc:k*g⁻¹*k⁻¹=z*g⁻¹:=by
      calc k*g⁻¹*k⁻¹=(k*g*k⁻¹)⁻¹:=by group
      _ = (z*g)⁻¹:=by rw[hk]
      _ = g⁻¹*z⁻¹:=Dm z g
      _ = g⁻¹*z:=by rw[zQ]
      _ = z*g⁻¹:=(zD g⁻¹).symm
     have h1:F (z*g⁻¹)=F g⁻¹:=by rw[<-vc,zy]
     rw[zS] at h1;linarith
    rw[zU,z8]
  have zL:∀ t:L,(∑ a:A,((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ))=if t∈I then (Nat.card A:ℚ) else 0:=by
   intro t;split_ifs with ht
   .
    have h1:∀ a:A,((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ)=1:=by
     intro a;rw[(zc t).mp ht a];rcases zr a with h | h <;> simp[h]
    simp[h1,Au]
   .
    rw[zc] at ht;push Not at ht;obtain ⟨a0,z6⟩:=ht;have zH:((za a0:ℤ):ℚ)*((za ⟨t*a0.1*t⁻¹,Ax ‹_› a0.1 a0.2 t⟩:ℤ):ℚ)=-1:=by
     rcases zr a0 with h1 | h1 <;>
     rcases zr ⟨t*a0.1*t⁻¹,Ax ‹_› a0.1 a0.2 t⟩ with h2 | h2
     . exact absurd (h2.trans h1.symm) z6
     . simp[h1,h2]
     . simp[h1,h2]
     . exact absurd (h2.trans h1.symm) z6
    set Ssum:=∑ a:A,((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ);have vd:Ssum=-Ssum:=by
     have z9:=DC (fun a:A=>a0*a) (Group.mulLeft_bijective a0)
      (fun a:A=>((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ))
      (fun a:A=>-(((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ)))
     have z2:Ssum=∑ a:A,-(((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ)):=by
      apply z9;intro a;have zI:(⟨t*(a0*a).1*t⁻¹,Ax ‹_› (a0*a).1 (a0*a).2 t⟩:A)=
        ⟨t*a0.1*t⁻¹,Ax ‹_› a0.1 a0.2 t⟩*
        ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:=by
       ext;simp[Ad]
      rw[zI,AF,AF];push_cast;symm
      calc -(((za a0:ℤ):ℚ)*((za a:ℤ):ℚ)*(((za ⟨t*a0.1*t⁻¹,_⟩:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,_⟩:ℤ):ℚ)))
        = -((((za a0:ℤ):ℚ)*((za ⟨t*a0.1*t⁻¹,_⟩:ℤ):ℚ))*(((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,_⟩:ℤ):ℚ))):=by ring
      _ = (((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,_⟩:ℤ):ℚ)):=by rw[zH];ring
     rw[Dy] at z2;exact z2
    linarith
  have zY:∑ a:A,((za a:ℤ):ℚ)*F (a.1*y.1)=(Nat.card A:ℚ)*(Nat.card I:ℚ):=by
   simp only[F,A6];rw[AY];have zB:∀ t:L,(∑ a:A,((za a:ℤ):ℚ)*if h:t*(a.1*y.1)*t⁻¹∈I then f ⟨t*(a.1*y.1)*t⁻¹,h⟩ else 0)=if t∈I then (Nat.card A:ℚ) else 0:=by
    intro t;have zp:∀ a:A,((za a:ℤ):ℚ)*(if h:t*(a.1*y.1)*t⁻¹∈I then f ⟨t*(a.1*y.1)*t⁻¹,h⟩ else 0)=((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ)*(if h:t*y.1*t⁻¹∈I then f ⟨t*y.1*t⁻¹,h⟩ else 0):=by
     intro a;have zw:t*(a.1*y.1)*t⁻¹=(t*a.1*t⁻¹)*(t*y.1*t⁻¹):=by group
     have z3:t*a.1*t⁻¹∈I:=zb (Ax ‹_› a.1 a.2 t);have zs:(t*a.1*t⁻¹)*(t*y.1*t⁻¹)∈I↔t*y.1*t⁻¹∈I:=I.mul_mem_cancel_left z3;rw[zw];by_cases zo:t*y.1*t⁻¹∈I
     . have h':=zs.mpr zo;rw[dif_pos h',dif_pos zo];have zx:=zu ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩ ⟨t*y.1*t⁻¹,zo⟩;have zv:(⟨t*a.1*t⁻¹,z3⟩:I)*⟨t*y.1*t⁻¹,zo⟩=⟨(t*a.1*t⁻¹)*(t*y.1*t⁻¹),h'⟩:=rfl;rw[zv] at zx;rw[zx];ring
     . have h':=mt zs.mp zo;rw[dif_neg h',dif_neg zo,AS,AS]
    simp_rw[zp,<-Bo,zL t];by_cases ht:t∈I
    .
     rw[Az ht];have zo:t*y.1*t⁻¹∈I:=I.mul_mem (I.mul_mem ht y.2) (I.inv_mem ht);rw[dif_pos zo];have zv:(⟨t*y.1*t⁻¹,zo⟩:I)=⟨t,ht⟩*y*⟨t,ht⟩⁻¹:=by ext;rfl
     rw[zv,zE,z7,AK]
    . rw[Aw ht,Bm]
   simp_rw[zB];rw[Finset.sum_ite,Finset.sum_const_zero,D8,Cm,nsmul_eq_mul,Bb];congr 1;have zC:(Finset.univ.filter (fun t:L=>t∈I)).card=Nat.card I:=by rw[Au];exact (Ev (fun t:L=>t∈I)).symm
   exact_mod_cast zC
  have zZ:∑ a:A,((za a:ℤ):ℚ)*F (a.1*y.1)=(Nat.card A:ℚ)*(Nat.card I:ℚ)*f y⁻¹:=by
   have zJ:∀ a:A,F (a.1*y.1)=F (y.1⁻¹*a.1):=(by intro a;rw[<-zT (a.1*y.1),Dm,zz a]);simp_rw[zJ,F,A6];rw[AY];have zB:∀ t:L,(∑ a:A,((za a:ℤ):ℚ)*if h:t*(y.1⁻¹*a.1)*t⁻¹∈I then f ⟨t*(y.1⁻¹*a.1)*t⁻¹,h⟩ else 0)=if t∈I then (Nat.card A:ℚ)*f y⁻¹ else 0:=by
    intro t;have zp:∀ a:A,((za a:ℤ):ℚ)*(if h:t*(y.1⁻¹*a.1)*t⁻¹∈I then f ⟨t*(y.1⁻¹*a.1)*t⁻¹,h⟩ else 0)=((za a:ℤ):ℚ)*((za ⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩:ℤ):ℚ)*(if h:t*y.1⁻¹*t⁻¹∈I then f ⟨t*y.1⁻¹*t⁻¹,h⟩ else 0):=by
     intro a;let ta:A:=⟨t*a.1*t⁻¹,Ax ‹_› a.1 a.2 t⟩;let b:A:=⟨(t*y.1⁻¹*t⁻¹)*ta.1*(t*y.1⁻¹*t⁻¹)⁻¹,Ax ‹_› ta.1 ta.2 (t*y.1⁻¹*t⁻¹)⟩;have zw:t*(y.1⁻¹*a.1)*t⁻¹=b.1*(t*y.1⁻¹*t⁻¹):=(by simp only[b,ta];group);have z4:b.1∈I:=zb b.2;have zs:b.1*(t*y.1⁻¹*t⁻¹)∈I↔t*y.1⁻¹*t⁻¹∈I:=I.mul_mem_cancel_left z4;rw[zw];by_cases zo:t*y.1⁻¹*t⁻¹∈I
     . have h':=zs.mpr zo;rw[dif_pos h',dif_pos zo];have zx:=zu b ⟨t*y.1⁻¹*t⁻¹,zo⟩;have zv:(⟨b.1,z4⟩:I)*⟨t*y.1⁻¹*t⁻¹,zo⟩=⟨b.1*(t*y.1⁻¹*t⁻¹),h'⟩:=rfl;rw[zv] at zx;have zV:za b=za ta:=(zc (t*y.1⁻¹*t⁻¹)).mp zo ta;rw[zx,zV];ring
     . have h':=mt zs.mp zo;rw[dif_neg h',dif_neg zo,AS,AS]
    simp_rw[zp,<-Bo,zL t];by_cases ht:t∈I
    .
     simp only[ht,↓reduceIte];have zo:t*y.1⁻¹*t⁻¹∈I:=I.mul_mem (I.mul_mem ht (I.inv_mem y.2)) (I.inv_mem ht);rw[dif_pos zo];have zv:(⟨t*y.1⁻¹*t⁻¹,zo⟩:I)=⟨t,ht⟩*y⁻¹*⟨t,ht⟩⁻¹:=by ext;rfl
     rw[zv,zE]
    . simp only[ht,↓reduceIte,Bm]
   simp_rw[zB];rw[Finset.sum_ite,Finset.sum_const_zero,D8,Cm,nsmul_eq_mul];have zC:(Finset.univ.filter (fun t:L=>t∈I)).card=Nat.card I:=by rw[Au];exact (Ev (fun t:L=>t∈I)).symm
   rw[zC];ring
  have zt:f y⁻¹=1:=by
   have z0:(0:ℚ) < Nat.card A:=by exact_mod_cast (CD (α:=A))
   have z1:(0:ℚ) < Nat.card I:=by exact_mod_cast (CD (α:=I))
   have zP:(Nat.card A:ℚ)*(Nat.card I:ℚ)≠0:=DM z0.ne' z1.ne';have zw:(Nat.card A:ℚ)*(Nat.card I:ℚ)*f y⁻¹=(Nat.card A:ℚ)*(Nat.card I:ℚ)*1:=(by rw[<-zZ,zY,AK]);exact Ck zP zw
  have ve:P 1 y⁻¹:=(by by_contra hno;dsimp only[f] at zt;rw[Aw hno] at zt;split_ifs at zt <;> norm_num at zt);obtain ⟨a,zX,hc⟩:=ve;have z5:=WH π hc.symm;rw[AF,zf a zX,AA,C5] at z5;exact z5
end RationalAndRealMinus
section MinimalCounterexample
def Qd (n p:ℕ):Aa (Fin n) (ZMod p) where
 val:=-1
 inv:=-1
 val_inv:=by simp
 inv_val:=by simp
@[simp] lemma negOneGL_val (n p:ℕ):(Qd n p).val=(-1:Matrix (Fin n) (Fin n) (ZMod p)):=rfl
lemma Yr (n p:ℕ):Qd n p*Qd n p=1:=by
 ext i j;simp[Qd]
lemma Ya (n p:ℕ) (g:Aa (Fin n) (ZMod p)) : Qd n p*g=g*Qd n p:=by
 ext i j;simp[Qd]
lemma Yy {n p:ℕ} [Fact p.Prime] (ze:p≠2) (H:Subgroup (Aa (Fin n) (ZMod p))) (zd:Group.IsSolvable H) (zb:¬ p∣Nat.card H) (za:Qw H) (zc:∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈H,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤) (zf:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈H,g.val.mulVec v=(a:ZMod p)•v) : ∃ L:Subgroup (Aa (Fin n) (ZMod p)), Group.IsSolvable L/\ ¬ p∣Nat.card L/\ Qw L/\ Qd n p∈L/\ (∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤)/\ (∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v):=by
 classical
 have zj:p.Prime:=Fact.out;let L:Subgroup (Aa (Fin n) (ZMod p)):=H ⊔ Subgroup.zpowers (Qd n p);have zi:H<=L:=le_sup_left;have zh:Qd n p∈L:=Subgroup.mem_sup_right (Co _);have zk:∀ U:Submodule (ZMod p) (Fin n->ZMod p),(∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤:=
  fun U hU=>zc U (fun g hg=>hU g (zi hg))
 have zo:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ),∃ g∈L,g.val.mulVec v=(a:ZMod p)•v:=(by intro v hv a;obtain ⟨g,hg,zA⟩:=zf v hv a;exact ⟨g,zi hg,zA⟩);by_cases zv:Qd n p∈H
 . have zw:L=H:=sup_eq_left.mpr ((Subgroup.zpowers_le).mpr zv);have zp:H≃*L:=MulEquiv.subgroupCongr zw.symm;exact ⟨L,Group.isSolvable_of_isSolvable_injective (f:=zp.symm.toMonoidHom) zp.symm.injective,by rwa[<-Bc zp.toEquiv],QT zp za,zh,zk,zo⟩
 .
  have zg:∀ ε:Multiplicative (ZMod 2),ε=1\/ε=Multiplicative.ofAdd (1:ZMod 2):=by
   intro ε;have h2:Multiplicative.toAdd ε=0\/Multiplicative.toAdd ε=1:=
    (by decide:∀ x:ZMod 2,x=0\/x=1) (Multiplicative.toAdd ε)
   rcases h2 with h0 | h1
   . left;exact Multiplicative.toAdd.injective h0
   . right;exact Multiplicative.toAdd.injective h1
  let ψ:H×Multiplicative (ZMod 2)→*L:=
   {toFun:=fun ⟨h,ε⟩=>
     ⟨h.1*(if Multiplicative.toAdd ε=0 then 1 else Qd n p),L.mul_mem (zi h.2) (by split_ifs;exact L.one_mem;exact zh)⟩
    map_one':=by ext;simp
    map_mul':=fun ⟨h₁,ε₁⟩ ⟨h₂,ε₂⟩=>by
     apply Ae;change h₁.1*h₂.1*(if Multiplicative.toAdd (ε₁*ε₂)=0 then 1 else Qd n p)=(h₁.1*(if Multiplicative.toAdd ε₁=0 then 1 else Qd n p))*(h₂.1*(if Multiplicative.toAdd ε₂=0 then 1 else Qd n p));rcases zg ε₁ with rfl | rfl <;> rcases zg ε₂ with rfl | rfl
     . simp
     . simp[Ad]
     . simp[Ad,Ya]
     .
      have zz:Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2)*Multiplicative.ofAdd (1:ZMod 2))=0:=(by change (1:ZMod 2)+1=0;decide);rw[zz,Az rfl];have zl:Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))≠0:=by decide
      rw[Aw zl]
      calc h₁.1*h₂.1*1=h₁.1*h₂.1*(Qd n p*Qd n p):=by rw[Yr]
      _ = h₁.1*(h₂.1*Qd n p)*Qd n p:=by group
      _ = h₁.1*(Qd n p*h₂.1)*Qd n p:=by rw[Ya]
      _ = (h₁.1*Qd n p)*(h₂.1*Qd n p):=by group }
  have zr:Function.Injective ψ:=by
   rintro ⟨h₁,ε₁⟩ ⟨h₂,ε₂⟩ heq;have hv:=Ah Subtype.val heq;dsimp[ψ] at hv;have zl:Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))≠0:=by decide
   rcases zg ε₁ with rfl | rfl <;> rcases zg ε₂ with rfl | rfl
   . simp at hv;exact Dr hv rfl
   . exfalso;rw[toAdd_one,Az rfl,AK,Aw zl] at hv;have:Qd n p=h₂.1⁻¹*h₁.1:=eq_inv_mul_of_mul_eq hv.symm;exact zv (this ▸ H.mul_mem (H.inv_mem h₂.2) h₁.2)
   . exfalso;rw[toAdd_one,Az rfl,AK,Aw zl] at hv;have:Qd n p=h₁.1⁻¹*h₂.1:=eq_inv_mul_of_mul_eq hv;exact zv (this ▸ H.mul_mem (H.inv_mem h₁.2) h₂.2)
   . rw[Aw zl] at hv;exact Dr (Ae (Cj hv)) rfl
  have zm:Function.Surjective ψ:=by
   intro ⟨x,hx⟩;have zt:x∈(H ⊔ Subgroup.zpowers (Qd n p):Subgroup _):=hx;have zx:H ⊔ Subgroup.zpowers (Qd n p)<=ψ.range.map L.subtype:=by
    rw[sup_le_iff];constructor
    . intro h hh;refine ⟨⟨h,zi hh⟩,⟨(⟨h,hh⟩,1),?_⟩,rfl⟩;apply Ae;simp[ψ]
    . rw[Subgroup.zpowers_le];refine ⟨⟨Qd n p,zh⟩,⟨(1,Multiplicative.ofAdd (1:ZMod 2)),?_⟩,rfl⟩;apply Ae;simp[ψ]
   obtain ⟨y,⟨p0,hp0⟩,hy⟩:=zx zt;exact ⟨p0,Ae (Ah Subtype.val hp0 |>.trans hy)⟩
  let zq:H×Multiplicative (ZMod 2)≃*L:=MulEquiv.ofBijective ψ ⟨zr,zm⟩;have zs:Group.IsSolvable L:=(by have:Group.IsSolvable H:=zd;have:Group.IsSolvable (H×Multiplicative (ZMod 2)):=inferInstance;exact Group.isSolvable_of_isSolvable_injective (f:=zq.symm.toMonoidHom) zq.symm.injective);have zn:¬ p∣Nat.card L:=by
   rw[<-Bc zq.toEquiv,EG];have h2:Nat.card (Multiplicative (ZMod 2))=2:=(by rw[Au];simp);rw[h2];intro zy;rcases zj.dvd_mul.mp zy with h1 | h2'
   . exact zb h1
   . exact ze ((CL zj DI).mp h2')
  have zu:Qw L:=QT zq (WX za);exact ⟨L,zs,zn,zu,zh,zk,zo⟩
lemma We {p:ℕ} [Fact p.Prime]
  {G:Type} [Group G] [Fintype G] [Group.IsSolvable G] (ze:Qw G)
  {W:Type} [AddCommGroup W] [Module (ZMod p) W] [Finite W] [Nontrivial W] (za:G→*(W≃ₗ[ZMod p] W)) (V:Subgroup G) [V.Normal] (zb:V<=za.ker) (zc:¬ p∣Nat.card (G ⧸ V)) (zd:∀ U:Submodule (ZMod p) W,(∀ g:G,∀ x∈U,za g x∈U)->U=⊥\/U=⊤) (zf:∀ (x:W),x≠0->∀ (a:(ZMod p)ˣ),∃ g:G,za g x=(a:ZMod p)•x) : ∃ (n:ℕ) (_:0 < n) (H:Subgroup (Aa (Fin n) (ZMod p))), Group.IsSolvable H/\ ¬ p∣Nat.card H/\ Qw H/\ (∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈H,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤)/\ (∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈H,g.val.mulVec v=(a:ZMod p)•v):=by
 classical
 have:FiniteDimensional (ZMod p) W:=Module.Finite.of_finite;set n:=Module.finrank (ZMod p) W;have zo:0 < n:=Module.finrank_pos;let b:Module.Basis (Fin n) (ZMod p) W:=Module.finBasis (ZMod p) W;let zt:(W≃ₗ[ZMod p] W)→*Aa (Fin n) (ZMod p):=
  {toFun:=fun e=>
    {val:=LinearMap.toMatrix b b e.toLinearMap
     inv:=LinearMap.toMatrix b b e.symm.toLinearMap
     val_inv:=by
      rw[<-Ct b b b];have zi:e.toLinearMap.comp e.symm.toLinearMap=(LinearMap.id:W→ₗ[ZMod p] W):=
       Ap fun x=>e.apply_symm_apply x
      rw[zi,DB]
     inv_val:=by
      rw[<-Ct b b b];have zi:e.symm.toLinearMap.comp e.toLinearMap=(LinearMap.id:W→ₗ[ZMod p] W):=
       Ap fun x=>e.symm_apply_apply x
      rw[zi,DB] }
   map_one':=by apply A7;ext i j;simp[Dg,BG,DS,eq_comm]
   map_mul':=fun e₁ e₂=>by
    apply A7;change LinearMap.toMatrix b b (e₁.toLinearMap.comp e₂.toLinearMap)=LinearMap.toMatrix b b e₁.toLinearMap*LinearMap.toMatrix b b e₂.toLinearMap
    exact Ct b b b _ _ }
 let φ:G→*Aa (Fin n) (ZMod p):=zt.comp za;have zg:∀ (g:G) (x:W),(φ g).val.mulVec (b.equivFun x)=b.equivFun (za g x):=
  fun g x=>EZ b b (za g).toLinearMap x
 let H:Subgroup (Aa (Fin n) (ZMod p)):=φ.range;have zh:V<=φ.ker:=fun v hv=>by
  rw[Bw,Et,(MonoidHom.mem_ker.mp (zb hv)),BI]
 have zm:Group.IsSolvable H:=(by have eH:G ⧸ φ.ker≃*H:=QuotientGroup.quotientKerEquivRange φ;exact Group.isSolvable_of_isSolvable_injective (f:=eH.symm.toMonoidHom) eH.symm.injective);have zp:Qw H:=
  QT (QuotientGroup.quotientKerEquivRange φ) (Wo φ.ker ze)
 have zk:¬ p∣Nat.card H:=by
  have h1:Nat.card H=Nat.card (G ⧸ φ.ker):=
   Bc (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  have h2:Nat.card (G ⧸ φ.ker)∣Nat.card (G ⧸ V):=(by let qmap:G ⧸ V→*G ⧸ φ.ker:=QuotientGroup.map V φ.ker (MonoidHom.id G) (by simpa using zh);have zq:Function.Surjective qmap:=(by intro y;obtain ⟨g,rfl⟩:=E9 y;exact ⟨QuotientGroup.mk g,rfl⟩);have e:(G ⧸ V) ⧸ qmap.ker≃*G ⧸ φ.ker:=QuotientGroup.quotientKerEquivOfSurjective qmap zq;rw[<-Bc e.toEquiv];exact ET qmap.ker);rw[h1];exact fun hpH=>zc (hpH.trans h2)
 have zl:∀ U:Submodule (ZMod p) (Fin n->ZMod p),(∀ g∈H,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤:=by
  intro U hU;let U':Submodule (ZMod p) W:=U.comap b.equivFun.toLinearMap;have zn:∀ g:G,∀ x∈U',za g x∈U':=by intro g x hx;show b.equivFun (za g x)∈U;rw[<-zg];exact hU (φ g) ⟨g,rfl⟩ _ hx
  rcases zd U' zn with hbot | htop
  .
   left;rw[BY];intro v hv;have zj:b.equivFun.symm v∈U':=by show b.equivFun (b.equivFun.symm v)∈U;rw[b.equivFun.apply_symm_apply];exact hv
   rw[hbot,Cr] at zj;have h0:=Ah b.equivFun zj;rw[b.equivFun.apply_symm_apply,Bn] at h0;exact h0
  . right;rw[Cg];intro v;have zj:b.equivFun.symm v∈U':=htop ▸ BW;change b.equivFun (b.equivFun.symm v)∈U at zj;rwa[b.equivFun.apply_symm_apply] at zj
 have zr:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ),∃ g∈H,g.val.mulVec v=(a:ZMod p)•v:=by
  intro v hv a;have zs:b.equivFun.symm v≠0:=by intro h;have h0:=Ah b.equivFun h;rw[b.equivFun.apply_symm_apply,Bn] at h0;exact hv h0
  obtain ⟨g,hg⟩:=zf (b.equivFun.symm v) zs a;refine ⟨φ g,⟨g,rfl⟩,?_⟩
  calc (φ g).val.mulVec v=(φ g).val.mulVec (b.equivFun (b.equivFun.symm v)):=by rw[b.equivFun.apply_symm_apply]
  _ = b.equivFun (za g (b.equivFun.symm v)):=zg g _
  _ = b.equivFun ((a:ZMod p)•b.equivFun.symm v):=by rw[hg]
  _ = (a:ZMod p)•v:=by rw[Bd,b.equivFun.apply_symm_apply]
 exact ⟨n,zo,H,zm,zk,zp,zl,zr⟩
lemma Wx {p:ℕ} [Fact p.Prime] (zd:p≠2)
  {G:Type} [Group G] [Fintype G] [Group.IsSolvable G] (ze:Qw G) (V:Subgroup G) [hV_norm:V.Normal] (zc:∀ x∈V,∀ y∈V,x*y=y*x) (zf:∀ N:Subgroup G,N.Normal->N<=V->N=⊥\/N=V) (zb:¬ p∣Nat.card (G ⧸ V)) (W:Type) [AddCommGroup W] [Module (ZMod p) W] [Finite W] [Nontrivial W] (eW:V ≃ W) (za:∀ a b:V,eW (a*b)=eW a+eW b) : ∃ (n:ℕ) (_:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))), Group.IsSolvable L/\ ¬ p∣Nat.card L/\ Qw L/\ Qd n p∈L/\ (∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤)/\ (∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v):=by
 classical
 have zq:p.Prime:=Fact.out;have zj:eW 1=0:=(by have h:=za 1 1;rw[AK] at h;simpa using Ah (· - eW 1) h.symm);have zm:∀ a:V,eW a⁻¹=-eW a:=fun a=>by
  have h:=za a a⁻¹;rw[By,zj] at h;exact eq_neg_of_add_eq_zero_right h.symm
 have zk:∀ (n:ℕ) (a:V),eW (a ^ n)=n•eW a:=fun n a=>by
  induction n with
  | zero=>simp[zj]
  | succ k ih=>rw[DK,za,ih,succ_nsmul]
 have zl:∀ (k:ℤ) (a:V),eW (a ^ k)=k•eW a:=fun k a=>by
  cases k with
  | ofNat n=>simpa using zk n a
  | negSucc n=>
   rw[zpow_negSucc,zm,zk,negSucc_zsmul]
 let zn (g:G):W≃ₗ[ZMod p] W:=
  {toFun:=fun x=>eW ⟨g*(eW.symm x).1*g⁻¹,hV_norm.conj_mem _ (eW.symm x).2 g⟩
   invFun:=fun x=>eW ⟨g⁻¹*(eW.symm x).1*g,by simpa using hV_norm.conj_mem _ (eW.symm x).2 g⁻¹⟩
   left_inv:=fun x=>by
    dsimp only;rw[eW.symm_apply_apply];have h:(⟨g⁻¹*(g*(eW.symm x).1*g⁻¹)*g,by simpa using hV_norm.conj_mem _ (hV_norm.conj_mem _ (eW.symm x).2 g) g⁻¹⟩:V)=eW.symm x:=
     Ae (by group)
    rw[h,eW.apply_symm_apply]
   right_inv:=fun x=>by
    dsimp only;rw[eW.symm_apply_apply];have h:(⟨g*(g⁻¹*(eW.symm x).1*g)*g⁻¹,hV_norm.conj_mem _ (by simpa using hV_norm.conj_mem _ (eW.symm x).2 g⁻¹) g⟩:V)=eW.symm x:=
     Ae (by group)
    rw[h,eW.apply_symm_apply]
   map_add':=fun x y=>by
    have zr:eW.symm (x+y)=eW.symm x*eW.symm y:=
     eW.injective (by rw[eW.apply_symm_apply,za,eW.apply_symm_apply,eW.apply_symm_apply])
    rw[<-za];congr 1;apply Ae;rw[zr];change g*((eW.symm x).1*(eW.symm y).1)*g⁻¹=(g*(eW.symm x).1*g⁻¹)*(g*(eW.symm y).1*g⁻¹);group
   map_smul':=fun c x=>by
    rcases ZMod.intCast_surjective c with ⟨k,rfl⟩
    have zx:∀ (y:W),(k:ZMod p)•y=k•y:=fun y=>by rw[<-Int.cast_smul_eq_zsmul (ZMod p)]
    simp only[DE];rw[zx,zx];have zr:eW.symm (k•x)=(eW.symm x) ^ k:=
     eW.injective (by rw[eW.apply_symm_apply,zl,eW.apply_symm_apply])
    rw[<-zl];congr 1;apply Ae;rw[zr];change g*((eW.symm x).1 ^ k)*g⁻¹=(g*(eW.symm x).1*g⁻¹) ^ k
    rw[conj_zpow] }
 let zg:G→*(W≃ₗ[ZMod p] W):=
  MonoidHom.mk' zn fun g₁ g₂=>by
   apply Em;intro x;rw[LinearEquiv.mul_apply];dsimp only[zn,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk];rw[eW.symm_apply_apply];congr 1;apply Ae;group
 have zp:V<=zg.ker:=by
  intro v hv;rw[Bw];apply Em;intro x;change eW ⟨v*(eW.symm x).1*v⁻¹,hV_norm.conj_mem _ (eW.symm x).2 v⟩=x;have h1:(⟨v*(eW.symm x).1*v⁻¹,hV_norm.conj_mem _ (eW.symm x).2 v⟩:V)=eW.symm x:=by apply Ae;change v*(eW.symm x).1*v⁻¹=(eW.symm x).1;rw[zc v hv (eW.symm x).1 (eW.symm x).2];group
  rw[h1,eW.apply_symm_apply]
 have zC:∀ U:Submodule (ZMod p) W,(∀ g:G,∀ x∈U,zg g x∈U)->U=⊥\/U=⊤:=by
  intro U hU;let N:Subgroup G:=
   {carrier:={v | ∃ hv:v∈V,eW ⟨v,hv⟩∈U}
    mul_mem':=fun {x y} ⟨hxV,hxU⟩ ⟨hyV,hyU⟩=>
     ⟨V.mul_mem hxV hyV,by
      have h:=U.add_mem hxU hyU
      rwa[<-za] at h⟩
    one_mem':=⟨V.one_mem,by change eW 1∈U;rw[zj];exact U.zero_mem⟩
    inv_mem':=fun {x} ⟨hxV,hxU⟩=>
     ⟨V.inv_mem hxV,by
      have h:=U.neg_mem hxU
      rwa[<-zm] at h⟩ }
  have zz:N.Normal:=⟨fun x ⟨hxV,hxU⟩ g=>
   ⟨hV_norm.conj_mem x hxV g,by
    have h:=hU g (eW ⟨x,hxV⟩) hxU
    simpa[zg,zn] using h⟩⟩
  rcases zf N zz (fun _ h=>h.1) with hbot | htop
  . left;rw[BY];intro x hx;have zo:(eW.symm x).1∈N:=⟨(eW.symm x).2,by rwa[eW.apply_symm_apply]⟩;rw[hbot,CG] at zo;have:eW.symm x=1:=Ae zo;rw[<-eW.apply_symm_apply x,this,zj]
  .
   right;rw[Cg];intro x;have zo:(eW.symm x).1∈N:=by rw[htop];exact (eW.symm x).2
   obtain ⟨_,zV⟩:=zo;simpa[eW.apply_symm_apply] using zV
 have zQ:∀ (x:W),x≠0->∀ (a:(ZMod p)ˣ),∃ g:G,zg g x=(a:ZMod p)•x:=by
  intro x _ a;set y:V:=eW.symm x;set B:=∏ q∈(Nat.card G).primeFactors.erase p,q;have zR:p.Coprime B:=by rw[Cb];by_contra hne;obtain ⟨q,zh,zi⟩:=B5 hne;have zD:q=p:=(CL zh zq).mp (zi.trans (CI p B));have zy:q∣B:=zi.trans (Cs p B);rw[Prime.dvd_finsetProd_iff zh.prime] at zy;obtain ⟨r,hr,zE⟩:=zy;have zs:r.Prime:=(Nat.mem_primeFactors.mp (Finset.mem_erase.mp hr).2).1;have zP:q=r:=(CL zh zs).mp zE;exact (Finset.mem_erase.mp hr).1 (zP.symm.trans zD)
  obtain ⟨m,zO,zW⟩:=Er zR (a:ZMod p).val 1;have zS:(Nat.card G).Coprime m:=by
   rw[Cb];by_contra hne;obtain ⟨q,zh,zi⟩:=B5 hne;have zT:q∣Nat.card G:=zi.trans (CI _ _);have zM:q∣m:=zi.trans (Cs _ _);by_cases zD:q=p
   .
    subst q;have zN:(a:ZMod p).val % p=0:=(by have:m % p=(a:ZMod p).val % p:=zO;rw[B7] at zM;omega);have zI:(a:ZMod p).val < p:=ZMod.val_lt _;rw[A9 zI] at zN;have:(a:ZMod p)=0:=by rw[<-CP (a:ZMod p),zN,Nat.cast_zero]
    exact a.ne_zero this
   .
    have zU:q∈(Nat.card G).primeFactors.erase p:=
     Finset.mem_erase.mpr ⟨zD,Nat.mem_primeFactors.mpr ⟨zh,zT,Nat.card_pos.ne'⟩⟩
    have zy:q∣B:=Ej _ zU;have h1:m % q=1 % q:=zW.of_dvd zy;rw[B7] at zM;have zY:1 % q=1:=A9 zh.one_lt;omega
  obtain ⟨g,hg⟩:=isConj_iff.mp (ze y.1 m zS);refine ⟨g,?_⟩;have zJ:(m:ZMod p)=(a:ZMod p):=(by rw[<-CP (a:ZMod p),E8];exact zO);rw[<-zJ,Nat.cast_smul_eq_nsmul (ZMod p) m x];change eW ⟨g*(eW.symm x).1*g⁻¹,hV_norm.conj_mem _ (eW.symm x).2 g⟩=m•x;have h1:(⟨g*(eW.symm x).1*g⁻¹,hV_norm.conj_mem _ (eW.symm x).2 g⟩:V)=y ^ m:=
   Ae hg
  rw[h1,zk,eW.apply_symm_apply]
 obtain ⟨n,zF,H,zA,zt,zG,zu,zK⟩:=
  We ze zg V zp zb zC zQ
 obtain ⟨L,zB,zv,zH,zX,zw,zL⟩:=
  Yy zd H zA zt zG zu zK
 exact ⟨n,zF,L,zB,zv,zH,zX,zw,zL⟩
lemma WY {p:ℕ} [Fact p.Prime] (zd:7<=p)
  {G:Type} [Group G] [Fintype G] [Group.IsSolvable G] (za:Qw G) (zb:p∣Nat.card G) (zc:∀ (G':Type) [Group G'] [Fintype G'] [Group.IsSolvable G'], Nat.card G' < Nat.card G->Qw G'-> ∀ q:ℕ,q.Prime->q∣Nat.card G'->q=2\/q=3\/q=5) : ∃ (n:ℕ) (_:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))), Group.IsSolvable L/\ ¬ p∣Nat.card L/\ Qw L/\ Qd n p∈L/\ (∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤)/\ (∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v):=by
 classical
 have ze:p.Prime:=Fact.out;have zw:p≠2:=by omega
 have zF:Nontrivial G:=(by have zJ:1 < Nat.card G:=lt_of_lt_of_le ze.one_lt (AP CD zb);exact Finite.one_lt_card_iff_nontrivial.mp zJ);let P:ℕ->Prop:=fun k=>∃ N:Subgroup G,N.Normal/\N≠⊥/\Nat.card N=k;have zx:∃ k,P k:=⟨Nat.card G,⊤,inferInstance,Fa,Bc Subgroup.topEquiv.toEquiv⟩;obtain ⟨V,zl,zn,zu⟩:=EF zx;have zk:∀ N:Subgroup G,N.Normal->N<=V->N=⊥\/N=V:=by
  intro N zv zN;by_cases zt:N=⊥
  . left;exact zt
  . right;have zK:Nat.card V<=Nat.card N:=(by rw[zu];exact Nat.find_min' zx ⟨N,zv,zt,rfl⟩);exact E4 zN zK
 have zf:∀ x∈V,∀ y∈V,x*y=y*x:=by
  have zm:(⁅V,V⁆:Subgroup G).Normal:=DY V V;have zo:⁅V,V⁆<=V:=E5 V V;rcases zk ⁅V,V⁆ zm zo with zr | htop
  .
   intro x hx y hy;have zy:x*y*x⁻¹*y⁻¹∈⁅V,V⁆:=Dj hx hy;rw[zr,CG] at zy
   calc x*y=(x*y*x⁻¹*y⁻¹)*(y*x):=by group
   _ = y*x:=by rw[zy,AA]
  .
   exfalso;have zz:commutator V=⊤:=(by apply Subgroup.map_injective V.subtype_injective;rw[<-Dt,Dq];change (⁅(⊤:Subgroup V),(⊤:Subgroup V)⁆).map V.subtype=V;rw[Subgroup.map_commutator,<-Dt,Dq,htop]);have zL:∀ k:ℕ,derivedSeries V k=⊤:=by
    intro k;induction k with
    | zero=>exact derivedSeries_zero V
    | succ k ih=>rw[derivedSeries_succ,ih];exact zz
   obtain ⟨k,hk⟩:=(inferInstance:Group.IsSolvable V).solvable;rw[zL k] at hk;have zi:Nontrivial V:=(CW V).mpr zn;exact Fa hk
 have zA:Nat.card (G ⧸ V) < Nat.card G:=(by have h1:=BX V;have zM:1 < Nat.card V:=(DA V).mpr zn;have zG:0 < V.index:=CM Subgroup.index_ne_zero_of_finite;change V.index < Nat.card G;nlinarith);have zg:¬ p∣Nat.card (G ⧸ V):=(by intro zI;have zO:=zc (G ⧸ V) zA (Wo V za) p ze zI;omega);have zp:p∣Nat.card V:=(by have h1:Nat.card V*Nat.card (G ⧸ V)=Nat.card G:=BX V;rw[<-h1] at zb;exact (ze.dvd_mul.mp zb).resolve_right zg);have zj:∀ v∈V,v ^ p=1:=by
  let Vp:Subgroup G:=
   {carrier:={v | v∈V/\v ^ p=1}
    mul_mem':=fun {a b} ⟨haV,hap⟩ ⟨hbV,hbp⟩=>
     ⟨V.mul_mem haV hbV,by
      rw[Commute.mul_pow (zf a haV b hbV),hap,hbp,AA]⟩
    one_mem':=⟨V.one_mem,B8 p⟩
    inv_mem':=fun {a} ⟨haV,hap⟩=>⟨V.inv_mem haV,by rw[E7,hap,inv_one]⟩ }
  have zq:Vp.Normal:=⟨fun x ⟨hxV,hxp⟩ g=>
   ⟨zl.conj_mem x hxV g,by rw[conj_pow,hxp,AK,By]⟩⟩
  have zB:Vp<=V:=fun _ h=>h.1;have zC:Vp≠⊥:=by
   obtain ⟨⟨v,hvV⟩,hv_ord⟩:=DD (G:=V) p zp;intro zr;have zD:v ^ p=1:=by have h1:(⟨v,hvV⟩:V) ^ p=1:=hv_ord ▸ BE _;exact Ah Subtype.val h1
   have zs:v∈Vp:=⟨hvV,zD⟩;rw[zr,CG] at zs;have:(⟨v,hvV⟩:V)=1:=Ae zs;rw[this,orderOf_one] at hv_ord;exact ze.ne_one hv_ord.symm
  have zE:Vp=V:=(zk Vp zq zB).resolve_left zC;intro v hv;have:v∈Vp:=zE ▸ hv;exact this.2
 let zh:AddCommGroup (Additive V):=
  {(inferInstance:AddGroup (Additive V)) with
   add_comm:=fun a b=>Additive.toMul.injective (Ae (zf _ (Additive.toMul a).2 _ (Additive.toMul b).2)) }
 let zH:@Module (ZMod p) (Additive V) _ zh.toAddCommMonoid:=
  @AddCommGroup.zmodModule p (Additive V) zh fun x=>by
   change Additive.ofMul (Additive.toMul x ^ p)=0;have h1:Additive.toMul x ^ p=1:=Ae (zj _ (Additive.toMul x).2);rw[h1];rfl
 have zi:Nontrivial (Additive V):=(by have:Nontrivial V:=(CW V).mpr zn;exact Additive.ofMul.surjective.nontrivial);exact @Wx p _ zw G _ _ _ za V zl zf zk zg
  (Additive V) zh zH inferInstance zi Additive.ofMul (fun _ _=>rfl)
end MinimalCounterexample
section BaseChangeDescent
variable {p:ℕ} [Fact p.Prime]
abbrev Qa (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)
lemma QO {x:Qa p} (hx:x≠0) : ∃ φ:Qa p→ₗ[ZMod p] ZMod p,φ x≠0:=by
 let B:=Module.Basis.ofVectorSpace (ZMod p) (Qa p);have za:B.repr x≠0:=(by intro h0;exact hx (B.repr.injective (h0.trans (Bn B.repr).symm)));obtain ⟨i,hi⟩:=Finsupp.ne_iff.mp za;exact ⟨(Fh i).comp B.repr.toLinearMap,hi⟩
lemma Ws {m n k:ℕ} (φ:Qa p→ₗ[ZMod p] ZMod p) (A:Matrix (Fin m) (Fin n) (Qa p)) (B:Matrix (Fin n) (Fin k) (ZMod p)) : (A*B.map (algebraMap (ZMod p) (Qa p))).map φ=A.map φ*B:=by
 ext i j;simp only[AZ,Av,Ba];refine Ag rfl fun r _=>?_;rw[Bb,<-Ed,Bd,Am,Bb]
lemma Wt {m n k:ℕ} (φ:Qa p→ₗ[ZMod p] ZMod p) (A:Matrix (Fin m) (Fin n) (ZMod p)) (B:Matrix (Fin n) (Fin k) (Qa p)) : (A.map (algebraMap (ZMod p) (Qa p))*B).map φ=A*B.map φ:=by
 ext i j;simp only[AZ,Av,Ba];refine Ag rfl fun r _=>?_;rw[<-Ed,Bd,Am]
lemma WZ {n:ℕ} {ι:Type*} (M:ι->Matrix (Fin n) (Fin n) (ZMod p)) (za:∀ A B:Matrix (Fin n) (Fin n) (ZMod p), (∀ i,A*M i=M i*A)->(∀ i,B*M i=M i*B)->A*B=B*A) : ∀ A B:Matrix (Fin n) (Fin n) (Qa p), (∀ i,A*(M i).map (algebraMap (ZMod p) (Qa p))=(M i).map (algebraMap (ZMod p) (Qa p))*A)-> (∀ i,B*(M i).map (algebraMap (ZMod p) (Qa p))=(M i).map (algebraMap (ZMod p) (Qa p))*B)-> A*B=B*A:=by
 classical
 let zb:=Module.Basis.ofVectorSpace (ZMod p) (Qa p);have zc:∀ X:Matrix (Fin n) (Fin n) (Qa p),(∀ i,X*(M i).map (algebraMap (ZMod p) (Qa p))=(M i).map (algebraMap (ZMod p) (Qa p))*X)->∃ (S:Finset (Module.Basis.ofVectorSpaceIndex (ZMod p) (Qa p)))
    (C:Module.Basis.ofVectorSpaceIndex (ZMod p) (Qa p)->Matrix (Fin n) (Fin n) (ZMod p)),
    (∀ s∈S,∀ i,C s*M i=M i*C s)/\
    X=∑ s∈S,zb s•(C s).map (algebraMap (ZMod p) (Qa p)):=by
  intro X hX;let S:=Finset.univ.biUnion fun a:Fin n=>
   Finset.univ.biUnion fun b:Fin n=>(zb.repr (X a b)).support
  let C:Module.Basis.ofVectorSpaceIndex (ZMod p) (Qa p)->Matrix (Fin n) (Fin n) (ZMod p):=
   fun s=>X.map ((Fh s).comp zb.repr.toLinearMap)
  refine ⟨S,C,?_,?_⟩
  . intro s _ i;have h:=Ah (Matrix.map · ((Fh s).comp zb.repr.toLinearMap)) (hX i);rwa[Ws,Wt] at h
  .
   ext a b;simp only[BR,A2,AZ,Am,C];have zd:∑ s∈(zb.repr (X a b)).support,(zb.repr (X a b) s)•zb s=X a b:=by
    have:=zb.linearCombination_repr (X a b)
    rwa[Finsupp.linearCombination_apply,Finsupp.sum] at this
   have ze:(zb.repr (X a b)).support⊆S:=(by intro s hs;exact Finset.mem_biUnion.mpr ⟨a,Ai _,Finset.mem_biUnion.mpr ⟨b,Ai _,hs⟩⟩)
   rw[D6 ze (fun s _ hs=>by
    have h0:zb.repr (X a b) s=0:=Finsupp.notMem_support_iff.mp hs
    simp[h0])] at zd
   conv_lhs=>rw[<-zd]
   refine Ag rfl fun s _=>?_;rw[Bb,Ed];rfl
 intro A B hA hB;obtain ⟨SA,CA,zf,rfl⟩:=zc A hA;obtain ⟨SB,CB,zg,rfl⟩:=zc B hB;rw[Bo,Bo];simp_rw[A6]
 conv_rhs=>rw[AY]
 refine Ag rfl fun s hs=>?_;refine Ag rfl fun t ht=>?_;rw[Ar,Ao,Ar,Ao,smul_comm];congr 2;rw[<-Aq,<-Aq,za (CA s) (CB t) (zf s hs) (zg t ht)]
lemma Wy {m n:ℕ} {ι:Type*} (A:ι->Matrix (Fin m) (Fin m) (ZMod p)) (B:ι->Matrix (Fin n) (Fin n) (ZMod p)) (T:Matrix (Fin m) (Fin n) (Qa p)) (za:T≠0) (hT:∀ i,T*(B i).map (algebraMap (ZMod p) (Qa p))= (A i).map (algebraMap (ZMod p) (Qa p))*T) : ∃ T₀:Matrix (Fin m) (Fin n) (ZMod p),T₀≠0/\∀ i,T₀*B i=A i*T₀:=by
 have zb:∃ a b,T a b≠0:=(by by_contra hall;push Not at hall;exact za (Ff hall));obtain ⟨a,b,zc⟩:=zb;obtain ⟨φ,zd⟩:=QO zc;refine ⟨T.map φ,?_,?_⟩
 .
  intro h0
  have:=Ah (fun M:Matrix (Fin m) (Fin n) (ZMod p)=>M a b) h0
  simp[zd] at this
 . intro i;have h:=Ah (Matrix.map · φ) (hT i);rwa[Ws,Wt] at h
lemma W7 {n:ℕ} {ι:Type*} (M:ι->Matrix (Fin n) (Fin n) (ZMod p)) (B:Matrix (Fin n) (Fin n) (Qa p)) (za:B≠0) (hB:∀ i,((M i).map (algebraMap (ZMod p) (Qa p)))ᵀ*B* (M i).map (algebraMap (ZMod p) (Qa p))=B) : ∃ B₀:Matrix (Fin n) (Fin n) (ZMod p),B₀≠0/\∀ i,(M i)ᵀ*B₀*M i=B₀:=by
 have zb:∃ a b,B a b≠0:=(by by_contra hall;push Not at hall;exact za (Ff hall));obtain ⟨a,b,zd⟩:=zb;obtain ⟨φ,ze⟩:=QO zd;refine ⟨B.map φ,?_,?_⟩
 .
  intro h0
  have:=Ah (fun X:Matrix (Fin n) (Fin n) (ZMod p)=>X a b) h0
  simp[ze] at this
 . intro i;have h:=Ah (Matrix.map · φ) (hB i);have zc:((M i).map (algebraMap (ZMod p) (Qa p)))ᵀ=(M i)ᵀ.map (algebraMap (ZMod p) (Qa p)):=(by ext a b;rfl);rw[zc,Ws,Wt] at h;exact h
end BaseChangeDescent
section DiagonalizationAndBrTr
variable {p:ℕ} [Fact p.Prime]
lemma Qy {N:ℕ} (zb:0 < N) (za:¬ p∣N) : Nat.card (Ab N (Qa p))=N:=by
 have:NeZero N:=⟨zb.ne'⟩;have zc:(N:ZMod p)≠0:=fun h=>za ((At N p).mp h);have:NeZero (N:ZMod p):=⟨zc⟩;have:NeZero (N:Qa p):=
  ⟨by
   rw[<-DO (algebraMap (ZMod p) (Qa p))]
   exact fun h=>zc ((algebraMap (ZMod p) (Qa p)).injective (by simpa using h))⟩
 have:HasEnoughRootsOfUnity (Qa p) N:=inferInstance;obtain ⟨ζ,zd⟩:=HasEnoughRootsOfUnity.exists_primitiveRoot (Qa p) N;exact zd.card_rootsOfUnity
noncomputable def Qx {N:ℕ} (hN_pos:0 < N) (hNp:¬ p∣N) : Fintype (Ab N (Qa p)):=by
 haveI:Finite (Ab N (Qa p)):=
  C8 (by rw[Qy hN_pos hNp];exact hN_pos.ne')
 exact Fintype.ofFinite _
noncomputable def WA {N:ℕ} (hN_pos:0 < N):Fintype (Ab N ℂ):=by
 haveI:NeZero N:=⟨hN_pos.ne'⟩;haveI:Finite (Ab N ℂ):=
  C8 (by rw[Complex.card_rootsOfUnity N];exact hN_pos.ne')
 exact Fintype.ofFinite _
lemma WI {N:ℕ} (za:0 < N) (zb:¬ p∣N) : Nonempty (Ab N (Qa p)≃*Ab N ℂ):=by
 have:NeZero N:=⟨za.ne'⟩;have zd:Nat.card (Ab N (Qa p))=N:=Qy za zb;have ze:Nat.card (Ab N ℂ)=N:=Complex.card_rootsOfUnity N;have:Finite (Ab N (Qa p)):=
  C8 (by rw[zd];exact za.ne')
 have:Finite (Ab N ℂ):=
  C8 (by rw[ze];exact za.ne')
 have zc:∀ (A:Type) [Group A] [Finite A] [IsCyclic A],Nat.card A=N->Nonempty (Multiplicative (ZMod N)≃*A):=by
  intro A _ _ _ zf;obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=A);have zh:orderOf g=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers hg,zf]
  have zo:g ^ N=1:=zh ▸ BE g;let f:Multiplicative (ZMod N)→*A:=
   {toFun:=fun x=>g ^ (Multiplicative.toAdd x).val
    map_one':=by simp
    map_mul':=fun x y=>by
     change g ^ (Multiplicative.toAdd x+Multiplicative.toAdd y).val=g ^ (Multiplicative.toAdd x).val*g ^ (Multiplicative.toAdd y).val;rw[ZMod.val_add,<-CT]
     conv_rhs=>rw[<-Cd ((Multiplicative.toAdd x).val+(Multiplicative.toAdd y).val) N]
     rw[CT,Cz,zo,B8,AA] }
  have zj:Function.Injective f:=by
   intro x y zk;change g ^ (Multiplicative.toAdd x).val=g ^ (Multiplicative.toAdd y).val at zk;have zi:(Multiplicative.toAdd x).val ≡ (Multiplicative.toAdd y).val [MOD orderOf g]:=
    pow_eq_pow_iff_modEq.mp zk
   rw[zh] at zi;have zl:(Multiplicative.toAdd x).val < N:=ZMod.val_lt _;have zm:(Multiplicative.toAdd y).val < N:=ZMod.val_lt _;have zn:(Multiplicative.toAdd x).val=(Multiplicative.toAdd y).val:=(by simpa[Nat.ModEq,A9 zl,A9 zm] using zi);apply Multiplicative.toAdd.injective;exact ZMod.val_injective N zn
  have:Fintype A:=Fintype.ofFinite A;have zg:Fintype.card (Multiplicative (ZMod N))=Fintype.card A:=by rw[<-Au,<-Au,zf];rw[Au];simp
  exact ⟨MulEquiv.ofBijective f ((Ci f).mpr ⟨zj,zg⟩)⟩
 obtain ⟨eK⟩:=zc (Ab N (Qa p)) zd;obtain ⟨eC⟩:=zc (Ab N ℂ) ze;exact ⟨eK.symm.trans eC⟩
def Qq {R:Type*} [CommRing R] {N:ℕ} (h2N:2∣N):Ab N R:=
 ⟨⟨-1,-1,by simp,by simp⟩,by
  rw[mem_rootsOfUnity']
  obtain ⟨k,rfl⟩:=h2N
  simp[Cz]⟩
@[simp] lemma negOneRootOfUnity_coe {R:Type*} [CommRing R] {N:ℕ} (h2N:2∣N) :
 ((Qq (R:=R) h2N:Rˣ):R)=-1:=rfl
lemma WB {N:ℕ} (za:2∣N) (zb:p≠2) (ι:Ab N (Qa p)≃*Ab N ℂ) : ι (Qq za)=Qq za:=by
 have zd:(ι (Qq za))*(ι (Qq za))=1:=(by rw[<-AF];have h1:(Qq (R:=Qa p) za)*(Qq za)=1:=(by ext;simp);rw[h1,BI]);have ze:ι (Qq za)≠1:=by
  intro h;have h1:Qq (R:=Qa p) za=1:=ι.injective (h.trans (BI ι).symm);have h2:(-1:Qa p)=1:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) h1;have zc:(2:Qa p)=0:=by
   have:(1:Qa p)+1=0:=by linear_combination -h2
   simpa[one_add_one_eq_two] using this
  have zf:(2:ZMod p)=0:=(by apply (algebraMap (ZMod p) (Qa p)).injective;rw[C2,Bn];exact zc);have zg:p∣2:=(At 2 p).mp zf;have zk:p<=2:=AP (by decide) zg;have zl:2<=p:=(Fact.out:p.Prime).two_le;exact zb (DP zk zl)
 have zh:(((ι (Qq za):ℂˣ):ℂ)) ^ 2=1:=by
  have:=Ah (fun u:Ab N ℂ=>((u:ℂˣ):ℂ)) zd
  simpa[sq] using this
 have zi:(((ι (Qq za):ℂˣ):ℂ))≠1:=(by intro h;apply ze;ext;exact h);have zj:(((ι (Qq za):ℂˣ):ℂ))=-1:=by
  rcases sq_eq_one_iff.mp zh with h1 | h2
  . exact absurd h1 zi
  . exact h2
 ext;exact zj
noncomputable def Wq {N:ℕ} (hN_pos:0 < N) (hNp:¬ p∣N)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] (T:Module.End (Qa p) V) (hTN:T ^ N=1) : V≃ₗ[Qa p] (∀ ζ:Ab N (Qa p), LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):=by
 classical
 haveI:NeZero N:=⟨hN_pos.ne'⟩;have zg:Nat.card (Ab N (Qa p))=N:=Qy hN_pos hNp;letI:Fintype (Ab N (Qa p)):=Qx hN_pos hNp;have zc:(N:Qa p)≠0:=by
  intro h;have h1:(N:ZMod p)=0:=by apply (algebraMap (ZMod p) (Qa p)).injective;rw[DO,Bn];exact h
  exact hNp ((At N p).mp h1)
 let P:Ab N (Qa p)->Module.End (Qa p) V:=fun ζ=>
  (N:Qa p)⁻¹•∑ k:Fin N,(((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)•T ^ k.val
 have zx:∀ ζ:Ab N (Qa p),T∘ₗP ζ=((ζ:(Qa p)ˣ):Qa p)•P ζ:=by
  intro ζ;have zf:(((ζ:(Qa p)ˣ):Qa p)) ^ N=1:=(mem_rootsOfUnity' N _).mp ζ.2;have za:(((ζ:(Qa p)ˣ):Qa p))≠0:=DH _;ext v;simp only[P,BZ,AU,CV,Bd,Ba];rw[smul_comm];congr 1;rw[BC];let e:Fin N ≃ Fin N:=
   {toFun:=fun k=>⟨(k.val+1) % N,DF _ hN_pos⟩
    invFun:=fun k=>⟨(k.val+N - 1) % N,DF _ hN_pos⟩
    left_inv:=fun k=>by
     ext;dsimp;have hk:=k.isLt;by_cases h:k.val+1 < N
     . rw[A9 h,show k.val+1+N - 1=k.val+N by omega,Nat.add_mod_right,A9 hk]
     .
      have zh:k.val+1=N:=by omega
      have zd:N - 1 < N:=Nat.sub_lt hN_pos Nat.one_pos;rw[zh,Ds,zero_add,A9 zd];omega
    right_inv:=fun k=>by
     ext;dsimp;have hk:=k.isLt;by_cases h:k.val=0
     . have zd:N - 1 < N:=Nat.sub_lt hN_pos Nat.one_pos;rw[h,zero_add,A9 zd,Dk hN_pos,Ds]
     .
      have zd:k.val - 1 < N:=by omega
      rw[show k.val+N - 1=(k.val - 1)+N by omega,Nat.add_mod_right,A9 zd,Dk (CM h),A9 hk] }
  refine AO e _ _ fun k=>?_;have hk:=k.isLt;change (((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)•T ((T ^ k.val) v)=(((ζ:(Qa p)ˣ):Qa p))•((((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ ((k.val+1) % N))•(T ^ ((k.val+1) % N)) v);rw[AR];have zj:T ((T ^ k.val) v)=(T ^ (k.val+1)) v:=(by rw[BA];rfl);rw[zj];by_cases h:k.val+1 < N
  . rw[A9 h];congr 1;rw[BA,<-Ad,mul_inv_cancel₀ za,AA]
  .
   have zh:k.val+1=N:=by omega
   rw[zh,Ds,D7,AK,D7,hTN];have zr:(((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)=((ζ:(Qa p)ˣ):Qa p):=by apply mul_right_cancel₀ (pow_ne_zero k.val za);rw[<-CC,inv_mul_cancel₀ za,B8,<-BA,zh,zf]
   rw[zr]
 have zk:∀ (ζ:Ab N (Qa p)) (v:V),P ζ v∈LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id):=(by intro ζ v;simp only[Bf,BU,AU,Br];have h1:=BV (zx ζ) v;simp only[BZ,AU] at h1;rw[h1,Cx]);have zl:∀ v:V,∑ ζ:Ab N (Qa p),P ζ v=v:=by
  intro v;simp only[P,AU,CV,<-BC];rw[AY];have zm:∀ k:Fin N,(∑ ζ:Ab N (Qa p),(((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)•(T ^ k.val) v)=if k=⟨0,hN_pos⟩ then (N:Qa p)•v else 0:=by
   intro k;rw[<-DU];split_ifs with hk0
   . subst hk0;simp only[D7,Cm,BS,nsmul_eq_mul,AK,<- Au,zg,Module.End.one_apply]
   .
    have zs:k.val≠0:=fun h=>hk0 (A4 h);have zb:∑ ζ:Ab N (Qa p),(((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)=0:=by
     obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=Ab N (Qa p));have zt:orderOf g=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers hg,zg]
     have zn:(((g:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)≠1:=by
      intro h1;have zy:g ^ k.val=1:=by
       ext;have h2:(((g:(Qa p)ˣ):Qa p) ^ k.val)⁻¹=1:=by simpa[E7] using h1
       simpa using inv_eq_one.mp h2
      have zu:N∣k.val:=by
       have:=Bl zy
       rwa[zt] at this
      have zC:=AP (CM zs) zu;omega
     set S:=∑ ζ:Ab N (Qa p),(((ζ:(Qa p)ˣ):Qa p)⁻¹ ^ k.val);have zv:(((g:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)*S=S:=by rw[A6];refine DC (fun ζ=>g*ζ) (Group.mulLeft_bijective g) _ _ fun ζ=>?_;simp only[BB,De,Dm,CC];ring
     have:((((g:(Qa p)ˣ):Qa p)⁻¹ ^ k.val) - 1)*S=0:=by linear_combination zv
     exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr zn)
    rw[zb,Dl]
  simp_rw[zm];rw[A8 Finset.univ (⟨0,hN_pos⟩:Fin N)];simp only[Ai,↓reduceIte,AR,inv_mul_cancel₀ zc,Bx]
 have ze:∀ (ω ζ:Ab N (Qa p))
   (v:LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)),
   P ω v.1=if ω=ζ then v.1 else 0:=by
  intro ω ζ v;have zj:T v.1=((ζ:(Qa p)ˣ):Qa p)•v.1:=by have hv:=v.2;rw[Bf,BU,AU,Br,CE] at hv;exact hv
  have zo:∀ k:ℕ,(T ^ k) v.1=(((ζ:(Qa p)ˣ):Qa p) ^ k)•v.1:=by
   intro k;induction k with
   | zero=>simp
   | succ k ih=>
    rw[BA,Module.End.mul_apply,ih,Bd,zj,AR,BA,Bb]
  simp only[P,AU,CV,zo,AR,<-DU];split_ifs with hωζ
  . subst hωζ;have zp:∀ k:Fin N,(((ω:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)*(((ω:(Qa p)ˣ):Qa p) ^ k.val)=1:=(by intro k;rw[<-CC,inv_mul_cancel₀ (DH _),B8]);simp_rw[zp];simp[inv_mul_cancel₀ zc]
  .
   set r:Qa p:=((ω:(Qa p)ˣ):Qa p)⁻¹*((ζ:(Qa p)ˣ):Qa p);have zq:r≠1:=by
    intro zB;apply hωζ;ext;have:((ζ:(Qa p)ˣ):Qa p)=((ω:(Qa p)ˣ):Qa p):=by
     have:=Ah (fun x=>((ω:(Qa p)ˣ):Qa p)*x) zB
     simpa[r,mul_inv_cancel_left₀ (DH _)] using this
    exact this.symm
   have zz:r ^ N=1:=(by have zw:(((ω:(Qa p)ˣ):Qa p)) ^ N=1:=(mem_rootsOfUnity' N _).mp ω.2;have zf:(((ζ:(Qa p)ˣ):Qa p)) ^ N=1:=(mem_rootsOfUnity' N _).mp ζ.2;rw[CC,E7,zw,zf,inv_one,AA]);have zb:∑ k:Fin N,(((ω:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)*(((ζ:(Qa p)ˣ):Qa p) ^ k.val)=0:=(by have zA:∑ k:Fin N,(((ω:(Qa p)ˣ):Qa p)⁻¹ ^ k.val)*(((ζ:(Qa p)ˣ):Qa p) ^ k.val)=∑ k∈Finset.range N,r ^ k:=(by rw[<-Fk (fun k=>r ^ k) N];refine Ag rfl fun k _=>?_;rw[<-CC]);rw[zA];have zi:=mul_geom_sum r N;rw[zz,Cx] at zi;exact (mul_eq_zero.mp zi).resolve_left (sub_ne_zero.mpr zq));rw[zb,AS,Dl]
 refine LinearEquiv.ofLinearMap
  {toFun:=fun v ζ=>⟨P ζ v,zk ζ v⟩
   map_add':=fun u v=>by ext ζ;simp
   map_smul':=fun c v=>by ext ζ;simp }
  {toFun:=fun f=>∑ ζ:Ab N (Qa p),(f ζ).1
   map_add':=fun f g=>by simp[Bt]
   map_smul':=fun c f=>by simp[BC] }
  ?_ ?_
 . apply Ap;intro f;funext ζ;apply Ae;simp only[BZ,LinearMap.coe_mk,AddHom.coe_mk,Br,Ba];simp_rw[ze];simp
 . apply Ap;intro v;exact zl v
lemma QR {N:ℕ} (za:0 < N) (zb:¬ p∣N)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] [FiniteDimensional (Qa p) V] (T:Module.End (Qa p) V) (zc:T ^ N=1) :
  letI:Fintype (Ab N (Qa p)):=Qx za zb
  LinearMap.trace (Qa p) V T=∑ ζ:Ab N (Qa p),(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):Qa p)*((ζ:(Qa p)ˣ):Qa p):=by
 classical
 let:Fintype (Ab N (Qa p)):=Qx za zb;let e:=Wq za zb T zc;let zd:Ab N (Qa p)->Type _:=
  fun ζ=>LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)
 let D:Module.End (Qa p) (∀ ζ:Ab N (Qa p),zd ζ):=
  {toFun:=fun f ζ=>((ζ:(Qa p)ˣ):Qa p)•f ζ
   map_add':=fun f g=>by funext ζ;exact Eq _ _ _
   map_smul':=fun c f=>by
    funext ζ
    exact (smul_comm c ((ζ:(Qa p)ˣ):Qa p) (f ζ)).symm }
 have zi:e.toLinearMap∘ₗT∘ₗe.symm.toLinearMap=D:=by
  apply Ap;intro f;funext ζ;apply Ae;have zo:∀ ω:Ab N (Qa p),T (f ω).1=((ω:(Qa p)ˣ):Qa p)•(f ω).1:=fun ω=>by
   have h1:=(f ω).2;rw[Bf,BU,AU,Br,CE] at h1;exact h1
  have zm:T (e.symm f)=e.symm (D f):=(by change T (∑ ω:Ab N (Qa p),(f ω).1)=∑ ω:Ab N (Qa p),(((ω:(Qa p)ˣ):Qa p)•(f ω)).1;rw[Ba];exact Ag rfl fun ω _=>zo ω);have zn:=Ah (fun x=>(e x ζ).1) zm;simpa[BZ] using zn
 have zp:LinearMap.trace (Qa p) V T=LinearMap.trace (Qa p) _ D:=(by rw[<-zi];exact (LinearMap.trace_conj' T e).symm);rw[zp];have zq:LinearMap.trace (Qa p) _ D=∑ ζ:Ab N (Qa p),LinearMap.trace (Qa p) (zd ζ) (((ζ:(Qa p)ˣ):Qa p)•LinearMap.id):=by
  let ze:∀ ζ:Ab N (Qa p),zd ζ→ₗ[Qa p] (∀ ω,zd ω):=
   fun ζ=>LinearMap.single (Qa p) zd ζ
  let zf:∀ ζ:Ab N (Qa p),(∀ ω,zd ω)→ₗ[Qa p] zd ζ:=
   fun ζ=>LinearMap.proj ζ
  have zg:D=∑ ζ:Ab N (Qa p),(ze ζ)∘ₗ((((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗ(zf ζ)):=by
   apply Ap;intro f;funext ω;simp only[CV,BZ,ze,zf,LinearMap.proj_apply,AU,Br,D];rw[AQ,Ay ω]
   . simp[Ei]
   . intro ζ _ zl;simp[Ei,zl.symm]
   . intro h;exact absurd (Ai ω) h
  rw[zg,Ba];refine Ag rfl fun ζ _=>?_;have zj:=Ah (fun F=>F (ze ζ) ((((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗzf ζ))
   (LinearMap.trace_comp_comm (Qa p) (∀ ω,zd ω) (zd ζ))
  change LinearMap.trace (Qa p) (∀ ω,zd ω) (ze ζ∘ₗ(((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗzf ζ)=LinearMap.trace (Qa p) (zd ζ) (((ζ:(Qa p)ˣ):Qa p)•LinearMap.id);rw[show LinearMap.trace (Qa p) (∀ ω,zd ω) (ze ζ∘ₗ(((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗzf ζ)=LinearMap.trace (Qa p) (zd ζ) (((((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗzf ζ)∘ₗze ζ) from zj];have zk:zf ζ∘ₗze ζ=LinearMap.id:=(by apply Ap;intro x;simp[zf,ze,Ei]);have zh:((((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)∘ₗzf ζ)∘ₗze ζ=((ζ:(Qa p)ˣ):Qa p)•LinearMap.id:=(by rw[LinearMap.comp_assoc,zk,LinearMap.comp_id]);exact Ah (LinearMap.trace (Qa p) (zd ζ)) zh
 rw[zq];refine Ag rfl fun ζ _=>?_;rw[Bd,LinearMap.trace_id,Am,Bb]
lemma Q3 {N m:ℕ} (za:0 < N) (zb:¬ p∣N) (zc:N.Coprime m)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] (T:Module.End (Qa p) V) (zd:T ^ N=1) (ζ:Ab N (Qa p)) : LinearMap.ker (T ^ m - (((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•LinearMap.id)= LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id):=by
 classical
 have zj:Nat.card (Ab N (Qa p))=N:=Qy za zb;let:Fintype (Ab N (Qa p)):=Qx za zb;have zf:Function.Injective (fun ω:Ab N (Qa p)=>ω ^ m):=
  (powCoprime (by rw[zj];exact zc)).injective
 let e:=Wq za zb T zd;ext v;simp only[Bf,BU,AU,Br,CE];constructor
 .
  intro hv;have ze:v=∑ ω:Ab N (Qa p),(e v ω).1:=(e.symm_apply_apply v).symm;have zk:∀ (k:ℕ) (ω:Ab N (Qa p)),(T ^ k) (e v ω).1=(((ω:(Qa p)ˣ):Qa p) ^ k)•(e v ω).1:=by
   intro k ω;have h1:T (e v ω).1=((ω:(Qa p)ˣ):Qa p)•(e v ω).1:=by have h2:=(e v ω).2;rw[Bf,BU,AU,Br,CE] at h2;exact h2
   induction k with
   | zero=>simp
   | succ k ih=>
    rw[BA,Module.End.mul_apply,ih,Bd,h1,AR,BA,Bb]
  have zl:(T ^ m) v=∑ ω:Ab N (Qa p),((((ω ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•(e v ω)).1:=by
   conv_lhs=>rw[ze]
   rw[Ba];refine Ag rfl fun ω _=>?_;rw[zk m ω];simp
  have zh:(((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•v=∑ ω:Ab N (Qa p),((((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•(e v ω)).1:=by
   conv_lhs=>rw[ze]
   rw[BC];rfl
  have zm:(fun ω=>(((ω ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•e v ω)=(fun ω=>(((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•e v ω):=(by apply e.symm.injective;change (∑ ω,_)=(∑ ω,_);rw[<-zl,<-zh,hv]);have zn:∀ ω≠ζ,e v ω=0:=by
   intro ω zi;have h1:=An zm ω
   have zp:((((ω ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p) -
     (((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p))•e v ω=0:=by
    rw[DJ,h1,Cx]
   have zq:(((ω ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)≠(((ζ ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p):=(by intro zr;apply zi;apply zf;ext;exact zr);exact (smul_eq_zero.mp zp).resolve_left (sub_ne_zero.mpr zq)
  have zo:v=(e v ζ).1:=by
   conv_lhs=>rw[ze]
   rw[Ay ζ]
   . intro ω _ zi;simp[zn ω zi]
   . intro h;exact absurd (Ai ζ) h
  rw[zo];have h2:=(e v ζ).2;rw[Bf,BU,AU,Br,CE] at h2;exact h2
 .
  intro hv;have zg:∀ k:ℕ,(T ^ k) v=(((ζ:(Qa p)ˣ):Qa p) ^ k)•v:=by
   intro k;induction k with
   | zero=>simp
   | succ k ih=>
    rw[BA,Module.End.mul_apply,ih,Bd,hv,AR,BA,Bb]
  simpa using zg m
lemma Yf {N:ℕ} (za:0 < N) (zb:¬ p∣N)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] [FiniteDimensional (Qa p) V] (T:Module.End (Qa p) V) (zc:T ^ N=1) : LinearMap.trace (Qa p) V (T ^ p)=(LinearMap.trace (Qa p) V T) ^ p:=by
 classical
 have zh:Nat.card (Ab N (Qa p))=N:=Qy za zb;let:Fintype (Ab N (Qa p)):=Qx za zb;have zi:(T ^ p) ^ N=1:=by rw[<-Cz,Bb,Cz,zc,B8]
 have h1:=QR za zb T zc;have h2:=QR za zb (T ^ p) zi;rw[h1,h2];have:CharP (Qa p) p:=charP_of_injective_algebraMap (algebraMap (ZMod p) (Qa p)).injective p;have zd:∀ (s:Finset (Ab N (Qa p)))
   (f:Ab N (Qa p)->Qa p),
   (∑ x∈s,f x) ^ p=∑ x∈s,(f x) ^ p:=by
  intro s f;induction s using Finset.induction_on with
  | empty=>simp[zero_pow (Fact.out:p.Prime).ne_zero]
  | insert a s ha ih=>
   rw[C7 ha,C7 ha,add_pow_char,ih]
 rw[zd];have zf:N.Coprime p:=((E1 Fact.out).mpr zb).symm;let zg:=powCoprime (G:=Ab N (Qa p)) (by rw[zh];exact zf);symm;refine AO zg _ _ fun ζ=>?_;dsimp only[zg,powCoprime,Equiv.coe_fn_mk];have zj:=Q3 za zb zf T zc ζ;have ze:Module.finrank (Qa p)
   (LinearMap.ker (T ^ p - (((ζ ^ p:Ab N (Qa p)):(Qa p)ˣ):Qa p)•LinearMap.id))=
   Module.finrank (Qa p)
   (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):=
  (LinearEquiv.ofEq _ _ zj).finrank_eq
 rw[ze,CC];have zk:((Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):ℕ):Qa p) ^ p=(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):Qa p):=(by rw[<-DO (algebraMap (ZMod p) (Qa p)),<-Dc,ZMod.pow_card]);rw[zk];simp
noncomputable def Qr {N:ℕ} (hN_pos:0 < N) (hNp:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ) (V:Type*) [AddCommGroup V] [Module (Qa p) V] (T:Module.End (Qa p) V):ℂ:=
 letI:Fintype (Ab N (Qa p)):=Qx hN_pos hNp
 ∑ ζ:Ab N (Qa p),(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):ℂ)*((ι ζ:ℂˣ):ℂ)
lemma Wz {N:ℕ} (za:0 < N) (zb:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ)
  {V W:Type*} [AddCommGroup V] [Module (Qa p) V] [AddCommGroup W] [Module (Qa p) W] (e:V≃ₗ[Qa p] W) (T:Module.End (Qa p) V) : Qr za zb ι W (e.toLinearMap∘ₗT∘ₗe.symm.toLinearMap)=Qr za zb ι V T:=by
 classical
 unfold Qr;refine Ag rfl fun ζ _=>?_;congr 1;have zc:LinearMap.ker (e.toLinearMap∘ₗT∘ₗe.symm.toLinearMap - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)=(LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)).map e.toLinearMap:=by
  ext w;simp only[Bf,BU,BZ,AU,Br,Submodule.mem_map,CE];constructor
  . intro hw;refine ⟨e.symm w,?_,e.apply_symm_apply w⟩;apply e.injective;simpa[Bd] using hw
  . rintro ⟨v,hv,rfl⟩;simp[hv,Bd]
 rw[zc];exact_mod_cast Fg e _
lemma YG {N:ℕ} (za:0 < N) (zb:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] (ω:Ab N (Qa p)) (T:Module.End (Qa p) V) : Qr za zb ι V (((ω:(Qa p)ˣ):Qa p)•T)= ((ι ω:ℂˣ):ℂ)*Qr za zb ι V T:=by
 classical
 let:Fintype (Ab N (Qa p)):=Qx za zb;unfold Qr;rw[A6];symm;refine DC (fun ζ=>ω*ζ) (Group.mulLeft_bijective ω) _ _ fun ζ=>?_
 have zc:LinearMap.ker (((ω:(Qa p)ˣ):Qa p)•T -
    (((ω*ζ:Ab N (Qa p)):(Qa p)ˣ):Qa p)•LinearMap.id)=
   LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id):=by
  ext v;simp only[Bf,BU,AU,Br,CE,De,BB];rw[mul_smul];exact smul_right_inj (DH (ω:(Qa p)ˣ))
 rw[zc,AF];push_cast;ring
lemma YS {N:ℕ} (za:0 < N) (zb:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ)
  {α:Type*} [Fintype α] [DecidableEq α] (W:α->Type*) [∀ i,AddCommGroup (W i)] [∀ i,Module (Qa p) (W i)] [∀ i,FiniteDimensional (Qa p) (W i)] (T:∀ i,Module.End (Qa p) (W i)) :
  let Tpi:Module.End (Qa p) (∀ i,W i):=
   {toFun:=fun f i=>T i (f i)
    map_add':=fun f g=>by ext i;simp
    map_smul':=fun c f=>by ext i;simp }
  Qr za zb ι (∀ i,W i) Tpi=∑ i:α,Qr za zb ι (W i) (T i):=by
 classical
 intro Tpi;unfold Qr;rw[AY];refine Ag rfl fun ζ _=>?_;rw[<-Bo];congr 1;have zd:LinearMap.ker (Tpi - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)≃ₗ[Qa p]
   (∀ i:α,LinearMap.ker (T i - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):=
  {toFun:=fun f i=>⟨f.1 i,by
    have hf:=An (LinearMap.mem_ker.mp f.2) i
    exact LinearMap.mem_ker.mpr hf⟩
   invFun:=fun g=>⟨fun i=>(g i).1,by
    rw[Bf];funext i
    exact LinearMap.mem_ker.mp (g i).2⟩
   left_inv:=fun f=>by ext i;rfl
   right_inv:=fun g=>by ext i;rfl
   map_add':=fun f₁ f₂=>by ext i;rfl
   map_smul':=fun c f=>by ext i;rfl }
 have zc:Module.finrank (Qa p) (LinearMap.ker (Tpi - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id))=∑ i:α,Module.finrank (Qa p) (LinearMap.ker (T i - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):=(by rw[zd.finrank_eq,Module.finrank_pi_fintype]);exact_mod_cast zc
lemma Wf {N:ℕ} (za:0 < N) (d:ℕ) (zb:d∣N) :
  letI:Fintype (Ab N ℂ):=WA za
  ∃ z:ℤ,∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>orderOf ζ=d),((ζ:ℂˣ):ℂ)=(z:ℂ):=by
 classical
 have:NeZero N:=⟨za.ne'⟩;have zl:Nat.card (Ab N ℂ)=N:=Complex.card_rootsOfUnity N;let:Fintype (Ab N ℂ):=WA za;obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=Ab N ℂ);have zq:orderOf g=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers hg,zl]
 induction d using Nat.strongRecOn with
 | ind d ih=>
  have zd:0 < d:=Nat.pos_of_dvd_of_pos zb za;have ze:∑ k∈d.divisors,∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>orderOf ζ=k),((ζ:ℂˣ):ℂ)=∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>ζ ^ d=1),((ζ:ℂˣ):ℂ):=by
   rw[<-Finset.sum_biUnion]
   .
    congr 1;ext ζ;simp only[Finset.mem_biUnion,AL,Ai,B3,Nat.mem_divisors];constructor
    . rintro ⟨k,⟨zj,_⟩,rfl⟩;exact orderOf_dvd_iff_pow_eq_one.mp zj
    . intro zx;exact ⟨orderOf ζ,⟨Bl zx,zd.ne'⟩,rfl⟩
   . intro zD _ zE _ zB;dsimp only[Function.onFun];rw[Ew];intro ζ h1 h2;rw[AL] at h1 h2;exact zB (h1.2.symm.trans h2.2)
  have zm:∃ w:ℤ,∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>ζ ^ d=1),((ζ:ℂˣ):ℂ)=(w:ℂ):=by
   by_cases zA:d=1
   . refine ⟨1,?_⟩;subst zA;have zr:(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>ζ ^ 1=1)={1}:=(by ext ζ;simp);rw[zr];simp
   .
    refine ⟨0,?_⟩;obtain ⟨q,hq⟩:=zb;let ω:Ab N ℂ:=g ^ q;have zn:ω ^ d=1:=by rw[<-Cz,Bb,<-hq];ext;exact (mem_rootsOfUnity' N _).mp g.2
    have zk:ω≠1:=by
     intro h1;have zt:N∣q:=zq ▸ Bl h1;have zo:0 < q:=by
      by_contra h0;have zy:q=0:=by omega
      rw[zy,AS] at hq;omega
     have zF:=AP zo zt;have zz:1 < d:=by omega
     nlinarith
    have zh:((ω:ℂˣ):ℂ)≠1:=fun h=>zk (by ext;exact h);set S:=∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>ζ ^ d=1),((ζ:ℂˣ):ℂ);have zu:((ω:ℂˣ):ℂ)*S=S:=by
     rw[A6];refine Fi (fun ζ _=>ω*ζ) ?_ ?_ ?_ ?_
     . intro ζ zg;rw[AL] at zg ⊢;exact ⟨Ai _,by rw[CC,zn,zg.2,AA]⟩
     . intro a _ b _ zC;exact E3 zC
     .
      intro ζ zg;rw[AL] at zg
      refine ⟨ω⁻¹*ζ,Finset.mem_filter.mpr ⟨Ai _,by
       rw[CC,E7,zn,inv_one,zg.2,AA]⟩,by group⟩
     . intro ζ _;simp
    have:(((ω:ℂˣ):ℂ) - 1)*S=0:=by linear_combination zu
    simpa using (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr zh)
  have zp:d.divisors=insert d (d.divisors.erase d):=
   (Finset.insert_erase (Nat.mem_divisors.mpr ⟨EO d,zd.ne'⟩)).symm
  rw[zp,C7 (Finset.notMem_erase d _)] at ze;have zs:∀ k∈d.divisors.erase d,∃ z:ℤ,∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>orderOf ζ=k),((ζ:ℂˣ):ℂ)=(z:ℂ):=by intro k hk;have zv:k≠d:=(Finset.mem_erase.mp hk).1;have zj:k∣d:=(Nat.mem_divisors.mp (Finset.mem_erase.mp hk).2).1;have zw:k < d:=lt_of_le_of_ne (AP zd zj) zv;exact ih k zw (zj.trans zb)
  choose zf hzf using zs;obtain ⟨w,hw⟩:=zm;refine ⟨w - ∑ k∈d.divisors.erase d,if hk:k∈d.divisors.erase d then zf k hk else 0,?_⟩;push_cast;have zc:∑ k∈d.divisors.erase d,∑ ζ∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ζ=>orderOf ζ=k),((ζ:ℂˣ):ℂ)=∑ k∈d.divisors.erase d,(if hk:k∈d.divisors.erase d then (zf k hk:ℂ) else 0):=by refine Ag rfl fun k hk=>?_;rw[dif_pos hk,hzf k hk]
  have zi:(∑ k∈d.divisors.erase d,(if hk:k∈d.divisors.erase d then zf k hk else 0:ℤ):ℂ)=∑ k∈d.divisors.erase d,(if hk:k∈d.divisors.erase d then (zf k hk:ℂ) else 0):=(by push_cast;refine Ag rfl fun k hk=>?_;split_ifs <;> simp);rw[zi];linear_combination ze+hw - zc
lemma Wn {N:ℕ} (za:0 < N) (zb:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ)
  {V:Type*} [AddCommGroup V] [Module (Qa p) V] (T:Module.End (Qa p) V) (zd:T ^ N=1) (zc:∀ m:ℕ,N.Coprime m->∃ e:V≃ₗ[Qa p] V,e.toLinearMap∘ₗT∘ₗe.symm.toLinearMap=T ^ m) : ∃ q:ℚ,Qr za zb ι V T=(q:ℂ):=by
 classical
 have zz:Nat.card (Ab N (Qa p))=N:=Qy za zb;let:Fintype (Ab N (Qa p)):=Qx za zb;have:NeZero N:=⟨za.ne'⟩;have z1:Nat.card (Ab N ℂ)=N:=Complex.card_rootsOfUnity N;let:Fintype (Ab N ℂ):=WA za;have zn:∀ a b:Ab N (Qa p),orderOf a=orderOf b->∃ m:ℕ,N.Coprime m/\a ^ m=b:=by
  intro a b zs;obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=Ab N (Qa p));have zm:orderOf g=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers hg,zz]
  have zl:∀ x:Ab N (Qa p),∃ k:ℕ,g ^ k=x:=by
   intro x;obtain ⟨k,hk⟩:=hg x;refine ⟨(k % (N:ℤ)).toNat,?_⟩;have zO:k % (N:ℤ)>=0:=Int.emod_nonneg k (by positivity);have zT:k=(N:ℤ)*(k / (N:ℤ))+(k % (N:ℤ)):=(Int.mul_ediv_add_emod k N).symm;have zP:g ^ N=1:=by ext;exact (mem_rootsOfUnity' N _).mp g.2
   rw[<-hk];change g ^ (k % (N:ℤ)).toNat=g ^ k
   conv_rhs=>rw[zT,Do,zpow_mul,Ee,zP,one_zpow,AA]
   rw[<-Ee,Int.toNat_of_nonneg zO]
  obtain ⟨ka,rfl⟩:=zl a;obtain ⟨kb,rfl⟩:=zl b;set d:=orderOf (g ^ ka);have zo:0 < d:=orderOf_pos _;have zV:d=N / Nat.gcd N ka:=by have h:=orderOf_pow (n:=ka) g;rwa[zm] at h
  have z2:d=N / Nat.gcd N kb:=(by rw[zs];have h:=orderOf_pow (n:=kb) g;rwa[zm] at h);have zP:g ^ N=1:=by ext;exact (mem_rootsOfUnity' N _).mp g.2
  have zW:d∣N:=Bl (by rw[<-Cz,Bb,Cz,zP,B8]);have zi:Nat.gcd N ka∣N:=CI N ka;have zI:Nat.gcd N kb∣N:=CI N kb;have zA:Nat.gcd N ka=Nat.gcd N kb:=by
   have h1:d*Nat.gcd N ka=N:=by rw[zV];exact EJ zi
   have h2:d*Nat.gcd N kb=N:=by rw[z2];exact EJ zI
   exact D1 zo (h1.trans h2.symm)
  set s:=Nat.gcd N ka;have zp:0 < s:=Nat.pos_of_dvd_of_pos zi za;have zQ:N=s*d:=by rw[zV];exact (Nat.mul_div_cancel' zi).symm
  obtain ⟨a',zG⟩:=Cs N ka;obtain ⟨b',zH⟩:=zA ▸ Cs N kb;have zJ:d.Coprime a':=by
   have h1:Nat.gcd (s*d) (s*a')=s:=by rw[<-zQ,<-zG]
   rw[Nat.gcd_mul_left] at h1;have h2:s*Nat.gcd d a'=s*1:=by simpa using h1
   exact D1 zp h2
  have zK:d.Coprime b':=by
   have h1:Nat.gcd (s*d) (s*b')=s:=by rw[<-zQ,<-zH,<-zA]
   rw[Nat.gcd_mul_left] at h1;have h2:s*Nat.gcd d b'=s*1:=by simpa using h1
   exact D1 zp h2
  have:NeZero d:=⟨zo.ne'⟩;let zB:(ZMod d)ˣ:=ZMod.unitOfCoprime a' zJ.symm;let zC:(ZMod d)ˣ:=ZMod.unitOfCoprime b' zK.symm;let m0:ℕ:=((zB⁻¹*zC:(ZMod d)ˣ):ZMod d).val;have zL:d.Coprime m0:=by have h1:(m0:ZMod d)=((zB⁻¹*zC:(ZMod d)ˣ):ZMod d):=CP _;exact (ZMod.isUnit_iff_coprime m0 d).mp (h1 ▸ Units.isUnit _) |>.symm
  have zR:a'*m0 ≡ b' [MOD d]:=(by rw[<-E8];push_cast;have h1:(a':ZMod d)=(zB:ZMod d):=rfl;have h2:(b':ZMod d)=(zC:ZMod d):=rfl;have h3:(m0:ZMod d)=((zB⁻¹*zC:(ZMod d)ˣ):ZMod d):=CP _;rw[h1,h2,h3,De,<-Ad,Units.mul_inv,AA]);set S:=N.primeFactors.filter (fun q=>¬ q∣d);set B:=∏ q∈S,q;have z3:d.Coprime B:=by rw[Cb];by_contra zj;obtain ⟨q,ze,zg⟩:=B5 zj;have zq:q∣d:=zg.trans (CI d B);have zD:q∣B:=zg.trans (Cs d B);rw[Prime.dvd_finsetProd_iff ze.prime] at zD;obtain ⟨r,zX,z7⟩:=zD;have zt:=(Nat.mem_primeFactors.mp (Finset.mem_filter.mp zX).1).1;have zU:=(CL ze zt).mp z7;exact (Finset.mem_filter.mp zX).2 (zU ▸ zq)
  obtain ⟨m,zY,z8⟩:=Er z3 m0 1;have zE:N.Coprime m:=by
   rw[Cb];by_contra zj;obtain ⟨q,ze,zg⟩:=B5 zj;have z4:q∣N:=zg.trans (CI N m);have zF:q∣m:=zg.trans (Cs N m);by_cases zq:q∣d
   . have z0:q∣m0:=(by have h1:m % q=m0 % q:=zY.of_dvd zq;rw[B7] at zF ⊢;omega);exact ze.not_dvd_one (zL.gcd_eq_one ▸ DR zq z0)
   . have z5:q∈S:=Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ze,z4,za.ne'⟩,zq⟩;have zD:q∣B:=Ej _ z5;have h1:m % q=1 % q:=z8.of_dvd zD;rw[B7] at zF;have z9:1 % q=1:=A9 ze.one_lt;omega
  refine ⟨m,zE,?_⟩;rw[<-Cz];rw[pow_eq_pow_iff_modEq,zm,zQ,zG,zH,Ad];have zu:a'*m ≡ b' [MOD d]:=(zY.mul_left a').trans zR;exact zu.mul_left' s
 have zv:∀ a b:Ab N (Qa p),orderOf a=orderOf b->Module.finrank (Qa p) (LinearMap.ker (T - ((a:(Qa p)ˣ):Qa p)•LinearMap.id))=Module.finrank (Qa p) (LinearMap.ker (T - ((b:(Qa p)ˣ):Qa p)•LinearMap.id)):=by
  intro a b zs;obtain ⟨m,zE,rfl⟩:=zn a b zs;obtain ⟨e,he⟩:=zc m zE;rw[<-Q3 za zb zE T zd a,<-he]
  have z6:LinearMap.ker (e.toLinearMap∘ₗT∘ₗe.symm.toLinearMap -
    (((a ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•LinearMap.id)=
    (LinearMap.ker (T - (((a ^ m:Ab N (Qa p)):(Qa p)ˣ):Qa p)•LinearMap.id)).map e.toLinearMap:=by
   ext w;simp only[Bf,BU,BZ,AU,Br,Submodule.mem_map,CE];constructor
   . intro hw;refine ⟨e.symm w,?_,e.apply_symm_apply w⟩;apply e.injective;simpa[Bd] using hw
   . rintro ⟨v,hv,rfl⟩;simp[hv,Bd]
  rw[z6];exact Fg e _
 have zM:Qr za zb ι V T=∑ d∈N.divisors,∑ ζ∈(Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d),(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):ℂ)*((ι ζ:ℂˣ):ℂ):=by
  unfold Qr;rw[<-Finset.sum_biUnion]
  . congr 1;ext ζ;simp only[Ai,Finset.mem_biUnion,Nat.mem_divisors,AL,B3,true_iff];refine ⟨orderOf ζ,⟨?_,za.ne'⟩,rfl⟩;exact Bl (by ext;exact (mem_rootsOfUnity' N _).mp ζ.2)
  . intro va _ vb _ zj;dsimp only[Function.onFun];rw[Ew];intro ζ h1 h2;rw[AL] at h1 h2;exact zj (h1.2.symm.trans h2.2)
 have zr:∀ d∈N.divisors,∃ z:ℤ,∑ ζ∈(Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d),(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):ℂ)*((ι ζ:ℂˣ):ℂ)=(z:ℂ):=by
  intro d hd;have zW:d∣N:=(Nat.mem_divisors.mp hd).1;by_cases zj:((Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d)).Nonempty
  .
   obtain ⟨zk,zy⟩:=zj;have zw:orderOf zk=d:=(Finset.mem_filter.mp zy).2;set c:=Module.finrank (Qa p) (LinearMap.ker (T - ((zk:(Qa p)ˣ):Qa p)•LinearMap.id));have zS:∑ ζ∈(Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d),(Module.finrank (Qa p) (LinearMap.ker (T - ((ζ:(Qa p)ˣ):Qa p)•LinearMap.id)):ℂ)*((ι ζ:ℂˣ):ℂ)=(c:ℂ)*∑ ζ∈(Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d),((ι ζ:ℂˣ):ℂ):=(by rw[A6];refine Ag rfl fun ζ zh=>?_;have zN:orderOf ζ=d:=(Finset.mem_filter.mp zh).2;rw[zv ζ zk (zN.trans zw.symm)]);rw[zS];have zx:∑ ζ∈(Finset.univ:Finset (Ab N (Qa p))).filter (fun ζ=>orderOf ζ=d),((ι ζ:ℂˣ):ℂ)=∑ ω∈(Finset.univ:Finset (Ab N ℂ)).filter (fun ω=>orderOf ω=d),((ω:ℂˣ):ℂ):=by
    refine Fi (fun ζ _=>ι ζ) ?_ ?_ ?_ ?_
    . intro ζ zh;rw[AL] at zh ⊢;exact ⟨Ai _,by rw[MulEquiv.orderOf_eq ι ζ];exact zh.2⟩
    . intro a _ b _ zs;exact ι.injective zs
    . intro ω zZ;rw[AL] at zZ;refine ⟨ι.symm ω,Finset.mem_filter.mpr ⟨Ai _,?_⟩,ι.apply_symm_apply ω⟩;rw[MulEquiv.orderOf_eq ι.symm ω];exact zZ.2
    . intro ζ _;rfl
   rw[zx];obtain ⟨z,hz⟩:=Wf za d zW;refine ⟨(c:ℤ)*z,?_⟩;rw[hz];push_cast;rfl
  . rw[Finset.not_nonempty_iff_eq_empty.mp zj];exact ⟨0,by simp⟩
 choose zf hzf using zr;refine ⟨∑ d∈N.divisors,if hd:d∈N.divisors then (zf d hd:ℚ) else 0,?_⟩;rw[zM];push_cast;refine Ag rfl fun d hd=>?_;rw[dif_pos hd,hzf d hd];push_cast;rfl
end DiagonalizationAndBrTr
section Section2Admissible
variable {p:ℕ} [Fact p.Prime]
structure Qg (p N:ℕ) [Fact p.Prime] (hN_pos:0 < N) (hNp:¬ p∣N)
  (ι:Ab N (Qa p)≃*Ab N ℂ) where
 n:ℕ
 hn_pos:0 < n
 L:Subgroup (Aa (Fin n) (ZMod p))
 solvable:Group.IsSolvable L
 card_dvd:Nat.card L∣N
 negOne_mem:Qd n p∈L
 realMinus:QQ (⟨Qd n p,negOne_mem⟩:L)
 ratTr:∀ g∈L,∃ q:ℚ,Qr hN_pos hNp ι (Fin n->Qa p)
   (Matrix.toLin' (g.val.map (algebraMap (ZMod p) (Qa p))))=(q:ℂ)
 absIrred:∀ U:Submodule (Qa p) (Fin n->Qa p),(∀ g∈L,∀ v∈U,(g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v∈U)->U=⊥\/U=⊤
 SF:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ),∃ g∈L,g.val.mulVec v=(a:ZMod p)•v
 B:Matrix (Fin n) (Fin n) (ZMod p)
 B_alt:Bᵀ=-B
 B_det:B.det≠0
 B_inv:∀ g∈L,g.valᵀ*B*g.val=B
noncomputable def Qi (p:ℕ) [Fact p.Prime]:Qa p ≃+*Qa p:=by
 haveI:CharP (Qa p) p:=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (Qa p)).injective p
 refine RingEquiv.ofBijective (frobenius (Qa p) p) ⟨?_,?_⟩
 . exact frobenius_inj (Qa p) p
 .
  intro c;have zb:(Polynomial.X ^ p - Polynomial.C c:Polynomial (Qa p)).degree≠0:=by
   have za:0 < p:=(Fact.out:p.Prime).pos;rw[Ef]
   . rw[Dn];exact_mod_cast za.ne'
   . rw[Dn];exact lt_of_le_of_lt Polynomial.degree_C_le (WithBot.coe_lt_coe.mpr za)
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C c) zb;refine ⟨r,?_⟩;rw[Polynomial.IsRoot,EA,DW,D3,Polynomial.eval_C,CE] at hr;exact hr
@[simp] lemma frobEquiv_apply (x:Qa p):Qi p x=x ^ p:=rfl
lemma Q6 {x:Qa p} (hx:x ^ p=x) : x∈Set.range (algebraMap (ZMod p) (Qa p)):=by
 classical
 let P:Polynomial (Qa p):=Polynomial.X ^ p - Polynomial.X;have zb:P≠0:=(by intro h0;have za:=Ah (fun q:Polynomial (Qa p)=>q.coeff p) h0;have zk:p≠1:=(Fact.out:p.Prime).ne_one;simp only[P,Polynomial.coeff_sub,Polynomial.coeff_X_pow,Polynomial.coeff_X,↓reduceIte,Polynomial.coeff_zero] at za;rw[Aw zk.symm,sub_zero] at za;exact DL za);have zl:P.natDegree<=p:=by
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  . exact Polynomial.natDegree_X_pow_le p
  . exact le_trans Polynomial.natDegree_X_le (Fact.out:p.Prime).one_lt.le
 let S:Finset (Qa p):=Finset.univ.image (algebraMap (ZMod p) (Qa p));have zc:S.card=p:=(by rw[E0 _ (algebraMap (ZMod p) (Qa p)).injective,BS,Ey]);have ze:S.val⊆P.roots:=(by intro a ha;rw[Finset.mem_val,Eb] at ha;obtain ⟨c,_,rfl⟩:=ha;rw[Polynomial.mem_roots zb,Polynomial.IsRoot,EA,DW,D3,<-Dc,ZMod.pow_card,Cx]);have zf:x∈P.roots:=(by rw[Polynomial.mem_roots zb,Polynomial.IsRoot,EA,DW,D3,hx,Cx]);by_contra hxS;have zd:x∉S:=(by intro h;rw[Eb] at h;obtain ⟨c,_,hc⟩:=h;exact hxS ⟨c,hc⟩);have zm:(insert x S).val<=P.roots:=by
  rw[Multiset.le_iff_count];intro a;by_cases ha:a∈insert x S
  .
   have zn:Multiset.count a (insert x S).val=1:=
    Multiset.count_eq_one_of_mem (Finset.nodup _) ha
   rw[zn];have zg:a∈P.roots:=by
    rw[Cu] at ha;rcases ha with rfl | hS'
    . exact zf
    . exact ze hS'
   exact Nat.one_le_iff_ne_zero.mpr (Multiset.count_ne_zero.mpr zg)
  . rw[Multiset.count_eq_zero.mpr ha];exact Nat.zero_le _
 have zj:=Multiset.card_le_card zm;have zh:=Polynomial.card_roots' P;have zi:((insert x S).val).card=p+1:=(by change (insert x S).card=p+1;rw[C1 zd,zc]);omega
lemma WT {n:ℕ} (hn_pos:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))) (za:∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤) : ∀ A B:Matrix (Fin n) (Fin n) (ZMod p), (∀ g∈L,A*g.val=g.val*A)->(∀ g∈L,B*g.val=g.val*B)->A*B=B*A:=by
 classical
 let D:Subring (Matrix (Fin n) (Fin n) (ZMod p)):=
  {carrier:={A | ∀ g∈L,A*g.val=g.val*A}
   mul_mem':=fun {A B} hA hB g hg=>by
    calc (A*B)*g.val=A*(B*g.val):=Af _ _ _
    _ = A*(g.val*B):=by rw[hB g hg]
    _ = (A*g.val)*B:=(Af _ _ _).symm
    _ = (g.val*A)*B:=by rw[hA g hg]
    _ = g.val*(A*B):=Af _ _ _
   one_mem':=fun g _=>by simp
   add_mem':=fun {A B} hA hB g hg=>by rw[add_mul,EM,hA g hg,hB g hg]
   zero_mem':=fun g _=>by simp
   neg_mem':=fun {A} hA g hg=>by rw[neg_mul,mul_neg,hA g hg] }
 have zb:∀ A:D,A≠0->IsUnit A.1.det:=by
  intro A zf;have zj:A.1≠0:=fun h=>zf (Ae h);have zg:∀ g∈L,∀ v∈LinearMap.ker (Matrix.toLin' A.1),g.val.mulVec v∈LinearMap.ker (Matrix.toLin' A.1):=by intro g hg v hv;rw[Bf,Aj] at hv ⊢;rw[Ac,A.2 g hg,<-Ac,hv,DZ]
  have zd:LinearMap.ker (Matrix.toLin' A.1)≠⊤:=(by intro zp;apply zj;apply Matrix.toLin'.injective;apply Ap;intro v;have:v∈LinearMap.ker (Matrix.toLin' A.1):=zp ▸ BW;simpa using this);have zh:LinearMap.ker (Matrix.toLin' A.1)=⊥:=
   (za _ zg).resolve_right zd
  have zo:Function.Injective (Matrix.toLin' A.1):=LinearMap.ker_eq_bot.mp zh;have zi:A.1.det≠0:=(by intro zn;obtain ⟨v,zm,zq⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr zn;exact zm (zo (by simpa[Aj] using zq)));exact isUnit_iff_ne_zero.mpr zi
 have zc:∀ (A:D) (hA:A≠0),A.1⁻¹∈D:=by
  intro A hA g hg;have hu:IsUnit A.1.det:=zb A hA;have zl:A.1⁻¹*A.1=1:=Du A.1 hu;have zk:A.1*A.1⁻¹=1:=B0 A.1 hu
  calc A.1⁻¹*g.val=A.1⁻¹*g.val*(A.1*A.1⁻¹):=by rw[zk,As]
  _ = A.1⁻¹*(g.val*A.1)*A.1⁻¹:=by simp[Af]
  _ = A.1⁻¹*(A.1*g.val)*A.1⁻¹:=by rw[<-A.2 g hg]
  _ = (A.1⁻¹*A.1)*g.val*A.1⁻¹:=by simp[Af]
  _ = g.val*A.1⁻¹:=by rw[zl,AC]
 have ze:Nontrivial D:=(by refine ⟨⟨0,1,?_⟩⟩;intro zr;have h:=Ah (fun M:D=>M.1 ⟨0,hn_pos⟩ ⟨0,hn_pos⟩) zr;simp at h);let:DivisionRing D:=
  {(inferInstance:Ring D) with
   inv:=fun A=>if h:A=0 then 0 else ⟨A.1⁻¹,zc A h⟩
   exists_pair_ne:=ze.exists_pair_ne
   mul_inv_cancel:=fun A hA=>by
    change A*(if h:A=0 then 0 else ⟨A.1⁻¹,zc A h⟩)=1;rw[dif_neg hA];apply Ae;exact B0 A.1 (zb A hA)
   inv_zero:=by simp
   nnqsmul:=_
   qsmul:=_ }
 let:Field D:=littleWedderburn D;intro A B hA hB;exact Ah Subtype.val (Bb (⟨A,hA⟩:D) (⟨B,hB⟩:D))
lemma Yc {p:ℕ} [Fact p.Prime]
  {n:ℕ} (hn_pos:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))) (za:¬ p∣Nat.card L) (zc:Qw L) (zb:∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤) : ∀ U:Submodule (Qa p) (Fin n->Qa p), (∀ g∈L,∀ v∈U,(g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v∈U)-> U=⊥\/U=⊤:=by
 classical
 set N:=Nat.card L with hN_def
 have vn:0 < N:=CD;have vM:¬ p∣N:=za;let ιK:=algebraMap (ZMod p) (Qa p);have zG:(Nat.card L:Qa p)≠0:=(by intro h;have h1:(Nat.card L:ZMod p)=0:=(by apply ιK.injective;rw[DO,Bn];exact h);exact za ((At (Nat.card L) p).mp h1));have:NeZero (Nat.card L:Qa p):=⟨zG⟩;have:Invertible (Nat.card L:Qa p):=invertibleOfNonzero zG;have:CharP (Qa p) p:=charP_of_injective_algebraMap ιK.injective p;let ρK:Representation (Qa p) L (Fin n->Qa p):=
  {toFun:=fun g=>Matrix.toLin' (g.1.val.map ιK)
   map_one':=by
    apply Ap;intro v;have h1:(1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK=1:=by
     ext i j;by_cases h:i=j
     . subst h;simp
     . simp[h]
    change (Matrix.toLin' ((1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK)) v=v;rw[h1];simp
   map_mul':=fun g₁ g₂=>by
    apply Ap;intro v;have hm:(g₁.1.val*g₂.1.val).map ιK=g₁.1.val.map ιK*g₂.1.val.map ιK:=
     Aq
    change ((g₁.1.val*g₂.1.val).map ιK).mulVec v=(g₁.1.val.map ιK).mulVec ((g₂.1.val.map ιK).mulVec v)
    rw[hm,Ac] }
 have zP:∀ A B:Matrix (Fin n) (Fin n) (Qa p),(∀ g:L,A*g.1.val.map ιK=g.1.val.map ιK*A)->(∀ g:L,B*g.1.val.map ιK=g.1.val.map ιK*B)->A*B=B*A:=
  WZ (fun g:L=>g.1.val)
   (fun A B hA hB=>WT hn_pos L zb A B (fun g hg=>hA ⟨g,hg⟩) (fun g hg=>hB ⟨g,hg⟩))
 intro U hU;by_cases vf:U=⊥
 . left;exact vf
 .
  right;let Q:ℕ->Prop:=fun d=>
   ∃ W:Submodule (Qa p) (Fin n->Qa p),W<=U/\W≠⊥/\(∀ g∈L,∀ v∈W,(g.val.map ιK).mulVec v∈W)/\Module.finrank (Qa p) W=d
  have vo:∃ d,Q d:=⟨Module.finrank (Qa p) U,U,le_refl U,vf,hU,rfl⟩;obtain ⟨W,vH,vb,zF,vx⟩:=EF vo;have vc:∀ W':Submodule (Qa p) (Fin n->Qa p),W'<=W->(∀ g∈L,∀ v∈W',(g.val.map ιK).mulVec v∈W')->W'=⊥\/W'=W:=by
   intro W' vy zK;by_cases zq:W'=⊥
   . left;exact zq
   . right;have vN:Module.finrank (Qa p) W<=Module.finrank (Qa p) W':=(by rw[vx];exact Nat.find_min' vo ⟨W',vy.trans vH,zq,zK,rfl⟩);exact EQ vy vN
  let zx:Subrepresentation ρK:=
   {toSubmodule:=W
    apply_mem_toSubmodule:=fun g v hv=>zF g.1 g.2 v hv }
  have zY:Representation.IsSemisimpleRepresentation ρK:=inferInstance;obtain ⟨zJ,zl⟩:=zY.exists_isCompl zx;let W':Submodule (Qa p) (Fin n->Qa p):=zJ.toSubmodule;have zK:∀ g∈L,∀ v∈W',(g.val.map ιK).mulVec v∈W':=fun g hg _ hv=>
   zJ.apply_mem_toSubmodule ⟨g,hg⟩ hv
  have zj:IsCompl W W':=by
   constructor
   . rw[disjoint_iff];have hd:zx ⊓ zJ=⊥:=zl.1.eq_bot;exact Ah Subrepresentation.toSubmodule hd
   . rw[codisjoint_iff];have hc:zx ⊔ zJ=⊤:=zl.2.eq_top;exact Ah Subrepresentation.toSubmodule hc
  let projW:(Fin n->Qa p)→ₗ[Qa p] W:=Submodule.projectionOnto W W' zj;let vA:Module.End (Qa p) (Fin n->Qa p):=W.subtype.comp projW;let P:Matrix (Fin n) (Fin n) (Qa p):=LinearMap.toMatrix' vA;have zi:∀ v,P.mulVec v=(projW v).1:=fun v=>by
   rw[<-Aj,Matrix.toLin'_toMatrix'];rfl
  have zn:∀ v∈W,P.mulVec v=v:=fun v hv=>by
   rw[zi];exact Ah Subtype.val (CF zj ⟨v,hv⟩)
  have z3:∀ v∈W',P.mulVec v=0:=fun v hv=>by
   rw[zi];exact Ah Subtype.val (Submodule.projectionOnto_apply_right zj ⟨v,hv⟩)
  have zo:∀ v,P.mulVec v∈W:=fun v=>by rw[zi];exact (projW v).2
  have zL:P*P=P:=(by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];exact zn _ (zo v));have zu:∀ g:L,P*g.1.val.map ιK=g.1.val.map ιK*P:=by
   intro g;apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];have vg:v=P.mulVec v+(v - P.mulVec v):=by abel
   have vO:v - P.mulVec v∈W':=(by have h1:=CF zj (projW v);have h2:v - (projW v).1∈LinearMap.ker projW:=(by rw[Bf,map_sub,h1,Cx]);rw[Submodule.ker_projectionOnto] at h2;simpa[zi] using h2)
   conv_lhs=>rw[vg]
   rw[A3,A3,zn _ (zF g.1 g.2 _ (zo v)),z3 _ (zK g.1 g.2 _ vO),D8]
  let Pp:Matrix (Fin n) (Fin n) (Qa p):=P.map (Qi p);have zZ:Pp*Pp=Pp:=(by rw[<-Aq,zL]);have zt:∀ g:L,(g.1.val.map ιK).map (Qi p)=g.1.val.map ιK:=(by intro g;ext i j;simp only[AZ,frobEquiv_apply,ιK,<-Dc,ZMod.pow_card]);have zM:∀ g:L,Pp*g.1.val.map ιK=g.1.val.map ιK*Pp:=by
   intro g
   calc Pp*g.1.val.map ιK=P.map (Qi p)*(g.1.val.map ιK).map (Qi p):=by rw[zt]
   _ = (P*g.1.val.map ιK).map (Qi p):=Matrix.map_mul.symm
   _ = (g.1.val.map ιK*P).map (Qi p):=by rw[zu g]
   _ = (g.1.val.map ιK).map (Qi p)*P.map (Qi p):=Aq
   _ = g.1.val.map ιK*Pp:=by rw[zt]
  let Wp:Submodule (Qa p) (Fin n->Qa p):=LinearMap.range (Matrix.toLin' Pp);have vp:∀ g∈L,∀ v∈Wp,(g.val.map ιK).mulVec v∈Wp:=(by rintro g hg _ ⟨v,rfl⟩;refine ⟨(g.val.map ιK).mulVec v,?_⟩;simp only[Aj,Ac];rw[zM ⟨g,hg⟩]);let zd:(Fin n->Qa p)->(Fin n->Qa p):=fun v i=>Qi p (v i);let zg:(Fin n->Qa p)->(Fin n->Qa p):=fun v i=>(Qi p).symm (v i);have z0:∀ u v,zd (u+v)=zd u+zd v:=fun u v=>by
   funext i;exact EN (Qi p) (u i) (v i)
  have zS:∀ (c:Qa p) v,zd (c•v)=Qi p c•zd v:=fun c v=>by
   funext i;exact AF (Qi p) c (v i)
  have zr:∀ (M:Matrix (Fin n) (Fin n) (Qa p)) v,zd (M.mulVec v)=(M.map (Qi p)).mulVec (zd v):=fun M v=>by
   funext i;simp only[zd,Matrix.mulVec,dotProduct,AZ,Ba,AF]
  have zQ:∀ (g:L) v,zd ((g.1.val.map ιK).mulVec v)=(g.1.val.map ιK).mulVec (zd v):=(by intro g v;rw[zr,zt]);have ze:∀ v∈W,zd v∈Wp:=(by intro v hv;refine ⟨zd v,?_⟩;rw[Aj,<-zr,zn v hv]);have zp:∀ v∈Wp,zg v∈W:=by
   rintro _ ⟨u,rfl⟩;have vP:zg (Pp.mulVec u)=P.mulVec (zg u):=by
    funext i;apply (Qi p).injective;change zd (zg (Pp.mulVec u)) i=zd (P.mulVec (zg u)) i;rw[zr];have h1:∀ w,zd (zg w)=w:=fun w=>by funext j;exact (Qi p).apply_symm_apply (w j)
    rw[h1,h1]
   rw[Aj,vP];exact zo _
  let zf:Representation (Qa p) L W:=
   {toFun:=fun g=>
     {toFun:=fun x=>⟨(g.1.val.map ιK).mulVec x.1,zF g.1 g.2 x.1 x.2⟩
      map_add':=fun x y=>Ae (A3 (g.1.val.map ιK) x.1 y.1)
      map_smul':=fun c x=>Ae (Al (g.1.val.map ιK) c x.1) }
    map_one':=by apply Ap;intro x;apply Ae;exact BV ρK.map_one x.1
    map_mul':=fun g₁ g₂=>by
     apply Ap;intro x;apply Ae
     exact BV (ρK.map_mul g₁ g₂) x.1 }
  let zk:Representation (Qa p) L Wp:=
   {toFun:=fun g=>
     {toFun:=fun x=>⟨(g.1.val.map ιK).mulVec x.1,vp g.1 g.2 x.1 x.2⟩
      map_add':=fun x y=>Ae (A3 (g.1.val.map ιK) x.1 y.1)
      map_smul':=fun c x=>Ae (Al (g.1.val.map ιK) c x.1) }
    map_one':=by apply Ap;intro x;apply Ae;exact BV ρK.map_one x.1
    map_mul':=fun g₁ g₂=>by
     apply Ap;intro x;apply Ae
     exact BV (ρK.map_mul g₁ g₂) x.1 }
  have:Nontrivial (Subrepresentation zf):=⟨⟨⊥,⊤,fun zq=>by
   have zB:(⊤:Submodule (Qa p) W)=(⊥:Submodule (Qa p) W):=
    Ah Subrepresentation.toSubmodule zq.symm
   apply vb;rw[BY];intro v hv;have zy:(⟨v,hv⟩:W)∈(⊥:Submodule (Qa p) W):=zB ▸ BW;rw[Cr] at zy
   exact Ah Subtype.val zy⟩⟩
  have vB:zf.IsIrreducible:=⟨fun S=>by
    let S':Submodule (Qa p) (Fin n->Qa p):=S.toSubmodule.map W.subtype;have vI:S'<=W:=Submodule.map_subtype_le W _;have zN:∀ g∈L,∀ v∈S',(g.val.map ιK).mulVec v∈S':=(by rintro g hg _ ⟨x,hx,rfl⟩;exact ⟨zf ⟨g,hg⟩ x,S.apply_mem_toSubmodule ⟨g,hg⟩ hx,rfl⟩);rcases vc S' vI zN with zq | zB
    . left;apply Subrepresentation.ext;change S.toSubmodule=(⊥:Submodule (Qa p) W);rw[BY];intro x hx;have vd:x.1∈S':=⟨x,hx,rfl⟩;rw[zq,Cr] at vd;exact Ae vd
    .
     right;apply Subrepresentation.ext;change S.toSubmodule=(⊤:Submodule (Qa p) W);rw[Cg];intro x;have vd:x.1∈S':=by rw[zB];exact x.2
     obtain ⟨y,hy,vW⟩:=vd;have:y=x:=Ae vW
     exact this ▸ hy⟩
  have:Nontrivial (Subrepresentation zk):=⟨⟨⊥,⊤,fun zq=>by
   have zB:(⊤:Submodule (Qa p) Wp)=(⊥:Submodule (Qa p) Wp):=
    Ah Subrepresentation.toSubmodule zq.symm
   apply vb;rw[BY];intro v hv;have vG:(⟨zd v,ze v hv⟩:Wp)∈(⊥:Submodule (Qa p) Wp):=
    zB ▸ BW
   rw[Cr] at vG;have h0:zd v=0:=Ah Subtype.val vG;funext i
   exact (Qi p).injective (by rw[EE,Bn];exact An h0 i)⟩⟩
  have vz:zk.IsIrreducible:=⟨fun S=>by
    let S':Submodule (Qa p) (Fin n->Qa p):=
     {carrier:={v | ∃ hv:v∈W,(⟨zd v,ze v hv⟩:Wp)∈S.toSubmodule}
      add_mem':=fun {u v} ⟨huW,huS⟩ ⟨hvW,hvS⟩=>
       ⟨W.add_mem huW hvW,by
        have zT:(⟨zd (u+v),ze _ (W.add_mem huW hvW)⟩:Wp)=
          ⟨zd u,ze u huW⟩+⟨zd v,ze v hvW⟩:=
         Ae (z0 u v)
        rw[zT];exact S.toSubmodule.add_mem huS hvS⟩
      zero_mem':=⟨W.zero_mem,by
       have hz:(⟨zd 0,ze 0 W.zero_mem⟩:Wp)=0:=
        Ae (by funext i;exact Bn (Qi p))
       rw[hz];exact S.toSubmodule.zero_mem⟩
      smul_mem':=fun c {v} ⟨hvW,hvS⟩=>
       ⟨W.smul_mem c hvW,by
        have vQ:(⟨zd (c•v),ze _ (W.smul_mem c hvW)⟩:Wp)=Qi p c•⟨zd v,ze v hvW⟩:=
         Ae (zS c v)
        rw[vQ];exact S.toSubmodule.smul_mem _ hvS⟩ }
    have zN:∀ g∈L,∀ v∈S',(g.val.map ιK).mulVec v∈S':=by
     rintro g hg v ⟨hvW,hvS⟩;refine ⟨zF g hg v hvW,?_⟩;have z4:(⟨zd ((g.val.map ιK).mulVec v),ze _ (zF g hg v hvW)⟩:Wp)=zk ⟨g,hg⟩ ⟨zd v,ze v hvW⟩:=
      Ae (zQ ⟨g,hg⟩ v)
     rw[z4];exact S.apply_mem_toSubmodule ⟨g,hg⟩ hvS
    rcases vc S' (fun _ h=>h.1) zN with zq | zB
    .
     left;apply Subrepresentation.ext;change S.toSubmodule=(⊥:Submodule (Qa p) Wp);rw[BY];intro x hx;have zC:zg x.1∈W:=zp x.1 x.2;have ve:zd (zg x.1)=x.1:=(by funext i;exact (Qi p).apply_symm_apply (x.1 i))
     have zU:zg x.1∈S':=⟨zC,by
      have:(⟨zd (zg x.1),ze _ zC⟩:Wp)=x:=Ae ve
      rw[this];exact hx⟩
     rw[zq,Cr] at zU;apply Ae;rw[<-ve,zU];funext i;exact Bn (Qi p)
    .
     right;apply Subrepresentation.ext;change S.toSubmodule=(⊤:Submodule (Qa p) Wp);rw[Cg];intro x;have zC:zg x.1∈W:=zp x.1 x.2;have ve:zd (zg x.1)=x.1:=(by funext i;exact (Qi p).apply_symm_apply (x.1 i));have zU:zg x.1∈S':=zB ▸ zC;obtain ⟨_,zy⟩:=zU;have:(⟨zd (zg x.1),ze _ zC⟩:Wp)=x:=Ae ve
     exact this ▸ zy⟩
  set d:=Module.finrank (Qa p) W;let bW:Module.Basis (Fin d) (Qa p) W:=Module.finBasis (Qa p) W;let zh:W->Wp:=fun x=>⟨zd x.1,ze x.1 x.2⟩;let zv:Wp->W:=fun y=>⟨zg y.1,zp y.1 y.2⟩;have zw:∀ (f:Fin d->Qa p),zh (∑ i,f i•bW i)=∑ i,Qi p (f i)•zh (bW i):=by intro f;apply Ae;simp only[zh,B4,Bp];funext j;simp only[zd,AQ,AX,Am,Ba,AF]
  have zD:LinearIndependent (Qa p) (fun i:Fin d=>zh (bW i)):=by
   rw[Fintype.linearIndependent_iff];intro f hf i;have h0:∑ k,(Qi p).symm (f k)•bW k=0:=by apply Ae;funext j;apply (Qi p).injective;have h1:=zw (fun k=>(Qi p).symm (f k));have h2:∑ k,Qi p ((Qi p).symm (f k))•zh (bW k)=0:=(by simpa using hf);rw[h2] at h1;have h3:=An (Ah Subtype.val h1) j;change zd (∑ k,(Qi p).symm (f k)•bW k).1 j=0 at h3;rw[Submodule.coe_zero,EE,Bn];exact h3
   have hc:=Fintype.linearIndependent_iff.mp bW.linearIndependent _ h0 i;exact (Qi p).symm.injective (by simpa using hc)
  have zH:⊤<=Submodule.span (Qa p) (Set.range (fun i:Fin d=>zh (bW i))):=by
   intro y _;have hy:zv y=∑ i,bW.repr (zv y) i•bW i:=(bW.sum_repr (zv y)).symm;have vR:y=∑ i,Qi p (bW.repr (zv y) i)•zh (bW i):=by rw[<-zw,<-hy];apply Ae;funext j;exact ((Qi p).apply_symm_apply (y.1 j)).symm
   rw[vR];exact Submodule.sum_mem _ fun i _=>EH _ _ (Submodule.subset_span ⟨i,rfl⟩)
  let zm:Module.Basis (Fin d) (Qa p) Wp:=Module.Basis.mk zD zH;have zE:∀ k,zm k=zh (bW k):=fun k=>Module.Basis.mk_apply zD zH k;have vh:Module.finrank (Qa p) Wp=Module.finrank (Qa p) W:=(by rw[Module.finrank_eq_card_basis zm,AW]);have z5:∀ g:L,zk.character g=zf.character g:=by
   intro g;have vJ:LinearMap.toMatrix zm zm (zk g)=(LinearMap.toMatrix bW bW (zf g)).map (Qi p):=by
    apply Ff;intro i j;have hj:zf g (bW j)=∑ k,(LinearMap.toMatrix bW bW (zf g) k j)•bW k:=by
     have:=(bW.sum_repr (zf g (bW j))).symm
     simpa[Dg] using this
    have vS:zk g (zm j)=∑ k,Qi p (LinearMap.toMatrix bW bW (zf g) k j)•zm k:=by
     have z4:zk g (zm j)=zh (zf g (bW j)):=(by apply Ae;rw[zE];simpa[zh,zk,zf] using (zQ g (bW j).1).symm);rw[z4,hj,zw];refine Ag rfl fun k _=>by rw[zE]
    have zV:=Ah (fun x=>zm.repr x i) vS;rw[Ba,Finsupp.finset_sum_apply] at zV;simp only[Bd,Module.Basis.repr_self,Finsupp.smul_apply,DS,Am,Ca,AK,AS,A8,Ai,↓reduceIte] at zV;simpa[Dg] using zV
   have z6:zk.character g=(zf.character g) ^ p:=(by change LinearMap.trace (Qa p) Wp (zk g)=(LinearMap.trace (Qa p) W (zf g)) ^ p;rw[EU (Qa p) zm (zk g),EU (Qa p) bW (zf g),vJ];simp only[Matrix.trace,D4,AZ];rw[<-Ba (Qi p)];rfl);have vT:(zf g) ^ N=1:=(by rw[<-Dc,hN_def,QC,BI]);have vi:(zf.character g) ^ p=zf.character (g ^ p):=(by change (LinearMap.trace (Qa p) W (zf g)) ^ p=LinearMap.trace (Qa p) W (zf (g ^ p));rw[Dc];exact (Yf vn vM (zf g) vT).symm);have vq:(Nat.card L).Coprime p:=((E1 Fact.out).mpr za).symm;obtain ⟨c,hc⟩:=isConj_iff.mp (zc g p vq);have z7:zf.character (g ^ p)=zf.character g:=(by rw[<-hc];exact zf.char_conj g c);rw[z6,vi,z7]
  have vr:=Representation.char_orthonormal zf zf;have vs:=Representation.char_orthonormal zf zk;have z1:Nonempty (zk.Equiv zf):=by
   by_contra hempty;have h1:(if Nonempty (zf.Equiv zf) then (1:Qa p) else 0)=1:=
    Az ⟨Representation.Equiv.refl zf⟩
   have h2:(if Nonempty (zk.Equiv zf) then (1:Qa p) else 0)=0:=Aw hempty;have zR:(Nat.card L:Qa p)⁻¹*∑ g:L,zf.character g*zk.character g⁻¹=(Nat.card L:Qa p)⁻¹*∑ g:L,zf.character g*zf.character g⁻¹:=by
    congr 1;refine Ag rfl fun g _=>by rw[z5 g⁻¹]
   rw[vs,vr,h1,h2] at zR;exact CX zR
  obtain ⟨zA⟩:=z1;let vC:Module.End (Qa p) (Fin n->Qa p):=
   Wp.subtype.comp (zA.symm.toLinearEquiv.toLinearMap.comp projW)
  let F:Matrix (Fin n) (Fin n) (Qa p):=LinearMap.toMatrix' vC;have zz:∀ v,F.mulVec v=(zA.symm (projW v)).1:=fun v=>by
   rw[<-Aj,Matrix.toLin'_toMatrix'];rfl
  have vj:∀ g:L,F*g.1.val.map ιK=g.1.val.map ιK*F:=by
   intro g;apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac,zz];have vk:projW ((g.1.val.map ιK).mulVec v)=zf g (projW v):=by apply Ae;rw[<-zi];have h1:=Ah (fun M:Matrix (Fin n) (Fin n) (Qa p)=>M.mulVec v) (zu g);simp only[<-Ac] at h1;rw[h1,zi];rfl
   rw[vk];have vK:=BV (zA.symm.isIntertwining' g) (projW v);exact Ah Subtype.val vK
  have vU:F*P=F:=by
   apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac,zz];have:projW (P.mulVec v)=projW v:=by rw[zi];exact CF zj (projW v)
   rw[this]
  have z8:Wp<=W:=by
   intro y hy;let x:W:=zA ⟨y,hy⟩;have vD:F.mulVec x.1=y:=by rw[zz];have hx:projW x.1=x:=CF zj x;rw[hx];exact Ah Subtype.val (zA.symm_apply_apply ⟨y,hy⟩)
   have vV:P*F=F:=(zP P F zu vj).trans vU;rw[<-vD,<-vV,<-Ac];exact zo _
  have zO:Wp=W:=EQ z8 vh.ge;have vE:P*Pp=Pp:=(by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];have zy:Pp.mulVec v∈W:=zO ▸ ⟨v,rfl⟩;exact zn _ zy);have vF:Pp*P=P:=(by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];have zy:P.mulVec v∈Wp:=zO.symm ▸ zo v;obtain ⟨u,hu⟩:=zy;rw[<-hu,Aj,Ac,zZ]);have z9:Pp=P:=by
   calc Pp=P*Pp:=vE.symm
   _ = Pp*P:=zP P Pp zu zM
   _ = P:=vF
  have vt:∀ i j,∃ c:ZMod p,ιK c=P i j:=(by intro i j;have vL:(P i j) ^ p=P i j:=Ah (fun M:Matrix (Fin n) (Fin n) (Qa p)=>M i j) z9;exact Q6 vL);choose P0 hP0 using vt;let P₀:Matrix (Fin n) (Fin n) (ZMod p):=Matrix.of P0;have zs:P=P₀.map ιK:=by ext i j;exact (hP0 i j).symm
  have va:∀ g∈L,P₀*g.val=g.val*P₀:=(by intro g hg;apply C9 ιK.injective;dsimp only;rw[Aq,Aq,<-zs];exact zu ⟨g,hg⟩);have z2:P₀*P₀=P₀:=(by apply C9 ιK.injective;dsimp only;rw[Aq,<-zs];exact zL);have vu:P₀≠0:=by
   intro h0;have vl:P=0:=by rw[zs,h0];ext i j;simp
   apply vb;rw[BY];intro v hv;rw[<-zn v hv,vl,BF]
  have zW:∀ g∈L,∀ v∈LinearMap.range (Matrix.toLin' P₀),g.val.mulVec v∈LinearMap.range (Matrix.toLin' P₀):=(by rintro g hg _ ⟨v,rfl⟩;refine ⟨g.val.mulVec v,?_⟩;simp only[Aj,Ac];rw[va g hg]);have zI:LinearMap.range (Matrix.toLin' P₀)≠⊥:=(by intro zq;apply vu;apply Matrix.toLin'.injective;apply Ap;intro v;have:Matrix.toLin' P₀ v∈(⊥:Submodule (ZMod p) (Fin n->ZMod p)):=zq ▸ ⟨v,rfl⟩;simpa using this);have zX:LinearMap.range (Matrix.toLin' P₀)=⊤:=
   (zb _ zW).resolve_left zI
  have vm:P₀=1:=(by apply Matrix.toLin'.injective;apply Ap;intro v;have hv:v∈LinearMap.range (Matrix.toLin' P₀):=zX ▸ BW;obtain ⟨u,rfl⟩:=hv;simp only[Aj,Ac,z2,AC]);have vv:P=1:=by
   rw[zs,vm];ext i j;by_cases h:i=j
   . subst h;simp
   . simp[h]
  have vw:W=⊤:=by
   rw[Cg];intro v
   have:=zo v
   simpa[vv] using this
  exact top_le_iff.mp (vw ▸ vH)
lemma Wu {p:ℕ} [Fact p.Prime] (zf:7<=p)
  {n:ℕ} (hn_pos:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))) (zb:¬ p∣Nat.card L) (zd:Qw L) (zc:∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤) (za:∀ U:Submodule (Qa p) (Fin n->Qa p), (∀ g∈L,∀ v∈U,(g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v∈U)-> U=⊥\/U=⊤) (ze:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) : ∃ B:Matrix (Fin n) (Fin n) (ZMod p), Bᵀ=-B/\B.det≠0/\∀ g∈L,g.valᵀ*B*g.val=B:=by
 classical
 let ιK:=algebraMap (ZMod p) (Qa p);have zo:(Nat.card L:Qa p)≠0:=(by intro h;have h1:(Nat.card L:ZMod p)=0:=(by apply ιK.injective;rw[DO,Bn];exact h);exact zb ((At (Nat.card L) p).mp h1));have:NeZero (Nat.card L:Qa p):=⟨zo⟩;have:Invertible (Nat.card L:Qa p):=invertibleOfNonzero zo;let zg:Representation (Qa p) L (Fin n->Qa p):=
  {toFun:=fun g=>Matrix.toLin' (g.1.val.map ιK)
   map_one':=by
    apply Ap;intro v;have h1:(1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK=1:=by
     ext i j;by_cases h:i=j
     . subst h;simp
     . simp[h]
    change (Matrix.toLin' ((1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK)) v=v;rw[h1];simp
   map_mul':=fun g₁ g₂=>by
    apply Ap;intro v;have hm:(g₁.1.val*g₂.1.val).map ιK=g₁.1.val.map ιK*g₂.1.val.map ιK:=
     Aq
    change ((g₁.1.val*g₂.1.val).map ιK).mulVec v=(g₁.1.val.map ιK).mulVec ((g₂.1.val.map ιK).mulVec v)
    rw[hm,Ac] }
 have:Nontrivial (Subrepresentation zg):=⟨⟨⊥,⊤,fun hbot=>by
  have zq:(⊤:Submodule (Qa p) (Fin n->Qa p))=(⊥:Submodule (Qa p) (Fin n->Qa p)):=
   Ah Subrepresentation.toSubmodule hbot.symm
  have hv:(Pi.single ⟨0,hn_pos⟩ (1:Qa p):Fin n->Qa p)∈(⊥:Submodule (Qa p) (Fin n->Qa p)):=zq ▸ BW;rw[Cr] at hv;have h0:=An hv ⟨0,hn_pos⟩
  simp at h0⟩⟩
 have z3:zg.IsIrreducible:=⟨fun S=>by
  rcases za S.toSubmodule (fun g hg _ hv=>S.apply_mem_toSubmodule ⟨g,hg⟩ hv) with hbot | zq
  . left;exact Subrepresentation.ext hbot
  . right;exact Subrepresentation.ext zq⟩
 have zy:∀ g:L,zg.character g⁻¹=zg.character g:=by
  intro g;have zN:0 < Nat.card L:=CD;have ve:(Nat.card L).Coprime (Nat.card L - 1):=by
   rcases Nat.eq_or_lt_of_le zN with h1 | _
   . rw[<-h1];simp
   .
    have z4:Nat.card L=(Nat.card L - 1)+1:=by omega
    rw[z4];exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have vf:g ^ (Nat.card L - 1)=g⁻¹:=(by apply eq_inv_of_mul_eq_one_left;rw[<-DK,Dk zN,QC]);obtain ⟨c,hc⟩:=isConj_iff.mp (vf ▸ zd g (Nat.card L - 1) ve);rw[<-hc];exact zg.char_conj g c
 have zz:Module.finrank (Qa p) (Representation.IntertwiningMap zg zg.dual)=1:=by
  have h1:=Representation.card_inv_mul_sum_char_mul_char_eq_finrank zg zg.dual;have h2:=Representation.card_inv_mul_sum_char_mul_char_eq_finrank zg zg;have vg:(Nat.card L:Qa p)⁻¹*∑ g:L,zg.dual.character g*zg.character g⁻¹=(Nat.card L:Qa p)⁻¹*∑ g:L,zg.character g*zg.character g⁻¹:=(by congr 1;refine Ag rfl fun g _=>?_;rw[Representation.char_dual,zy g]);have zI:Module.finrank (Qa p) (Representation.IntertwiningMap zg zg)=1:=
   Representation.IsIrreducible.finrank_intertwiningMap_self zg
  have vd:(Module.finrank (Qa p) (Representation.IntertwiningMap zg zg.dual):Qa p)=1:=(by rw[<-h1,vg,h2,zI,Nat.cast_one]);have vh:Module.finrank (Qa p) (Representation.IntertwiningMap zg zg.dual)≠0:=(by intro h0;rw[h0,Nat.cast_zero] at vd;exact CX vd);have vn:Nontrivial (Representation.IntertwiningMap zg zg.dual):=
   ER (CM vh)
  obtain ⟨f,vb⟩:=exists_ne (0:Representation.IntertwiningMap zg zg.dual);have zJ:Function.Injective f:=(Representation.IsIrreducible.injective_or_eq_zero f).resolve_right vb;have z5:Function.Bijective f:=by
   have zK:Module.finrank (Qa p) (Fin n->Qa p)=Module.finrank (Qa p) (Module.Dual (Qa p) (Fin n->Qa p)):=
    (Subspace.dual_finrank_eq).symm
   exact ⟨zJ,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank zK).mp zJ⟩
  let zw:zg.Equiv zg.dual:=f.ofBijective z5;let vo:Representation.IntertwiningMap zg zg≃ₗ[Qa p] Representation.IntertwiningMap zg zg.dual:=
   {toFun:=fun u=>zw.toIntertwiningMap.comp u
    invFun:=fun v=>zw.symm.toIntertwiningMap.comp v
    left_inv:=fun u=>Representation.IntertwiningMap.ext (Ap fun x=>zw.symm_apply_apply (u x))
    right_inv:=fun v=>Representation.IntertwiningMap.ext (Ap fun x=>zw.apply_symm_apply (v x))
    map_add':=fun u₁ u₂=>Representation.IntertwiningMap.ext (Ap fun x=>by simp)
    map_smul':=fun c u=>Representation.IntertwiningMap.ext (Ap fun x=>by simp) }
  rw[<-vo.finrank_eq,zI]
 let InvMatK:Submodule (Qa p) (Matrix (Fin n) (Fin n) (Qa p)):=
  {carrier:={B | ∀ g:L,(g.1.val.map ιK)ᵀ*B*g.1.val.map ιK=B}
   add_mem':=fun {A B} hA hB g=>by rw[EM,add_mul,hA g,hB g]
   zero_mem':=fun g=>by simp
   smul_mem':=fun c {A} hA g=>by rw[Ao,Ar,hA g] }
 have zl:∀ w:Fin n->Qa p,w=∑ k:Fin n,w k•(Pi.single k (1:Qa p):Fin n->Qa p):=(by intro w;funext i;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]);let zC:Representation.IntertwiningMap zg zg.dual≃ₗ[Qa p] InvMatK:=
  {toFun:=fun f=>
    ⟨Matrix.of fun i j=>f (Pi.single j 1) (Pi.single i 1),by
     intro g;ext i j;have vp:∀ u v,f ((g.1.val.map ιK).mulVec u) ((g.1.val.map ιK).mulVec v)=f u v:=by
      intro u v;have h1:=Ah (fun φ=>φ ((g.1.val.map ιK).mulVec v))
       (BV (f.isIntertwining' g) u)
      change f ((g.1.val.map ιK).mulVec u) ((g.1.val.map ιK).mulVec v)=f u (((g⁻¹).1.val.map ιK).mulVec ((g.1.val.map ιK).mulVec v)) at h1;rw[h1,Ac,<-Aq];have zn:(g⁻¹).1.val*g.1.val=1:=g.1.inv_val;rw[zn];have z6:(1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK=1:=by
       ext a b;by_cases h:a=b
       . subst h;simp
       . simp[h]
      rw[z6,AN]
     have vi:∀ u v,f u v=∑ a,∑ b,v a*(f (Pi.single b 1) (Pi.single a 1))*u b:=by
      intro u v
      conv_lhs=>rw[zl u,zl v]
      rw[Ba];refine Ag rfl fun a _=>?_;rw[Bd,Ba,CV,BC];refine Ag rfl fun b _=>?_;simp only[Bd,AU,Am];ring
     have zO:∀ k,(g.1.val.map ιK).mulVec (Pi.single k 1)=fun a=>(g.1.val.map ιK) a k:=(by intro k;funext a;simp only[Matrix.mulVec,dotProduct,AZ,AG,Ca,AK,AS,A8,Ai,↓reduceIte]);have zP:=vp (Pi.single j 1) (Pi.single i 1);rw[vi,zO,zO] at zP;rw[AY] at zP
     simpa[Av,AM,Bo,A6,Ad] using zP⟩
   invFun:=fun B=>
    {toLinearMap:=
      {toFun:=fun u=>
        {toFun:=fun v=>dotProduct v (B.1.mulVec u)
         map_add':=fun v₁ v₂=>add_dotProduct v₁ v₂ _
         map_smul':=fun c v=>smul_dotProduct c v _ }
       map_add':=fun u₁ u₂=>Ap fun v=>by simp[A3,dotProduct_add]
       map_smul':=fun c u=>Ap fun v=>by simp[Al,dotProduct_smul] }
     isIntertwining':=fun g=>Ap fun u=>Ap fun v=>by
      change dotProduct v (B.1.mulVec ((g.1.val.map ιK).mulVec u))=dotProduct (((g⁻¹).1.val.map ιK).mulVec v) (B.1.mulVec u);have hB:=B.2 g⁻¹;have z7:(g⁻¹).1.val.map ιK*g.1.val.map ιK=1:=by
       rw[<-Aq];change (g.1.inv*g.1.val).map ιK=1;rw[g.1.inv_val];ext a b;by_cases h:a=b
       . subst h;simp
       . simp[h]
      calc dotProduct v (B.1.mulVec ((g.1.val.map ιK).mulVec u))
        = dotProduct v (((((g⁻¹).1.val.map ιK)ᵀ*B.1*(g⁻¹).1.val.map ιK)*g.1.val.map ιK).mulVec u):=by rw[hB,Ac]
      _ = dotProduct v ((((g⁻¹).1.val.map ιK)ᵀ*B.1).mulVec u):=by rw[Af,Af,z7,As]
      _ = dotProduct (((g⁻¹).1.val.map ιK).mulVec v) (B.1.mulVec u):=by
             rw[<-Ac,AB,AI] }
   left_inv:=fun f=>Representation.IntertwiningMap.ext (Ap fun u=>Ap fun v=>by
    change dotProduct v ((Matrix.of fun i j=>f (Pi.single j 1) (Pi.single i 1)).mulVec u)=f u v
    conv_rhs=>rw[zl u,zl v]
    simp only[dotProduct,Matrix.mulVec,Ak,Ba,CV,Bd,AU,Am];refine Ag rfl fun a _=>?_;rw[A6,A6];refine Ag rfl fun b _=>?_
    ring)
   right_inv:=fun B=>by
    apply Ae;ext i j;change dotProduct (Pi.single i 1) (B.1.mulVec (Pi.single j 1))=B.1 i j;simp[dotProduct,Matrix.mulVec,AG]
   map_add':=fun f₁ f₂=>by apply Ae;ext i j;rfl
   map_smul':=fun c f=>by apply Ae;ext i j;rfl }
 have zj:Module.finrank (Qa p) InvMatK=1:=(by rw[<-zC.finrank_eq,zz]);have z2:Nontrivial InvMatK:=ER (by rw[zj];exact Nat.zero_lt_one);obtain ⟨BK,zs⟩:=exists_ne (0:InvMatK);have zL:BK.1≠0:=fun h=>zs (Ae h);obtain ⟨B,zk,zM⟩:=W7 (fun g:L=>g.1.val) BK.1 zL BK.2;have zi:∀ g∈L,g.valᵀ*B*g.val=B:=fun g hg=>zM ⟨g,hg⟩;have zQ:B.det≠0:=by
  have zD:∀ g∈L,∀ v∈LinearMap.ker (Matrix.toLin' B),g.val.mulVec v∈LinearMap.ker (Matrix.toLin' B):=by
   intro g hg v hv;rw[Bf,Aj] at hv ⊢;have h1:g.valᵀ.mulVec (B.mulVec (g.val.mulVec v))=0:=(by rw[Ac,Ac,zi g hg,hv]);have zn:g.invᵀ*g.valᵀ=1:=(by rw[<-AT,g.val_inv,BM])
   calc B.mulVec (g.val.mulVec v)=(g.invᵀ*g.valᵀ).mulVec (B.mulVec (g.val.mulVec v)):=by rw[zn,AN]
   _ = g.invᵀ.mulVec (g.valᵀ.mulVec (B.mulVec (g.val.mulVec v))):=(Ac _ _ _).symm
   _ = 0:=by rw[h1,DZ]
  have zt:LinearMap.ker (Matrix.toLin' B)≠⊤:=(by intro zq;apply zk;apply Matrix.toLin'.injective;apply Ap;intro v;have:v∈LinearMap.ker (Matrix.toLin' B):=zq ▸ BW;simpa using this);have zE:LinearMap.ker (Matrix.toLin' B)=⊥:=(zc _ zD).resolve_right zt;intro vc;obtain ⟨v,zx,vs⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr vc;have zA:v∈LinearMap.ker (Matrix.toLin' B):=by simpa[Aj] using vs
  rw[zE,Cr] at zA;exact zx zA
 have zr:∀ g∈L,g.valᵀ*Bᵀ*g.val=Bᵀ:=(by intro g hg;have h:=Ah Matrix.transpose (zi g hg);simpa[AT,Af] using h);have zp:∃ c:ZMod p,Bᵀ=c•B:=by
  have zh:B.map ιK∈InvMatK:=fun g=>by
   have h:=Ah (Matrix.map · ιK) (zi g.1 g.2);have zR:(g.1.valᵀ).map ιK=(g.1.val.map ιK)ᵀ:=by ext a b;rfl
   rwa[Aq,Aq,zR] at h
  have zS:Bᵀ.map ιK∈InvMatK:=fun g=>by
   have h:=Ah (Matrix.map · ιK) (zr g.1 g.2);have zR:(g.1.valᵀ).map ιK=(g.1.val.map ιK)ᵀ:=by ext a b;rfl
   rwa[Aq,Aq,zR] at h
  have zF:(⟨B.map ιK,zh⟩:InvMatK)≠0:=(by intro h0;apply zk;apply C9 ιK.injective;simpa using Ah Subtype.val h0);have z8:Submodule.span (Qa p) {(⟨B.map ιK,zh⟩:InvMatK)}=⊤:=(by apply EV;rw[zj,finrank_span_singleton zF]);have zT:(⟨Bᵀ.map ιK,zS⟩:InvMatK)∈Submodule.span (Qa p) {(⟨B.map ιK,zh⟩:InvMatK)}:=
   z8 ▸ BW
  rw[Submodule.mem_span_singleton] at zT;obtain ⟨cK,zu⟩:=zT;have zU:cK•B.map ιK=Bᵀ.map ιK:=Ah Subtype.val zu;have zV:∃ a b,B a b≠0:=(by by_contra hall;push Not at hall;exact zk (Ff hall));obtain ⟨a,b,vt⟩:=zV;refine ⟨B b a / B a b,?_⟩;apply C9 ιK.injective;dsimp only;have zW:cK=ιK (B b a / B a b):=by have zX:=Ah (fun M:Matrix (Fin n) (Fin n) (Qa p)=>M a b) zU;simp only[A2,AZ,AM,Am] at zX;rw[map_div₀];exact eq_div_of_mul_eq (by simpa using vt) zX
  rw[<-zU,zW];ext i j;simp[Am]
 obtain ⟨c0,zm⟩:=zp;have zY:c0 ^ 2=1:=by
  have h1:B=(c0*c0)•B:=by
   calc B=Bᵀᵀ:=(Cc B).symm
   _ = (c0•B)ᵀ:=by rw[zm]
   _ = c0•Bᵀ:=Ch c0 B
   _ = c0•(c0•B):=by rw[zm]
   _ = (c0*c0)•B:=AR c0 c0 B
  have vj:(c0*c0 - 1)•B=0:=by rw[DJ,Bx,<-h1,Cx]
  have vk:c0*c0 - 1=0:=(smul_eq_zero.mp vj).resolve_right zk;simpa[sq] using sub_eq_zero.mp vk
 have zZ:Bᵀ=-B:=by
  rcases sq_eq_one_iff.mp zY with hc1 | hcneg
  .
   exfalso;rw[hc1,Bx] at zm;have z0:(2:ZMod p)≠0:=by intro h2;have zG:p∣2:=(At 2 p).mp (by simpa using h2);have vq:=AP (by decide) zG;omega
   have vl:(3:ZMod p)≠0:=(by intro h3;have zG:p∣3:=(At 3 p).mp (by simpa using h3);have vq:=AP (by decide) zG;omega);have zH:∃ v:Fin n->ZMod p,dotProduct v (B.mulVec v)≠0:=by
    by_contra hall;push Not at hall;have vr:∀ u v:Fin n->ZMod p,dotProduct u (B.mulVec v)=0:=by
     intro u v;have z1:dotProduct (u+v) (B.mulVec (u+v))=dotProduct u (B.mulVec u)+dotProduct u (B.mulVec v)+dotProduct v (B.mulVec u)+dotProduct v (B.mulVec v):=(by simp only[A3,add_dotProduct,dotProduct_add];ring);have vm:dotProduct v (B.mulVec u)=dotProduct u (B.mulVec v):=(by rw[dotProduct_comm,AB,<-AI,zm,<- AB,dotProduct_comm]);rw[hall (u+v),hall u,hall v,vm] at z1;have z9:(2:ZMod p)*dotProduct u (B.mulVec v)=0:=by linear_combination -z1
     exact (mul_eq_zero.mp z9).resolve_left z0
    apply zk;ext i j
    have:=vr (Pi.single i 1) (Pi.single j 1)
    simpa[dotProduct,Matrix.mulVec,AG] using this
   obtain ⟨v,zv⟩:=zH;have zx:v≠0:=fun h=>zv (by simp[h]);obtain ⟨g,vu,vv⟩:=ze v zx (Units.mk0 2 z0);have zB:dotProduct (g.val.mulVec v) (B.mulVec (g.val.mulVec v))=dotProduct v (B.mulVec v):=by
    calc dotProduct (g.val.mulVec v) (B.mulVec (g.val.mulVec v))
      = dotProduct (Matrix.vecMul v g.valᵀ) (B.mulVec (g.val.mulVec v)):=by rw[AI]
    _ = dotProduct v (g.valᵀ.mulVec (B.mulVec (g.val.mulVec v))):=
       (AB _ _ _).symm
    _ = dotProduct v ((g.valᵀ*B*g.val).mulVec v):=by simp only[Ac,Af]
    _ = dotProduct v (B.mulVec v):=by rw[zi g vu]
   rw[vv,DG,Al,smul_dotProduct,dotProduct_smul,Am,Am] at zB;have va:(3:ZMod p)*dotProduct v (B.mulVec v)=0:=by linear_combination zB
   exact zv ((mul_eq_zero.mp va).resolve_left vl)
  . rw[zm,hcneg,neg_one_smul]
 exact ⟨B,zZ,zQ,zi⟩
lemma W1 {p:ℕ} [Fact p.Prime] (zi:7<=p)
  {n:ℕ} (hn_pos:0 < n) (L:Subgroup (Aa (Fin n) (ZMod p))) (zg:Group.IsSolvable L) (zb:¬ p∣Nat.card L) (zc:Qw L) (zh:Qd n p∈L) (zd:∀ U:Submodule (ZMod p) (Fin n->ZMod p), (∀ g∈L,∀ v∈U,g.val.mulVec v∈U)->U=⊥\/U=⊤) (zf:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) : ∃ (N:ℕ) (za:0 < N) (ze:¬ p∣N) (ι:Ab N (Qa p)≃*Ab N ℂ), Nonempty (Qg p N za ze ι):=by
 set N:=Nat.card L with hN_def
 have za:0 < N:=CD;have ze:¬ p∣N:=zb;obtain ⟨ι⟩:=WI (p:=p) za ze;refine ⟨N,za,ze,ι,?_⟩;let ιK:=algebraMap (ZMod p) (Qa p);have zk:=Yc hn_pos L zb zc zd;obtain ⟨B,zp,zq,zr⟩:=
  Wu zi hn_pos L zb zc zd zk zf
 let zj:Representation (Qa p) L (Fin n->Qa p):=
  {toFun:=fun g=>Matrix.toLin' (g.1.val.map ιK)
   map_one':=by
    apply Ap;intro v;have h1:(1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK=1:=by
     ext i j;by_cases h:i=j
     . subst h;simp
     . simp[h]
    change (Matrix.toLin' ((1:Matrix (Fin n) (Fin n) (ZMod p)).map ιK)) v=v;rw[h1];simp
   map_mul':=fun g₁ g₂=>by
    apply Ap;intro v;have hm:(g₁.1.val*g₂.1.val).map ιK=g₁.1.val.map ιK*g₂.1.val.map ιK:=
     Aq
    change ((g₁.1.val*g₂.1.val).map ιK).mulVec v=(g₁.1.val.map ιK).mulVec ((g₂.1.val.map ιK).mulVec v)
    rw[hm,Ac] }
 have zo:∀ g∈L,∃ q:ℚ,Qr za ze ι (Fin n->Qa p) (Matrix.toLin' (g.val.map ιK))=(q:ℂ):=by
  intro g zn;have zs:(Matrix.toLin' (g.val.map ιK)) ^ N=1:=by
   have h1:(zj ⟨g,zn⟩) ^ N=1:=by rw[<-Dc,hN_def,QC,BI]
   exact h1
  apply Wn za ze ι _ zs;intro m hm;obtain ⟨c,hc⟩:=isConj_iff.mp (zc ⟨g,zn⟩ m hm);let e:(Fin n->Qa p)≃ₗ[Qa p] (Fin n->Qa p):=
   {toLinearMap:=zj c
    invFun:=zj c⁻¹
    left_inv:=fun v=>by
     have h:=BV (by rw[<-Module.End.mul_eq_comp,<-AF,CK,BI] :
      zj c⁻¹∘ₗzj c=1) v
     exact h
    right_inv:=fun v=>by
     have h:=BV (by rw[<-Module.End.mul_eq_comp,<-AF,By,BI] :
      zj c∘ₗzj c⁻¹=1) v
     exact h }
  refine ⟨e,?_⟩;have zm:e.toLinearMap∘ₗzj ⟨g,zn⟩∘ₗe.symm.toLinearMap=zj (c*⟨g,zn⟩*c⁻¹):=by apply Ap;intro v;rw[AF,AF];rfl
  rw[hc,Dc] at zm;exact zm
 have zl:QQ (⟨Qd n p,zh⟩:L):=
  WS (G:=L) ⟨Qd n p,zh⟩ zc
 exact ⟨{
  n:=n
  hn_pos:=hn_pos
  L:=L
  solvable:=zg
  card_dvd:=EO N
  negOne_mem:=zh
  realMinus:=zl
  ratTr:=zo
  absIrred:=zk
  SF:=zf
  B:=B
  B_alt:=zp
  B_det:=zq
  B_inv:=zr
 }⟩
end Section2Admissible
section Section3Quartics
variable {p:ℕ} [Fact p.Prime]
noncomputable def Qz {R:Type*} [CommSemiring R] {n:ℕ} (M:Matrix (Fin n) (Fin n) R) (F:MvPolynomial (Fin n) R):MvPolynomial (Fin n) R:=
 MvPolynomial.aeval (fun i=>∑ j:Fin n,MvPolynomial.C (M i j)*MvPolynomial.X j) F
lemma Yg {R:Type*} [CommSemiring R] {n:ℕ} (M:Matrix (Fin n) (Fin n) R) (F:MvPolynomial (Fin n) R) (v:Fin n->R) : MvPolynomial.eval v (Qz M F)=MvPolynomial.eval (M.mulVec v) F:=by
 let lhs:MvPolynomial (Fin n) R →ₐ[R] R:=
  (MvPolynomial.aeval v).comp
   (MvPolynomial.aeval (fun i=>∑ j:Fin n,MvPolynomial.C (M i j)*MvPolynomial.X j))
 let rhs:MvPolynomial (Fin n) R →ₐ[R] R:=MvPolynomial.aeval (M.mulVec v);have za:lhs=rhs:=(by apply MvPolynomial.algHom_ext;intro i;simp only[lhs,rhs,AlgHom.comp_apply,MvPolynomial.aeval_X,Ba,AF,Es,Algebra.algebraMap_self,DE,Matrix.mulVec,dotProduct]);have h:=AlgHom.congr_fun za F;simp only[lhs,rhs,AlgHom.comp_apply,Qz,MvPolynomial.aeval_def,Algebra.algebraMap_self] at h;exact h
lemma YP {R S:Type*} [CommSemiring R] [CommSemiring S] {n:ℕ} (f:R →+*S) (M:Matrix (Fin n) (Fin n) R) (F:MvPolynomial (Fin n) R) : Qz (M.map f) (MvPolynomial.map f F)=MvPolynomial.map f (Qz M F):=by
 induction F using MvPolynomial.induction_on with
 | C a=>
  simp[Qz]
 | add F₁ F₂ ih₁ ih₂=>
  simp only[EN,Qz] at ih₁ ih₂ ⊢;rw[ih₁,ih₂]
 | mul_X F i ih=>
  simp only[AF,MvPolynomial.map_X,Qz,MvPolynomial.aeval_X,Ba,MvPolynomial.map_C,AZ] at ih ⊢;rw[ih]
lemma Q1 {R:Type*} [CommSemiring R] {n r:ℕ}
  {F:MvPolynomial (Fin n) R} (hF:F.IsHomogeneous r) (c:R) (v:Fin n->R) : MvPolynomial.eval (c•v) F=c ^ r*MvPolynomial.eval v F:=by
 conv_lhs=>rw[F.as_sum]
 conv_rhs=>rw[F.as_sum]
 rw[Ba,Ba,A6];refine Ag rfl fun d hd=>?_;rw[Fd,Fd];have za:(d.prod fun i e=>(c•v) i ^ e)=c ^ r*(d.prod fun i e=>v i ^ e):=by simp only[Finsupp.prod,AX,Am,CC,Finset.prod_mul_distrib];congr 1;rw[Finset.prod_pow_eq_pow_sum];congr 1;exact (hF.degree_eq_sum_deg_support hd).symm
 rw[za];ring
lemma YB {n r:ℕ} (L:Subgroup (Aa (Fin n) (ZMod p))) (F:MvPolynomial (Fin n) (Qa p)) (zc:F≠0) (za:F.IsHomogeneous r) (zb:∀ g∈L,∀ v:Fin n->Qa p, MvPolynomial.eval ((g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v) F= MvPolynomial.eval v F) : ∃ F₀:MvPolynomial (Fin n) (ZMod p), F₀≠0/\F₀.IsHomogeneous r/\ ∀ g∈L,∀ v:Fin n->ZMod p,MvPolynomial.eval (g.val.mulVec v) F₀=MvPolynomial.eval v F₀:=by
 classical
 let ze:=algebraMap (ZMod p) (Qa p);have zh:∀ g∈L,Qz (g.val.map ze) F=F:=(by intro g hg;apply MvPolynomial.funext;intro v;rw[Yg];exact zb g hg v);obtain ⟨zm,zp⟩:=MvPolynomial.exists_coeff_ne_zero zc;obtain ⟨φ,zo⟩:=QO (p:=p) zp;let F₀:MvPolynomial (Fin n) (ZMod p):=
  ∑ m∈F.support,MvPolynomial.monomial m (φ (MvPolynomial.coeff m F))
 have zd:∀ m:Fin n →₀ ℕ,MvPolynomial.coeff m F₀=φ (MvPolynomial.coeff m F):=by
  intro m;simp only[F₀,Eh,MvPolynomial.coeff_monomial];by_cases hm:m∈F.support
  . rw[A8 F.support m,Az hm]
  . rw[A8 F.support m,Aw hm,MvPolynomial.notMem_support_iff.mp hm,Bn]
 have zk:F₀≠0:=by
  intro h0
  have:=Ah (MvPolynomial.coeff zm) h0
  rw[zd,MvPolynomial.coeff_zero] at this;exact zo this
 have zi:F₀.IsHomogeneous r:=(by intro m hm;rw[zd] at hm;have zq:MvPolynomial.coeff m F≠0:=fun h0=>hm (by rw[h0,Bn]);exact za zq);have zf:∀ g∈L,Qz g.val F₀=F₀:=by
  intro g hg;ext m';have zj:Qz (g.val.map ze) F=∑ m∈F.support,MvPolynomial.C (MvPolynomial.coeff m F)*MvPolynomial.map ze (Qz g.val (MvPolynomial.monomial m 1)):=by
   conv_lhs=>rw[F.as_sum]
   simp only[Qz,Ba];refine Ag rfl fun m _=>?_;have zl:MvPolynomial.monomial m (MvPolynomial.coeff m F)=MvPolynomial.C (MvPolynomial.coeff m F)*MvPolynomial.map ze (MvPolynomial.monomial m (1:ZMod p)):=(by rw[MvPolynomial.map_monomial,BI,MvPolynomial.C_mul_monomial,AK]);rw[zl,AF,Es];change MvPolynomial.C (MvPolynomial.coeff m F)*Qz (g.val.map ze) (MvPolynomial.map ze (MvPolynomial.monomial m (1:ZMod p)))=_;rw[YP];rfl
  have zg:Qz g.val F₀=∑ m∈F.support,MvPolynomial.C (φ (MvPolynomial.coeff m F))*Qz g.val (MvPolynomial.monomial m 1):=(by simp only[F₀,Qz,Ba];refine Ag rfl fun m _=>?_;have zl:MvPolynomial.monomial m (φ (MvPolynomial.coeff m F))=MvPolynomial.C (φ (MvPolynomial.coeff m F))*MvPolynomial.monomial m 1:=(by rw[MvPolynomial.C_mul_monomial,AK]);rw[zl,AF,Es];rfl);have h1:MvPolynomial.coeff m' (Qz (g.val.map ze) F)=∑ m∈F.support,MvPolynomial.coeff m F*ze (MvPolynomial.coeff m' (Qz g.val (MvPolynomial.monomial m 1))):=(by rw[zj,Eh];refine Ag rfl fun m _=>?_;rw[MvPolynomial.coeff_C_mul,MvPolynomial.coeff_map]);have h2:MvPolynomial.coeff m' (Qz g.val F₀)=∑ m∈F.support,φ (MvPolynomial.coeff m F)*MvPolynomial.coeff m' (Qz g.val (MvPolynomial.monomial m 1)):=(by rw[zg,Eh];refine Ag rfl fun m _=>?_;rw[MvPolynomial.coeff_C_mul]);have zn:φ (MvPolynomial.coeff m' (Qz (g.val.map ze) F))=MvPolynomial.coeff m' (Qz g.val F₀):=(by rw[h1,Ba,h2];refine Ag rfl fun m _=>?_;have zr:MvPolynomial.coeff m F*ze (MvPolynomial.coeff m' (Qz g.val (MvPolynomial.monomial m 1)))=(MvPolynomial.coeff m' (Qz g.val (MvPolynomial.monomial m 1)))•MvPolynomial.coeff m F:=(by rw[Ed,Bb]);rw[zr,Bd,Am,Bb]);rw[<-zn,zh g hg,zd]
 refine ⟨F₀,zk,zi,fun g hg v=>?_⟩;rw[<-Yg,zf g hg]
lemma QW {n r:ℕ} (L:Subgroup (Aa (Fin n) (ZMod p))) (zd:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) (ze:1<=r) (zc:r < p) (a:(ZMod p)ˣ) (ha:(a:ZMod p) ^ r≠1) (F:MvPolynomial (Fin n) (Qa p)) (za:F.IsHomogeneous r) (zb:∀ g∈L,∀ v:Fin n->Qa p, MvPolynomial.eval ((g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v) F= MvPolynomial.eval v F) : F=0:=by
 classical
 by_contra hF_ne;obtain ⟨zf,zn,zg,zj⟩:=YB L F hF_ne za zb;have zr:∃ v:Fin n->ZMod p,MvPolynomial.eval v zf≠0:=by
  by_contra hall;push Not at hall;have zs:r<=Fintype.card (ZMod p):=by rw[Ey];omega
  have zo:=MvPolynomial.schwartz_zippel_totalDegree zn (Finset.univ:Finset (ZMod p));have zx:(Fintype.piFinset fun _:Fin n=>(Finset.univ:Finset (ZMod p)))=Finset.univ:=(by ext f;simp);have zt:(Finset.univ.filter fun f:Fin n->ZMod p=>MvPolynomial.eval f zf=0)=Finset.univ:=(by ext f;simp[hall f]);rw[zx,zt] at zo;have zl:(Finset.univ:Finset (Fin n->ZMod p)).card=p ^ n:=(by rw[BS,Cl,Ey,AW]);have zm:(Finset.univ:Finset (ZMod p)).card=p:=(by rw[BS,Ey]);rw[zl,zm] at zo;have zi:(0:ℚ≥0) < (p:ℚ≥0):=by exact_mod_cast (Fact.out:p.Prime).pos
  have zp:(0:ℚ≥0) < ((p:ℚ≥0) ^ n):=pow_pos zi n;have zu:((p ^ n:ℕ):ℚ≥0) / ((p:ℚ≥0) ^ n)=1:=(by push_cast;exact div_self zp.ne');rw[zu] at zo;have zq:zf.totalDegree<=r:=zg.totalDegree_le;have zv:(zf.totalDegree:ℚ≥0) / (p:ℚ≥0) < 1:=by rw[div_lt_one zi];exact_mod_cast lt_of_le_of_lt zq zc
  exact not_lt_of_ge zo zv
 obtain ⟨v,zk⟩:=zr;have zh:v≠0:=by
  intro h0;subst h0;have zw:MvPolynomial.eval (0:Fin n->ZMod p) zf=0:=by
   have:=Q1 zg (0:ZMod p) (0:Fin n->ZMod p)
   rw[Dl,zero_pow (by omega:r≠0),Bm] at this;exact this
  exact zk zw
 obtain ⟨g,zy,zz⟩:=zd v zh a;have h1:=zj g zy v;rw[zz,Q1 zg] at h1;have h2:((a:ZMod p) ^ r - 1)*MvPolynomial.eval v zf=0:=by linear_combination h1
 exact ha (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right zk))
lemma Wg (zd:7<=p) {n:ℕ} (L:Subgroup (Aa (Fin n) (ZMod p))) (zc:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) (F:MvPolynomial (Fin n) (Qa p)) (za:F.IsHomogeneous 4) (zb:∀ g∈L,∀ v:Fin n->Qa p, MvPolynomial.eval ((g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v) F= MvPolynomial.eval v F) : F=0:=by
 have zh:(2:ZMod p)≠0:=(by intro h;have ze:p∣2:=(At 2 p).mp (by simpa using h);have zl:=AP (by decide) ze;omega);have zj:((Units.mk0 (2:ZMod p) zh:(ZMod p)ˣ):ZMod p) ^ 4≠1:=by
  rw[DG];intro h;have zi:((15:ℕ):ZMod p)=0:=by
   have:(2:ZMod p) ^ 4 - 1=0:=sub_eq_zero.mpr h;have zk:((15:ℕ):ZMod p)=(2:ZMod p) ^ 4 - 1:=by norm_num
   rw[zk,this]
  have ze:p∣15:=(At 15 p).mp zi;have zl:=AP (by decide) ze;have zf:p.Prime:=Fact.out;have zg:p∣3*5:=by simpa using ze
  rcases zf.dvd_mul.mp zg with h3 | h5
  . have:=AP (by decide) h3;omega
  . have:=AP (by decide) h5;omega
 exact QW L zc (by omega) (by omega) (Units.mk0 2 zh) zj F za zb
lemma Yh (zd:11<=p) {n:ℕ} (L:Subgroup (Aa (Fin n) (ZMod p))) (zc:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) (F:MvPolynomial (Fin n) (Qa p)) (za:F.IsHomogeneous 8) (zb:∀ g∈L,∀ v:Fin n->Qa p, MvPolynomial.eval ((g.val.map (algebraMap (ZMod p) (Qa p))).mulVec v) F= MvPolynomial.eval v F) : F=0:=by
 obtain ⟨a,zf⟩:=IsCyclic.exists_generator (α:=(ZMod p)ˣ);have zg:orderOf a=p - 1:=(by rw[orderOf_eq_card_of_forall_mem_zpowers zf,Au,ZMod.card_units]);have zh:(a:ZMod p) ^ 8≠1:=by intro h;have hu:a ^ 8=1:=A7 (by simpa using h);have ze:orderOf a∣8:=Bl hu;rw[zg] at ze;have zi:=AP (by decide) ze;omega
 exact QW L zc (by omega) (by omega) a zh F za zb
noncomputable def QH {R:Type*} [CommSemiring R] {n:ℕ} (A:Matrix (Fin n) (Fin n) R):MvPolynomial (Fin n) R:=
 ∑ i:Fin n,∑ j:Fin n,MvPolynomial.C (A i j)*MvPolynomial.X i*MvPolynomial.X j
lemma Q8 {R:Type*} [CommSemiring R] {n:ℕ} (A:Matrix (Fin n) (Fin n) R):(QH A).IsHomogeneous 2:=by
 refine MvPolynomial.IsHomogeneous.sum _ _ 2 fun i _=>
  MvPolynomial.IsHomogeneous.sum _ _ 2 fun j _=>?_
 exact (EK (A i j) i).mul (MvPolynomial.isHomogeneous_X R j)
lemma WC {R:Type*} [CommSemiring R] {n:ℕ} (A:Matrix (Fin n) (Fin n) R) (v:Fin n->R) : MvPolynomial.eval v (QH A)=dotProduct v (A.mulVec v):=by
 simp only[QH,Ba,AF,EB,MvPolynomial.eval_X,dotProduct,Matrix.mulVec,A6];refine Ag rfl fun i _=>Ag rfl fun j _=>?_;ring
lemma Yi (zl:7<=p) {n:ℕ} (L:Subgroup (Aa (Fin n) (ZMod p))) (zm:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) (B:Matrix (Fin n) (Fin n) (ZMod p)) (zg:Bᵀ=-B) (zh:B.det≠0) (zi:∀ g∈L,g.valᵀ*B*g.val=B)
  {α:Type*} [Fintype α] [DecidableEq α] (P:α->Matrix (Fin n) (Fin n) (Qa p)) (zj:∑ i:α,P i=1) (zd:∀ i j:α,P i*P j=if i=j then P i else 0) (zk:∀ i:α,P i≠0) (zc:Nonempty α) (τ:α->α) (ze:∀ i,τ (τ i)=i) (za:∀ i,τ i≠i) (zf:∀ g∈L,∃ σ:Equiv.Perm α, ∀ i,(g.val.map (algebraMap (ZMod p) (Qa p)))*P i=P (σ i)*(g.val.map (algebraMap (ZMod p) (Qa p)))) (zb:∀ i j:α,j≠τ i->(P i)ᵀ*B.map (algebraMap (ZMod p) (Qa p))*P j=0) : False:=by
 classical
 let zo:=algebraMap (ZMod p) (Qa p);let BK:Matrix (Fin n) (Fin n) (Qa p):=B.map zo;have zr:BKᵀ=-BK:=by
  ext i j
  have:=Ah (fun M:Matrix (Fin n) (Fin n) (ZMod p)=>zo (M i j)) zg
  simpa[BK] using this
 have zw:BK.det≠0:=(by have:BK.det=zo B.det:=(DT zo B).symm;rw[this];intro h0;exact zh (zo.injective (by rwa[Bn])));have zs:∀ g∈L,(g.val.map zo)ᵀ*BK*g.val.map zo=BK:=by
  intro g hg;have h:=Ah (Matrix.map · zo) (zi g hg);have zO:(g.valᵀ).map zo=(g.val.map zo)ᵀ:=by ext a b;rfl
  rwa[Aq,Aq,zO] at h
 have zp:∀ i:α,∃ u w:Fin n->Qa p,dotProduct (P i*ᵥu) (BK*ᵥ(P (τ i)*ᵥw))≠0:=by
  intro i;have zy:P i≠0:=zk i;have zI:∃ u,P i*ᵥu≠0:=by by_contra hall;push Not at hall;apply zy;apply Matrix.toLin'.injective;apply Ap;intro u;simpa using hall u
  obtain ⟨u,hu⟩:=zI;have zP:BKᵀ*ᵥ(P i*ᵥu)≠0:=by intro h0;rw[zr,BJ,neg_eq_zero] at h0;exact zw (Matrix.exists_mulVec_eq_zero_iff.mp ⟨P i*ᵥu,hu,h0⟩)
  have zJ:∃ w,dotProduct (P i*ᵥu) (BK*ᵥw)≠0:=(by by_contra hall;push Not at hall;apply zP;funext k;have h1:=hall (Pi.single k 1);rw[AB,<-Cc BK,AI] at h1;simpa[dotProduct,AG] using h1);obtain ⟨w,hw⟩:=zJ;refine ⟨u,w,?_⟩;have zz:w=∑ j:α,P j*ᵥw:=by
   calc w=(1:Matrix (Fin n) (Fin n) (Qa p))*ᵥw:=(AN w).symm
   _ = (∑ j:α,P j)*ᵥw:=by rw[zj]
   _ = ∑ j:α,P j*ᵥw:=by funext k;simp only[Matrix.mulVec,dotProduct,AQ,BR,Bo];exact AY
  have zx:dotProduct (P i*ᵥu) (BK*ᵥw)=dotProduct (P i*ᵥu) (BK*ᵥ(P (τ i)*ᵥw)):=by
   conv_lhs=>rw[zz]
   rw[AJ,dotProduct_sum];rw[Ay (τ i)]
   .
    intro j _ hj
    calc dotProduct (P i*ᵥu) (BK*ᵥ(P j*ᵥw))
      = dotProduct (Matrix.vecMul u (P i)ᵀ) (BK*ᵥ(P j*ᵥw)):=by rw[AI]
     _ = dotProduct u ((P i)ᵀ*ᵥ(BK*ᵥ(P j*ᵥw))):=(AB _ _ _).symm
     _ = dotProduct u (((P i)ᵀ*BK*P j)*ᵥw):=by simp only[Ac,Af]
     _ = 0:=by rw[zb i j hj,BF,dotProduct_zero]
   . intro h;exact absurd (Ai (τ i)) h
  rwa[<-zx]
 let F:MvPolynomial (Fin n) (Qa p):=
  ∑ i:α,(QH ((P i)ᵀ*BK*P (τ i))) ^ 2
 have zA:F.IsHomogeneous 4:=
  MvPolynomial.IsHomogeneous.sum _ _ 4 fun i _=>
   by simpa using (Q8 ((P i)ᵀ*BK*P (τ i))).pow 2
 have zq:∀ v:Fin n->Qa p,MvPolynomial.eval v F=∑ i:α,(dotProduct (P i*ᵥv) (BK*ᵥ(P (τ i)*ᵥv))) ^ 2:=by
  intro v;simp only[F,Ba,Dc,WC];refine Ag rfl fun i _=>?_;congr 1
  calc dotProduct v (((P i)ᵀ*BK*P (τ i))*ᵥv)
    = dotProduct v ((P i)ᵀ*ᵥ(BK*ᵥ(P (τ i)*ᵥv))):=by simp only[Ac,Af]
   _ = dotProduct (Matrix.vecMul v (P i)ᵀ) (BK*ᵥ(P (τ i)*ᵥv)):=AB _ _ _
   _ = dotProduct (P i*ᵥv) (BK*ᵥ(P (τ i)*ᵥv)):=by rw[AI]
 have zB:∀ g∈L,∀ v:Fin n->Qa p,MvPolynomial.eval ((g.val.map zo)*ᵥv) F=MvPolynomial.eval v F:=by
  intro g hg v;obtain ⟨σ,zt⟩:=zf g hg;have zC:∀ i:α,σ (τ i)=τ (σ i):=by
   intro i;by_contra zy;obtain ⟨u,w,zH⟩:=zp i;have h0:dotProduct (P (σ i)*ᵥ((g.val.map zo)*ᵥu)) (BK*ᵥ(P (σ (τ i))*ᵥ((g.val.map zo)*ᵥw)))=0:=by
    calc dotProduct (P (σ i)*ᵥ((g.val.map zo)*ᵥu)) (BK*ᵥ(P (σ (τ i))*ᵥ((g.val.map zo)*ᵥw)))
      = dotProduct ((g.val.map zo)*ᵥu) (((P (σ i))ᵀ*BK*P (σ (τ i)))*ᵥ((g.val.map zo)*ᵥw)):=by rw[<-AI,<-AB];simp only[Ac,Af]
     _ = 0:=by rw[zb (σ i) (σ (τ i)) zy,BF,dotProduct_zero]
   have h1:P (σ i)*ᵥ((g.val.map zo)*ᵥu)=(g.val.map zo)*ᵥ(P i*ᵥu):=(by rw[Ac,<-zt i,<-Ac]);have h2:P (σ (τ i))*ᵥ((g.val.map zo)*ᵥw)=(g.val.map zo)*ᵥ(P (τ i)*ᵥw):=(by rw[Ac,<-zt (τ i),<-Ac]);rw[h1,h2] at h0;have h3:dotProduct ((g.val.map zo)*ᵥ(P i*ᵥu)) (BK*ᵥ((g.val.map zo)*ᵥ(P (τ i)*ᵥw)))=dotProduct (P i*ᵥu) (BK*ᵥ(P (τ i)*ᵥw)):=by
    calc dotProduct ((g.val.map zo)*ᵥ(P i*ᵥu)) (BK*ᵥ((g.val.map zo)*ᵥ(P (τ i)*ᵥw)))
      = dotProduct (P i*ᵥu) (((g.val.map zo)ᵀ*BK*(g.val.map zo))*ᵥ(P (τ i)*ᵥw)):=by rw[<-AI,<-AB];simp only[Ac,Af]
     _ = dotProduct (P i*ᵥu) (BK*ᵥ(P (τ i)*ᵥw)):=by rw[zs g hg]
   rw[h3] at h0;exact zH h0
  rw[zq,zq];symm;refine AO σ _ _ fun i=>?_;congr 1;rw[<-zC i];have h1:P (σ i)*ᵥ((g.val.map zo)*ᵥv)=(g.val.map zo)*ᵥ(P i*ᵥv):=(by rw[Ac,<-zt i,<-Ac]);have h2:P (σ (τ i))*ᵥ((g.val.map zo)*ᵥv)=(g.val.map zo)*ᵥ(P (τ i)*ᵥv):=(by rw[Ac,<-zt (τ i),<-Ac]);rw[h1,h2];symm
  calc dotProduct ((g.val.map zo)*ᵥ(P i*ᵥv)) (BK*ᵥ((g.val.map zo)*ᵥ(P (τ i)*ᵥv)))
    = dotProduct (P i*ᵥv) (((g.val.map zo)ᵀ*BK*(g.val.map zo))*ᵥ(P (τ i)*ᵥv)):=by rw[<-AI,<-AB];simp only[Ac,Af]
   _ = dotProduct (P i*ᵥv) (BK*ᵥ(P (τ i)*ᵥv)):=by rw[zs g hg]
 have zQ:F=0:=Wg zl L zm F zA zB;obtain ⟨zn⟩:=zc;obtain ⟨u,w,zH⟩:=zp zn;let v:Fin n->Qa p:=P zn*ᵥu+P (τ zn)*ᵥw;have zD:∀ j:α,P j*ᵥv=(if j=zn then P zn*ᵥu else 0)+(if j=τ zn then P (τ zn)*ᵥw else 0):=by
  intro j;simp only[v,A3,Ac,zd];by_cases h1:j=zn <;> by_cases h2:j=τ zn <;>
   simp[h1,h2,za zn,(za zn).symm]
 have zv:P zn*ᵥv=P zn*ᵥu:=(by rw[zD zn,Az rfl,Aw (za zn).symm,D8]);have zE:P (τ zn)*ᵥv=P (τ zn)*ᵥw:=(by rw[zD (τ zn),Aw (za zn),Az rfl,zero_add]);have zu:∀ j:α,j≠zn->j≠τ zn->P j*ᵥv=0:=(by intro j zS zT;rw[zD j,Aw zS,Aw zT,D8]);have zF:MvPolynomial.eval v F=2*(dotProduct (P zn*ᵥu) (BK*ᵥ(P (τ zn)*ᵥw))) ^ 2:=by
  rw[zq];have zG:∀ j:α,j∉({zn,τ zn}:Finset α)->(dotProduct (P j*ᵥv) (BK*ᵥ(P (τ j)*ᵥv))) ^ 2=0:=by intro j hj;simp only[Cu,Da,not_or] at hj;rw[zu j hj.1 hj.2,zero_dotProduct,zero_pow (by decide)]
  rw[<-D6 (Finset.subset_univ ({zn,τ zn}:Finset α)) (fun j _ hj=>zG j hj)];rw[Finset.sum_pair (za zn).symm,zv,zE,ze zn,zv];have zK:dotProduct (P (τ zn)*ᵥw) (BK*ᵥ(P zn*ᵥu))=- dotProduct (P zn*ᵥu) (BK*ᵥ(P (τ zn)*ᵥw)):=by
   calc dotProduct (P (τ zn)*ᵥw) (BK*ᵥ(P zn*ᵥu))
     = dotProduct (BK*ᵥ(P zn*ᵥu)) (P (τ zn)*ᵥw):=dotProduct_comm _ _
    _ = dotProduct (Matrix.vecMul (P zn*ᵥu) BKᵀ) (P (τ zn)*ᵥw):=by rw[AI]
    _ = dotProduct (P zn*ᵥu) (BKᵀ*ᵥ(P (τ zn)*ᵥw)):=
      (AB _ _ _).symm
    _ = - dotProduct (P zn*ᵥu) (BK*ᵥ(P (τ zn)*ᵥw)):=by rw[zr,BJ,dotProduct_neg]
  rw[zK,neg_sq];ring
 rw[zQ,Bn] at zF;have zL:(2:Qa p)≠0:=by
  intro h2;have zR:(2:ZMod p)=0:=zo.injective (by rw[C2,Bn];exact h2);have zM:p∣2:=(At 2 p).mp (by simpa using zR)
  have:=AP (by decide) zM;omega
 have zN:(dotProduct (P zn*ᵥu) (BK*ᵥ(P (τ zn)*ᵥw))) ^ 2=0:=
  (mul_eq_zero.mp zF.symm).resolve_left zL
 exact zH (sq_eq_zero_iff.mp zN)
lemma QX (zc:7<=p) {d:ℕ} (hd:2<=d) (b:Matrix (Fin d) (Fin d) (Qa p)) (zb:bᵀ=b) (za:b.det≠0) : ∃ x₁ x₂:Fin d->Qa p, dotProduct x₁ (b*ᵥx₁)=1/\dotProduct x₂ (b*ᵥx₂)=1/\ dotProduct x₁ (b*ᵥx₂)=0:=by
 have zs:(2:Qa p)≠0:=by
  intro h2;have zI:(2:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[C2,Bn];exact h2);have zD:p∣2:=(At 2 p).mp (by simpa using zI)
  have:=AP (by decide) zD;omega
 have zj:∀ c:Qa p,∃ r:Qa p,r ^ 2=c:=by
  intro c;have zE:(Polynomial.X ^ 2 - Polynomial.C c:Polynomial (Qa p)).degree≠0:=by
   rw[Ef]
   . rw[Dn];exact by decide
   . rw[Dn];exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_root _ zE;exact ⟨r,sub_eq_zero.mp (by simpa[Polynomial.IsRoot] using hr)⟩
 have zF:∀ u v:Fin d->Qa p,dotProduct v (b*ᵥu)=dotProduct u (b*ᵥv):=by
  intro u v
  calc dotProduct v (b*ᵥu)=dotProduct (b*ᵥu) v:=dotProduct_comm _ _
   _ = dotProduct (Matrix.vecMul u bᵀ) v:=by rw[AI]
   _ = dotProduct u (bᵀ*ᵥv):=(AB _ _ _).symm
   _ = dotProduct u (b*ᵥv):=by rw[zb]
 have zt:∀ u v:Fin d->Qa p,dotProduct (u+v) (b*ᵥ(u+v)) - dotProduct u (b*ᵥu) - dotProduct v (b*ᵥv)=2*dotProduct u (b*ᵥv):=(by intro u v;simp only[A3,add_dotProduct,dotProduct_add,zF u v];ring);have zu:∃ u:Fin d->Qa p,dotProduct u (b*ᵥu)≠0:=by
  by_contra hall;push Not at hall;have zJ:∀ u v,dotProduct u (b*ᵥv)=0:=fun u v=>by
   have:=zt u v
   rw[hall (u+v),hall u,hall v] at this;exact (mul_eq_zero.mp (by linear_combination -this)).resolve_left zs
  have h0:b*ᵥ(Pi.single ⟨0,by omega⟩ (1:Qa p))=0:=by
   funext i
   have:=zJ (Pi.single i 1) (Pi.single ⟨0,by omega⟩ 1)
   simpa[dotProduct,Matrix.mulVec,AG] using this
  exact za (Matrix.exists_mulVec_eq_zero_iff.mp
   ⟨Pi.single ⟨0,by omega⟩ 1,fun h=>by simpa using An h ⟨0,by omega⟩,h0⟩)
 obtain ⟨zf,zA⟩:=zu;obtain ⟨zh,zB⟩:=zj (dotProduct zf (b*ᵥzf))⁻¹;let x₁:Fin d->Qa p:=zh•zf;have ze:dotProduct x₁ (b*ᵥx₁)=1:=by
  simp only[x₁,Al,smul_dotProduct,dotProduct_smul,Am]
  calc zh*(zh*dotProduct zf (b*ᵥzf))=zh ^ 2*dotProduct zf (b*ᵥzf):=by ring
   _ = 1:=by rw[zB,inv_mul_cancel₀ zA]
 have zv:∃ zd:Fin d->Qa p,dotProduct x₁ (b*ᵥzd)=0/\dotProduct zd (b*ᵥzd)≠0:=by
  by_contra hall;push Not at hall;have zo:x₁≠0:=fun h=>by rw[h,zero_dotProduct] at ze;exact CX ze
  have zl:Module.finrank (Qa p) (Submodule.span (Qa p) {x₁}) <
    Module.finrank (Qa p) (Fin d->Qa p):=by
   rw[finrank_span_singleton zo,CQ,AW];omega
  have zr:Submodule.span (Qa p) {x₁}≠⊤:=(by intro zH;rw[zH,finrank_top] at zl;exact lt_irrefl _ zl);have zx:∃ w:Fin d->Qa p,w∉Submodule.span (Qa p) {x₁}:=(by by_contra h;push Not at h;exact zr (Submodule.eq_top_iff'.mpr h));obtain ⟨w,hw⟩:=zx;let v:Fin d->Qa p:=w - dotProduct x₁ (b*ᵥw)•x₁;have zy:v≠0:=(by intro h0;apply hw;have:w=dotProduct x₁ (b*ᵥw)•x₁:=sub_eq_zero.mp h0;rw[this];exact EH _ _ (Submodule.subset_span (Set.mem_singleton x₁)));have zg:dotProduct x₁ (b*ᵥv)=0:=(by simp only[v,Matrix.mulVec_sub,Al,dotProduct_sub,dotProduct_smul,Am,ze,AK,Cx]);have zG:∀ y:Fin d->Qa p,dotProduct y (b*ᵥv)=0:=by
   intro y;let y':Fin d->Qa p:=y - dotProduct x₁ (b*ᵥy)•x₁;have zk:dotProduct x₁ (b*ᵥy')=0:=(by simp only[y',Matrix.mulVec_sub,Al,dotProduct_sub,dotProduct_smul,Am,ze,AK,Cx]);have zn:dotProduct x₁ (b*ᵥ(y'+v))=0:=(by rw[A3,dotProduct_add,zk,zg,D8]);have h1:=zt y' v;rw[hall (y'+v) zn,hall y' zk,hall v zg] at h1;have zp:dotProduct y' (b*ᵥv)=0:=(mul_eq_zero.mp (by linear_combination -h1)).resolve_left zs;have zz:y=y'+dotProduct x₁ (b*ᵥy)•x₁:=by simp[y']
   rw[zz,add_dotProduct,smul_dotProduct,Am,zp,zg,AS,D8]
  have zw:b*ᵥv=0:=by
   funext i
   have:=zG (Pi.single i 1)
   simpa[dotProduct,AG] using this
  exact za (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v,zy,zw⟩)
 obtain ⟨zd,zm,zq⟩:=zv;obtain ⟨zi,zC⟩:=zj (dotProduct zd (b*ᵥzd))⁻¹;let x₂:Fin d->Qa p:=zi•zd;refine ⟨x₁,x₂,ze,?_,?_⟩
 .
  simp only[x₂,Al,smul_dotProduct,dotProduct_smul,Am]
  calc zi*(zi*dotProduct zd (b*ᵥzd))=zi ^ 2*dotProduct zd (b*ᵥzd):=by ring
   _ = 1:=by rw[zC,inv_mul_cancel₀ zq]
 . simp only[x₂,Al,dotProduct_smul,Am,zm,AS]
lemma Q2 (zc:7<=p) {d:ℕ} (hd:2<=d) (b:Matrix (Fin d) (Fin d) (Qa p)) (za:bᵀ=-b) (zb:b.det≠0) : ∃ x₁ x₂:Fin d->Qa p, dotProduct x₁ (b*ᵥx₁)=0/\dotProduct x₂ (b*ᵥx₂)=0/\ dotProduct x₁ (b*ᵥx₂)=1/\dotProduct x₂ (b*ᵥx₁)=-1:=by
 have zl:(2:Qa p)≠0:=by
  intro h2;have zn:(2:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[C2,Bn];exact h2);have zm:p∣2:=(At 2 p).mp (by simpa using zn)
  have:=AP (by decide) zm;omega
 have ze:∀ u v:Fin d->Qa p,dotProduct v (b*ᵥu)=-dotProduct u (b*ᵥv):=by
  intro u v
  calc dotProduct v (b*ᵥu)=dotProduct (b*ᵥu) v:=dotProduct_comm _ _
   _ = dotProduct (Matrix.vecMul u bᵀ) v:=by rw[AI]
   _ = dotProduct u (bᵀ*ᵥv):=(AB _ _ _).symm
   _ = -dotProduct u (b*ᵥv):=by rw[za,BJ,dotProduct_neg]
 have zh:∀ u:Fin d->Qa p,dotProduct u (b*ᵥu)=0:=by
  intro u;have h1:=ze u u;have h2:(2:Qa p)*dotProduct u (b*ᵥu)=0:=by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left zl
 let x₁:Fin d->Qa p:=Pi.single ⟨0,by omega⟩ 1;have zg:x₁≠0:=fun h=>by simpa[x₁] using An h ⟨0,by omega⟩
 have zf:b*ᵥx₁≠0:=fun h=>zb (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x₁,zg,h⟩);have zi:∃ zd,dotProduct x₁ (b*ᵥzd)≠0:=(by by_contra hall;push Not at hall;apply zf;funext i;have h1:=hall (Pi.single i 1);rw[<-neg_eq_zero,<-ze] at h1;simpa[dotProduct,AG] using h1);obtain ⟨zd,zk⟩:=zi;let x₂:Fin d->Qa p:=(dotProduct x₁ (b*ᵥzd))⁻¹•zd;have zj:dotProduct x₁ (b*ᵥx₂)=1:=(by simp only[x₂,Al,dotProduct_smul,Am,inv_mul_cancel₀ zk]);exact ⟨x₁,x₂,zh x₁,zh x₂,zj,by rw[ze,zj]⟩
lemma YC (za:7<=p) {n d k:ℕ} (hd:2<=d) (hk:2<=k) (L:Subgroup (Aa (Fin n) (ZMod p))) (zf:∀ (v:Fin n->ZMod p),v≠0->∀ (a:(ZMod p)ˣ), ∃ g∈L,g.val.mulVec v=(a:ZMod p)•v) (e:(Fin n->Qa p)≃ₗ[Qa p] Matrix (Fin d) (Fin k) (Qa p)) (b:Matrix (Fin d) (Fin d) (Qa p)) (zb:b.det≠0) (c:Matrix (Fin k) (Fin k) (Qa p)) (zc:c.det≠0) (zd:(bᵀ=b/\cᵀ=-c)\/(bᵀ=-b/\cᵀ=c)) (ze:∀ g∈L,∃ (s:Matrix (Fin d) (Fin d) (Qa p)) (t:Matrix (Fin k) (Fin k) (Qa p)) (α:Qa p),α≠0/\s.det≠0/\ sᵀ*b*s=α•b/\tᵀ*c*t=α⁻¹•c/\ ∀ v:Fin n->Qa p, e ((g.val.map (algebraMap (ZMod p) (Qa p)))*ᵥv)=s*e v*tᵀ) : False:=by
 classical
 let zN:=algebraMap (ZMod p) (Qa p);let zi (i:Fin d) (j:Fin k):MvPolynomial (Fin n) (Qa p):=
  ∑ r:Fin n,MvPolynomial.C (e (Pi.single r 1) i j)*MvPolynomial.X r
 have zv:∀ i j,(zi i j).IsHomogeneous 1:=fun i j=>
  MvPolynomial.IsHomogeneous.sum _ _ 1 fun r _=>EK _ _
 have zB:∀ v:Fin n->Qa p,v=∑ r:Fin n,v r•Pi.single r (1:Qa p):=(by intro v;funext m;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]);have zC:∀ (v:Fin n->Qa p) i j,MvPolynomial.eval v (zi i j)=e v i j:=by
  intro v i j
  conv_rhs=>rw[zB v]
  rw[Ba];simp only[zi,Ba,AF,EB,MvPolynomial.eval_X,BR,Bd,A2,Am];refine Ag rfl fun r _=>Bb _ _
 let zj (i l:Fin d):MvPolynomial (Fin n) (Qa p):=
  ∑ j2:Fin k,∑ j1:Fin k,∑ i1:Fin d,MvPolynomial.C (b i i1*c j1 j2)*zi i1 j1*zi l j2
 have zw:∀ i l,(zj i l).IsHomogeneous 2:=fun i l=>
  MvPolynomial.IsHomogeneous.sum _ _ 2 fun j2 _=>
  MvPolynomial.IsHomogeneous.sum _ _ 2 fun j1 _=>
  MvPolynomial.IsHomogeneous.sum _ _ 2 fun i1 _=>
   ((zv i1 j1).C_mul _).mul (zv l j2)
 have zD:∀ (v:Fin n->Qa p) i l,MvPolynomial.eval v (zj i l)=(b*e v*c*(e v)ᵀ) i l:=by
  intro v i l;simp only[zj,Ba,AF,EB,zC,Av,AM,Bo];refine Ag rfl fun j2 _=>Ag rfl fun j1 _=>
   Ag rfl fun i1 _=>by ring
 let F:MvPolynomial (Fin n) (Qa p):=
  ∑ i:Fin d,∑ l:Fin d,zj i l*zj l i
 have zF:F.IsHomogeneous 4:=
  MvPolynomial.IsHomogeneous.sum _ _ 4 fun i _=>
  MvPolynomial.IsHomogeneous.sum _ _ 4 fun l _=>
   (zw i l).mul (zw l i)
 have zk:∀ v:Fin n->Qa p,MvPolynomial.eval v F=((b*e v*c*(e v)ᵀ)*(b*e v*c*(e v)ᵀ)).trace:=(by intro v;simp only[F,Ba,AF,zD,Matrix.trace,D4,Av]);have zG:∀ g∈L,∀ v:Fin n->Qa p,MvPolynomial.eval ((g.val.map zN)*ᵥv) F=MvPolynomial.eval v F:=by
  intro g hg v;obtain ⟨s,t,α,zT,zI,zJ,zK,zL⟩:=ze g hg;rw[zk,zk,zL v];set A:=e v;set U:=b*A*c*Aᵀ;have zl:IsUnit sᵀ.det:=by rw[Eu];exact isUnit_iff_ne_zero.mpr zI
  have zQ:b*s=α•(sᵀ⁻¹*b):=by
   calc b*s=(sᵀ⁻¹*sᵀ)*(b*s):=by rw[Du _ zl,AC]
    _ = sᵀ⁻¹*(sᵀ*b*s):=by simp only[Af]
    _ = sᵀ⁻¹*(α•b):=by rw[zJ]
    _ = α•(sᵀ⁻¹*b):=Ao _ _ _
  have zE:b*(s*A*tᵀ)*c*(s*A*tᵀ)ᵀ=sᵀ⁻¹*U*sᵀ:=by
   have zM:(s*A*tᵀ)ᵀ=t*Aᵀ*sᵀ:=(by simp only[AT,Cc,Af]);rw[zM]
   calc b*(s*A*tᵀ)*c*(t*Aᵀ*sᵀ)
     = (b*s)*A*(tᵀ*c*t)*Aᵀ*sᵀ:=by simp only[Af]
    _ = (α•(sᵀ⁻¹*b))*A*(α⁻¹•c)*Aᵀ*sᵀ:=by rw[zQ,zK]
    _ = (α⁻¹*α)•(sᵀ⁻¹*(b*A*c*Aᵀ)*sᵀ):=by simp only[Ar,Ao,AR,Af]
    _ = sᵀ⁻¹*U*sᵀ:=by rw[inv_mul_cancel₀ zT,Bx]
  rw[zE];have zR:(sᵀ⁻¹*U*sᵀ)*(sᵀ⁻¹*U*sᵀ)=sᵀ⁻¹*(U*U)*sᵀ:=by
   calc (sᵀ⁻¹*U*sᵀ)*(sᵀ⁻¹*U*sᵀ)
     = sᵀ⁻¹*U*(sᵀ*sᵀ⁻¹)*U*sᵀ:=by simp only[Af]
    _ = sᵀ⁻¹*(U*U)*sᵀ:=by rw[B0 _ zl,As];simp only[Af]
  rw[zR,Matrix.trace_mul_comm,<-Af,B0 _ zl,AC]
 have zO:F=0:=Wg za L zf F zF zG;have zA:(-2:Qa p)≠0:=by
  intro h;have h2:(2:Qa p)=0:=neg_eq_zero.mp h;have zS:(2:ZMod p)=0:=zN.injective (by rw[C2,Bn];exact h2);have zP:p∣2:=(At 2 p).mp (by simpa using zS)
  have:=AP (by decide) zP;omega
 rcases zd with ⟨hb_symm,hc_alt⟩ | ⟨hb_alt,hc_symm⟩
 .
  obtain ⟨zg,x₂,zs,zt,zp⟩:=QX za hd b hb_symm zb;obtain ⟨zh,y₂,zy,zz,zu,zx⟩:=Q2 za hk c hc_alt zc;have zq:dotProduct x₂ (b*ᵥzg)=0:=by
   calc dotProduct x₂ (b*ᵥzg)=dotProduct (b*ᵥzg) x₂:=dotProduct_comm _ _
    _ = dotProduct (Matrix.vecMul zg bᵀ) x₂:=by rw[AI]
    _ = dotProduct zg (bᵀ*ᵥx₂):=(AB _ _ _).symm
    _ = 0:=by rw[hb_symm,zp]
  let A0:Matrix (Fin d) (Fin k) (Qa p):=Matrix.of fun i j=>zg i*zh j+x₂ i*y₂ j;have zr:A0*c*A0ᵀ=Matrix.of fun i l=>zg i*x₂ l - x₂ i*zg l:=by
   ext i l;simp only[Av,AM,Ak,A0];have h1:∑ j2:Fin k,(∑ j1:Fin k,(zg i*zh j1+x₂ i*y₂ j1)*c j1 j2)*(zg l*zh j2+x₂ l*y₂ j2)=zg i*zg l*dotProduct zh (c*ᵥzh)+zg i*x₂ l*dotProduct zh (c*ᵥy₂)+x₂ i*zg l*dotProduct y₂ (c*ᵥzh)+x₂ i*x₂ l*dotProduct y₂ (c*ᵥy₂):=by simp only[dotProduct,Matrix.mulVec,Bo,A6,add_mul,EM];simp only[<-Bt];rw[AY];refine Ag rfl fun j1 _=>Ag rfl fun j2 _=>?_;ring
   rw[h1,zy,zu,zx,zz];ring
  have zm:b*A0*c*A0ᵀ=Matrix.of fun i l=>(b*ᵥzg) i*x₂ l - (b*ᵥx₂) i*zg l:=by
   rw[Af b A0 c,Af b (A0*c) A0ᵀ,zr];ext i l;simp only[Av,Ak,Matrix.mulVec,dotProduct,mul_sub,CY,Bo];congr 1 <;> refine Ag rfl fun r _=>by ring
  have zn:(b*A0*c*A0ᵀ)*(b*A0*c*A0ᵀ)=Matrix.of fun i l=>-(b*ᵥzg) i*zg l - (b*ᵥx₂) i*x₂ l:=by
   rw[zm];ext i l;simp only[Av,Ak];have h2:∑ r:Fin d,((b*ᵥzg) i*x₂ r - (b*ᵥx₂) i*zg r)*((b*ᵥzg) r*x₂ l - (b*ᵥx₂) r*zg l)=(b*ᵥzg) i*x₂ l*dotProduct x₂ (b*ᵥzg) -
     (b*ᵥzg) i*zg l*dotProduct x₂ (b*ᵥx₂) -
     (b*ᵥx₂) i*x₂ l*dotProduct zg (b*ᵥzg)+
     (b*ᵥx₂) i*zg l*dotProduct zg (b*ᵥx₂):=by
    simp only[dotProduct,A6];rw[<-CY,<-CY,<-Bt];refine Ag rfl fun r _=>?_;ring
   rw[h2,zq,zt,zs,zp];ring
  have zH:((b*A0*c*A0ᵀ)*(b*A0*c*A0ᵀ)).trace=-2:=by
   rw[zn];simp only[Matrix.trace,D4,Ak,CY];have h1:∑ i:Fin d,-(b*ᵥzg) i*zg i=-dotProduct zg (b*ᵥzg):=by simp only[dotProduct,neg_mul,Dy];congr 1;refine Ag rfl fun i _=>Bb _ _
   have h2:∑ i:Fin d,(b*ᵥx₂) i*x₂ i=dotProduct x₂ (b*ᵥx₂):=(by simp only[dotProduct];refine Ag rfl fun i _=>Bb _ _);rw[h1,h2,zs,zt];ring
  have zo:=zk (e.symm A0);rw[zO,Bn,e.apply_symm_apply,zH] at zo;exact zA zo.symm
 .
  obtain ⟨zg,x₂,zs,zt,zp,zq⟩:=Q2 za hd b hb_alt zb;obtain ⟨zh,y₂,zy,zz,zu⟩:=QX za hk c hc_symm zc;have zx:dotProduct y₂ (c*ᵥzh)=0:=by
   calc dotProduct y₂ (c*ᵥzh)=dotProduct (c*ᵥzh) y₂:=dotProduct_comm _ _
    _ = dotProduct (Matrix.vecMul zh cᵀ) y₂:=by rw[AI]
    _ = dotProduct zh (cᵀ*ᵥy₂):=(AB _ _ _).symm
    _ = 0:=by rw[hc_symm,zu]
  let A0:Matrix (Fin d) (Fin k) (Qa p):=Matrix.of fun i j=>zg i*zh j+x₂ i*y₂ j;have zr:A0*c*A0ᵀ=Matrix.of fun i l=>zg i*zg l+x₂ i*x₂ l:=by
   ext i l;simp only[Av,AM,Ak,A0];have h1:∑ j2:Fin k,(∑ j1:Fin k,(zg i*zh j1+x₂ i*y₂ j1)*c j1 j2)*(zg l*zh j2+x₂ l*y₂ j2)=zg i*zg l*dotProduct zh (c*ᵥzh)+zg i*x₂ l*dotProduct zh (c*ᵥy₂)+x₂ i*zg l*dotProduct y₂ (c*ᵥzh)+x₂ i*x₂ l*dotProduct y₂ (c*ᵥy₂):=by simp only[dotProduct,Matrix.mulVec,Bo,A6,add_mul,EM];simp only[<-Bt];rw[AY];refine Ag rfl fun j1 _=>Ag rfl fun j2 _=>?_;ring
   rw[h1,zy,zu,zx,zz];ring
  have zm:b*A0*c*A0ᵀ=Matrix.of fun i l=>(b*ᵥzg) i*zg l+(b*ᵥx₂) i*x₂ l:=by
   rw[Af b A0 c,Af b (A0*c) A0ᵀ,zr];ext i l;simp only[Av,Ak,Matrix.mulVec,dotProduct,EM,Bt,Bo];congr 1 <;> refine Ag rfl fun r _=>by ring
  have zn:(b*A0*c*A0ᵀ)*(b*A0*c*A0ᵀ)=Matrix.of fun i l=>(b*ᵥzg) i*x₂ l - (b*ᵥx₂) i*zg l:=by
   rw[zm];ext i l;simp only[Av,Ak];have h2:∑ r:Fin d,((b*ᵥzg) i*zg r+(b*ᵥx₂) i*x₂ r)*((b*ᵥzg) r*zg l+(b*ᵥx₂) r*x₂ l)=(b*ᵥzg) i*zg l*dotProduct zg (b*ᵥzg)+(b*ᵥzg) i*x₂ l*dotProduct zg (b*ᵥx₂)+(b*ᵥx₂) i*zg l*dotProduct x₂ (b*ᵥzg)+(b*ᵥx₂) i*x₂ l*dotProduct x₂ (b*ᵥx₂):=by simp only[dotProduct,A6];rw[<-Bt,<-Bt,<-Bt];refine Ag rfl fun r _=>?_;ring
   rw[h2,zs,zp,zq,zt];ring
  have zH:((b*A0*c*A0ᵀ)*(b*A0*c*A0ᵀ)).trace=-2:=(by rw[zn];simp only[Matrix.trace,D4,Ak,CY];have h1:∑ i:Fin d,(b*ᵥzg) i*x₂ i=dotProduct x₂ (b*ᵥzg):=(by simp only[dotProduct];refine Ag rfl fun i _=>Bb _ _);have h2:∑ i:Fin d,(b*ᵥx₂) i*zg i=dotProduct zg (b*ᵥx₂):=(by simp only[dotProduct];refine Ag rfl fun i _=>Bb _ _);rw[h1,h2,zq,zp];ring);have zo:=zk (e.symm A0);rw[zO,Bn,e.apply_symm_apply,zH] at zo;exact zA zo.symm
end Section3Quartics
section Section4TwoTerminal
variable {p:ℕ} [Fact p.Prime]
def Qf {R:Type*} [CommRing R] {n:ℕ} : ∀ {m:ℕ},(Fin m->Matrix (Fin n) (Fin n) R)->Matrix (Fin n) (Fin n) R
 | 0,_=>1
 | _+1,f=>f 0*Qf (fun i=>f i.succ)
lemma QU {R:Type*} [CommRing R] {n m:ℕ} (M:Matrix (Fin n) (Fin n) R) (f:Fin m->Matrix (Fin n) (Fin n) R) (za:∀ i,M*f i=f i*M):M*Qf f=Qf f*M:=by
 induction m with
 | zero=>simp[Qf]
 | succ m ih=>
  simp only[Qf];rw[<-Af,za 0,Af,ih (fun i=>f i.succ) (fun i=>za i.succ),<- Af]
lemma QG {R:Type*} [CommRing R] {n m:ℕ} (f g:Fin m->Matrix (Fin n) (Fin n) R) (za:∀ i j,f i*g j=g j*f i) : Qf f*Qf g=Qf (fun i=>f i*g i):=by
 induction m with
 | zero=>simp[Qf]
 | succ m ih=>
  simp only[Qf];have zb:g 0*Qf (fun i=>f i.succ)=Qf (fun i=>f i.succ)*g 0:=
   QU (g 0) (fun i=>f i.succ) (fun i=>(za i.succ 0).symm)
  calc (f 0*Qf (fun i=>f i.succ))*(g 0*Qf (fun i=>g i.succ))
    = f 0*(Qf (fun i=>f i.succ)*g 0)*Qf (fun i=>g i.succ):=by simp only[Af]
   _ = f 0*(g 0*Qf (fun i=>f i.succ))*Qf (fun i=>g i.succ):=by rw[<-zb]
   _ = (f 0*g 0)*(Qf (fun i=>f i.succ)*Qf (fun i=>g i.succ)):=by simp only[Af]
   _ = (f 0*g 0)*Qf (fun i=>f i.succ*g i.succ):=by rw[ih (fun i=>f i.succ) (fun i=>g i.succ) (fun i j=>za i.succ j.succ)]
lemma QS {R:Type*} [CommRing R] {n m:ℕ} (f:Fin m->Matrix (Fin n) (Fin n) R) (za:Fin m) (zb:f za=0) : Qf f=0:=by
 induction m with
 | zero=>exact Ez za
 | succ m ih=>
  simp only[Qf];refine Fin.cases ?_ ?_ za zb
  . intro h0;rw[h0,Ce]
  . intro j hj;rw[ih (fun i=>f i.succ) j hj,CZ]
lemma WL {R:Type*} [CommRing R] {n m:ℕ} (f:Fin (m+1)->Matrix (Fin n) (Fin n) R) (zb:∀ i j,f i*f j=f j*f i) (za:Fin (m+1)) : Qf f=f za*Qf (fun j:Fin m=>f (za.succAbove j)):=by
 induction m with
 | zero=>
  have zd:za=0:=CR za;subst zd;simp[Qf]
 | succ m ih=>
  refine Fin.cases ?_ ?_ za
  . simp only[Qf,Fin.succAbove_zero]
  .
   intro k;change f 0*Qf (fun j=>f j.succ)=f k.succ*Qf (fun j=>f (k.succ.succAbove j));have hk:=ih (fun j=>f j.succ) (fun i j=>zb i.succ j.succ) k;rw[hk,<-Af,zb 0 k.succ,Af];congr 1;have zc:(fun j:Fin (m+1)=>f (k.succ.succAbove j))=Fin.cons (f 0) (fun j:Fin m=>f (k.succAbove j).succ):=by
    funext j;refine Fin.cases ?_ ?_ j
    . simp[Fin.succAbove]
    .
     intro r;have h1:k.succ.succAbove r.succ=(k.succAbove r).succ:=by
      apply A4;simp only[Fin.succAbove];split_ifs with ha hb hb <;>
       simp[Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at ha hb ⊢ <;> omega
     simp[h1]
   rw[zc];rfl
lemma Yb {R:Type*} [CommRing R] {n m:ℕ} (f:Fin m->Matrix (Fin n) (Fin n) R) (za:∀ i j,f i*f j=f j*f i) (σ:Equiv.Perm (Fin m)) : Qf (f ∘ σ)=Qf f:=by
 induction m with
 | zero=>simp[Qf]
 | succ m ih=>
  let i₀:Fin (m+1):=σ.symm 0;have zc:σ i₀=0:=σ.apply_symm_apply 0;have h1:=WL (f ∘ σ) (fun i j=>za (σ i) (σ j)) i₀;rw[h1];simp only[EC,zc,Qf];congr 1;have zh:∀ j:Fin m,σ (i₀.succAbove j)≠0:=(by intro j hj;have:i₀.succAbove j=i₀:=σ.injective (hj.trans zc.symm);exact Fin.succAbove_ne i₀ j this);let τfun:Fin m->Fin m:=fun j=>(σ (i₀.succAbove j)).pred (zh j);have zb:∀ j:Fin m,(τfun j).succ=σ (i₀.succAbove j):=fun j=>Fin.succ_pred _ _;have zd:Function.Injective τfun:=by
   intro ze zf h;have h':σ (i₀.succAbove ze)=σ (i₀.succAbove zf):=by rw[<-zb ze,<-zb zf,h]
   exact Fin.succAbove_right_injective (σ.injective h')
  let τ:Equiv.Perm (Fin m):=Equiv.ofBijective τfun (Finite.injective_iff_bijective.mp zd);have zg:(fun j:Fin m=>f (σ (i₀.succAbove j)))=(fun r:Fin m=>f r.succ) ∘ τ:=(by funext j;change f (σ (i₀.succAbove j))=f (τfun j).succ;rw[zb]);rw[zg];exact ih (fun r=>f r.succ) (fun i j=>za i.succ j.succ) τ
lemma WM {R:Type*} [CommRing R] {n m:ℕ} {β:Type*} [Fintype β] (E:Fin m->β->Matrix (Fin n) (Fin n) R) : ∑ χ:Fin m->β,Qf (fun i=>E i (χ i))=Qf (fun i=>∑ b:β,E i b):=by
 induction m with
 | zero=>
  simp[Qf]
 | succ m ih=>
  let za:(Fin (m+1)->β) ≃ β×(Fin m->β):=
   {toFun:=fun χ=>(χ 0,fun i=>χ i.succ)
    invFun:=fun p=>Fin.cons p.1 p.2
    left_inv:=fun χ=>by funext i;refine Fin.cases rfl (fun _=>rfl) i
    right_inv:=fun ⟨b,χ'⟩=>by ext <;> rfl }
  rw[AO za (fun χ=>Qf (fun i=>E i (χ i))) (fun p=>E 0 p.1*Qf (fun i=>E i.succ (p.2 i))) (fun χ=>rfl)];rw[C4];simp only[<-BD,ih (fun i=>E i.succ),<-BP,Qf]
lemma WD {R:Type*} [CommRing R] {n m:ℕ} (g za:Matrix (Fin n) (Fin n) R) (h1:g*za=1) (h2:za*g=1) (f:Fin m->Matrix (Fin n) (Fin n) R) : g*Qf f*za=Qf (fun i=>g*f i*za):=by
 induction m with
 | zero=>simp[Qf,h1]
 | succ m ih=>
  simp only[Qf];rw[<-ih (fun i=>f i.succ)]
  calc g*(f 0*Qf (fun i=>f i.succ))*za
    = g*f 0*(za*g)*Qf (fun i=>f i.succ)*za:=by rw[h2,As];simp only[Af]
   _ = (g*f 0*za)*(g*Qf (fun i=>f i.succ)*za):=by simp only[Af]
lemma QV {R:Type*} [CommRing R] {n m:ℕ} (M:Matrix (Fin n) (Fin n) R) (f:Fin m->Matrix (Fin n) (Fin n) R) (zc:∀ i j,f i*f j=f j*f i) (zd:∀ i,M*f i=f i*M) (za:Fin m) (c:R) (zb:M*f za=c•f za) : M*Qf f=c•Qf f:=by
 cases m with
 | zero=>exact Ez za
 | succ m=>
  rw[WL f zc za,<-Af,zb,Ar]
noncomputable def Qj {N n:ℕ} (hN_pos:0 < N) (hNp:¬ p∣N) (M:Matrix (Fin n) (Fin n) (Qa p)) (ζ:Ab N (Qa p)) : Matrix (Fin n) (Fin n) (Qa p):=
 (N:Qa p)⁻¹•∑ k:Fin N,(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val•M ^ k.val
lemma WN {N n:ℕ} (za:0 < N) (zb:¬ p∣N) (M:Matrix (Fin n) (Fin n) (Qa p)) (zc:M ^ N=1) (ζ:Ab N (Qa p)) : M*Qj za zb M ζ=((ζ:(Qa p)ˣ):Qa p)•Qj za zb M ζ:=by
 haveI:NeZero N:=⟨za.ne'⟩;unfold Qj;rw[Ao,BD,smul_comm (M:=Qa p) (N:=Qa p)];congr 1;rw[BC];have zj:(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ N=1:=
  (mem_rootsOfUnity' N _).mp ζ⁻¹.2
 have zd:((ζ:(Qa p)ˣ):Qa p)*(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p)=1:=(by have h1:(ζ*ζ⁻¹:Ab N (Qa p))=1:=By ζ;have h2:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) h1;simpa using h2);have zh:∀ k:Fin N,M*((((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val•M ^ k.val)=((ζ:(Qa p)ˣ):Qa p)•((((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ (k+1:Fin N).val•M ^ (k+1:Fin N).val):=by
  intro k;rw[Ao,AR];have zi:M*M ^ k.val=M ^ (k.val+1):=(BA M k.val).symm;rw[zi];have zg:(k+1:Fin N).val=if k.val+1 < N then k.val+1 else 0:=by
   by_cases h1:N=1
   . subst h1;have zk:k=0:=CR k;subst zk;simp
   .
    change (k.val+1 % N) % N=_;have zl:1 % N=1:=A9 (by omega);rw[zl];split_ifs with zf
    . exact A9 zf
    .
     have ze:k.val+1=N:=by omega
     rw[ze,Ds]
  by_cases zf:k.val+1 < N
  . rw[zg,Az zf];congr 1;rw[BA,<-Ad,zd,AA]
  .
   have ze:k.val+1=N:=by omega
   rw[zg,Aw zf,D7,D7,AK,ze,zc];have zm:(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val=((ζ:(Qa p)ˣ):Qa p):=by
    calc (((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val
      = ((ζ:(Qa p)ˣ):Qa p)*(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p)*(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val:=by rw[zd,AA]
     _ = ((ζ:(Qa p)ˣ):Qa p)*(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ (k.val+1):=by rw[Ad,<-BA]
     _ = ((ζ:(Qa p)ˣ):Qa p):=by rw[ze,zj,AK]
   rw[zm]
 calc ∑ k:Fin N,M*((((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val•M ^ k.val)
   = ∑ k:Fin N,((ζ:(Qa p)ˣ):Qa p)•((((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ (k+1:Fin N).val•M ^ (k+1:Fin N).val):=Ag rfl fun k _=>zh k
  _ = ∑ j:Fin N,((ζ:(Qa p)ˣ):Qa p)•((((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val•M ^ j.val):=
    AO (Equiv.addRight (1:Fin N)) _ _ (fun _=>rfl)
lemma YQ {N n:ℕ} (za:0 < N) (zb:¬ p∣N) (M:Matrix (Fin n) (Fin n) (Qa p)) :
  letI:Fintype (Ab N (Qa p)):=Qx za zb
  ∑ ζ:Ab N (Qa p),Qj za zb M ζ=1:=by
 classical
 haveI:NeZero N:=⟨za.ne'⟩;have ze:Nat.card (Ab N (Qa p))=N:=Qy za zb;let:Fintype (Ab N (Qa p)):=Qx za zb;have zj:(N:Qa p)≠0:=by intro h;have h1:(N:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[DO,Bn];exact h);exact zb ((At N p).mp h1)
 unfold Qj;rw[<-BC,AY];have zf:∀ k:Fin N,(∑ ζ:Ab N (Qa p),(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val•M ^ k.val)=if k=0 then (N:Qa p)•(1:Matrix (Fin n) (Fin n) (Qa p)) else 0:=by
  intro k;rw[<-DU];split_ifs with hk
  . subst hk;simp only[Fin.val_zero,D7,Cm,BS,nsmul_eq_mul,AK];rw[<-Au,ze]
  .
   have zg:0 < k.val:=CM (fun h=>hk (A4 h));obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=Ab N (Qa p));have zk:orderOf g=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers hg,ze]
   have zh:g ^ k.val≠1:=(by intro h;have zi:=Bl h;rw[zk] at zi;have zo:=AP zg zi;omega);have zl:(((g⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val≠1:=by
    intro hc;apply zh;have zc:g⁻¹ ^ k.val=1:=by apply Ae;apply A7;simpa using hc
    rw[E7,inv_eq_one] at zc;exact zc
   set S:=∑ ζ:Ab N (Qa p),(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val;have zd:S=(((g⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val*S:=by rw[A6];symm;refine AO (Equiv.mulLeft g) _ _ fun ζ=>?_;have zc:((g*ζ)⁻¹:Ab N (Qa p))=g⁻¹*ζ⁻¹:=(by rw[Dm,Bb]);change (((g⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val*(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val=((((g*ζ)⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val;rw[zc];simp[CC]
   have zn:S=0:=(by have zm:((((g⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val - 1)*S=0:=(by linear_combination -zd);exact (mul_eq_zero.mp zm).resolve_left (sub_ne_zero.mpr zl));rw[zn,Dl]
 calc (N:Qa p)⁻¹•∑ k:Fin N,∑ ζ:Ab N (Qa p),(((ζ⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ k.val•M ^ k.val
   = (N:Qa p)⁻¹•∑ k:Fin N,(if k=0 then (N:Qa p)•(1:Matrix (Fin n) (Fin n) (Qa p)) else 0):=by congr 1;exact Ag rfl fun k _=>zf k
  _ = (N:Qa p)⁻¹•((N:Qa p)•(1:Matrix (Fin n) (Fin n) (Qa p))):=by rw[A8 Finset.univ (0:Fin N),Az (Ai _)]
  _ = 1:=by rw[AR,inv_mul_cancel₀ zj,Bx]
lemma Wr {N n:ℕ} (za:0 < N) (zb:¬ p∣N) (M:Matrix (Fin n) (Fin n) (Qa p)) (zc:M ^ N=1) (ζ ω:Ab N (Qa p)) [Decidable (ζ=ω)] : Qj za zb M ζ*Qj za zb M ω= if ζ=ω then Qj za zb M ζ else 0:=by
 have:NeZero N:=⟨za.ne'⟩;have ze:(N:Qa p)≠0:=by intro h;have h1:(N:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[DO,Bn];exact h);exact zb ((At N p).mp h1)
 have zi:∀ k:ℕ,M ^ k*Qj za zb M ω=(((ω:(Qa p)ˣ):Qa p) ^ k)•Qj za zb M ω:=by
  intro k;induction k with
  | zero=>simp
  | succ k ih=>
   rw[BA,Af,ih,Ao,WN za zb M zc ω,AR,BA,Bb]
 have zf:Qj za zb M ζ*Qj za zb M ω=((N:Qa p)⁻¹*∑ k:Fin N,((((ζ⁻¹*ω:Ab N (Qa p)):(Qa p)ˣ):Qa p)) ^ k.val)•Qj za zb M ω:=by
  conv_lhs=>arg 1;unfold Qj
  rw[Ar,BP,mul_smul,DU];congr 1;refine Ag rfl fun k _=>?_;rw[Ar,zi k.val,AR];congr 1;simp[CC]
 rw[zf];split_ifs with hζω
 . subst hζω;simp only[CK,CH,Cn,B8,Cm,BS,AW,nsmul_eq_mul,AK,inv_mul_cancel₀ ze,Bx]
 . set c:Qa p:=(((ζ⁻¹*ω:Ab N (Qa p)):(Qa p)ˣ):Qa p);have zk:c ^ N=1:=(mem_rootsOfUnity' N _).mp (ζ⁻¹*ω).2;have zg:c≠1:=(by intro h1;apply hζω;have zj:ζ⁻¹*ω=1:=Ae (A7 (by simpa[c] using h1));exact inv_mul_eq_one.mp zj);have zh:∑ k:Fin N,c ^ k.val=0:=(by have zd:(∑ k∈Finset.range N,c ^ k)*(c - 1)=c ^ N - 1:=geom_sum_mul c N;have zl:∑ k:Fin N,c ^ k.val=∑ k∈Finset.range N,c ^ k:=Fk _ N;rw[zl];rw[zk,Cx] at zd;exact (mul_eq_zero.mp zd).resolve_right (sub_ne_zero.mpr zg));rw[zh,AS,Dl]
lemma WO {N n:ℕ} (zc:0 < N) (ze:¬ p∣N)
  {za zb:Matrix (Fin n) (Fin n) (Qa p)} (zd:za*zb=zb*za) (ζ:Ab N (Qa p)) : za*Qj zc ze zb ζ=Qj zc ze zb ζ*za:=by
 unfold Qj;rw[Ao,Ar,BD,BP];congr 1;refine Ag rfl fun k _=>?_;rw[Ao,Ar];congr 1;exact Commute.pow_right zd k.val
lemma WP {N n:ℕ} (za:0 < N) (zd:¬ p∣N)
  {zb zc:Matrix (Fin n) (Fin n) (Qa p)} (zg:zb*zc=zc*zb) (ze zf:Ab N (Qa p)) : Qj za zd zb ze*Qj za zd zc zf= Qj za zd zc zf*Qj za zd zb ze:=by
 have zh:∀ a b:ℕ,zb ^ a*zc ^ b=zc ^ b*zb ^ a:=fun a b=>
  Commute.pow_pow zg a b
 unfold Qj;rw[Ar,Ao,Ar,Ao];congr 1;congr 1;rw[BP,BP];simp only[BD];rw[AY];refine Ag rfl fun k₂ _=>Ag rfl fun k₁ _=>?_;rw[Ar,Ao,Ar,Ao,smul_comm,zh]
lemma YK {N n:ℕ} (zb:0 < N) (zc:¬ p∣N) (g za M:Matrix (Fin n) (Fin n) (Qa p)) (h1:g*za=1) (h2:za*g=1) (ζ:Ab N (Qa p)) : g*Qj zb zc M ζ*za=Qj zb zc (g*M*za) ζ:=by
 have zd:∀ k:ℕ,g*M ^ k*za=(g*M*za) ^ k:=by
  intro k;induction k with
  | zero=>simp[h1]
  | succ k ih=>
   rw[BA,BA,<-ih]
   calc g*(M*M ^ k)*za
     = g*M*(za*g)*M ^ k*za:=by rw[h2,As];simp only[Af]
    _ = (g*M*za)*(g*M ^ k*za):=by simp only[Af]
 unfold Qj;simp only[Ao,Ar,BD,BP];congr 1;refine Ag rfl fun k _=>?_;simp only[Ao,Ar,zd]
lemma Wh (zk:7<=p) {N:ℕ} {zh:0 < N} {zj:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zh zj ι) (A:Subgroup S.L) [A.Normal] (m:ℕ) (eA:Fin m ≃ A) (P:(Fin m->Ab N (Qa p))->Matrix (Fin S.n) (Fin S.n) (Qa p)) (zi:letI:Fintype (Ab N (Qa p)):=Qx zh zj
   ∑ χ:Fin m->Ab N (Qa p),P χ=1)
  (zg:∀ χ ψ,(χ=ψ->P χ*P ψ=P χ)/\(χ≠ψ->P χ*P ψ=0))
  (ze:∀ (i:Fin m) χ,(eA i).1.1.val.map (algebraMap (ZMod p) (Qa p))*P χ=((χ i:(Qa p)ˣ):Qa p)•P χ)
  (zc:S.L->Equiv.Perm (Fin m))
  (zd:∀ (g:S.L) (i:Fin m),(eA (zc g i)).1=g*(eA i).1*g⁻¹)
  (za:S.L->Equiv.Perm (Fin m->Ab N (Qa p)))
  (zb:∀ g χ i,za g χ i=χ ((zc g).symm i))
  (zf:∀ (g:S.L) χ,(g.1.val.map (algebraMap (ZMod p) (Qa p)))*P χ=P (za g χ)*(g.1.val.map (algebraMap (ZMod p) (Qa p)))) :
  ∀ a∈A,a*a=1:=by
 classical
 let ιK:=algebraMap (ZMod p) (Qa p);letI:Fintype (Ab N (Qa p)):=Qx zh zj;let zl:Fin m->Matrix (Fin S.n) (Fin S.n) (Qa p):=fun i=>(eA i).1.1.val.map ιK;by_contra hall;push Not at hall;obtain ⟨zq,zU,zz⟩:=hall;let α:={χ:Fin m->Ab N (Qa p) // P χ≠0};have zo:∑ x:α,P x.1=1:=by
  rw[<-zi];rw[<-Finset.sum_subtype (Finset.univ.filter fun χ=>P χ≠0) (fun χ=>by simp)]
  exact D6 (Finset.filter_subset _ _) (fun χ _ hχ=>by
   simp only[AL,Ai,B3,not_not] at hχ;exact hχ)
 have zH:Nonempty α:=by
  by_contra hempty;rw[not_nonempty_iff] at hempty;have z6:(0:Matrix (Fin S.n) (Fin S.n) (Qa p))=1:=by simpa using zo
  have:=Ah (fun M:Matrix (Fin S.n) (Fin S.n) (Qa p)=>M ⟨0,S.hn_pos⟩ ⟨0,S.hn_pos⟩) z6
  simp at this
 let zm:(Fin m->Ab N (Qa p))->(Fin m->Ab N (Qa p)):=
  fun χ i=>(χ i)⁻¹
 have zp:∀ χ ψ,ψ≠zm χ->(P χ)ᵀ*S.B.map ιK*P ψ=0:=by
  intro χ ψ va;have zI:∃ i,ψ i≠(χ i)⁻¹:=(by by_contra hall;push Not at hall;exact va (funext hall));obtain ⟨i,hi⟩:=zI;have zV:(zl i)ᵀ*S.B.map ιK*zl i=S.B.map ιK:=by
   have h:=Ah (Matrix.map · ιK) (S.B_inv (eA i).1.1 (eA i).1.2);have zJ:((eA i).1.1.valᵀ).map ιK=(zl i)ᵀ:=by ext a b;rfl
   rwa[Aq,Aq,zJ] at h
  have z7:(P χ)ᵀ*S.B.map ιK*P ψ=(((χ i:(Qa p)ˣ):Qa p)*((ψ i:(Qa p)ˣ):Qa p))•((P χ)ᵀ*S.B.map ιK*P ψ):=by
   calc (P χ)ᵀ*S.B.map ιK*P ψ
     = (P χ)ᵀ*((zl i)ᵀ*S.B.map ιK*zl i)*P ψ:=by rw[zV]
    _ = (zl i*P χ)ᵀ*S.B.map ιK*(zl i*P ψ):=by rw[AT];simp only[Af]
    _ = (((χ i:(Qa p)ˣ):Qa p)•P χ)ᵀ*S.B.map ιK*(((ψ i:(Qa p)ˣ):Qa p)•P ψ):=by rw[ze,ze]
    _ = (((χ i:(Qa p)ˣ):Qa p)*((ψ i:(Qa p)ˣ):Qa p))•((P χ)ᵀ*S.B.map ιK*P ψ):=by rw[Ch,Ar,Ar,Ao,AR,Bb]
  have zK:((χ i:(Qa p)ˣ):Qa p)*((ψ i:(Qa p)ˣ):Qa p)≠1:=(by intro h1;apply hi;have z1:χ i*ψ i=1:=Ae (A7 (by simpa using h1));exact eq_inv_of_mul_eq_one_right z1);have zv:(((χ i:(Qa p)ˣ):Qa p)*((ψ i:(Qa p)ˣ):Qa p) - 1)•((P χ)ᵀ*S.B.map ιK*P ψ)=0:=(by rw[DJ,Bx,<-z7,Cx]);exact (smul_eq_zero.mp zv).resolve_left (sub_ne_zero.mpr zK)
 have zw:∀ x:α,P (zm x.1)≠0:=by
  intro x h0;have zC:(S.B.map ιK).det≠0:=by have:(S.B.map ιK).det=ιK S.B.det:=(DT ιK S.B).symm;rw[this];intro h;exact S.B_det (ιK.injective (by rwa[Bn]))
  have z8:(P x.1)ᵀ*S.B.map ιK=0:=by
   calc (P x.1)ᵀ*S.B.map ιK=(P x.1)ᵀ*S.B.map ιK*(∑ ψ,P ψ):=by rw[zi,As]
    _ = ∑ ψ,(P x.1)ᵀ*S.B.map ιK*P ψ:=BD _ _ _
    _ = 0:=A1 fun ψ _=>by
      by_cases z0:ψ=zm x.1
      . rw[z0,h0,CZ]
      . exact zp x.1 ψ z0
  have zL:(P x.1)ᵀ=0:=by
   have zr:=isUnit_iff_ne_zero.mpr zC
   calc (P x.1)ᵀ=(P x.1)ᵀ*(S.B.map ιK*(S.B.map ιK)⁻¹):=by
           rw[B0 _ zr,As]
         _ = ((P x.1)ᵀ*S.B.map ιK)*(S.B.map ιK)⁻¹:=(Af _ _ _).symm
         _ = 0:=by rw[z8,Ce]
  exact x.2 (by rw[<-Cc (P x.1),zL,Matrix.transpose_zero])
 have zM:∀ x y:α,∃ g:S.L,za g x.1=y.1:=by
  intro x y;let W_orb:Submodule (Qa p) (Fin S.n->Qa p):=
   ⨆ g:S.L,LinearMap.range (Matrix.toLin' (P (za g x.1)))
  have zW:W_orb≠⊥:=by
   intro z5;have h1:za 1 x.1=x.1:=by
    funext i;rw[zb];have z9:(zc 1).symm i=i:=by apply (zc 1).injective;rw[AV];apply eA.injective;apply Ae;rw[zd];group
    rw[z9]
   have zA:LinearMap.range (Matrix.toLin' (P (za 1 x.1)))<=W_orb:=
    le_iSup (fun g:S.L=>LinearMap.range (Matrix.toLin' (P (za g x.1)))) (1:S.L)
   rw[h1,z5] at zA;apply x.2;apply Matrix.toLin'.injective;apply Ap;intro v;have:P x.1*ᵥv∈(⊥:Submodule (Qa p) (Fin S.n->Qa p)):=zA ⟨v,rfl⟩;simpa using this
  have zN:∀ g∈S.L,∀ v∈W_orb,(g.val.map ιK)*ᵥv∈W_orb:=by
   intro g hg;have zD:W_orb.map (Matrix.toLin' (g.val.map ιK))<=W_orb:=by
    simp only[W_orb,EI];refine iSup_le fun h=>?_;rintro _ ⟨_,⟨v,rfl⟩,rfl⟩;have zx:za ⟨g,hg⟩ (za h x.1)=za (⟨g,hg⟩*h) x.1:=by
     funext i;rw[zb,zb,zb];apply Ah x.1;apply (zc (⟨g,hg⟩*h)).injective;rw[AV];have zX:∀ j,zc (⟨g,hg⟩*h) j=zc ⟨g,hg⟩ (zc h j):=fun j=>by
      apply eA.injective;apply Ae;rw[zd,zd,zd];group
     rw[zX,AV,AV]
    have z2:(g.val.map ιK)*ᵥ(P (za h x.1)*ᵥv)∈LinearMap.range (Matrix.toLin' (P (za (⟨g,hg⟩*h) x.1))):=(by refine ⟨(g.val.map ιK)*ᵥv,?_⟩;simp only[Aj,Ac];rw[<-zx,zf ⟨g,hg⟩ (za h x.1)]);exact le_iSup (fun k:S.L=>LinearMap.range (Matrix.toLin' (P (za k x.1)))) (⟨g,hg⟩*h) z2
   intro v hv;exact zD ⟨v,hv,rfl⟩
  have zO:W_orb=⊤:=(S.absIrred W_orb zN).resolve_left zW;by_contra hnot;push Not at hnot;have zE:∀ v∈W_orb,P y.1*ᵥv=0:=(by have zA:W_orb<=LinearMap.ker (Matrix.toLin' (P y.1)):=(by refine iSup_le fun g=>?_;rintro _ ⟨v,rfl⟩;rw[Bf,Aj,Aj,Ac,(zg y.1 (za g x.1)).2 (Ne.symm (hnot g)),BF]);intro v hv;exact LinearMap.mem_ker.mp (zA hv));apply y.2;apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,BF];exact zE v (zO ▸ BW)
 have zP:∃ zn:α,zm zn.1≠zn.1:=by
  let i₀:Fin m:=eA.symm ⟨zq,zU⟩;by_contra hall;push Not at hall;have zs:zl i₀*zl i₀=1:=by
   calc zl i₀*zl i₀=zl i₀*(zl i₀*∑ x:α,P x.1):=by rw[zo,As]
    _ = ∑ x:α,zl i₀*(zl i₀*P x.1):=by simp only[BD]
    _ = ∑ x:α,(((x.1 i₀:(Qa p)ˣ):Qa p)*((x.1 i₀:(Qa p)ˣ):Qa p))•P x.1:=by refine Ag rfl fun x _=>?_;rw[ze,Ao,ze,AR]
    _ = ∑ x:α,P x.1:=by
          refine Ag rfl fun x _=>?_;have zr:(x.1 i₀)⁻¹=x.1 i₀:=An (hall x) i₀;have zQ:x.1 i₀*x.1 i₀=1:=by
           calc x.1 i₀*x.1 i₀=(x.1 i₀)⁻¹*x.1 i₀:=by rw[zr]
            _ = 1:=CK _
          have z3:((x.1 i₀:(Qa p)ˣ):Qa p)*((x.1 i₀:(Qa p)ˣ):Qa p)=1:=by
           have:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) zQ
           simpa using this
          rw[z3,Bx]
    _ = 1:=zo
  apply zz;apply Ae;apply A7;apply C9 ιK.injective;have zF:zq.1.val.map ιK=zl i₀:=by simp[zl,i₀]
  have zY:(1:Matrix (Fin S.n) (Fin S.n) (ZMod p)).map ιK=1:=(by ext a b;simp[BG]);change (zq.1.val*zq.1.val).map ιK=(1:Matrix (Fin S.n) (Fin S.n) (ZMod p)).map ιK;rw[Aq,zF,zY,zs]
 obtain ⟨zn,zZ⟩:=zP;let τ:α->α:=fun x=>⟨zm x.1,zw x⟩;have zG:∀ x:α,τ (τ x)=x:=fun x=>Ae (funext fun i=>inv_inv (x.1 i));have zR:∀ x:α,τ x≠x:=by intro x zt;obtain ⟨g,hg⟩:=zM zn x;apply zZ;have zB:zm (za g zn.1)=za g zn.1:=hg.symm ▸ Ah Subtype.val zt;have zu:zm (za g zn.1)=za g (zm zn.1):=(by funext i;rw[zb];simp only[zm,zb]);rw[zu] at zB;exact (za g).injective zB
 exact Yi zk S.L S.SF S.B S.B_alt S.B_det S.B_inv
  (fun x:α=>P x.1) zo
  (fun x y=>by
   by_cases h:x=y
   . rw[Az h,(zg x.1 y.1).1 (Ah Subtype.val h)]
   . rw[Aw h,(zg x.1 y.1).2 (fun h'=>h (Ae h'))])
  (fun x=>x.2) zH τ zG zR
  (fun g hg=>by
   have zy:∀ x:α,P (za ⟨g,hg⟩ x.1)≠0:=by
    intro x h0;have h1:=zf ⟨g,hg⟩ x.1;rw[h0,Ce] at h1;have zS:g.inv.map ιK*g.val.map ιK=1:=(by rw[<-Aq,g.inv_val];ext a b;simp[BG]);have zL:P x.1=0:=by
     calc P x.1=(g.inv.map ιK*g.val.map ιK)*P x.1:=by rw[zS,AC]
      _ = g.inv.map ιK*(g.val.map ιK*P x.1):=Af _ _ _
      _ = 0:=by rw[h1,CZ]
    exact x.2 zL
   let σ:Equiv.Perm α:=
    {toFun:=fun x=>⟨za ⟨g,hg⟩ x.1,zy x⟩
     invFun:=fun x=>⟨(za ⟨g,hg⟩).symm x.1,by
      have h1:=zf ⟨g,hg⟩ ((za ⟨g,hg⟩).symm x.1);rw[AV] at h1;intro h0;rw[h0,CZ] at h1;have zT:g.val.map ιK*g.inv.map ιK=1:=(by rw[<-Aq,g.val_inv];ext a b;simp[BG]);have z4:P x.1=0:=by
       calc P x.1=P x.1*(g.val.map ιK*g.inv.map ιK):=by rw[zT,As]
        _ = (P x.1*g.val.map ιK)*g.inv.map ιK:=(Af _ _ _).symm
        _ = 0:=by rw[<-h1,Ce]
      exact x.2 z4⟩
     left_inv:=fun x=>Ae ((za ⟨g,hg⟩).symm_apply_apply x.1)
     right_inv:=fun x=>Ae ((za ⟨g,hg⟩).apply_symm_apply x.1) }
   exact ⟨σ,fun x=>zf ⟨g,hg⟩ x.1⟩)
  (fun x y hxy=>zp x.1 y.1 (fun h=>hxy (Ae h)))
lemma QP (zd:7<=p) {N:ℕ} {za:0 < N} {zb:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N za zb ι) (A:Subgroup S.L) [A.Normal] (zc:∀ a b:A,a*b=b*a) : ∀ a∈A,a*a=1:=by
 let zg:=algebraMap (ZMod p) (Qa p);let:Fintype (Ab N (Qa p)):=Qx za zb;have:Fintype A:=Fintype.ofFinite A;let m:=Fintype.card A;let eA:Fin m ≃ A:=(Fintype.equivFin A).symm;let ze:Fin m->Matrix (Fin S.n) (Fin S.n) (Qa p):=fun i=>(eA i).1.1.val.map zg;have zj:∀ i:Fin m,ze i ^ N=1:=by
  intro i;have zt:(eA i).1 ^ N=1:=by
   obtain ⟨k,hk⟩:=S.card_dvd
   calc (eA i).1 ^ N=(eA i).1 ^ (Nat.card S.L*k):=Ah ((eA i).1 ^ ·) hk
    _ = ((eA i).1 ^ Nat.card S.L) ^ k:=Cz _ _ _
    _ = 1:=by rw[QC,B8]
  have h1:(eA i).1.1.val ^ N=1:=by
   have:=Ah (fun g:S.L=>g.1.val) zt
   simpa using this
  have zw:∀ (M:Matrix (Fin S.n) (Fin S.n) (ZMod p)) (k:ℕ),(M ^ k).map zg=(M.map zg) ^ k:=by
   intro M k;induction k with
   | zero=>ext a b;simp[BG]
   | succ k ih=>rw[DK,DK,Aq,ih]
  rw[<-zw,h1];ext a b;simp[BG]
 have zh:∀ i j:Fin m,ze i*ze j=ze j*ze i:=(by intro i j;simp only[ze,<-Aq];congr 1;exact Ah (fun x:A=>x.1.1.val) (zc (eA i) (eA j)));let P:(Fin m->Ab N (Qa p))->Matrix (Fin S.n) (Fin S.n) (Qa p):=
  fun χ=>Qf (fun i=>Qj za zb (ze i) (χ i))
 have zs:∑ χ:Fin m->Ab N (Qa p),P χ=1:=by
  dsimp only[P];rw[WM];have h1:(fun i:Fin m=>∑ b:Ab N (Qa p),Qj za zb (ze i) b)=fun _=>1:=funext fun i=>YQ za zb (ze i);rw[h1];clear h1;induction m with
  | zero=>rfl
  | succ m ih=>simp[Qf,ih]
 have zp:∀ χ ψ,(χ=ψ->P χ*P ψ=P χ)/\(χ≠ψ->P χ*P ψ=0):=by
  classical
  intro χ ψ;dsimp only[P];rw[QG _ _ (fun i j=>WP za zb (zh i j) (χ i) (ψ j))];constructor
  . intro h;subst h;congr 1;funext i;rw[Wr za zb (ze i) (zj i),Az rfl]
  . intro h;have zy:∃ i,χ i≠ψ i:=(by by_contra hall;push Not at hall;exact h (funext hall));obtain ⟨zm,zv⟩:=zy;exact QS _ zm (by rw[Wr za zb (ze zm) (zj zm),Aw zv])
 have zq:∀ (i:Fin m) χ,ze i*P χ=((χ i:(Qa p)ˣ):Qa p)•P χ:=fun i χ=>
  QV (ze i) _
   (fun a b=>WP za zb (zh a b) (χ a) (χ b))
   (fun j=>WO za zb (zh i j) (χ j))
   i _ (WN za zb (ze i) (zj i) (χ i))
 let zf (g:S.L):Equiv.Perm (Fin m):=
  {toFun:=fun i=>eA.symm ⟨g*(eA i).1*g⁻¹,Ax ‹_› (eA i).1 (eA i).2 g⟩
   invFun:=fun i=>eA.symm ⟨g⁻¹*(eA i).1*g,by simpa using Ax ‹_› (eA i).1 (eA i).2 g⁻¹⟩
   left_inv:=fun i=>by
    apply eA.injective;apply Ae;apply Ae;simp only[AV];group
   right_inv:=fun i=>by
    apply eA.injective;apply Ae;apply Ae
    simp only[AV];group }
 have zk:∀ (g:S.L) (i:Fin m),(eA (zf g i)).1=g*(eA i).1*g⁻¹:=fun g i=>by
  simp[zf]
 let zi (g:S.L):Equiv.Perm (Fin m->Ab N (Qa p)):=
  {toFun:=fun χ i=>χ ((zf g).symm i)
   invFun:=fun χ i=>χ (zf g i)
   left_inv:=fun χ=>by funext i;simp
   right_inv:=fun χ=>by funext i;simp }
 have zr:∀ (g:S.L) χ,(g.1.val.map zg)*P χ=P (zi g χ)*(g.1.val.map zg):=by
  intro g χ;have zn:g.1.val.map zg*g.1.inv.map zg=1:=(by rw[<-Aq,g.1.val_inv];ext a b;simp[BG]);have zl:g.1.inv.map zg*g.1.val.map zg=1:=(by rw[<-Aq,g.1.inv_val];ext a b;simp[BG]);suffices h:(g.1.val.map zg)*P χ*(g.1.inv.map zg)=P (zi g χ) by
   calc (g.1.val.map zg)*P χ=((g.1.val.map zg)*P χ*(g.1.inv.map zg))*(g.1.val.map zg):=by
           rw[Af,zl,As]
         _ = P (zi g χ)*(g.1.val.map zg):=by rw[h]
  dsimp only[P];rw[WD _ _ zn zl];have zu:(fun i=>(g.1.val.map zg)*Qj za zb (ze i) (χ i)*(g.1.inv.map zg))=(fun j=>Qj za zb (ze j) (zi g χ j)) ∘ zf g:=by
   funext i;rw[YK za zb _ _ _ zn zl];have zo:(g.1.val.map zg)*ze i*(g.1.inv.map zg)=ze (zf g i):=by
    have h1:g.1.val*(eA i).1.1.val*g.1.inv=(eA (zf g i)).1.1.val:=
     (Ah (fun x:S.L=>x.1.val) (zk g i)).symm
    dsimp only[ze];rw[<-Aq,<-Aq,h1]
   have zx:zi g χ (zf g i)=χ i:=by simp[zi]
   simp only[EC,zo,zx]
  rw[zu];exact Yb _ (fun a b=>WP za zb (zh a b) _ _) (zf g)
 exact Wh zd S A m eA P zs zp zq
  zf zk zi (fun _ _ _=>rfl) zr
def Qh (p:ℕ) (b:Bool):ZMod p:=if b then 1 else -1
def Qo {n:ℕ} (M:Matrix (Fin n) (Fin n) (ZMod p)) (b:Bool) : Matrix (Fin n) (Fin n) (ZMod p):=
 (2:ZMod p)⁻¹•(1+Qh p b•M)
lemma WU (zb:7<=p) {n:ℕ} (M:Matrix (Fin n) (Fin n) (ZMod p)) (za:M*M=1) (b:Bool) : M*Qo M b=Qh p b•Qo M b:=by
 unfold Qo;rw[Ao,smul_comm (M:=ZMod p) (N:=ZMod p)];congr 1;rw[BH,As,Ao,za,Eq,AR];cases b <;> simp[Qh,DQ]
lemma YT (za:7<=p) {n:ℕ} (M:Matrix (Fin n) (Fin n) (ZMod p)) : ∑ b:Bool,Qo M b=1:=by
 have zb:(2:ZMod p)≠0:=by
  intro h2;have zc:p∣2:=(At 2 p).mp (by simpa using h2)
  have:=AP (by decide) zc;omega
 rw[Ea];simp only[Qo,Qh,↓reduceIte,AE,Bx,neg_one_smul,<-Eq];have zd:(1+M)+(1+-M)=(2:ZMod p)•(1:Matrix (Fin n) (Fin n) (ZMod p)):=(by ext i j;simp[EL];ring);rw[zd,AR,inv_mul_cancel₀ zb,Bx]
lemma WF (zc:7<=p) {n:ℕ} (M:Matrix (Fin n) (Fin n) (ZMod p)) (zd:M*M=1) (zb za:Bool) : Qo M zb*Qo M za=if zb=za then Qo M zb else 0:=by
 have ze:(2:ZMod p)≠0:=by
  intro h2;have zf:p∣2:=(At 2 p).mp (by simpa using h2)
  have:=AP (by decide) zf;omega
 conv_lhs=>arg 1;unfold Qo
 rw[Ar,BQ,AC,Ar,WU zc M zd za,AR,show Qo M za+(Qh p zb*Qh p za)•Qo M za=(1+Qh p zb*Qh p za)•Qo M za by rw[Fc,Bx],AR];cases zb <;> cases za
 . simp[Qh,show (1:ZMod p)+1=2 by ring,inv_mul_cancel₀ ze]
 . simp[Qh]
 . simp[Qh]
 . simp[Qh,show (1:ZMod p)+1=2 by ring,inv_mul_cancel₀ ze]
lemma WV {n:ℕ} {za zb:Matrix (Fin n) (Fin n) (ZMod p)} (h:za*zb=zb*za) (zc zd:Bool):Qo za zc*Qo zb zd=Qo zb zd*Qo za zc:=by
 unfold Qo;rw[Ar,Ao,Ar,Ao];congr 1;congr 1;simp only[BQ,BH,AC,As,Ar,Ao,Eq,AR,h,Bb];abel
lemma YR {n:ℕ} (g za M:Matrix (Fin n) (Fin n) (ZMod p)) (h1:g*za=1) (b:Bool) : g*Qo M b*za=Qo (g*M*za) b:=by
 unfold Qo;simp only[Ao,Ar,BH,BQ,As,h1]
set_option maxHeartbeats 400000 in
lemma W2 (zn:7<=p) {N:ℕ} {zb:0 < N} {zd:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zb zd ι) (A:Subgroup S.L) [A.Normal] (ze:∀ a∈A,a*a=1) (m:ℕ) (eA:Fin m ≃ A) (Q:(Fin m->Bool)->Matrix (Fin S.n) (Fin S.n) (ZMod p)) (zi:∀ χ,Q χ=Qf (fun i=>Qo (eA i).1.1.val (χ i))) (zl:∑ χ:Fin m->Bool,Q χ=1) (zk:∀ χ ψ,Q χ*Q ψ=if χ=ψ then Q χ else 0) (zh:∀ (i:Fin m) χ,(eA i).1.1.val*Q χ=Qh p (χ i)•Q χ) (zc:S.L->Equiv.Perm (Fin m)) (zj:∀ g i,(eA (zc g i)).1=g*(eA i).1*g⁻¹) (zf:∀ (g:S.L) χ,g.1.val*Q χ=Q (fun i=>χ ((zc g).symm i))*g.1.val) (za:Fin m->Bool) (zm:Q za≠0) (t:S.L) (zg:∀ i:Fin m,za ((zc t).symm i)=za i) :
  let ιK:=algebraMap (ZMod p) (Qa p)
  let UK0:Submodule (Qa p) (Fin S.n->Qa p):=LinearMap.range (Matrix.toLin' ((Q za).map ιK))
  have ht_inv:∀ v∈UK0,(t.1.val.map ιK)*ᵥv∈UK0:=by
   rintro _ ⟨v,rfl⟩;refine ⟨(t.1.val.map ιK)*ᵥv,?_⟩;simp only[Aj,Ac,<-Aq];have ul:=zf t za;have hfix:(fun i=>za ((zc t).symm i))=za:=funext zg;rw[hfix] at ul;rw[ul]
  let T0:Module.End (Qa p) UK0:=
   {toFun:=fun x=>⟨(t.1.val.map ιK)*ᵥx.1,ht_inv x.1 x.2⟩
    map_add':=fun x y=>Ae (A3 _ x.1 y.1)
    map_smul':=fun c x=>Ae (Al _ c x.1) }
  ∃ q:ℚ,Qr zb zd ι UK0 T0=(q:ℂ):=by
 classical
 intro ιK UK0 ht_inv T0;have zX:2∣N:=by
  let z:S.L:=⟨Qd S.n p,S.negOne_mem⟩;have v9:z≠1:=by
   intro h1;have h0:=Ah (fun g:S.L=>g.1.val ⟨0,S.hn_pos⟩ ⟨0,S.hn_pos⟩) h1;simp only[z,Qd,EP,Bh,BT,CH,Cn] at h0;have vR:(2:ZMod p)=0:=by linear_combination -h0
   have zF:p∣2:=(At 2 p).mp (by simpa using vR)
   have:=AP (by decide) zF;omega
  have ut:z ^ 2=1:=(by apply Ae;apply A7;change (-1:Matrix (Fin S.n) (Fin S.n) (ZMod p)) ^ 2=1;simp);have ua:orderOf z=2:=orderOf_eq_prime ut v9;have vz:orderOf z∣Nat.card S.L:=Dd z;rw[ua] at vz;exact vz.trans S.card_dvd
 let σ:Equiv.Perm (Fin m->Bool):=
  {toFun:=fun χ i=>χ ((zc t).symm i)
   invFun:=fun χ i=>χ (zc t i)
   left_inv:=fun χ=>by funext i;simp
   right_inv:=fun χ=>by funext i;simp }
 have z7:σ ^ N=1:=by
  have uu:t ^ N=1:=by
   obtain ⟨k,hk⟩:=S.card_dvd
   calc t ^ N=t ^ (Nat.card S.L*k):=Ah (t ^ ·) hk
    _ = (t ^ Nat.card S.L) ^ k:=Cz _ _ _
    _ = 1:=by rw[QC,B8]
  have ve:∀ k:ℕ,∀ i:Fin m,(eA ((zc t ^ k) i)).1=t ^ k*(eA i).1*(t ^ k)⁻¹:=by
   intro k;induction k with
   | zero=>intro i;simp
   | succ k ih=>
    intro i;rw[BA,Equiv.Perm.mul_apply,zj,ih,BA];group
  have vS:zc t ^ N=1:=(by apply Ec;intro i;apply eA.injective;apply Ae;rw[ve N i,uu];simp);ext χ i;have vD:∀ k:ℕ,∀ ψ j,(σ ^ k) ψ j=ψ (((zc t) ^ k)⁻¹ j):=by
   intro k;induction k with
   | zero=>intro ψ j;simp
   | succ k ih=>
    intro ψ j;rw[BA,Equiv.Perm.mul_apply];change (σ ^ k) ψ ((zc t).symm j)=ψ (((zc t ^ (k+1))⁻¹) j);rw[ih,BA,Dm];rfl
  rw[vD N χ i,vS,inv_one];rfl
 let zq:Setoid (Fin m->Bool):=
  {r:=fun χ ψ=>∃ k:ℕ,(σ ^ k) χ=ψ
   iseqv:=
    {refl:=fun χ=>⟨0,rfl⟩
     symm:=fun {χ ψ} ⟨k,hk⟩=>by
      refine ⟨(N - k % N) % N,?_⟩;have zM:∀ r:ℕ,σ ^ r=σ ^ (r % N):=by
       intro r;conv_lhs=>rw[<-Cd r N]
       rw[CT,Cz,z7,B8,AA]
      rw[<-hk,<-Equiv.Perm.mul_apply,<-CT];have um:((N - k % N) % N+k) % N=0:=by
       have zC:k % N < N:=DF k zb;rw[Nat.add_mod,Nat.mod_mod];by_cases h0:k % N=0
       . simp[h0]
       . rw[A9 (show N - k % N < N by omega),Dk zC.le,Ds]
      rw[zM,um,D7];rfl
     trans:=fun {χ ψ θ} ⟨k₁,h1⟩ ⟨k₂,h2⟩=>
      ⟨k₂+k₁,by rw[CT,Equiv.Perm.mul_apply,h1,h2]⟩ } }
 let Orb:=Quotient zq;let zz (o:Orb):Finset (Fin m->Bool):=Finset.univ.filter fun χ=>Quotient.mk zq χ=o;let QK (χ:Fin m->Bool):Matrix (Fin S.n) (Fin S.n) (Qa p):=(Q χ).map ιK;let zp (o:Orb):Matrix (Fin S.n) (Fin S.n) (Qa p):=∑ χ∈zz o,QK χ;have zr:∀ χ ψ,QK χ*QK ψ=if χ=ψ then QK χ else 0:=by
  intro χ ψ;simp only[QK,<-Aq,zk];split_ifs
  . rfl
  . ext a b;simp
 have vE:∑ χ:Fin m->Bool,QK χ=1:=by
  have h1:(∑ χ:Fin m->Bool,Q χ).map ιK=∑ χ:Fin m->Bool,QK χ:=(by ext a b;simp only[QK,AZ,BR,Ba]);rw[<-h1,zl];ext a b;by_cases h:a=b
  . subst h;simp
  . simp[h]
 have vf:∑ o:Orb,zp o=1:=(by rw[<-vE];exact Finset.sum_fiberwise_of_maps_to (fun χ _=>Ai (Quotient.mk zq χ)) _);have zt:∀ z4 vd:Orb,zp z4*zp vd=if z4=vd then zp z4 else 0:=by
  intro z4 vd;simp only[zp,BP,BD,zr];by_cases h:z4=vd
  . subst h;rw[Az rfl];refine Ag rfl fun χ zy=>?_;rw[A8,Az zy]
  . rw[Aw h];refine A1 fun χ zy=>A1 fun ψ zJ=>?_;rw[Aw];intro zH;subst zH;rw[AL] at zy zJ;exact h (zJ.2.symm.trans zy.2)
 have z8:∀ χ,(t.1.val.map ιK)*QK χ=QK (σ χ)*(t.1.val.map ιK):=(by intro χ;simp only[QK,<-Aq];congr 1;exact zf t χ);have ub:∀ (i:Fin m) χ,((eA i).1.1.val.map ιK)*QK χ=ιK (Qh p (χ i))•QK χ:=(by intro i χ;simp only[QK,<-Aq,zh i χ];ext a b;simp[Am]);have zY:∀ (i:Fin m) (o:Orb),((t*(eA i).1).1.val.map ιK)*zp o=zp o*((t*(eA i).1).1.val.map ιK):=by
  intro i o;have zD:(t*(eA i).1).1.val.map ιK=(t.1.val.map ιK)*((eA i).1.1.val.map ιK):=Aq;rw[zD];have vF:∀ χ,((eA i).1.1.val.map ιK)*QK χ=QK χ*((eA i).1.1.val.map ιK):=by
   intro χ;have zR:(eA i).1.1.val*Q χ=Q χ*(eA i).1.1.val:=by
    rw[zi];exact QU _ _ fun j=>by
     have vT:(eA i).1.1.val*(eA j).1.1.val=(eA j).1.1.val*(eA i).1.1.val:=by
      have h1:=ze ((eA i).1*(eA j).1) (A.mul_mem (eA i).2 (eA j).2);have hi:=ze (eA i).1 (eA i).2;have hj:=ze (eA j).1 (eA j).2;have zZ:(eA i).1*(eA j).1=(eA j).1*(eA i).1:=by
       calc (eA i).1*(eA j).1=(eA i).1*(eA j).1*1:=(AK _).symm
        _ = (eA i).1*(eA j).1*((eA i).1*(eA j).1*((eA i).1*(eA j).1)):=by rw[h1]
        _ = ((eA i).1*(eA j).1*((eA i).1*(eA j).1))*((eA i).1*(eA j).1):=by group
        _ = (eA j).1*(eA i).1:=by
             have vG:((eA i).1*(eA j).1)⁻¹=(eA i).1*(eA j).1:=
              inv_eq_of_mul_eq_one_right h1
             have zB:(eA i).1⁻¹=(eA i).1:=inv_eq_of_mul_eq_one_right hi;have vU:(eA j).1⁻¹=(eA j).1:=inv_eq_of_mul_eq_one_right hj;rw[h1,AA,<-vG,Dm,zB,vU]
      exact Ah (fun g:S.L=>g.1.val) zZ
     unfold Qo;simp only[Ao,Ar,BH,BQ,As,AC,vT]
   simp only[QK,<-Aq,zR]
  have vH:((eA i).1.1.val.map ιK)*zp o=zp o*((eA i).1.1.val.map ιK):=(by simp only[zp,BD,BP];exact Ag rfl fun χ _=>vF χ);have vI:(t.1.val.map ιK)*zp o=zp o*(t.1.val.map ιK):=by
   simp only[zp,BD,BP];have un:∑ χ∈zz o,(t.1.val.map ιK)*QK χ=∑ χ∈zz o,QK (σ χ)*(t.1.val.map ιK):=
    Ag rfl fun χ _=>z8 χ
   rw[un];refine Fi (fun χ _=>σ χ) ?_ ?_ ?_ (fun _ _=>rfl)
   . intro χ zy;rw[AL] at zy ⊢;refine ⟨Ai _,?_⟩;rw[<-zy.2];exact (Quotient.sound (s:=zq) ⟨1,by simp⟩).symm
   . intro uB _ uC _ h;exact σ.injective h
   . intro ψ zJ;refine ⟨σ.symm ψ,?_,σ.apply_symm_apply ψ⟩;rw[AL] at zJ ⊢;refine ⟨Ai _,?_⟩;rw[<-zJ.2];exact Quotient.sound (s:=zq) ⟨1,by simp⟩
  calc (t.1.val.map ιK)*((eA i).1.1.val.map ιK)*zp o
    = (t.1.val.map ιK)*(zp o*((eA i).1.1.val.map ιK)):=by rw[Af,vH]
   _ = zp o*((t.1.val.map ιK)*((eA i).1.1.val.map ιK)):=by rw[<-Af,vI,Af]
 let zs (o:Orb):Submodule (Qa p) (Fin S.n->Qa p):=LinearMap.range (Matrix.toLin' (zp o));let zT:(Fin S.n->Qa p)≃ₗ[Qa p] (∀ o:Orb,zs o):=
  {toFun:=fun v o=>⟨zp o*ᵥv,⟨v,rfl⟩⟩
   invFun:=fun f=>∑ o:Orb,(f o).1
   left_inv:=fun v=>by
    dsimp only;have vq:(∑ o:Orb,zp o*ᵥv)=(∑ o:Orb,zp o)*ᵥv:=by funext j;simp only[AQ,Matrix.mulVec,dotProduct,BR,Bo];exact AY
    rw[vq,vf,AN]
   right_inv:=fun f=>by
    funext o;apply Ae;dsimp only;rw[AJ,Ay o]
    . obtain ⟨u,hu⟩:=(f o).2;rw[<-hu,Aj,Ac,zt o o,Az rfl]
    . intro o' _ v8;obtain ⟨u,hu⟩:=(f o').2;rw[<-hu,Aj,Ac,zt o o',Aw (Ne.symm v8),BF]
    . intro h;exact absurd (Ai o) h
   map_add':=fun u v=>by funext o;apply Ae;exact A3 _ u v
   map_smul':=fun c v=>by funext o;apply Ae;exact Al _ c v }
 have vg:∀ (i:Fin m) (o:Orb) v,v∈zs o->((t*(eA i).1).1.val.map ιK)*ᵥv∈zs o:=(by rintro i o _ ⟨v,rfl⟩;refine ⟨((t*(eA i).1).1.val.map ιK)*ᵥv,?_⟩;simp only[Aj,Ac,zY i o]);let zv (i:Fin m) (o:Orb):Module.End (Qa p) (zs o):=
  {toFun:=fun x=>⟨((t*(eA i).1).1.val.map ιK)*ᵥx.1,vg i o x.1 x.2⟩
   map_add':=fun x y=>Ae (A3 _ x.1 y.1)
   map_smul':=fun c x=>Ae (Al _ c x.1) }
 have z0:∀ i:Fin m,Qr zb zd ι (Fin S.n->Qa p) (Matrix.toLin' ((t*(eA i).1).1.val.map ιK))=∑ o:Orb,Qr zb zd ι (zs o) (zv i o):=by
  intro i;let Tpi:Module.End (Qa p) (∀ o:Orb,zs o):=
   {toFun:=fun f o=>zv i o (f o)
    map_add':=fun f g=>by ext o;simp
    map_smul':=fun c f=>by ext o;simp }
  have zA:zT.toLinearMap∘ₗMatrix.toLin' ((t*(eA i).1).1.val.map ιK)∘ₗzT.symm.toLinearMap=Tpi:=by
   apply Ap;intro f;funext o;apply Ae;change zp o*ᵥ(((t*(eA i).1).1.val.map ιK)*ᵥ∑ o':Orb,(f o').1)=((t*(eA i).1).1.val.map ιK)*ᵥ(f o).1;rw[Ac,<-zY i o,<-Ac];congr 1;rw[AJ,Ay o]
   . obtain ⟨u,hu⟩:=(f o).2;rw[<-hu,Aj,Ac,zt o o,Az rfl]
   . intro o' _ v8;obtain ⟨u,hu⟩:=(f o').2;rw[<-hu,Aj,Ac,zt o o',Aw (Ne.symm v8),BF]
   . intro h;exact absurd (Ai o) h
  rw[<-Wz zb zd ι zT,zA];exact YS zb zd ι (fun o=>zs o) (zv i)
 have z1:∀ (i:Fin m) (o:Orb),(∀ χ∈zz o,σ χ≠χ)->Qr zb zd ι (zs o) (zv i o)=0:=by
  intro i o vQ;let χ:Fin m->Bool:=Quotient.out o;have zU:χ∈zz o:=(by rw[AL];exact ⟨Ai _,Quotient.out_eq o⟩);have z2:∃ k:ℕ,0 < k/\(σ ^ k) χ=χ:=⟨N,zb,by rw[z7];rfl⟩;set k:=Nat.find z2 with hk_def
  have zx:0 < k/\(σ ^ k) χ=χ:=EF z2;have uv:2<=k:=by
   by_contra zC;have uw:k=1:=by omega
   have hfix:σ χ=χ:=by simpa[uw] using zx.2
   exact vQ χ zU hfix
  have zN:k∣N:=by
   rw[B7];by_contra zM;have vr:0 < N % k:=CM zM;have vJ:N % k < k:=DF N zx.1;have zO:∀ q:ℕ,(σ ^ (k*q)) χ=χ:=by
    intro q;induction q with
    | zero=>simp
    | succ q ih=>rw[Nat.mul_succ,DQ,CT,Equiv.Perm.mul_apply,ih,zx.2]
   have uo:(σ ^ (N % k)) χ=χ:=by
    have uc:=Cd N k;have h1:(σ ^ (k*(N / k)+N % k)) χ=χ:=by rw[uc,z7];rfl
    rw[DQ,CT,Equiv.Perm.mul_apply,zO] at h1;exact h1
   exact Nat.find_min z2 vJ ⟨vr,uo⟩
  have zK:Function.Injective (fun j:Fin k=>(σ ^ j.val) χ):=by
   intro zu zE zH;rcases lt_trichotomy zu.val zE.val with zC | hveq | hgt
   .
    exfalso;have zI:0 < zE.val - zu.val:=by omega
    have zP:zE.val - zu.val < k:=by omega
    have hfix:(σ ^ (zE.val - zu.val)) χ=χ:=(by apply (σ ^ zu.val).injective;rw[<-Equiv.Perm.mul_apply,<-CT,Nat.add_sub_of_le zC.le];exact zH.symm);exact Nat.find_min z2 zP ⟨zI,hfix⟩
   . exact A4 hveq
   .
    exfalso;have zI:0 < zu.val - zE.val:=by omega
    have zP:zu.val - zE.val < k:=by omega
    have hfix:(σ ^ (zu.val - zE.val)) χ=χ:=(by apply (σ ^ zE.val).injective;rw[<-Equiv.Perm.mul_apply,<-CT,Nat.add_sub_of_le hgt.le];exact zH);exact Nat.find_min z2 zP ⟨zI,hfix⟩
  have vs:zz o=Finset.univ.image (fun j:Fin k=>(σ ^ j.val) χ):=by
   ext ψ;simp only[zz,AL,Ai,B3,Eb];constructor
   .
    intro zJ;have up:zq.r χ ψ:=Quotient.exact ((Quotient.out_eq o).trans zJ.symm);obtain ⟨r,hr⟩:=up;refine ⟨⟨r % k,DF r zx.1⟩,?_⟩;have zO:∀ q:ℕ,(σ ^ (k*q)) χ=χ:=by
     intro q;induction q with
     | zero=>simp
     | succ q ih=>rw[Nat.mul_succ,DQ,CT,Equiv.Perm.mul_apply,ih,zx.2]
    rw[<-hr]
    conv_rhs=>rw[<-Cd r k,DQ,CT,Equiv.Perm.mul_apply,zO]
   . rintro ⟨j,rfl⟩;exact (Quotient.sound (s:=zq) ⟨j.val,rfl⟩).symm.trans (Quotient.out_eq o)
  have:NeZero N:=⟨zb.ne'⟩;have ud:Nat.card (Ab N (Qa p))=N:=Qy zb zd;obtain ⟨g0,uA⟩:=IsCyclic.exists_generator (α:=Ab N (Qa p));have vh:orderOf g0=N:=by rw[orderOf_eq_card_of_forall_mem_zpowers uA,ud]
  let ω:Ab N (Qa p):=g0 ^ (N / k);have ue:ω ^ k=1:=by
   calc (g0 ^ (N / k)) ^ k=g0 ^ (N / k*k):=(Cz _ _ _).symm
    _ = g0 ^ N:=Ah (g0 ^ ·) (EJ zN)
    _ = g0 ^ orderOf g0:=Ah (g0 ^ ·) vh.symm
    _ = 1:=BE g0
  have vK:ω≠1:=(by intro h1;have zF:=Bl h1;rw[vh] at zF;have vt:0 < N / k:=Nat.div_pos (AP zb zN) zx.1;have uE:=AP vt zF;have zD:k*(N / k)=N:=Nat.mul_div_cancel' zN;nlinarith);let D:Matrix (Fin S.n) (Fin S.n) (Qa p):=
   ∑ j:Fin k,(((ω:(Qa p)ˣ):Qa p) ^ j.val)•QK ((σ ^ j.val) χ)
  let Dinv:Matrix (Fin S.n) (Fin S.n) (Qa p):=
   ∑ j:Fin k,(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val•QK ((σ ^ j.val) χ)
  have zw:zp o=∑ j:Fin k,QK ((σ ^ j.val) χ):=(by simp only[zp,vs,Finset.sum_image (fun a _ b _ h=>zK h)]);have vL:D*Dinv=zp o:=by
   simp only[D,Dinv,zw,BP,BD];refine Ag rfl fun zu _=>?_;rw[Ay zu]
   . rw[Ar,Ao,AR,zr,Az rfl];have h1:((ω:(Qa p)ˣ):Qa p) ^ zu.val*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ zu.val=1:=(by rw[<-CC];have:(ω*ω⁻¹:Ab N (Qa p))=1:=By ω;have h2:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) this;simp only[BB,De,CH,Cn] at h2;rw[h2,B8]);rw[h1,Bx]
   .
    intro zE _ hj;rw[Ar,Ao,zr];split_ifs with h
    . exact absurd (zK h) hj
    . simp
   . intro h;exact absurd (Ai zu) h
  have vM:Dinv*D=zp o:=by
   simp only[D,Dinv,zw,BP,BD];refine Ag rfl fun zu _=>?_;rw[Ay zu]
   . rw[Ar,Ao,AR,zr,Az rfl];have h1:(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ zu.val*((ω:(Qa p)ˣ):Qa p) ^ zu.val=1:=(by rw[<-CC];have:(ω⁻¹*ω:Ab N (Qa p))=1:=CK ω;have h2:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) this;simp only[BB,De,CH,Cn] at h2;rw[h2,B8]);rw[h1,Bx]
   .
    intro zE _ hj;rw[Ar,Ao,zr];split_ifs with h
    . exact absurd (zK h) hj
    . simp
   . intro h;exact absurd (Ai zu) h
  have vN:zp o*D=D:=by
   simp only[D,zw,BP,BD];rw[AY];refine Ag rfl fun j _=>?_;rw[Ay j]
   . rw[Ao,zr,Az rfl]
   .
    intro j' _ vp;rw[Ao,zr];split_ifs with h
    . exact absurd (zK h) (Ne.symm vp)
    . simp
   . intro h;exact absurd (Ai j) h
  have z9:zp o*Dinv=Dinv:=by
   simp only[Dinv,zw,BP,BD];rw[AY];refine Ag rfl fun j _=>?_;rw[Ay j]
   . rw[Ao,zr,Az rfl]
   .
    intro j' _ vp;rw[Ao,zr];split_ifs with h
    . exact absurd (zK h) (Ne.symm vp)
    . simp
   . intro h;exact absurd (Ai j) h
  have vO:D*((t*(eA i).1).1.val.map ιK)*Dinv=((ω:(Qa p)ˣ):Qa p)•(((t*(eA i).1).1.val.map ιK)*zp o):=by
   haveI:NeZero k:=⟨zx.1.ne'⟩;have zD:(t*(eA i).1).1.val.map ιK=(t.1.val.map ιK)*((eA i).1.1.val.map ιK):=Aq;have vA:∀ j:Fin k,((t*(eA i).1).1.val.map ιK)*QK ((σ ^ j.val) χ)=QK ((σ ^ (j+1:Fin k).val) χ)*((t*(eA i).1).1.val.map ιK):=by
    intro j;have uf:σ ((σ ^ j.val) χ)=(σ ^ (j+1:Fin k).val) χ:=by
     have zQ:(j+1:Fin k).val=if j.val+1 < k then j.val+1 else 0:=by
      change (j.val+1 % k) % k=_;have vV:1 % k=1:=A9 (by omega);rw[vV];split_ifs with zC
      . exact A9 zC
      .
       have zH:j.val+1=k:=by omega
       rw[zH,Ds]
     rw[<-Equiv.Perm.mul_apply,<-BA];by_cases zC:j.val+1 < k
     . rw[zQ,Az zC]
     .
      have zH:j.val+1=k:=by omega
      rw[zQ,Aw zC,zH,zx.2];simp
    have vi:((eA i).1.1.val.map ιK)*QK ((σ ^ j.val) χ)=QK ((σ ^ j.val) χ)*((eA i).1.1.val.map ιK):=by
     have h1:(eA i).1.1.val*Q ((σ ^ j.val) χ)=Q ((σ ^ j.val) χ)*(eA i).1.1.val:=by
      rw[zi];exact QU _ _ fun r=>by
       have vT:(eA i).1.1.val*(eA r).1.1.val=(eA r).1.1.val*(eA i).1.1.val:=(by have h1:=ze ((eA i).1*(eA r).1) (A.mul_mem (eA i).2 (eA r).2);have hi:=ze (eA i).1 (eA i).2;have hr:=ze (eA r).1 (eA r).2;have vP:((eA i).1*(eA r).1)⁻¹=(eA i).1*(eA r).1:=inv_eq_of_mul_eq_one_right h1;have zB:(eA i).1⁻¹=(eA i).1:=inv_eq_of_mul_eq_one_right hi;have vW:(eA r).1⁻¹=(eA r).1:=inv_eq_of_mul_eq_one_right hr;have zZ:(eA i).1*(eA r).1=(eA r).1*(eA i).1:=(by rw[<-vP,Dm,zB,vW]);exact Ah (fun g:S.L=>g.1.val) zZ);unfold Qo;simp only[Ao,Ar,BH,BQ,As,AC,vT]
     simp only[QK,<-Aq,h1]
    rw[zD,Af,vi,<-Af,z8,uf,Af]
   have vu:∀ j:Fin k,((ω:(Qa p)ˣ):Qa p) ^ (j+1:Fin k).val*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val=((ω:(Qa p)ˣ):Qa p):=by
    intro j;have ug:((ω:(Qa p)ˣ):Qa p) ^ k=1:=by
     have:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) ue
     simpa using this
    have z5:((ω:(Qa p)ˣ):Qa p)*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p)=1:=by
     have:=Ah (fun u:Ab N (Qa p)=>((u:(Qa p)ˣ):Qa p)) (By ω)
     simpa using this
    have zQ:(j+1:Fin k).val=if j.val+1 < k then j.val+1 else 0:=by
     change (j.val+1 % k) % k=_;have vV:1 % k=1:=A9 (by omega);rw[vV];split_ifs with zC
     . exact A9 zC
     .
      have zH:j.val+1=k:=by omega
      rw[zH,Ds]
    by_cases zC:j.val+1 < k
    . rw[zQ,Az zC,BA,Ad,<-CC,z5,B8,AK]
    .
     have zH:j.val+1=k:=by omega
     rw[zQ,Aw zC,D7,AA]
     calc (((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val
       = ((ω:(Qa p)ˣ):Qa p) ^ k*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val:=by rw[ug,AA]
      _ = ((ω:(Qa p)ˣ):Qa p) ^ (j.val+1)*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val:=
        Ah (fun e=>((ω:(Qa p)ˣ):Qa p) ^ e*_) zH.symm
      _ = ((ω:(Qa p)ˣ):Qa p)*(((ω:(Qa p)ˣ):Qa p)*(((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p)) ^ j.val:=by rw[BA,Ad,CC]
      _ = ((ω:(Qa p)ˣ):Qa p):=by rw[z5,B8,AK]
   calc D*((t*(eA i).1).1.val.map ιK)*Dinv
     = ∑ j:Fin k,D*((((ω⁻¹:Ab N (Qa p)):(Qa p)ˣ):Qa p) ^ j.val•(((t*(eA i).1).1.val.map ιK)*QK ((σ ^ j.val) χ))):=by simp only[Dinv,BD,Ao,Af]
    _ = ∑ j:Fin k,((ω:(Qa p)ˣ):Qa p)•(((t*(eA i).1).1.val.map ιK)*QK ((σ ^ j.val) χ)):=by
          refine Ag rfl fun j _=>?_;rw[Ao,vA j,<-Af];have ux:D*QK ((σ ^ (j+1:Fin k).val) χ)=((ω:(Qa p)ˣ):Qa p) ^ (j+1:Fin k).val•QK ((σ ^ (j+1:Fin k).val) χ):=by
           simp only[D,BP];rw[Ay (j+1)]
           . rw[Ar,zr,Az rfl]
           . intro j' _ vp;rw[Ar,zr,Aw (fun h=>vp (zK h)),smul_zero]
           . intro h;exact absurd (Ai _) h
          rw[ux,Ar,AR,Bb,vu j,<-vA j]
    _ = ((ω:(Qa p)ˣ):Qa p)•(((t*(eA i).1).1.val.map ιK)*zp o):=by rw[<-BC,zw,BD]
  let eD:zs o≃ₗ[Qa p] zs o:=
   {toFun:=fun x=>⟨D*ᵥx.1,by
     refine ⟨D*ᵥx.1,?_⟩
     rw[Aj,Ac,vN]⟩
    invFun:=fun x=>⟨Dinv*ᵥx.1,by
     refine ⟨Dinv*ᵥx.1,?_⟩
     rw[Aj,Ac,z9]⟩
    left_inv:=fun x=>by
     apply Ae;change Dinv*ᵥ(D*ᵥx.1)=x.1;obtain ⟨u,hu⟩:=x.2;rw[Ac,vM,<-hu,Aj,Ac,zt o o,Az rfl]
    right_inv:=fun x=>by
     apply Ae;change D*ᵥ(Dinv*ᵥx.1)=x.1;obtain ⟨u,hu⟩:=x.2;rw[Ac,vL,<-hu,Aj,Ac,zt o o,Az rfl]
    map_add':=fun x y=>Ae (A3 _ x.1 y.1)
    map_smul':=fun c x=>Ae (Al _ c x.1) }
  have vv:eD.toLinearMap∘ₗzv i o∘ₗeD.symm.toLinearMap=((ω:(Qa p)ˣ):Qa p)•zv i o:=(by apply Ap;intro x;apply Ae;change D*ᵥ(((t*(eA i).1).1.val.map ιK)*ᵥ(Dinv*ᵥx.1))=((ω:(Qa p)ˣ):Qa p)•(((t*(eA i).1).1.val.map ιK)*ᵥx.1);rw[Ac,Ac,vO,Bv];congr 1;obtain ⟨u,hu⟩:=x.2;rw[<-hu,Aj,Ac,Af,zt o o,Az rfl,<- Ac]);have zV:=Wz zb zd ι eD (zv i o);rw[vv,YG zb zd ι ω] at zV;have vj:((ι ω:ℂˣ):ℂ)≠1:=(by intro h1;apply vK;apply ι.injective;rw[BI];exact Ae (A7 (by simpa using h1)));have zD:(((ι ω:ℂˣ):ℂ) - 1)*Qr zb zd ι (zs o) (zv i o)=0:=(by linear_combination zV);exact (mul_eq_zero.mp zD).resolve_left (sub_ne_zero.mpr vj)
 let zo (b:Bool):ℂ:=if b then 1 else -1;let UK (χ:Fin m->Bool):Submodule (Qa p) (Fin S.n->Qa p):=LinearMap.range (Matrix.toLin' (QK χ));let vk (χ:Fin m->Bool) (hfix:σ χ=χ):Module.End (Qa p) (UK χ):=
  {toFun:=fun x=>⟨(t.1.val.map ιK)*ᵥx.1,by
    obtain ⟨v,hv⟩:=x.2;refine ⟨(t.1.val.map ιK)*ᵥv,?_⟩
    rw[<-hv,Aj,Aj,Ac,Ac,z8,hfix]⟩
   map_add':=fun x y=>Ae (A3 _ x.1 y.1)
   map_smul':=fun c x=>Ae (Al _ c x.1) }
 have z3:∀ (χ:Fin m->Bool) (hfix:σ χ=χ) (i:Fin m),Qr zb zd ι (zs (Quotient.mk zq χ)) (zv i (Quotient.mk zq χ))=zo (χ i)*Qr zb zd ι (UK χ) (vk χ hfix):=by
  intro χ hfix i;let o:=Quotient.mk zq χ;have va:zz o={χ}:=by
   ext ψ;simp only[zz,AL,Ai,B3,Da];constructor
   .
    intro zJ;obtain ⟨r,hr⟩:=Quotient.exact zJ.symm;have vw:∀ r:ℕ,(σ ^ r) χ=χ:=by
     intro r;induction r with
     | zero=>rfl
     | succ r ih=>rw[BA,Equiv.Perm.mul_apply,ih,hfix]
    exact (hr.symm.trans (vw r))
   . rintro rfl;rfl
  have zw:zp o=QK χ:=by simp[zp,va]
  have uh:zs o=UK χ:=by simp[zs,UK,zw]
  let vX:zs o≃ₗ[Qa p] UK χ:=LinearEquiv.ofEq _ _ uh;have zD:(t*(eA i).1).1.val.map ιK=(t.1.val.map ιK)*((eA i).1.1.val.map ιK):=Aq;have zA:vX.toLinearMap∘ₗzv i o∘ₗvX.symm.toLinearMap=ιK (Qh p (χ i))•vk χ hfix:=(by apply Ap;intro x;apply Ae;change ((t*(eA i).1).1.val.map ιK)*ᵥx.1=ιK (Qh p (χ i))•((t.1.val.map ιK)*ᵥx.1);obtain ⟨u,hu⟩:=x.2;rw[zD,<-hu,Aj,Ac,Ac,Af,ub i χ,Ao,Bv,<-Ac]);rw[<-Wz zb zd ι vX (zv i o),zA];cases uD:χ i;·
   let zG:=Qq (R:=Qa p) zX;have vb:((zG:(Qa p)ˣ):Qa p)=ιK (Qh p false):=(by simp[zG,Qq,Qh]);rw[<-vb,YG zb zd ι zG];have vY:=WB (p:=p) zX (by omega) ι;have vZ:((ι zG:ℂˣ):ℂ)=-1:=by
    have:=Ah (fun u:Ab N ℂ=>((u:ℂˣ):ℂ)) vY
    simpa[zG] using this
   rw[vZ];simp[zo]
  ·
   simp[Qh,zo]
 have v0:∀ χ:Fin m->Bool,Q χ≠0->∀ i j:Fin m,Qh p (χ (eA.symm ((eA i)*(eA j))))=Qh p (χ i)*Qh p (χ j):=(by intro χ vy i j;have vx:(eA (eA.symm (eA i*eA j))).1.1.val=(eA i).1.1.val*(eA j).1.1.val:=(by simp);have h1:=zh (eA.symm (eA i*eA j)) χ;rw[vx,Af,zh j χ,Ao,zh i χ,AR,Bb] at h1;have v1:(Qh p (χ (eA.symm (eA i*eA j))) - Qh p (χ i)*Qh p (χ j))•Q χ=0:=(by rw[DJ,h1,Cx]);exact sub_eq_zero.mp ((smul_eq_zero.mp v1).resolve_right vy));have vl:∀ χ:Fin m->Bool,Q χ≠0->∑ i:Fin m,zo (za i)*zo (χ i)=if χ=za then (m:ℂ) else 0:=by
  intro χ vy;split_ifs with h
  .
   rw[h];have v2:∀ i:Fin m,zo (za i)*zo (za i)=1:=fun i=>by cases za i <;> simp[zo]
   simp[v2,BS,AW]
  .
   have uy:∃ i₀:Fin m,χ i₀≠za i₀:=(by by_contra hall;push Not at hall;exact h (funext hall));obtain ⟨i₀,uk⟩:=uy;have zS:∀ ψ:Fin m->Bool,Q ψ≠0->∀ a b:Fin m,zo (ψ (eA.symm (eA a*eA b)))=zo (ψ a)*zo (ψ b):=by
    intro ψ zJ a b;have hz:=v0 ψ zJ a b;have v3:(1:ZMod p)≠-1:=by
     intro h1;have vR:(2:ZMod p)=0:=by linear_combination h1
     have zF:p∣2:=(At 2 p).mp (by simpa using vR)
     have:=AP (by decide) zF;omega
    cases h1:ψ (eA.symm (eA a*eA b)) <;> cases h2:ψ a <;> cases h3:ψ b <;>
     simp[Qh,zo,h1,h2,h3] at hz ⊢
    all_goals first | exact absurd hz v3 | exact absurd hz.symm v3
   set Ssum:=∑ i:Fin m,zo (za i)*zo (χ i);let zW:Equiv.Perm (Fin m):=
    {toFun:=fun i=>eA.symm (eA i₀*eA i)
     invFun:=fun i=>eA.symm ((eA i₀)⁻¹*eA i)
     left_inv:=fun i=>by simp
     right_inv:=fun i=>by simp }
   have vm:Ssum=(zo (za i₀)*zo (χ i₀))*Ssum:=(by rw[A6];symm;refine AO zW _ _ fun i=>?_;change (zo (za i₀)*zo (χ i₀))*(zo (za i)*zo (χ i))=zo (za (eA.symm (eA i₀*eA i)))*zo (χ (eA.symm (eA i₀*eA i)));rw[zS za zm i₀ i,zS χ vy i₀ i];ring);have vn:zo (za i₀)*zo (χ i₀)=-1:=(by cases h1:za i₀ <;> cases h2:χ i₀ <;> simp[zo,h1,h2] at uk ⊢);rw[vn] at vm;have uz:(2:ℂ)*Ssum=0:=by linear_combination vm
   exact (mul_eq_zero.mp uz).resolve_left (by norm_num)
 have uq:∑ i:Fin m,zo (za i)*Qr zb zd ι (Fin S.n->Qa p) (Matrix.toLin' ((t*(eA i).1).1.val.map ιK))=(m:ℂ)*Qr zb zd ι UK0 T0:=by
  simp_rw[z0,A6];rw[AY];let vc:Orb:=Quotient.mk zq za;have z6:σ za=za:=funext zg;rw[Ay vc]
  .
   have v4:vk za z6=T0:=(by apply Ap;intro x;apply Ae;rfl);have ui:∀ i:Fin m,zo (za i)*Qr zb zd ι (zs vc) (zv i vc)=Qr zb zd ι UK0 T0:=by
    intro i;rw[z3 za z6 i];have v2:zo (za i)*zo (za i)=1:=by cases za i <;> simp[zo]
    rw[<-Ad,v2,AA,v4]
   simp[ui,BS,AW]
  .
   intro o _ ho;by_cases hfix:∃ χ∈zz o,σ χ=χ
   .
    obtain ⟨χ,zU,zL⟩:=hfix;have uj:o=Quotient.mk zq χ:=(Finset.mem_filter.mp zU).2.symm;subst uj;by_cases v7:Q χ=0
    .
     refine A1 fun i _=>?_;rw[z3 χ zL i];have ur:QK χ=0:=by simp[QK,v7]
     have us:Qr zb zd ι (UK χ) (vk χ zL)=0:=by
      unfold Qr;refine A1 fun ζ _=>?_
      have v1:Subsingleton (UK χ):=⟨fun x y=>by
       apply Ae;obtain ⟨u,hu⟩:=x.2;obtain ⟨v,hv⟩:=y.2
       rw[<-hu,<-hv,Aj,Aj,ur,BF,BF]⟩
      rw[Module.finrank_zero_of_subsingleton];simp
     rw[us,AS,AS]
    . have v5:χ≠za:=fun h=>ho (by subst h;rfl);have h1:∑ i:Fin m,zo (za i)*Qr zb zd ι (zs (Quotient.mk zq χ)) (zv i (Quotient.mk zq χ))=(∑ i:Fin m,zo (za i)*zo (χ i))*Qr zb zd ι (UK χ) (vk χ zL):=(by rw[Bo];refine Ag rfl fun i _=>?_;rw[z3 χ zL i,Ad]);rw[h1,vl χ v7,Aw v5,Bm]
   . push Not at hfix;refine A1 fun i _=>?_;rw[z1 i o hfix,AS]
  . intro h;exact absurd (Ai vc) h
 have vo:∀ i:Fin m,∃ q:ℚ,Qr zb zd ι (Fin S.n->Qa p) (Matrix.toLin' ((t*(eA i).1).1.val.map ιK))=(q:ℂ):=
  fun i=>S.ratTr (t*(eA i).1).1 (t*(eA i).1).2
 choose qf hqf using vo;let vB (b:Bool):ℚ:=if b then 1 else -1;have v6:0 < m:=by rw[<-AW m,Fintype.card_congr eA];exact Fintype.card_pos
 have vC:(m:ℂ)≠0:=Nat.cast_ne_zero.mpr v6.ne';refine ⟨(m:ℚ)⁻¹*∑ i:Fin m,vB (za i)*qf i,?_⟩;apply Ck vC;rw[<-uq];push_cast;rw[<-Ad,mul_inv_cancel₀ vC,AA];refine Ag rfl fun i _=>?_;have zQ:(t*(eA i).1).1.val=t.1.val*(eA i).1.1.val:=rfl;rw[<-zQ,hqf i];cases za i <;> simp[zo,vB]
lemma W3 (zp:7<=p) {N:ℕ} {zf:0 < N} {zk:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zf zk ι) (A:Subgroup S.L) [A.Normal] (zq:∀ a∈A,a*a=1) (m:ℕ) (eA:Fin m ≃ A) (Q:(Fin m->Bool)->Matrix (Fin S.n) (Fin S.n) (ZMod p)) (zl:∀ χ,Q χ=Qf (fun i=>Qo (eA i).1.1.val (χ i))) (zm:∑ χ:Fin m->Bool,Q χ=1) (zd:∀ χ ψ,Q χ*Q ψ=if χ=ψ then Q χ else 0) (zo:∀ (i:Fin m) χ,(eA i).1.1.val*Q χ=Qh p (χ i)•Q χ) (zb:S.L->Equiv.Perm (Fin m)) (zh:∀ g i,(eA (zb g i)).1=g*(eA i).1*g⁻¹) (zi:∀ (g:S.L) χ,g.1.val*Q χ=Q (fun i=>χ ((zb g).symm i))*g.1.val) (za:Fin m->Bool) (zn:Q za≠0) (I:Subgroup S.L) (zj:∀ g∈I,∀ i:Fin m,za ((zb g).symm i)=za i) (zc:∀ g∈I,g.1.val*Q za=Q za*g.1.val) (d:ℕ) (bU:Module.Basis (Fin d) (ZMod p) (LinearMap.range (Matrix.toLin' (Q za)))) (ze:I→*Aa (Fin d) (ZMod p)) (zg:∀ (g:I) (x:LinearMap.range (Matrix.toLin' (Q za))), (ze g).val*ᵥ(bU.equivFun x)=bU.equivFun ⟨g.1.1.val*ᵥx.1,by
    obtain ⟨v,hv⟩:=x.2;refine ⟨g.1.1.val*ᵥv,?_⟩
    rw[<-hv,Aj,Aj,Ac,Ac,zc g.1 g.2]⟩)
  (g:Aa (Fin d) (ZMod p)) (hg:g∈ze.range) :
  ∃ q:ℚ,Qr zf zk ι (Fin d->Qa p)
    (Matrix.toLin' (g.val.map (algebraMap (ZMod p) (Qa p))))=(q:ℂ):=by
 let U:Submodule (ZMod p) (Fin S.n->ZMod p):=LinearMap.range (Matrix.toLin' (Q za));let zr:=algebraMap (ZMod p) (Qa p);rcases hg with ⟨t,rfl⟩
 let UK0:Submodule (Qa p) (Fin S.n->Qa p):=LinearMap.range (Matrix.toLin' ((Q za).map zr));have zG:∀ j:Fin d,(Q za).map zr*ᵥ(fun k=>zr ((bU j).1 k))=fun k=>zr ((bU j).1 k):=(by intro j;obtain ⟨u,hu⟩:=(bU j).2;have zL:Q za*ᵥ(bU j).1=(bU j).1:=(by rw[<-hu,Aj,Ac,zd za za,Az rfl]);funext k;have hk:=Ah zr (An zL k);simpa[Matrix.mulVec,dotProduct,Ba,AF] using hk);have zE:∀ j:Fin d,(fun k=>zr ((bU j).1 k))∈UK0:=fun j=>
  ⟨fun k=>zr ((bU j).1 k),by rw[Aj,zG j]⟩
 let zt:(Fin d->Qa p)→ₗ[Qa p] UK0:=
  {toFun:=fun c=>⟨∑ j:Fin d,c j•(fun k=>zr ((bU j).1 k)),Submodule.sum_mem _ fun j _=>EH _ _ (zE j)⟩
   map_add':=fun c₁ c₂=>Ae (by simp[Fc,Bt])
   map_smul':=fun r c=>Ae (by simp[BC,AR]) }
 let zs:Matrix (Fin d) (Fin S.n) (ZMod p):=
  Matrix.of fun j k=>bU.equivFun ⟨Q za*ᵥ(Pi.single k 1),⟨Pi.single k 1,rfl⟩⟩ j
 have zx:∀ x:U,zs*ᵥx.1=bU.equivFun x:=by
  intro x;have zH:x.1=∑ k:Fin S.n,x.1 k•(Pi.single k 1:Fin S.n->ZMod p):=(by funext r;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]);have zM:Q za*ᵥx.1=x.1:=by obtain ⟨u,hu⟩:=x.2;rw[<-hu,Aj,Ac,zd za za,Az rfl]
  have zy:x=∑ k:Fin S.n,x.1 k•(⟨Q za*ᵥ(Pi.single k 1),⟨Pi.single k 1,rfl⟩⟩:U):=by
   apply Ae;simp only[B4,Bp]
   conv_lhs=>rw[<-zM,zH]
   rw[AJ];refine Ag rfl fun k _=>Al _ _ _
  conv_rhs=>rw[zy,Ba]
  funext j;simp only[Matrix.mulVec,dotProduct,zs,Ak,AQ,Bd,AX,Am];refine Ag rfl fun k _=>Bb _ _
 have zB:∀ v:Fin S.n->ZMod p,∑ j:Fin d,(zs*ᵥv) j•(bU j).1=Q za*ᵥv:=by
  intro v;have hQ:(Q za*ᵥv)∈U:=⟨v,rfl⟩;have h1:zs*ᵥ(Q za*ᵥv)=bU.equivFun ⟨Q za*ᵥv,hQ⟩:=zx ⟨Q za*ᵥv,hQ⟩;have h2:zs*ᵥ(Q za*ᵥv)=zs*ᵥv:=by
   funext j;have zw:v=∑ k:Fin S.n,v k•(Pi.single k 1:Fin S.n->ZMod p):=(by funext r;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte])
   conv_lhs=>rw[zw,AJ,AJ]
   conv_rhs=>rw[zw,AJ]
   simp only[AQ,Al,AX,Am];refine Ag rfl fun k _=>?_;congr 1;have h3:=An (zx ⟨Q za*ᵥ(Pi.single k 1),⟨Pi.single k 1,rfl⟩⟩) j;have h4:zs*ᵥ(Pi.single k 1)=fun j'=>zs j' k:=(by funext j';simp[Matrix.mulVec,dotProduct,AG]);rw[h3,h4];rfl
  rw[<-h2,h1];have zv:=Ah Subtype.val (bU.sum_repr ⟨Q za*ᵥv,hQ⟩);rw[B4] at zv;simp only[Bp] at zv;exact zv
 let zu:UK0→ₗ[Qa p] (Fin d->Qa p):=
  {toFun:=fun x=>(zs.map zr)*ᵥx.1
   map_add':=fun x y=>A3 _ x.1 y.1
   map_smul':=fun c x=>Al _ c x.1 }
 have zK:∀ c:Fin d->Qa p,zu (zt c)=c:=by
  intro c;have h1:∀ j:Fin d,(zs.map zr)*ᵥ(fun k=>zr ((bU j).1 k))=Pi.single j 1:=by
   intro j;have hj:=zx (bU j);funext i;have hi:=Ah zr (An hj i);have zP:bU.equivFun (bU j) i=if i=j then 1 else 0:=by simp[eq_comm]
   rw[zP] at hi;simpa[Matrix.mulVec,dotProduct,Ba,AF,AG] using hi
  change (zs.map zr)*ᵥ∑ j:Fin d,c j•(fun k=>zr ((bU j).1 k))=c;rw[AJ];funext i;simp only[AQ,Al,h1,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]
 have zz:∀ x:UK0,zt (zu x)=x:=by
  intro x;apply Ae;obtain ⟨v,hv⟩:=x.2;dsimp only[zt,zu,LinearMap.coe_mk,AddHom.coe_mk];rw[<-hv,Aj];have zF:∀ k:Fin S.n,∑ j:Fin d,(zs.map zr*ᵥ((Q za).map zr*ᵥ(Pi.single k 1))) j•(fun r=>zr ((bU j).1 r))=(Q za).map zr*ᵥ(Pi.single k 1):=by
   intro k;have h1:=zB (Q za*ᵥ(Pi.single k 1))
   conv_rhs at h1=>rw[Ac,zd za za,Az rfl]
   funext r;have hr:=Ah zr (An h1 r);simpa[AQ,AX,Am,Matrix.mulVec,dotProduct,Ba,AF,AG] using hr
  have zw:v=∑ k:Fin S.n,v k•(Pi.single k 1:Fin S.n->Qa p):=(by funext r;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte])
  conv_lhs=>rw[zw,AJ,AJ]
  conv_rhs=>rw[zw,AJ]
  simp only[AQ,Al,AX,Am,DU];rw[AY];refine Ag rfl fun k _=>?_
  have:=Ah (v k•·) (zF k)
  simpa[BC,AR] using this
 let eU:(Fin d->Qa p)≃ₗ[Qa p] UK0:=
  {toLinearMap:=zt
   invFun:=zu
   left_inv:=zK
   right_inv:=zz }
 have zA:∀ v∈UK0,(t.1.1.val.map zr)*ᵥv∈UK0:=(by rintro _ ⟨v,rfl⟩;refine ⟨(t.1.1.val.map zr)*ᵥv,?_⟩;simp only[Aj,Ac,<-Aq,zc t.1 t.2]);let T0:Module.End (Qa p) UK0:=
  {toFun:=fun x=>⟨(t.1.1.val.map zr)*ᵥx.1,zA x.1 x.2⟩
   map_add':=fun x y=>Ae (A3 _ x.1 y.1)
   map_smul':=fun c x=>Ae (Al _ c x.1) }
 have zD:eU.toLinearMap∘ₗMatrix.toLin' ((ze t).val.map zr)∘ₗeU.symm.toLinearMap=T0:=by
  apply Ap;intro x;apply Ae;have zy:x=zt (zu x):=(zz x).symm;have zI:∀ j:Fin d,(zt ((ze t).val.map zr*ᵥ(Pi.single j 1))).1=(t.1.1.val.map zr)*ᵥ(fun k=>zr ((bU j).1 k)):=by
   intro j;set M:Matrix (Fin d) (Fin d) (ZMod p):=(ze t).val
   let yU:U:=⟨t.1.1.val*ᵥ(bU j).1,by
    obtain ⟨v,hv⟩:=(bU j).2;refine ⟨t.1.1.val*ᵥv,?_⟩
    rw[<-hv,Aj,Aj,Ac,Ac,zc t.1 t.2]⟩
   have h1:M*ᵥ(Pi.single j 1)=bU.equivFun yU:=by
    have:=zg t (bU j)
    have zQ:bU.equivFun (bU j)=Pi.single j 1:=(by funext i;simp[AG,eq_comm]);rwa[zQ] at this
   have h2:∑ i:Fin d,(M*ᵥ(Pi.single j 1)) i•(bU i).1=t.1.1.val*ᵥ(bU j).1:=(by rw[h1];have zv:=Ah Subtype.val (bU.sum_repr yU);rw[B4] at zv;simp only[Bp] at zv;exact zv);have zC:∀ i:Fin d,(M.map zr*ᵥ(Pi.single j 1)) i=zr ((M*ᵥ(Pi.single j 1)) i):=(by intro i;simp only[Matrix.mulVec,dotProduct,AG,Ca,AK,AS,A8,Ai,↓reduceIte,AZ]);funext r;have hr:=Ah zr (An h2 r);dsimp only[zt,LinearMap.coe_mk,AddHom.coe_mk];simp only[AQ,AX,Am,zC];have zN:∑ i:Fin d,zr ((M*ᵥPi.single j 1) i)*zr ((bU i).1 r)=zr (∑ i:Fin d,(M*ᵥPi.single j 1) i*(bU i).1 r):=(by simp only[Ba,AF]);have zO:(t.1.1.val.map zr*ᵥfun k=>zr ((bU j).1 k)) r=zr ((t.1.1.val*ᵥ(bU j).1) r):=(by simp only[Matrix.mulVec,dotProduct,AZ,Ba,AF]);rw[zN,zO];simpa only[AQ,AX,Am] using hr
  set c:=zu x;have zJ:c=∑ j:Fin d,c j•(Pi.single j 1:Fin d->Qa p):=(by funext i;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]);change (zt ((ze t).val.map zr*ᵥc)).1=(t.1.1.val.map zr)*ᵥx.1
  conv_lhs=>rw[zJ,AJ,Ba,B4]
  conv_rhs=>rw[zy]
  change ∑ j:Fin d,(zt ((ze t).val.map zr*ᵥ(c j•Pi.single j 1))).1=(t.1.1.val.map zr)*ᵥ(∑ j:Fin d,c j•(fun k=>zr ((bU j).1 k)));rw[AJ];refine Ag rfl fun j _=>?_;rw[Al,Bd,Bp,zI j,Al]
 rw[<-Wz zf zk ι eU,zD];exact W2 zp S A zq m eA Q zl zm zd zo zb zh zi
  za zn t.1 (zj t.1 t.2)
lemma WQ {N:ℕ} {zi:0 < N} {zj:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zi zj ι) (m:ℕ) (Q:(Fin m->Bool)->Matrix (Fin S.n) (Fin S.n) (ZMod p)) (ze:∀ χ ψ,Q χ*Q ψ=if χ=ψ then Q χ else 0) (zb:S.L->Equiv.Perm (Fin m)) (zh:∀ (g:S.L) χ,g.1.val*Q χ=Q (fun i=>χ ((zb g).symm i))*g.1.val) (za:Fin m->Bool) (I:Subgroup S.L) (zg:∀ g:S.L,g∈I↔∀ i:Fin m,za (zb g i)=za i) (zd:∀ g∈I,g.1.val*Q za=Q za*g.1.val) (d:ℕ) (bU:Module.Basis (Fin d) (ZMod p) (LinearMap.range (Matrix.toLin' (Q za)))) (zc:I→*Aa (Fin d) (ZMod p)) (zf:∀ (g:I) (x:LinearMap.range (Matrix.toLin' (Q za))), (zc g).val*ᵥ(bU.equivFun x)=bU.equivFun ⟨g.1.1.val*ᵥx.1,by
    obtain ⟨v,hv⟩:=x.2;refine ⟨g.1.1.val*ᵥv,?_⟩
    rw[<-hv,Aj,Aj,Ac,Ac,zd g.1 g.2]⟩)
  (W:Submodule (Qa p) (Fin d->Qa p))
  (hW:∀ g∈zc.range,∀ v∈W,(g.val.map (algebraMap (ZMod p) (Qa p)))*ᵥv∈W) :
  W=⊥\/W=⊤:=by
 classical
 let U:Submodule (ZMod p) (Fin S.n->ZMod p):=LinearMap.range (Matrix.toLin' (Q za));let ιK:=algebraMap (ZMod p) (Qa p);by_cases zB:W=⊥
 . left;exact zB
 .
  right;let QK (χ:Fin m->Bool):Matrix (Fin S.n) (Fin S.n) (Qa p):=(Q χ).map ιK;have zs:∀ χ ψ,QK χ*QK ψ=if χ=ψ then QK χ else 0:=by
   intro χ ψ;simp only[QK,<-Aq,ze];split_ifs
   . rfl
   . ext a b;simp
  let φ_emb:(Fin d->Qa p)→ₗ[Qa p] (Fin S.n->Qa p):=
   {toFun:=fun c=>∑ j:Fin d,c j•(fun k=>ιK ((bU j).1 k))
    map_add':=fun c₁ c₂=>by simp[Fc,Bt]
    map_smul':=fun r c=>by simp[BC,AR] }
  have zn:Function.Injective φ_emb:=by
   rw[injective_iff_map_eq_zero];intro c hc;let zk:Matrix (Fin d) (Fin S.n) (ZMod p):=
    Matrix.of fun j k=>bU.equivFun ⟨Q za*ᵥ(Pi.single k 1),⟨Pi.single k 1,rfl⟩⟩ j
   have zt:∀ j:Fin d,(zk.map ιK)*ᵥ(fun k=>ιK ((bU j).1 k))=Pi.single j 1:=by
    intro j;have zy:(bU j).1=∑ k:Fin S.n,(bU j).1 k•(Pi.single k 1:Fin S.n->ZMod p):=(by funext r;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte]);have zF:Q za*ᵥ(bU j).1=(bU j).1:=by obtain ⟨u,hu⟩:=(bU j).2;rw[<-hu,Aj,Ac,ze za za,Az rfl]
    have zC:bU j=∑ k:Fin S.n,(bU j).1 k•(⟨Q za*ᵥ(Pi.single k 1),⟨Pi.single k 1,rfl⟩⟩:U):=by
     apply Ae;simp only[B4,Bp]
     conv_lhs=>rw[<-zF,zy]
     rw[AJ];refine Ag rfl fun k _=>Al _ _ _
    have hZ:zk*ᵥ(bU j).1=Pi.single j 1:=by
     funext i;have zK:bU.equivFun (bU j) i=if i=j then 1 else 0:=by simp[eq_comm]
     rw[AG,<-zK]
     conv_rhs=>rw[zC,Ba]
     simp only[Matrix.mulVec,dotProduct,zk,Ak,AQ,Bd,AX,Am];refine Ag rfl fun k _=>Bb _ _
    funext i
    have:=Ah ιK (An hZ i)
    simpa[Matrix.mulVec,dotProduct,Ba,AF,AG] using this
   have h0:=Ah ((zk.map ιK)*ᵥ·) hc;rw[DZ] at h0;change (zk.map ιK)*ᵥ(∑ j:Fin d,c j•(fun k=>ιK ((bU j).1 k)))=0 at h0;rw[AJ] at h0;funext i;have hi:=An h0 i;simp only[AQ,Al,zt,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte,EE] at hi;exact hi
  have zl:∀ c,QK za*ᵥφ_emb c=φ_emb c:=(by intro c;change QK za*ᵥ∑ j:Fin d,c j•(fun k=>ιK ((bU j).1 k))=_;rw[AJ];refine Ag rfl fun j _=>?_;rw[Al];congr 1;obtain ⟨u,hu⟩:=(bU j).2;have zm:Q za*ᵥ(bU j).1=(bU j).1:=(by rw[<-hu,Aj,Ac,ze za za,Az rfl]);funext k;have:=Ah ιK (An zm k);simpa[QK,Matrix.mulVec,dotProduct,Ba,AF] using this);have zD:∀ (t:I) c,(t.1.1.val.map ιK)*ᵥφ_emb c=φ_emb ((zc t).val.map ιK*ᵥc):=by
   intro t c;have zz:∀ j:Fin d,(t.1.1.val.map ιK)*ᵥ(fun k=>ιK ((bU j).1 k))=φ_emb ((zc t).val.map ιK*ᵥ(Pi.single j 1)):=by
    intro j;set M:Matrix (Fin d) (Fin d) (ZMod p):=(zc t).val
    let yU:U:=⟨t.1.1.val*ᵥ(bU j).1,by
     obtain ⟨v,hv⟩:=(bU j).2;refine ⟨t.1.1.val*ᵥv,?_⟩
     rw[<-hv,Aj,Aj,Ac,Ac,zd t.1 t.2]⟩
    have h1:M*ᵥ(Pi.single j 1)=bU.equivFun yU:=by
     have:=zf t (bU j)
     have zL:bU.equivFun (bU j)=Pi.single j 1:=(by funext i;simp[AG,eq_comm]);rwa[zL] at this
    have h2:∑ i:Fin d,(M*ᵥ(Pi.single j 1)) i•(bU i).1=t.1.1.val*ᵥ(bU j).1:=(by rw[h1];have zo:=Ah Subtype.val (bU.sum_repr yU);rw[B4] at zo;simp only[Bp] at zo;exact zo);have zu:∀ i:Fin d,(M.map ιK*ᵥ(Pi.single j 1)) i=ιK ((M*ᵥ(Pi.single j 1)) i):=(by intro i;simp only[Matrix.mulVec,dotProduct,AG,Ca,AK,AS,A8,Ai,↓reduceIte,AZ]);funext r;have hr:=Ah ιK (An h2 r);dsimp only[φ_emb,LinearMap.coe_mk,AddHom.coe_mk];simp only[AQ,AX,Am,zu];have zG:(t.1.1.val.map ιK*ᵥfun k=>ιK ((bU j).1 k)) r=ιK ((t.1.1.val*ᵥ(bU j).1) r):=(by simp only[Matrix.mulVec,dotProduct,AZ,Ba,AF]);have zH:∑ i:Fin d,ιK ((M*ᵥPi.single j 1) i)*ιK ((bU i).1 r)=ιK (∑ i:Fin d,(M*ᵥPi.single j 1) i*(bU i).1 r):=(by simp only[Ba,AF]);rw[zG,zH];simpa only[AQ,AX,Am] using hr.symm
   have zA:c=∑ j:Fin d,c j•(Pi.single j 1:Fin d->Qa p):=(by funext i;simp only[AQ,AX,Am,AG,Ca,AK,AS,Bq,Ai,↓reduceIte])
   conv_rhs=>rw[zA,AJ,Ba]
   change (t.1.1.val.map ιK)*ᵥ∑ j:Fin d,c j•(fun k=>ιK ((bU j).1 k))=_;rw[AJ];refine Ag rfl fun j _=>?_;rw[Al,Al,Bd,zz j]
  let W0:Submodule (Qa p) (Fin S.n->Qa p):=W.map φ_emb;let Wfull:Submodule (Qa p) (Fin S.n->Qa p):=
   ⨆ g:S.L,W0.map (Matrix.toLin' (g.1.val.map ιK))
  have zr:Wfull≠⊥:=by
   intro h0;have h1:W0<=⊥:=by
    have zw:W0.map (Matrix.toLin' ((1:S.L).1.val.map ιK))<=Wfull:=
     le_iSup (fun k:S.L=>W0.map (Matrix.toLin' (k.1.val.map ιK))) (1:S.L)
    have zE:((1:S.L).1.val.map ιK)=1:=(by ext a b;simp[BG]);rw[zE,Matrix.toLin'_one,Submodule.map_id,h0] at zw;exact zw
   apply zB;rw[BY];intro v hv;have:φ_emb v∈(⊥:Submodule (Qa p) (Fin S.n->Qa p)):=h1 ⟨v,hv,rfl⟩;rw[Cr] at this;exact zn (this.trans (Bn φ_emb).symm)
  have zp:∀ g∈S.L,∀ v∈Wfull,(g.val.map ιK)*ᵥv∈Wfull:=by
   intro g hg;have zw:Wfull.map (Matrix.toLin' (g.val.map ιK))<=Wfull:=by
    simp only[Wfull,EI];refine iSup_le fun h=>?_;rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩;have zI:(g.val.map ιK)*ᵥ(h.1.val.map ιK*ᵥw)=((⟨g,hg⟩*h).1.val.map ιK)*ᵥw:=(by rw[Ac,<-Aq];rfl);exact le_iSup (fun k:S.L=>W0.map (Matrix.toLin' (k.1.val.map ιK))) (⟨g,hg⟩*h)
     ⟨w,hw,zI.symm⟩
   intro v hv;exact zw ⟨v,hv,rfl⟩
  have zq:Wfull=⊤:=(S.absIrred Wfull zp).resolve_left zr;have zv:Wfull.map (Matrix.toLin' (QK za))<=W0:=by
   simp only[Wfull,EI];refine iSup_le fun g=>?_;rintro _ ⟨_,⟨_,⟨c,hc,rfl⟩,rfl⟩,rfl⟩;change QK za*ᵥ(g.1.val.map ιK*ᵥφ_emb c)∈W0;rw[<-zl c,Ac,Ac];have zM:g.1.val.map ιK*QK za=QK (fun i=>za ((zb g).symm i))*g.1.val.map ιK:=(by simp only[QK,<-Aq];congr 1;exact zh g za);rw[Af,zM,<-Af,zs];by_cases zm:za=fun i=>za ((zb g).symm i)
   .
    rw[Az zm];have zx:g∈I:=(zg g).mpr fun i=>by
     have:=An zm (zb g i)
     rw[Ek] at this;exact this.symm.symm
    rw[<-Ac,zD ⟨g,zx⟩ c,zl];exact ⟨(zc ⟨g,zx⟩).val.map ιK*ᵥc,hW (zc ⟨g,zx⟩) ⟨⟨g,zx⟩,rfl⟩ c hc,rfl⟩
   . rw[Aw zm,Ce,BF];exact W0.zero_mem
  rw[Cg];intro c;have zJ:φ_emb c∈Wfull.map (Matrix.toLin' (QK za)):=
   ⟨φ_emb c,zq ▸ BW,zl c⟩
  obtain ⟨c',zN,zO⟩:=zv zJ;exact (zn zO) ▸ zN
lemma W4 (zi:7<=p) {N:ℕ} {ze:0 < N} {zh:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N ze zh ι) (A:Subgroup S.L) (m:ℕ) (eA:Fin m ≃ A) (Q:(Fin m->Bool)->Matrix (Fin S.n) (Fin S.n) (ZMod p)) (zf:∑ χ:Fin m->Bool,Q χ=1) (zg:∀ (i:Fin m) χ,(eA i).1.1.val*Q χ=Qh p (χ i)•Q χ) (za:Fin m->Bool) (I:Subgroup S.L) (zd:∀ g∈I,g.1.val*Q za=Q za*g.1.val) (d:ℕ) (bU:Module.Basis (Fin d) (ZMod p) (LinearMap.range (Matrix.toLin' (Q za)))) (zb:I→*Aa (Fin d) (ZMod p)) (zc:∀ (g:I) (x:LinearMap.range (Matrix.toLin' (Q za))), (zb g).val*ᵥ(bU.equivFun x)=bU.equivFun ⟨g.1.1.val*ᵥx.1,by
    obtain ⟨v,hv⟩:=x.2;refine ⟨g.1.1.val*ᵥv,?_⟩
    rw[<-hv,Aj,Aj,Ac,Ac,zd g.1 g.2]⟩) :
  let B_U:Matrix (Fin d) (Fin d) (ZMod p):=
   Matrix.of fun i j=>dotProduct (bU i).1 (S.B*ᵥ(bU j).1)
  B_Uᵀ=-B_U/\B_U.det≠0/\∀ g∈zb.range,g.valᵀ*B_U*g.val=B_U:=by
 let U:Submodule (ZMod p) (Fin S.n->ZMod p):=LinearMap.range (Matrix.toLin' (Q za));intro B_U;have zp:B_Uᵀ=-B_U:=by
  ext i j;simp only[AM,Bh,B_U,Ak]
  calc dotProduct (bU j).1 (S.B*ᵥ(bU i).1)
    = dotProduct (S.B*ᵥ(bU i).1) (bU j).1:=dotProduct_comm _ _
   _ = dotProduct (Matrix.vecMul (bU i).1 S.Bᵀ) (bU j).1:=by rw[AI]
   _ = dotProduct (bU i).1 (S.Bᵀ*ᵥ(bU j).1):=(AB _ _ _).symm
   _ = -dotProduct (bU i).1 (S.B*ᵥ(bU j).1):=by rw[S.B_alt,BJ,dotProduct_neg]
 have zl:∀ zj zk:Fin d->ZMod p,dotProduct zj (B_U*ᵥzk)=dotProduct (bU.equivFun.symm zj).1 (S.B*ᵥ(bU.equivFun.symm zk).1):=by
  intro zj zk;have zo:∀ c:Fin d->ZMod p,(bU.equivFun.symm c).1=∑ i:Fin d,c i•(bU i).1:=by
   intro c;have h:=Ah Subtype.val (bU.sum_repr (bU.equivFun.symm c));have zv:∀ i,bU.repr (bU.equivFun.symm c) i=c i:=fun i=>
    An (bU.equivFun.apply_symm_apply c) i
   simpa[B4,Bp,zv] using h.symm
  rw[zo zj,zo zk,AJ,sum_dotProduct];have hL:dotProduct zj (B_U*ᵥzk)=∑ i:Fin d,∑ j:Fin d,zj i*(B_U i j*zk j):=(by simp only[dotProduct,Matrix.mulVec,A6]);rw[hL];refine Ag rfl fun i _=>?_;rw[smul_dotProduct,dotProduct_sum,BC];refine Ag rfl fun j _=>?_;rw[Al,dotProduct_smul,Am,Am];simp only[B_U,Ak];ring
 have zq:∀ g∈zb.range,g.valᵀ*B_U*g.val=B_U:=by
  rintro g ⟨t,rfl⟩;ext i j;have h1:dotProduct (Pi.single i 1) (((zb t).valᵀ*B_U*(zb t).val)*ᵥ(Pi.single j 1))=dotProduct ((zb t).val*ᵥ(Pi.single i 1)) (B_U*ᵥ((zb t).val*ᵥ(Pi.single j 1))):=by
   calc dotProduct (Pi.single i 1) (((zb t).valᵀ*B_U*(zb t).val)*ᵥ(Pi.single j 1))
     = dotProduct (Pi.single i 1) ((zb t).valᵀ*ᵥ(B_U*ᵥ((zb t).val*ᵥ(Pi.single j 1)))):=by simp only[Ac,Af]
    _ = dotProduct (Matrix.vecMul (Pi.single i 1) (zb t).valᵀ) (B_U*ᵥ((zb t).val*ᵥ(Pi.single j 1))):=
      AB _ _ _
    _ = dotProduct ((zb t).val*ᵥ(Pi.single i 1)) (B_U*ᵥ((zb t).val*ᵥ(Pi.single j 1))):=by rw[AI]
  have h2:dotProduct (Pi.single i 1) (((zb t).valᵀ*B_U*(zb t).val)*ᵥ(Pi.single j 1))=((zb t).valᵀ*B_U*(zb t).val) i j:=(by simp[dotProduct,Matrix.mulVec,AG]);rw[<-h2,h1,zl];have zs:∀ k:Fin d,(bU.equivFun.symm ((zb t).val*ᵥ(Pi.single k 1))).1=t.1.1.val*ᵥ(bU k).1:=(by intro k;have hk:=zc t (bU k);have zE:bU.equivFun (bU k)=Pi.single k 1:=(by funext r;simp[AG,eq_comm]);rw[zE] at hk;rw[hk,bU.equivFun.symm_apply_apply]);rw[zs i,zs j]
  calc dotProduct (t.1.1.val*ᵥ(bU i).1) (S.B*ᵥ(t.1.1.val*ᵥ(bU j).1))
    = dotProduct (Matrix.vecMul (bU i).1 t.1.1.valᵀ) (S.B*ᵥ(t.1.1.val*ᵥ(bU j).1)):=by rw[AI]
   _ = dotProduct (bU i).1 (t.1.1.valᵀ*ᵥ(S.B*ᵥ(t.1.1.val*ᵥ(bU j).1))):=
     (AB _ _ _).symm
   _ = dotProduct (bU i).1 ((t.1.1.valᵀ*S.B*t.1.1.val)*ᵥ(bU j).1):=by simp only[Ac,Af]
   _ = B_U i j:=by rw[S.B_inv t.1.1 t.1.2];rfl
 have zr:B_U.det≠0:=by
  intro zz;obtain ⟨c,zy,zI⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr zz;let u:U:=bU.equivFun.symm c;have zw:u.1≠0:=by
   intro h0;have zt:u=0:=Ae h0
   have:=Ah bU.equivFun zt
   rw[bU.equivFun.apply_symm_apply,Bn] at this;exact zy this
  have zm:∀ χ:Fin m->Bool,χ≠za->(Q χ)ᵀ*S.B*Q za=0:=by
   intro χ zJ;have zF:∃ i,χ i≠za i:=by by_contra hall;push Not at hall;exact zJ (funext hall)
   obtain ⟨i,hi⟩:=zF;have zx:Qh p (χ i)*Qh p (za i)=-1:=(by cases h1:χ i <;> cases h2:za i <;> simp[h1,h2,Qh] at hi ⊢);have zG:(Q χ)ᵀ*S.B*Q za=-((Q χ)ᵀ*S.B*Q za):=by
    calc (Q χ)ᵀ*S.B*Q za
      = (Q χ)ᵀ*((eA i).1.1.valᵀ*S.B*(eA i).1.1.val)*Q za:=by rw[S.B_inv (eA i).1.1 (eA i).1.2]
     _ = ((eA i).1.1.val*Q χ)ᵀ*S.B*((eA i).1.1.val*Q za):=by rw[AT];simp only[Af]
     _ = (Qh p (χ i)•Q χ)ᵀ*S.B*(Qh p (za i)•Q za):=by rw[zg,zg]
     _ = (Qh p (χ i)*Qh p (za i))•((Q χ)ᵀ*S.B*Q za):=by rw[Ch,Ar,Ar,Ao,AR,Bb]
     _ = -((Q χ)ᵀ*S.B*Q za):=by rw[zx,neg_one_smul]
   have zB:(2:ZMod p)≠0:=by
    intro h2;have zC:p∣2:=(At 2 p).mp (by simpa using h2)
    have:=AP (by decide) zC;omega
   have zH:(2:ZMod p)•((Q χ)ᵀ*S.B*Q za)=0:=(by ext a b;have h0:=Ah (fun M:Matrix (Fin S.n) (Fin S.n) (ZMod p)=>M a b) zG;simp only[Bh] at h0;simp only[A2,Am,ES];linear_combination h0);exact (smul_eq_zero.mp zH).resolve_left zB
  have zn:∀ w:Fin S.n->ZMod p,dotProduct w (S.B*ᵥu.1)=0:=by
   intro w;have zu:w=∑ χ:Fin m->Bool,Q χ*ᵥw:=by
    calc w=(1:Matrix (Fin S.n) (Fin S.n) (ZMod p))*ᵥw:=(AN w).symm
     _ = (∑ χ:Fin m->Bool,Q χ)*ᵥw:=by rw[zf]
     _ = ∑ χ:Fin m->Bool,Q χ*ᵥw:=by funext r;simp only[Matrix.mulVec,dotProduct,AQ,BR,Bo];exact AY
   conv_lhs=>rw[zu]
   rw[sum_dotProduct];refine A1 fun χ _=>?_;by_cases zA:χ=za
   . rw[zA];let wU:U:=⟨Q za*ᵥw,⟨w,rfl⟩⟩;have h1:=zl (bU.equivFun wU) c;rw[bU.equivFun.symm_apply_apply,zI,dotProduct_zero] at h1;exact h1.symm
   .
    obtain ⟨u0,zt⟩:=u.2;rw[<-zt,Aj]
    calc dotProduct (Q χ*ᵥw) (S.B*ᵥ(Q za*ᵥu0))
      = dotProduct (Matrix.vecMul w (Q χ)ᵀ) (S.B*ᵥ(Q za*ᵥu0)):=by rw[AI]
     _ = dotProduct w ((Q χ)ᵀ*ᵥ(S.B*ᵥ(Q za*ᵥu0))):=(AB _ _ _).symm
     _ = dotProduct w (((Q χ)ᵀ*S.B*Q za)*ᵥu0):=by simp only[Ac,Af]
     _ = 0:=by rw[zm χ zA,BF,dotProduct_zero]
  have zD:S.B*ᵥu.1=0:=by
   funext i
   have:=zn (Pi.single i 1)
   simpa[dotProduct,AG] using this
  exact S.B_det (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u.1,zw,zD⟩)
 exact ⟨zp,zr,zq⟩
lemma QE (zc:7<=p) {N:ℕ} {zd:0 < N} {zf:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zd zf ι) (za:Subgroup S.L) [za.Normal] (ze:∀ a b:za,a*b=b*a) (zb:∃ a∈za,a.1≠1/\a.1≠Qd S.n p) : ∃ S':Qg p N zd zf ι,S'.n < S.n:=by
 let zL:S.L:=⟨Qd S.n p,S.negOne_mem⟩;have zr:zL∈Subgroup.center S.L:=(by rw[Bk];intro g;apply Ae;apply A7;change g.1.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))=(-1)*g.1.val;simp);let A:Subgroup S.L:=za ⊔ Subgroup.zpowers zL;have vc:A.Normal:=by
  have:(Subgroup.zpowers zL).Normal:=⟨fun x hx g=>by
   obtain ⟨k,rfl⟩:=hx;have zz:g*zL=zL*g:=Subgroup.mem_center_iff.mp zr g;have vi:g*zL ^ k=zL ^ k*g:=Commute.zpow_right zz k;rw[vi,DN]
   exact ⟨k,rfl⟩⟩
  exact Subgroup.sup_normal za (Subgroup.zpowers zL)
 haveI:A.Normal:=vc;have zU:∀ a b:A,a*b=b*a:=by
  have zw:∀ x:S.L,∀ k:ℤ,x*zL ^ k=zL ^ k*x:=fun x k=>
   Commute.zpow_right (Subgroup.mem_center_iff.mp zr x) k
  have zH:∀ x∈A,∃ a∈za,∃ k:ℤ,x=a*zL ^ k:=by
   intro x hx;rw[show A=Subgroup.closure ((za:Set S.L)∪(Subgroup.zpowers zL:Set S.L)) from Subgroup.sup_eq_closure za (Subgroup.zpowers zL)] at hx;refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
   .
    rintro y (hyA | ⟨k,rfl⟩)
    . exact ⟨y,hyA,0,by simp⟩
    . exact ⟨1,za.one_mem,k,by simp⟩
   . exact ⟨1,za.one_mem,0,by simp⟩
   . rintro _ _ _ _ ⟨a₁,zB,k₁,rfl⟩ ⟨zj,zV,k₂,rfl⟩;refine ⟨a₁*zj,za.mul_mem zB zV,k₁+k₂,?_⟩;rw[Do,Ad,<-Ad (zL ^ k₁),<-zw zj k₁];group
   . rintro _ _ ⟨a₁,zB,k₁,rfl⟩;refine ⟨a₁⁻¹,za.inv_mem zB,-k₁,?_⟩;rw[Dm,<-zpow_neg,<-zw a₁⁻¹ (-k₁)]
  intro a b;obtain ⟨a₁,zB,k₁,h1⟩:=zH a.1 a.2;obtain ⟨zj,zV,k₂,h2⟩:=zH b.1 b.2;apply Ae;change a.1*b.1=b.1*a.1;rw[h1,h2];have vH:a₁*zj=zj*a₁:=Ah Subtype.val (ze ⟨a₁,zB⟩ ⟨zj,zV⟩)
  calc a₁*zL ^ k₁*(zj*zL ^ k₂)=a₁*(zL ^ k₁*zj)*zL ^ k₂:=by group
   _ = a₁*(zj*zL ^ k₁)*zL ^ k₂:=by rw[<-zw zj k₁]
   _ = (a₁*zj)*(zL ^ k₁*zL ^ k₂):=by group
   _ = (zj*a₁)*(zL ^ k₂*zL ^ k₁):=by rw[vH,<-Do,<-Do,DQ]
   _ = zj*(a₁*zL ^ k₂)*zL ^ k₁:=by group
   _ = zj*(zL ^ k₂*a₁)*zL ^ k₁:=by rw[zw a₁ k₂]
   _ = zj*zL ^ k₂*(a₁*zL ^ k₁):=by group
 have vj:∀ a∈A,a*a=1:=QP zc S A zU;have zI:zL∈A:=(le_sup_right:Subgroup.zpowers zL<=A) (Co zL);obtain ⟨zp,z1,z2,z3⟩:=zb;have zJ:zp∈A:=(le_sup_left:za<=A) z1;haveI:Fintype A:=Fintype.ofFinite A;let m:=Fintype.card A;let eA:Fin m ≃ A:=(Fintype.equivFin A).symm;have zK:∀ i:Fin m,(eA i).1.1.val*(eA i).1.1.val=1:=fun i=>
  Ah (fun g:S.L=>g.1.val) (vj (eA i).1 (eA i).2)
 have zn:∀ i j:Fin m,(eA i).1.1.val*(eA j).1.1.val=(eA j).1.1.val*(eA i).1.1.val:=
  fun i j=>Ah (fun g:A=>g.1.1.val) (zU (eA i) (eA j))
 let Q:(Fin m->Bool)->Matrix (Fin S.n) (Fin S.n) (ZMod p):=
  fun χ=>Qf (fun i=>Qo (eA i).1.1.val (χ i))
 have zM:∑ χ:Fin m->Bool,Q χ=1:=by
  dsimp only[Q];rw[WM];have h1:(fun i:Fin m=>∑ b:Bool,Qo (eA i).1.1.val b)=fun _=>1:=
   funext fun i=>YT zc (eA i).1.1.val
  rw[h1];clear h1;induction m with
  | zero=>rfl
  | succ m ih=>simp[Qf,ih]
 have zD:∀ χ ψ,Q χ*Q ψ=if χ=ψ then Q χ else 0:=by
  intro χ ψ;dsimp only[Q];rw[QG _ _ (fun i j=>WV (zn i j) (χ i) (ψ j))];by_cases h:χ=ψ
  . subst h;rw[Az rfl];congr 1;funext i;rw[WF zc _ (zK i),Az rfl]
  .
   rw[Aw h];have vk:∃ i,χ i≠ψ i:=by by_contra hall;push Not at hall;exact h (funext hall)
   obtain ⟨zt,vD⟩:=vk;exact QS _ zt (by rw[WF zc _ (zK zt),Aw vD])
 have zs:∀ (i:Fin m) χ,(eA i).1.1.val*Q χ=Qh p (χ i)•Q χ:=by
  intro i χ;apply QV (eA i).1.1.val _
   (fun a b=>WV (zn a b) (χ a) (χ b))
   (fun j=>by
    unfold Qo
    simp only[Ao,Ar,BH,BQ,As,AC,zn i j])
   i _ (WU zc _ (zK i) (χ i))
 let zg (g:S.L):Equiv.Perm (Fin m):=
  {toFun:=fun i=>eA.symm ⟨g*(eA i).1*g⁻¹,Ax ‹_› (eA i).1 (eA i).2 g⟩
   invFun:=fun i=>eA.symm ⟨g⁻¹*(eA i).1*g,by simpa using Ax ‹_› (eA i).1 (eA i).2 g⁻¹⟩
   left_inv:=fun i=>by
    apply eA.injective;apply Ae;apply Ae;simp only[AV];group
   right_inv:=fun i=>by
    apply eA.injective;apply Ae;apply Ae
    simp only[AV];group }
 have zi:∀ g i,(eA (zg g i)).1=g*(eA i).1*g⁻¹:=fun g i=>by
  simp[zg]
 have zE:∀ (g:S.L) χ,g.1.val*Q χ=Q (fun i=>χ ((zg g).symm i))*g.1.val:=by
  intro g χ;suffices h:g.1.val*Q χ*g.1.inv=Q (fun i=>χ ((zg g).symm i)) by
   calc g.1.val*Q χ=(g.1.val*Q χ*g.1.inv)*g.1.val:=by
           rw[Af,g.1.inv_val,As]
         _ = Q (fun i=>χ ((zg g).symm i))*g.1.val:=by rw[h]
  dsimp only[Q];rw[WD _ _ g.1.val_inv g.1.inv_val];have vx:(fun i=>g.1.val*Qo (eA i).1.1.val (χ i)*g.1.inv)=(fun j=>Qo (eA j).1.1.val (χ ((zg g).symm j))) ∘ zg g:=by funext i;rw[YR _ _ _ g.1.val_inv];simp only[EC,Ek];congr 1;have h1:=Ah (fun u:S.L=>u.1.val) (zi g i);exact h1.symm
  rw[vx];exact Yb _ (fun a b=>WV (zn a b) _ _) (zg g)
 have vd:∃ χ₀:Fin m->Bool,Q χ₀≠0:=by
  by_contra hall;push Not at hall;have vO:(0:Matrix (Fin S.n) (Fin S.n) (ZMod p))=1:=(by rw[<-zM];exact (A1 fun χ _=>hall χ).symm)
  have:=Ah (fun M:Matrix (Fin S.n) (Fin S.n) (ZMod p)=>M ⟨0,S.hn_pos⟩ ⟨0,S.hn_pos⟩) vO
  simp at this
 obtain ⟨χ₀,zC⟩:=vd;let U:Submodule (ZMod p) (Fin S.n->ZMod p):=LinearMap.range (Matrix.toLin' (Q χ₀));let d:=Module.finrank (ZMod p) U;have vl:0 < d:=by
  by_contra h0;have vP:d=0:=by omega
  have vy:U=⊥:=Submodule.finrank_eq_zero.mp vP;apply zC;apply Matrix.toLin'.injective;apply Ap;intro v;have hv:Q χ₀*ᵥv∈(⊥:Submodule (ZMod p) (Fin S.n->ZMod p)):=vy ▸ ⟨v,rfl⟩;simpa using hv
 have vz:d < S.n:=by
  have zW:U≠⊤:=by
   intro vN;have ve:Q χ₀=1:=by apply Matrix.toLin'.injective;apply Ap;intro v;have hv:v∈U:=vN ▸ BW;obtain ⟨u,rfl⟩:=hv;simp only[Aj,Ac,zD χ₀ χ₀,↓reduceIte,AC]
   let zt:Fin m:=eA.symm ⟨zp,zJ⟩;have zF:=zs zt χ₀;rw[ve,As] at zF;have zX:zp.1.val=Qh p (χ₀ zt)•(1:Matrix (Fin S.n) (Fin S.n) (ZMod p)):=(by simpa[zt] using zF);cases vt:χ₀ zt
   . apply z3;apply A7;rw[zX,vt];simp[Qh,Qd]
   . apply z2;apply A7;rw[zX,vt];simp[Qh]
  have vX:d<=S.n:=by
   have:=Submodule.finrank_le U
   rwa[CQ,AW] at this
  by_contra hge;have vm:d=S.n:=by omega
  apply zW;apply EV;rw[CQ,AW];exact vm
 let I:Subgroup S.L:=
  {carrier:={g | ∀ i:Fin m,χ₀ (zg g i)=χ₀ i}
   one_mem':=fun i=>by
    have:zg 1 i=i:=by apply eA.injective;apply Ae;simp[zg]
    rw[this]
   mul_mem':=fun {g₁ g₂} h₁ h₂ i=>by
    have zA:zg (g₁*g₂) i=zg g₁ (zg g₂ i):=(by apply eA.injective;apply Ae;rw[zi,zi,zi];group);rw[zA,h₁,h₂]
   inv_mem':=fun {g} hg i=>by
    have z4:zg g⁻¹ i=(zg g).symm i:=(by apply (zg g).injective;rw[AV];apply eA.injective;apply Ae;rw[zi,zi];group);rw[z4]
    have:=hg ((zg g).symm i)
    rw[AV] at this
    exact this.symm }
 have zT:∀ g∈I,∀ i:Fin m,χ₀ ((zg g).symm i)=χ₀ i:=fun g hg i=>by
  have:=hg ((zg g).symm i)
  rw[AV] at this;exact this.symm
 have zo:∀ g∈I,g.1.val*Q χ₀=Q χ₀*g.1.val:=fun g hg=>by
  have h:=zE g χ₀;have z5:(fun i=>χ₀ ((zg g).symm i))=χ₀:=funext (zT g hg);rwa[z5] at h
 have zN:∀ g∈I,∀ v∈U,g.1.val*ᵥv∈U:=(by rintro g hg _ ⟨v,rfl⟩;refine ⟨g.1.val*ᵥv,?_⟩;simp only[Aj,Ac,zo g hg]);let bU:Module.Basis (Fin d) (ZMod p) U:=Module.finBasis (ZMod p) U;let zO:I→*(U≃ₗ[ZMod p] U):=
  {toFun:=fun g=>
    {toFun:=fun x=>⟨g.1.1.val*ᵥx.1,zN g.1 g.2 x.1 x.2⟩
     invFun:=fun x=>⟨g.1.1.inv*ᵥx.1,by
      have z4:=zN g.1⁻¹ (I.inv_mem g.2) x.1 x.2
      exact z4⟩
     left_inv:=fun x=>Ae (by dsimp only;rw[Ac,g.1.1.inv_val,AN])
     right_inv:=fun x=>Ae (by dsimp only;rw[Ac,g.1.1.val_inv,AN])
     map_add':=fun x y=>Ae (A3 _ x.1 y.1)
     map_smul':=fun c x=>Ae (Al _ c x.1) }
   map_one':=by apply Em;intro x;apply Ae;simp
   map_mul':=fun g₁ g₂=>by
    apply Em;intro x;apply Ae;change (g₁.1.1.val*g₂.1.1.val)*ᵥx.1=g₁.1.1.val*ᵥ(g₂.1.1.val*ᵥx.1)
    exact (Ac _ _ _).symm }
 let vI:(U≃ₗ[ZMod p] U)→*Aa (Fin d) (ZMod p):=
  {toFun:=fun e=>
    {val:=LinearMap.toMatrix bU bU e.toLinearMap
     inv:=LinearMap.toMatrix bU bU e.symm.toLinearMap
     val_inv:=by
      rw[<-Ct bU bU bU];have zA:e.toLinearMap.comp e.symm.toLinearMap=(LinearMap.id:U→ₗ[ZMod p] U):=
       Ap fun x=>e.apply_symm_apply x
      rw[zA,DB]
     inv_val:=by
      rw[<-Ct bU bU bU];have zA:e.symm.toLinearMap.comp e.toLinearMap=(LinearMap.id:U→ₗ[ZMod p] U):=
       Ap fun x=>e.symm_apply_apply x
      rw[zA,DB] }
   map_one':=by apply A7;ext i j;simp[Dg,BG,DS,eq_comm]
   map_mul':=fun e₁ e₂=>by
    apply A7
    exact Ct bU bU bU e₁.toLinearMap e₂.toLinearMap }
 let zh:I→*Aa (Fin d) (ZMod p):=vI.comp zO;let L_U:Subgroup (Aa (Fin d) (ZMod p)):=zh.range;have zk:∀ (g:I) (x:U),(zh g).val*ᵥ(bU.equivFun x)=bU.equivFun (zO g x):=
  fun g x=>EZ bU bU (zO g).toLinearMap x
 have zm:A<=I:=fun a ha i=>by
  have z5:zg a i=i:=(by apply eA.injective;apply Ae;rw[zi];have zz:a*(eA i).1=(eA i).1*a:=Ah Subtype.val (zU ⟨a,ha⟩ (eA i));rw[zz,DN]);rw[z5]
 have z6:Group.IsSolvable L_U:=(by haveI:Group.IsSolvable S.L:=S.solvable;haveI:Group.IsSolvable I:=inferInstance;have vE:I ⧸ zh.ker≃*L_U:=QuotientGroup.quotientKerEquivRange zh;exact Group.isSolvable_of_isSolvable_injective (f:=vE.symm.toMonoidHom) vE.symm.injective);have zP:Nat.card L_U∣N:=by
  have h1:Nat.card L_U=Nat.card (I ⧸ zh.ker):=
   Bc (QuotientGroup.quotientKerEquivRange zh).symm.toEquiv
  have h2:Nat.card (I ⧸ zh.ker)∣Nat.card I:=ET zh.ker;have h3:Nat.card I∣Nat.card S.L:=Cf I;rw[h1];exact (h2.trans h3).trans S.card_dvd
 have zQ:∀ (a:A),zh ⟨a.1,zm a.2⟩=if χ₀ (eA.symm a) then 1 else Qd d p:=by
  intro a;have vn:∀ x:U,zO ⟨a.1,zm a.2⟩ x=Qh p (χ₀ (eA.symm a))•x:=by
   intro x;apply Ae;obtain ⟨u,hu⟩:=x.2;change a.1.1.val*ᵥx.1=Qh p (χ₀ (eA.symm a))•x.1;rw[<-hu,Aj,Ac];have vA:a.1.1.val=(eA (eA.symm a)).1.1.val:=by simp
   rw[vA,zs (eA.symm a) χ₀,Bv]
  apply A7;apply Matrix.toLin'.injective;apply Ap;intro v;have hv:=zk ⟨a.1,zm a.2⟩ (bU.equivFun.symm v);rw[bU.equivFun.apply_symm_apply,vn,Bd,bU.equivFun.apply_symm_apply] at hv;simp only[Aj,hv];cases χ₀ (eA.symm a)
  . simp[Qh,Qd,BJ,AN]
  . simp[Qh]
 have zY:χ₀ (eA.symm ⟨zL,zI⟩)=false:=by
  by_contra hne;have vB:χ₀ (eA.symm ⟨zL,zI⟩)=true:=B6 hne;have h1:=zs (eA.symm ⟨zL,zI⟩) χ₀;simp only[AV,vB,Qh,↓reduceIte,Bx] at h1;have vJ:zL.1.val*Q χ₀=-Q χ₀:=by simp[zL,Qd]
  rw[vJ] at h1;have vQ:(2:ZMod p)•Q χ₀=0:=by ext i j;have h0:=Ah (fun M:Matrix (Fin S.n) (Fin S.n) (ZMod p)=>M i j) h1;simp only[Bh] at h0;simp only[A2,Am,ES];linear_combination -h0
  have vK:(2:ZMod p)≠0:=by
   intro h2;have zu:p∣2:=(At 2 p).mp (by simpa using h2)
   have:=AP (by decide) zu;omega
  exact zC ((smul_eq_zero.mp vQ).resolve_left vK)
 have z7:Qd d p∈L_U:=(by refine ⟨⟨zL,zm zI⟩,?_⟩;rw[zQ ⟨zL,zI⟩,zY];rfl);have zG:QQ (⟨Qd d p,z7⟩:L_U):=by
  have:Fintype S.L:=Fintype.ofFinite S.L;have vR:zL*zL=1:=(by apply Ae;apply A7;change (-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))*(-1)=1;simp);have vC:zL≠1:=by
   intro h1;have h0:=Ah (fun g:S.L=>g.1.val ⟨0,S.hn_pos⟩ ⟨0,S.hn_pos⟩) h1;simp only[zL,Qd,EP,Bh,BT,CH,Cn] at h0;have zR:(2:ZMod p)=0:=by linear_combination -h0
   have zu:p∣2:=(At 2 p).mp (by simpa using zR)
   have:=AP (by decide) zu;omega
  have zZ:∀ a b:A,Qh p (χ₀ (eA.symm (a*b)))=Qh p (χ₀ (eA.symm a))*Qh p (χ₀ (eA.symm b)):=by
   intro a b;have h1:=zs (eA.symm (a*b)) χ₀;have vL:(eA (eA.symm (a*b))).1.1.val=(eA (eA.symm a)).1.1.val*(eA (eA.symm b)).1.1.val:=by simp
   rw[vL,Af,zs (eA.symm b) χ₀,Ao,zs (eA.symm a) χ₀,AR,Bb] at h1;have vM:(Qh p (χ₀ (eA.symm (a*b))) - Qh p (χ₀ (eA.symm a))*Qh p (χ₀ (eA.symm b)))•Q χ₀=0:=(by rw[DJ,h1,Cx]);exact sub_eq_zero.mp ((smul_eq_zero.mp vM).resolve_right zC)
  let zv:A→*ℤˣ:=
   {toFun:=fun a=>if χ₀ (eA.symm a) then 1 else -1
    map_one':=by
     have h1:=zZ 1 1;rw[AK] at h1;have zx:(1:ZMod p)≠-1:=by
      intro h;have zR:(2:ZMod p)=0:=by linear_combination h
      have zu:p∣2:=(At 2 p).mp (by simpa using zR)
      have:=AP (by decide) zu;omega
     cases hb:χ₀ (eA.symm 1)
     . simp[hb,Qh] at h1;exact absurd h1.symm zx
     . simp
    map_mul':=fun a b=>by
     have h1:=zZ a b;have zx:(1:ZMod p)≠-1:=by
      intro h;have zR:(2:ZMod p)=0:=by linear_combination h
      have zu:p∣2:=(At 2 p).mp (by simpa using zR)
      have:=AP (by decide) zu;omega
     cases vu:χ₀ (eA.symm (a*b)) <;> cases vv:χ₀ (eA.symm a) <;> cases vU:χ₀ (eA.symm b) <;>
      simp[vu,vv,vU,Qh] at h1 ⊢
     all_goals first | exact absurd h1 zx | exact absurd h1.symm zx }
  have vo:zv ⟨zL,zI⟩=-1:=by simp[zv,zY]
  have vp:∀ g:S.L,g∈I↔∀ a:A,zv ⟨g*a.1*g⁻¹,Ax ‹_› a.1 a.2 g⟩=zv a:=by
   intro g;constructor
   . intro hg a;dsimp only[zv,MonoidHom.coe_mk,OneHom.coe_mk];have z8:eA.symm ⟨g*a.1*g⁻¹,Ax ‹_› a.1 a.2 g⟩=zg g (eA.symm a):=(by simp[zg]);rw[z8,hg (eA.symm a)]
   . intro h i;have h1:=h (eA i);dsimp only[zv,MonoidHom.coe_mk,OneHom.coe_mk] at h1;have z8:eA.symm ⟨g*(eA i).1*g⁻¹,Ax ‹_› (eA i).1 (eA i).2 g⟩=zg g i:=rfl;rw[z8,Ek] at h1;cases vV:χ₀ (zg g i) <;> cases vW:χ₀ i <;> simp[vV,vW] at h1 ⊢
  let π:I→*L_U:=zh.rangeRestrict;have z9:Function.Surjective π:=zh.rangeRestrict_surjective;exact W6 (L:=S.L) (L_U:=L_U) zr vR vC S.realMinus A vj zI zv vo I vp
   π z9 ⟨Qd d p,z7⟩ zm
   (fun a ha=>by
    apply Ae;change zh ⟨a.1,zm a.2⟩=1;rw[zQ a];have ht:χ₀ (eA.symm a)=true:=(by cases hc:χ₀ (eA.symm a) <;> simp[zv,hc] at ha ⊢)
    rw[ht];rfl)
   (fun a ha=>by
    apply Ae;change zh ⟨a.1,zm a.2⟩=Qd d p;rw[zQ a];have hf:χ₀ (eA.symm a)=false:=(by cases hc:χ₀ (eA.symm a) <;> simp[zv,hc] at ha ⊢)
    rw[hf];rfl)
 have z0:∀ g∈L_U,∃ q:ℚ,Qr zd zf ι (Fin d->Qa p)
    (Matrix.toLin' (g.val.map (algebraMap (ZMod p) (Qa p))))=(q:ℂ):=
  fun g hg=>W3 zc S A vj m eA Q (fun _=>rfl) zM zD zs
   zg zi zE χ₀ zC I zT zo d bU zh zk g hg
 have zS:∀ W:Submodule (Qa p) (Fin d->Qa p),(∀ g∈L_U,∀ v∈W,(g.val.map (algebraMap (ZMod p) (Qa p)))*ᵥv∈W)->W=⊥\/W=⊤:=
  fun W hW=>WQ S m Q zD zg zE χ₀ I (fun _=>Iff.rfl)
   zo d bU zh zk W hW
 have vq:∀ (v:Fin d->ZMod p),v≠0->∀ (a:(ZMod p)ˣ),∃ g∈L_U,g.val*ᵥv=(a:ZMod p)•v:=by
  intro v hv a;let u:U:=bU.equivFun.symm v;have va:u.1≠0:=by intro h0;have vS:u=0:=Ae h0;have vF:=Ah bU.equivFun vS;rw[bU.equivFun.apply_symm_apply,Bn] at vF;exact hv vF
  obtain ⟨g,zq,vw⟩:=S.SF u.1 va a;have vb:(⟨g,zq⟩:S.L)∈I:=by
   intro i;have vr:∀ j:Fin m,(eA j).1.1.val*ᵥu.1=Qh p (χ₀ j)•u.1:=by intro j;obtain ⟨w,hw⟩:=u.2;rw[<-hw,Aj,Ac,zs j χ₀,Bv]
   have h1:(eA (zg ⟨g,zq⟩ i)).1.1.val*ᵥ(g.val*ᵥu.1)=Qh p (χ₀ (zg ⟨g,zq⟩ i))•((a:ZMod p)•u.1):=(by rw[vw,Al,vr (zg ⟨g,zq⟩ i),smul_comm]);have h2:(eA (zg ⟨g,zq⟩ i)).1.1.val*ᵥ(g.val*ᵥu.1)=Qh p (χ₀ i)•((a:ZMod p)•u.1):=by
    have zl:(eA (zg ⟨g,zq⟩ i)).1.1.val*g.val=g.val*(eA i).1.1.val:=by
     have h:=Ah (fun x:S.L=>x.1.val) (zi ⟨g,zq⟩ i)
     calc (eA (zg ⟨g,zq⟩ i)).1.1.val*g.val
       = (g.val*(eA i).1.1.val*g.inv)*g.val:=by rw[h];rfl
      _ = g.val*(eA i).1.1.val:=by rw[Af,g.inv_val,As]
    rw[Ac,zl,<-Ac,vr i,Al,vw]
   have vm:(Qh p (χ₀ (zg ⟨g,zq⟩ i)) - Qh p (χ₀ i))•((a:ZMod p)•u.1)=0:=(by rw[DJ,<-h1,<-h2,Cx]);have vs:(a:ZMod p)•u.1≠0:=(by intro h0;exact va ((smul_eq_zero.mp h0).resolve_left a.ne_zero));have zy:Qh p (χ₀ (zg ⟨g,zq⟩ i))=Qh p (χ₀ i):=
    sub_eq_zero.mp ((smul_eq_zero.mp vm).resolve_right vs)
   have zx:(1:ZMod p)≠-1:=by
    intro h;have zR:(2:ZMod p)=0:=by linear_combination h
    have zu:p∣2:=(At 2 p).mp (by simpa using zR)
    have:=AP (by decide) zu;omega
   cases vu:χ₀ (zg ⟨g,zq⟩ i) <;> cases vv:χ₀ i <;>
    simp[vu,vv,Qh] at zy ⊢
   all_goals first | exact absurd zy zx | exact absurd zy.symm zx
  refine ⟨zh ⟨⟨g,zq⟩,vb⟩,⟨⟨⟨g,zq⟩,vb⟩,rfl⟩,?_⟩;have vG:=zk ⟨⟨g,zq⟩,vb⟩ u;have zF:zO ⟨⟨g,zq⟩,vb⟩ u=(a:ZMod p)•u:=Ae vw;rw[zF,Bd,bU.equivFun.apply_symm_apply] at vG;exact vG
 let vT:Matrix (Fin d) (Fin d) (ZMod p):=
  Matrix.of fun i j=>dotProduct (bU i).1 (S.B*ᵥ(bU j).1)
 obtain ⟨vf,vg,vh⟩:=
  W4 zc S A m eA Q zM zs χ₀ I zo d bU zh zk
 exact ⟨{
  n:=d
  hn_pos:=vl
  L:=L_U
  solvable:=z6
  card_dvd:=zP
  negOne_mem:=z7
  realMinus:=zG
  ratTr:=z0
  absIrred:=zS
  SF:=vq
  B:=vT
  B_alt:=vf
  B_det:=vg
  B_inv:=vh
 },vz⟩
lemma Yd (zd:7<=p) {N:ℕ} {za:0 < N} {zb:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (zc:Qg p N za zb ι) : ∃ S:Qg p N za zb ι, ∀ (A:Subgroup S.L),A.Normal->(∀ a b:A,a*b=b*a)-> ∀ a∈A,a.1=1\/a.1=Qd S.n p:=by
 suffices h:∀ k:ℕ,∀ S:Qg p N za zb ι,S.n=k->∃ S':Qg p N za zb ι,∀ (A:Subgroup S'.L),A.Normal->(∀ a b:A,a*b=b*a)->∀ a∈A,a.1=1\/a.1=Qd S'.n p from
  h zc.n zc rfl
 intro k;induction k using Nat.strongRecOn with
 | ind k ih=>
  intro S zl;by_cases ze:∀ (A:Subgroup S.L),A.Normal->(∀ a b:A,a*b=b*a)->∀ a∈A,a.1=1\/a.1=Qd S.n p
  . exact ⟨S,ze⟩
  . push Not at ze;obtain ⟨A,zf,zh,a,zi,zj,zk⟩:=ze;haveI:A.Normal:=zf;obtain ⟨S',zg⟩:=QE zd S A zh ⟨a,zi,zj,zk⟩;exact ih S'.n (zl ▸ zg) S' rfl
end Section4TwoTerminal
section Section5Extraspecial
def O2 (G:Type*) [Group G] [Finite G]:Subgroup G:=
 sSup {N:Subgroup G | N.Normal/\IsPGroup 2 N}
lemma YW {G:Type*} [Group G] [Finite G] {N:Subgroup G} (hN:N.Normal) (h2:IsPGroup 2 N):N<=O2 G:=
 le_sSup ⟨hN,h2⟩
lemma Q9 (G:Type*) [Group G] [Finite G] : (O2 G).Normal/\IsPGroup 2 (O2 G):=by
 classical
 haveI:Fact (Nat.Prime 2):=⟨DI⟩;have zd:Finite (Subgroup G):=
  Finite.of_injective (fun H:Subgroup G=>(H:Set G)) SetLike.coe_injective
 have za:{N:Subgroup G | N.Normal/\IsPGroup 2 N}.Finite:=Set.toFinite _;let S:Finset (Subgroup G):=za.toFinset;have zb:O2 G=S.sup (fun N:Subgroup G=>N):=by
  apply DP
  . exact sSup_le fun N hN=>Finset.le_sup (f:=fun N:Subgroup G=>N) (za.mem_toFinset.mpr hN)
  . exact Finset.sup_le fun N hN=>le_sSup (za.mem_toFinset.mp hN)
 rw[zb];have h:∀ T:Finset (Subgroup G),(∀ N∈T,N.Normal/\IsPGroup 2 N)->
   let H:Subgroup G:=T.sup (fun N:Subgroup G=>N);H.Normal/\IsPGroup 2 H:=by
  intro T;induction T using Finset.induction_on with
  | empty=>
   intro _;change (Finset.sup ∅ (fun N:Subgroup G=>N)).Normal/\IsPGroup 2 (Finset.sup ∅ (fun N:Subgroup G=>N):Subgroup G);rw[Finset.sup_empty];exact ⟨inferInstance,IsPGroup.of_bot⟩
  | @insert N T hNT ih=>
   intro zc;have hN:=zc N (Finset.mem_insert_self N T);have hT:=ih fun K hK=>zc K (Finset.mem_insert_of_mem hK);set H':Subgroup G:=T.sup (fun N:Subgroup G=>N);have ze:(insert N T).sup (fun K:Subgroup G=>K)=N ⊔ H':=Finset.sup_insert;change ((insert N T).sup (fun K:Subgroup G=>K)).Normal/\IsPGroup 2 ((insert N T).sup (fun K:Subgroup G=>K):Subgroup G);rw[ze];haveI:N.Normal:=hN.1;haveI:H'.Normal:=hT.1;exact ⟨Subgroup.sup_normal N H',IsPGroup.to_sup_of_normal_left hN.2 hT.2⟩
 exact h S fun N hN=>za.mem_toFinset.mp hN
lemma QI (G:Type*) [Group G] [Finite G]:(O2 G).Normal:=
 (Q9 G).1
lemma Wv (G:Type*) [Group G] [Finite G]:IsPGroup 2 (O2 G):=
 (Q9 G).2
lemma Wa {G:Type*} [Group G] [Finite G] [Group.IsSolvable G] (C:Subgroup G) [C.Normal] (hC:C≠⊥) : ∃ (M:Subgroup G),M.Normal/\M<=C/\M≠⊥/\ (∀ x∈M,∀ y∈M,x*y=y*x)/\∃ q:ℕ,q.Prime/\IsPGroup q M:=by
 classical
 let P:ℕ->Prop:=fun k=>∃ N:Subgroup G,N.Normal/\N<=C/\N≠⊥/\Nat.card N=k;have zo:∃ k,P k:=⟨Nat.card C,C,inferInstance,le_rfl,hC,rfl⟩;obtain ⟨M,zb,zx,ze,zm⟩:=EF zo;haveI:M.Normal:=zb;have zf:∀ N:Subgroup G,N.Normal->N<=M->N=⊥\/N=M:=by
  intro N zn zy;by_cases zl:N=⊥
  . left;exact zl
  . right;have zz:Nat.card M<=Nat.card N:=(by rw[zm];exact Nat.find_min' zo ⟨N,zn,zy.trans zx,zl,rfl⟩);exact E4 zy zz
 have zj:∀ x∈M,∀ y∈M,x*y=y*x:=by
  have zd:(⁅M,M⁆:Subgroup G).Normal:=DY M M;have zg:⁅M,M⁆<=M:=E5 M M;rcases zf ⁅M,M⁆ zd zg with zi | htop
  .
   intro x hx y hy;have zp:x*y*x⁻¹*y⁻¹∈⁅M,M⁆:=Dj hx hy;rw[zi,CG] at zp
   calc x*y=(x*y*x⁻¹*y⁻¹)*(y*x):=by group
    _ = y*x:=by rw[zp,AA]
  .
   exfalso;have zq:commutator M=⊤:=(by apply Subgroup.map_injective M.subtype_injective;rw[<-Dt,Dq];change (⁅(⊤:Subgroup M),(⊤:Subgroup M)⁆).map M.subtype=M;rw[Subgroup.map_commutator,<-Dt,Dq,htop]);have zA:∀ k:ℕ,derivedSeries M k=⊤:=by
    intro k;induction k with
    | zero=>exact derivedSeries_zero M
    | succ k ih=>rw[derivedSeries_succ,ih];exact zq
   obtain ⟨k,hk⟩:=(inferInstance:Group.IsSolvable M).solvable;rw[zA k] at hk;have:Nontrivial M:=(CW M).mpr ze;exact Fa hk
 have zr:1 < Nat.card M:=(DA M).mpr ze;obtain ⟨q,za,zv⟩:=B5 zr.ne';haveI:Fact q.Prime:=⟨za⟩;have zc:∀ v∈M,v ^ q=1:=by
  let Mq:Subgroup G:=
   {carrier:={v | v∈M/\v ^ q=1}
    mul_mem':=fun {a b} ⟨ha,hap⟩ ⟨hb,hbp⟩=>
     ⟨M.mul_mem ha hb,by rw[Commute.mul_pow (zj a ha b hb),hap,hbp,AA]⟩
    one_mem':=⟨M.one_mem,B8 q⟩
    inv_mem':=fun {a} ⟨ha,hap⟩=>⟨M.inv_mem ha,by rw[E7,hap,inv_one]⟩ }
  have zh:Mq.Normal:=⟨fun x ⟨hxM,hxq⟩ g=>
   ⟨zb.conj_mem x hxM g,by rw[conj_pow,hxq,AK,By]⟩⟩
  have zs:Mq≠⊥:=(by obtain ⟨⟨v,hvM⟩,hv_ord⟩:=DD (G:=M) q zv;intro zi;have zt:v ^ q=1:=Ah Subtype.val (hv_ord ▸ BE (⟨v,hvM⟩:M));have zk:v∈Mq:=⟨hvM,zt⟩;rw[zi,CG] at zk;have:(⟨v,hvM⟩:M)=1:=Ae zk;rw[this,orderOf_one] at hv_ord;exact za.ne_one hv_ord.symm);have zu:Mq=M:=(zf Mq zh (fun _ h=>h.1)).resolve_left zs;intro v hv;exact (zu ▸ hv:v∈Mq).2
 have zw:IsPGroup q M:=(by intro ⟨v,hv⟩;refine ⟨1,?_⟩;apply Ae;simpa using zc v hv);exact ⟨M,zb,zx,ze,zj,q,za,zw⟩
lemma Ys {p:ℕ} [Fact p.Prime] (zd:7<=p) {N:ℕ} {za:0 < N} {zc:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N za zc ι) (zb:∀ (A:Subgroup S.L),A.Normal->(∀ a b:A,a*b=b*a)-> ∀ a∈A,a.1=1\/a.1=Qd S.n p) : Subgroup.centralizer (O2 S.L:Set S.L)<=O2 S.L:=by
 classical
 haveI:Fact (Nat.Prime 2):=⟨DI⟩;haveI:Group.IsSolvable S.L:=S.solvable;let R:Subgroup S.L:=O2 S.L;haveI hR_norm:R.Normal:=QI S.L;have z4:IsPGroup 2 R:=Wv S.L;let C:Subgroup S.L:=Subgroup.centralizer (R:Set S.L)
 have zs:C.Normal:=⟨fun c hc g=>by
  rw[Cv] at hc ⊢;intro r hr;have z8:g⁻¹*r*g∈R:=(by simpa using hR_norm.conj_mem r hr g⁻¹);have zm:=hc (g⁻¹*r*g) z8
  calc r*(g*c*g⁻¹)=g*((g⁻¹*r*g)*c)*g⁻¹:=by group
   _ = g*(c*(g⁻¹*r*g))*g⁻¹:=by rw[zm]
   _ = (g*c*g⁻¹)*r:=by group⟩
 by_contra hnot;let π:S.L→*S.L ⧸ R:=QuotientGroup.mk' R;let zi:Subgroup (S.L ⧸ R):=C.map π
 have zx:zi.Normal:=⟨fun y ⟨c,zA,hy⟩ q=>by
  obtain ⟨g,rfl⟩:=Bi R q
  exact ⟨g*c*g⁻¹,zs.conj_mem c zA g,by rw[<-hy,<-C5,<-AF,<-AF]⟩⟩
 have zC:zi≠⊥:=(by have z9:∃ c∈C,c∉R:=(by by_contra hall;push Not at hall;exact hnot hall);obtain ⟨c,zA,vl⟩:=z9;intro z7;have zM:π c∈(⊥:Subgroup (S.L ⧸ R)):=z7 ▸ ⟨c,zA,rfl⟩;rw[CG,<-Bw,En] at zM;exact vl zM);haveI:zi.Normal:=zx;obtain ⟨Mbar,zo,zE,zr,zF,q,zl,zw⟩:=
  Wa zi zC
 haveI:Mbar.Normal:=zo;haveI:Fact q.Prime:=⟨zl⟩;let M:Subgroup S.L:=Mbar.comap π ⊓ C;have zt:M.Normal:=by haveI:(Mbar.comap π).Normal:=Subgroup.Normal.comap zo π;haveI:C.Normal:=zs;exact Subgroup.normal_inf_normal (Mbar.comap π) C
 have zy:M.map π=Mbar:=by
  apply DP
  . rintro _ ⟨x,⟨hxM,_⟩,rfl⟩;exact hxM
  . intro y hy;obtain ⟨c,zA,rfl⟩:=zE hy;exact ⟨c,⟨hy,zA⟩,rfl⟩
 let ze:M→*S.L ⧸ R:=π.comp M.subtype;let K:Subgroup M:=ze.ker;have zf:ze.range=Mbar:=(by rw[<-zy];ext y;simp[ze,Subgroup.mem_map]);have va:M ⧸ K≃*Mbar:=
  (QuotientGroup.quotientKerEquivRange ze).trans (MulEquiv.subgroupCongr zf)
 have zu:∀ x:K,x.1.1∈R:=fun x=>by
  have hx:=x.2;rw[Bw] at hx;exact (En R ▸ hx:x.1.1∈R)
 have zN:IsPGroup 2 K:=by
  let f:K→*R:=
   {toFun:=fun x=>⟨x.1.1,zu x⟩
    map_one':=rfl
    map_mul':=fun _ _=>rfl }
  have zO:Function.Injective f:=fun a b h=>
   Ae (Ae (Ah (fun r:R=>r.1) h))
  exact z4.of_injective f zO
 have zz:K<=Subgroup.center M:=(by intro k hk;rw[Bk];intro x;apply Ae;have vb:k.1∈R:=zu ⟨k,hk⟩;have vc:x.1∈C:=x.2.2;exact (Subgroup.mem_centralizer_iff.mp vc k.1 vb).symm);have zn:K.index=Nat.card Mbar:=(by change Nat.card (M ⧸ K)=Nat.card Mbar;exact Bc va.toEquiv);by_cases zY:q=2
 . subst zY;have z5:IsPGroup 2 M:=(by obtain ⟨a,ha⟩:=(Dx (p:=2) (G:=K)).mp zN;obtain ⟨b,hb⟩:=(Dx (p:=2) (G:=Mbar)).mp zw;rw[Dx];refine ⟨a+b,?_⟩;rw[<-K.card_mul_index,ha,zn,hb,CT]);have vd:M<=R:=YW zt z5;apply zr;rw[<-zy,Subgroup.eq_bot_iff_forall];rintro _ ⟨x,hxM,rfl⟩;rw[<-Bw,En];exact vd hxM
 ·
  obtain ⟨a,ha⟩:=(Dx (p:=2) (G:=K)).mp zN;obtain ⟨b,hb⟩:=(Dx (p:=q) (G:=Mbar)).mp zw;have zP:Nat.Coprime (Nat.card K) K.index:=by rw[ha,zn,hb];exact (Nat.prime_two.coprime_iff_not_dvd.mpr fun hdvd=>zY (zl.eq_one_or_self_of_dvd 2 hdvd |>.resolve_left (by decide)).symm).pow a b
  obtain ⟨Q,zB⟩:=Subgroup.exists_right_complement'_of_coprime zP;have zp:Nat.card Q=Nat.card Mbar:=by change Nat.card (Q:Set M)=Nat.card Mbar;rw[zB.card_right,zn]
  set e:=Nat.card Mbar;have zv:∀ x:M,x∈Q↔x ^ e=1:=by
   intro x;constructor
   . intro zk;have h1:(⟨x,zk⟩:Q) ^ e=1:=(by rw[<-zp];exact QC _);exact Ah Subtype.val h1
   .
    intro zS;let k:K:=(zB.equiv x).1;let u:Q:=(zB.equiv x).2;have z1:k.1*u.1=x:=zB.equiv_fst_mul_equiv_snd x;have zm:k.1*u.1=u.1*k.1:=(Subgroup.mem_center_iff.mp (zz k.2) u.1).symm;have ve:u.1 ^ e=1:=Ah Subtype.val (zp ▸ QC u);have zG:k.1 ^ e=1:=by
     have:=zS
     rw[<-z1,Commute.mul_pow zm,ve,AK] at this;exact this
    have zQ:k ^ e=1:=Ae zG;have zj:orderOf k∣e:=Bl zQ;have zJ:orderOf k∣Nat.card K:=Dd k;have zK:orderOf k=1:=Nat.eq_one_of_dvd_coprimes (zn ▸ zP) zJ zj;have vf:k=1:=orderOf_eq_one_iff.mp zK;have vg:x=u.1:=by rw[<-z1,vf,CH,AA]
    exact vg ▸ u.2
  let Q':Subgroup S.L:=Q.map M.subtype
  have zD:Q'.Normal:=⟨fun y hy g=>by
   obtain ⟨x,zk,rfl⟩:=hy;have zR:g*x.1*g⁻¹∈M:=zt.conj_mem x.1 x.2 g;refine ⟨⟨g*x.1*g⁻¹,zR⟩,?_,rfl⟩;change ⟨g*x.1*g⁻¹,zR⟩∈Q;rw[zv];apply Ae;have zS:x.1 ^ e=1:=Ah Subtype.val ((zv x).mp zk);change (g*x.1*g⁻¹) ^ e=1
   rw[conj_pow,zS,AK,By]⟩
  have zT:∀ x y:Q',x*y=y*x:=by
   have zU:Function.Injective (ze.comp Q.subtype):=by
    intro zg zh h;change ze zg.1=ze zh.1 at h;have zV:zg.1⁻¹*zh.1∈K:=(by rw[Bw,AF,C5,h,CK]);have zH:zg.1⁻¹*zh.1∈Q:=Q.mul_mem (Q.inv_mem zg.2) zh.2;have z6:(⟨zg.1⁻¹*zh.1,zV⟩:K).1*(1:Q).1=(1:K).1*(⟨zg.1⁻¹*zh.1,zH⟩:Q).1:=(by simp);have zZ:(⟨zg.1⁻¹*zh.1,zV⟩,(1:Q))=((1:K),⟨zg.1⁻¹*zh.1,zH⟩):=
     zB.equiv.symm.injective z6
    have h1:zg.1⁻¹*zh.1=1:=Ah (fun p:K×Q=>p.1.1) zZ;exact Ae (eq_of_inv_mul_eq_one h1)
   intro x y;obtain ⟨u,z2,vm⟩:=x.2;obtain ⟨v,z3,vn⟩:=y.2;apply Ae;change x.1*y.1=y.1*x.1;rw[<-vm,<-vn];have zW:(⟨u,z2⟩:Q)*⟨v,z3⟩=⟨v,z3⟩*⟨u,z2⟩:=by apply zU;simp only[Et,Subgroup.coe_subtype,AF];have vh:ze u∈Mbar:=zf ▸ ⟨u,rfl⟩;have vi:ze v∈Mbar:=zf ▸ ⟨v,rfl⟩;exact zF (ze u) vh (ze v) vi
   exact Ah (fun z:Q=>z.1.1) zW
  have zq:Nat.card Q'=e:=by
   have h1:Nat.card Q'=Nat.card Q:=
    Bc (Equiv.ofBijective (fun u:Q=>(⟨u.1.1,⟨u.1,u.2,rfl⟩⟩:Q'))
     ⟨fun a b h=>Ae (Ae (Ah (fun z:Q'=>z.1) h)),fun ⟨y,x,zk,hxy⟩=>⟨⟨x,zk⟩,Ae hxy⟩⟩).symm
   rw[h1,zp]
  have zL:1 < Nat.card Q':=(by rw[zq];exact (DA Mbar).mpr zr);haveI:Nontrivial Q':=Finite.one_lt_card_iff_nontrivial.mp zL;obtain ⟨⟨x,hxQ'⟩,hx_ne1⟩:=exists_ne (1:Q');have zX:x.1=Qd S.n p:=
   (zb Q' zD zT x hxQ').resolve_left fun h1=>
    hx_ne1 (Ae (Ae h1))
  have vj:(⟨x,hxQ'⟩:Q') ^ 2=1:=(by apply Ae;apply Ae;apply A7;change x.1.val ^ 2=1;rw[zX];simp[Qd]);have z0:orderOf (⟨x,hxQ'⟩:Q')=2:=orderOf_eq_prime vj hx_ne1;have zI:2∣Nat.card Q':=z0 ▸ Dd (⟨x,hxQ'⟩:Q');rw[zq,show e=q ^ b from hb] at zI;have vk:2∣q:=Nat.prime_two.dvd_of_dvd_pow zI;exact zY ((zl.eq_one_or_self_of_dvd 2 vk).resolve_left (by decide)).symm
lemma YI {p:ℕ} [Fact p.Prime] (zc:7<=p) {N:ℕ} {zb:0 < N} {zd:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zb zd ι) (za:∀ (A:Subgroup S.L),A.Normal->(∀ a b:A,a*b=b*a)-> ∀ a∈A,a.1=1\/a.1=Qd S.n p) : ∃ x y:O2 S.L,x*y≠y*x:=by
 by_contra hab;push Not at hab;have zf:∀ r∈O2 S.L,r∈Subgroup.center S.L:=by
  intro r hr;rw[Bk];intro g;rcases za (O2 S.L) (QI S.L) hab r hr with h1 | hz
  . apply Ae;apply A7;change g.1.val*r.1.val=r.1.val*g.1.val;rw[h1];simp
  . apply Ae;apply A7;change g.1.val*r.1.val=r.1.val*g.1.val;rw[hz];simp[Qd]
 have zh:Subgroup.centralizer (O2 S.L:Set S.L)=⊤:=(by rw[Subgroup.eq_top_iff'];intro g;rw[Cv];intro r hr;exact (Subgroup.mem_center_iff.mp (zf r hr) g).symm);have zg:O2 S.L=⊤:=top_unique (zh ▸ Ys zc S za);have zk:(2:ZMod p)≠0:=by
  intro h2;have ze:p∣2:=(At 2 p).mp (by simpa using h2)
  have:=AP (by decide) ze;omega
 let v:Fin S.n->ZMod p:=Pi.single ⟨0,S.hn_pos⟩ 1;have hv:v≠0:=by
  intro h0
  have:=An h0 ⟨0,S.hn_pos⟩
  simp[v] at this
 obtain ⟨g,zi,zj⟩:=S.SF v hv (Units.mk0 (2:ZMod p) zk);have zl:(⟨g,zi⟩:S.L)∈O2 S.L:=zg ▸ D9 _;rcases za (O2 S.L) (QI S.L) hab ⟨g,zi⟩ zl with h1 | hz
 .
  change g=1 at h1;have h0:=An zj ⟨0,S.hn_pos⟩;simp only[h1,Cn,AN,DG,AX,Am,v,Pi.single_eq_same,AK] at h0;have zm:(1:ZMod p)=0:=by linear_combination -h0
  exact DL zm
 .
  change g=Qd S.n p at hz;have h0:=An zj ⟨0,S.hn_pos⟩;simp only[hz,Qd,EP,BJ,AN,Pi.neg_apply,DG,AX,Am,v,Pi.single_eq_same,AK] at h0;have zn:(3:ZMod p)=0:=by linear_combination -h0
  have ze:p∣3:=(At 3 p).mp (by simpa using zn)
  have:=AP (by decide) ze;omega
structure Qn (R:Type*) [Group R] [Finite R] (z:R):Prop where
 z_ne_one:z≠1
 z_sq:z*z=1
 center_iff:∀ x:R,x∈Subgroup.center R↔x=1\/x=z
 comm_mem:∀ x y:R,x*y*x⁻¹*y⁻¹=1\/x*y*x⁻¹*y⁻¹=z
 sq_mem:∀ x:R,x*x=1\/x*x=z
 nonabelian:∃ x y:R,x*y≠y*x
lemma W8 {E Z:Type*} [Group E] [Finite E] [Group Z] [Finite Z] (zb:∀ x y:E,x*y=y*x) (zd:∀ x:E,x*x=1) (z:Z) (za:z≠1) (zc:z*z=1) (hZ:∀ u:Z,u=1\/u=z) : Nat.card (E→*Z)=Nat.card E:=by
 classical
 haveI:Fact (Nat.Prime 2):=⟨DI⟩;letI:AddCommGroup (Additive E):=
  {toAddGroup:=inferInstance
   add_comm:=fun a b=>by
    apply Additive.toMul.injective
    exact zb (Additive.toMul a) (Additive.toMul b) }
 letI:Module (ZMod 2) (Additive E):=
  AddCommGroup.zmodModule (n:=2) fun a=>by
   apply Additive.toMul.injective;change Additive.toMul (2•a)=1;rw[two_smul];exact zd (Additive.toMul a)
 let k:=Module.finrank (ZMod 2) (Additive E);let bE:Module.Basis (Fin k) (ZMod 2) (Additive E):=Module.finBasis (ZMod 2) (Additive E);have zl:Nat.card E=Nat.card (Fin k->ZMod 2):=(by have h1:Nat.card E=Nat.card (Additive E):=Bc Additive.ofMul;rw[h1];exact Bc bE.equivFun.toEquiv);rw[zl];have zj:(1:ZMod 2)≠0:=DL;have zu:(1:ZMod 2)+1=0:=by rw[<-EL,AK];exact ZMod.natCast_self 2
 have zf:∀ c:ZMod 2,c=0\/c=1:=fun c=>by
  fin_cases c
  . exact Or.inl rfl
  . exact Or.inr rfl
 let toZ (c:ZMod 2):Z:=if c=0 then 1 else z;have zg:∀ a b:ZMod 2,toZ (a+b)=toZ a*toZ b:=by
  intro a b;rcases zf a with rfl | rfl <;> rcases zf b with rfl | rfl <;>
   simp[toZ,zc,zj,zu]
 have zq:Function.Injective toZ:=by
  intro a b h;rcases zf a with rfl | rfl <;> rcases zf b with rfl | rfl
  . rfl
  . simp[toZ,zj] at h;exact absurd h.symm za
  . simp[toZ,zj] at h;exact absurd h za
  . rfl
 let ze (u:Z):ZMod 2:=if u=1 then 0 else 1;have zh:∀ u:Z,toZ (ze u)=u:=by
  intro u;rcases hZ u with rfl | rfl
  . simp[toZ,ze]
  . simp[toZ,ze,za,zj]
 have zi:∀ c:ZMod 2,ze (toZ c)=c:=by
  intro c;rcases zf c with rfl | rfl <;> simp[toZ,ze,za,zj]
 let fwd:(E→*Z)->(Fin k->ZMod 2):=fun φ i=>ze (φ (Additive.toMul (bE i)));let zk:(Fin k->ZMod 2)->(E→*Z):=fun w=>
  {toFun:=fun x=>toZ (∑ i:Fin k,w i*bE.equivFun (Additive.ofMul x) i)
   map_one':=by have h0:Additive.ofMul (1:E)=(0:Additive E):=rfl;rw[h0,Bn];simp[toZ]
   map_mul':=fun x y=>by
    have zr:Additive.ofMul (x*y)=Additive.ofMul x+Additive.ofMul y:=rfl;rw[zr,EN];have zs:(∑ i:Fin k,w i*(bE.equivFun (Additive.ofMul x)+bE.equivFun (Additive.ofMul y)) i)=(∑ i:Fin k,w i*bE.equivFun (Additive.ofMul x) i)+(∑ i:Fin k,w i*bE.equivFun (Additive.ofMul y) i):=(by rw[<-Bt];refine Ag rfl fun i _=>?_;simp only[Pi.add_apply,EM])
    rw[zs,zg] }
 have zo:Function.LeftInverse zk fwd:=by
  intro φ;ext x;have zp:Additive.ofMul x=∑ i:Fin k,(bE.equivFun (Additive.ofMul x) i)•bE i:=
   (bE.sum_repr (Additive.ofMul x)).symm
  have zm:∀ (s:Finset (Fin k)) (c:Fin k->ZMod 2),φ (Additive.toMul (∑ i∈s,c i•bE i))=toZ (∑ i∈s,ze (φ (Additive.toMul (bE i)))*c i):=by
   intro s c;induction s using Finset.induction_on with
   | empty=>simp[toZ]
   | @insert j s hj ih=>
    rw[C7 hj,C7 hj,zg];have zt:Additive.toMul (c j•bE j+∑ i∈s,c i•bE i)=Additive.toMul (c j•bE j)*Additive.toMul (∑ i∈s,c i•bE i):=rfl;rw[zt,AF,ih];congr 1;rcases zf (c j) with h0 | h1
    . rw[h0,Dl,AS];simp[toZ]
    . rw[h1,Bx,AK,zh]
  calc zk (fwd φ) x=toZ (∑ i:Fin k,ze (φ (Additive.toMul (bE i)))*bE.equivFun (Additive.ofMul x) i):=rfl
   _ = φ (Additive.toMul (∑ i:Fin k,bE.equivFun (Additive.ofMul x) i•bE i)):=(zm _ _).symm
   _ = φ x:=by rw[<-zp];rfl
 have zn:Function.RightInverse zk fwd:=(by intro w;funext j;dsimp only[fwd,zk,MonoidHom.coe_mk,OneHom.coe_mk];have zv:bE.equivFun (bE j)=Pi.single j 1:=(by funext i;simp[AG,eq_comm]);change ze (toZ (∑ i:Fin k,w i*bE.equivFun (bE j) i))=w j;rw[zv];simp only[AG,Ca,AK,AS,A8,Ai,↓reduceIte];exact zi (w j));exact Bc ⟨fwd,zk,zo,zn⟩
lemma WE {R:Type*} [Group R] [Finite R] (ze:IsPGroup 2 R) (zR:R) (zd:zR≠1) (zc:zR*zR=1) (zb:∀ x:R,x∈Subgroup.center R↔x=1\/x=zR) (za:(Subgroup.center (R ⧸ Subgroup.center R)).comap (QuotientGroup.mk' (Subgroup.center R)) ⊓ Subgroup.centralizer (((Subgroup.center (R ⧸ Subgroup.center R)).comap (QuotientGroup.mk' (Subgroup.center R))):Set R)=Subgroup.center R) : ∀ g:R,g∈(Subgroup.center (R ⧸ Subgroup.center R)).comap (QuotientGroup.mk' (Subgroup.center R)):=by
 classical
 haveI:Fact (Nat.Prime 2):=⟨DI⟩;let Z:Subgroup R:=Subgroup.center R;let zi:R→*R ⧸ Z:=QuotientGroup.mk' Z;let Z₂:Subgroup R:=(Subgroup.center (R ⧸ Z)).comap zi;let C₂:Subgroup R:=Subgroup.centralizer (Z₂:Set R);have zq:zR∈Z:=(zb zR).mpr (Or.inr rfl);have zr:Z<=Z₂:=fun x hx=>by
  change zi x∈Subgroup.center (R ⧸ Z);have zT:zi x=1:=(Bs x).mpr hx;rw[zT];exact (Subgroup.center (R ⧸ Z)).one_mem
 have zj:∀ (g:R) (x:R),x∈Z₂->g*x*g⁻¹*x⁻¹∈Z:=(by intro g x hx;rw[<-Bs];change zi (g*x*g⁻¹*x⁻¹)=1;simp only[AF,C5];have hc:zi g*zi x=zi x*zi g:=Subgroup.mem_center_iff.mp hx (zi g);rw[hc];group);have zn:∀ x∈Z₂,x*x∈Z:=by
  intro x hx;rw[Bk];intro y;have zw:x*y*x⁻¹*y⁻¹∈Z:=by
   have h1:=zj y x hx;have h2:(y*x*y⁻¹*x⁻¹)⁻¹=x*y*x⁻¹*y⁻¹:=by group
   rw[<-h2];exact Z.inv_mem h1
  set c:=x*y*x⁻¹*y⁻¹;have zM:x*y=c*(y*x):=by simp only[c];group
  have zC:∀ u:R,u*c=c*u:=fun u=>Subgroup.mem_center_iff.mp zw u;have zJ:c*c=1:=by
   rcases (zb c).mp zw with h1 | hz
   . rw[h1,AK]
   . rw[hz,zc]
  calc y*(x*x)=(y*x)*x:=(Ad _ _ _).symm
   _ = (c*c)*((y*x)*x):=by rw[zJ,AA]
   _ = c*(c*(y*x))*x:=by group
   _ = c*(x*y)*x:=by rw[<-zM]
   _ = x*(c*(y*x)):=by rw[<-Ad,<-zC x,Ad,Ad]
   _ = x*(x*y):=by rw[<-zM]
   _ = (x*x)*y:=(Ad _ _ _).symm
 let Zsub:Subgroup Z₂:=Z.subgroupOf Z₂;haveI:Zsub.Normal:=Subgroup.Normal.comap (inferInstance:Z.Normal) Z₂.subtype;let E:=Z₂ ⧸ Zsub;have zK:∀ u v:E,u*v=v*u:=by
  intro u v;obtain ⟨x,rfl⟩:=Bi Zsub u;obtain ⟨y,rfl⟩:=Bi Zsub v;have zh:x*y*x⁻¹*y⁻¹∈Zsub:=zj x.1 y.1 y.2;have h1:QuotientGroup.mk' Zsub (x*y*x⁻¹*y⁻¹)=1:=
   (Bs _).mpr zh
  simp only[AF,C5] at h1
  calc QuotientGroup.mk' Zsub x*QuotientGroup.mk' Zsub y
    = (QuotientGroup.mk' Zsub x*QuotientGroup.mk' Zsub y*(QuotientGroup.mk' Zsub x)⁻¹*(QuotientGroup.mk' Zsub y)⁻¹)*(QuotientGroup.mk' Zsub y*QuotientGroup.mk' Zsub x):=by group
   _ = QuotientGroup.mk' Zsub y*QuotientGroup.mk' Zsub x:=by rw[h1,AA]
 have zU:∀ u:E,u*u=1:=(by intro u;obtain ⟨x,rfl⟩:=Bi Zsub u;rw[<-AF];exact (Bs _).mpr (zn x.1 x.2));let φ (g:R):Z₂→*Z:=
  {toFun:=fun x=>⟨g*x.1*g⁻¹*x.1⁻¹,zj g x.1 x.2⟩
   map_one':=Ae (by simp)
   map_mul':=fun x y=>by
    apply Ae;have zV:=zj g y.1 y.2;have zh:x.1*(g*y.1*g⁻¹*y.1⁻¹)=(g*y.1*g⁻¹*y.1⁻¹)*x.1:=
     Subgroup.mem_center_iff.mp zV x.1
    change g*(x.1*y.1)*g⁻¹*(x.1*y.1)⁻¹=(g*x.1*g⁻¹*x.1⁻¹)*(g*y.1*g⁻¹*y.1⁻¹)
    calc g*(x.1*y.1)*g⁻¹*(x.1*y.1)⁻¹
      = (g*x.1*g⁻¹*x.1⁻¹)*(x.1*(g*y.1*g⁻¹*y.1⁻¹))*x.1⁻¹:=by group
     _ = (g*x.1*g⁻¹*x.1⁻¹)*((g*y.1*g⁻¹*y.1⁻¹)*x.1)*x.1⁻¹:=by rw[zh]
     _ = (g*x.1*g⁻¹*x.1⁻¹)*(g*y.1*g⁻¹*y.1⁻¹):=by group }
 let ψ (g:R):E→*Z:=
  QuotientGroup.lift Zsub (φ g) fun x hx=>by
   apply Ae;change g*x.1*g⁻¹*x.1⁻¹=1;have zW:x.1∈Z:=hx;rw[Subgroup.mem_center_iff.mp zW g];group
 let Θ:E->(E→*Z):=
  Quotient.lift (fun h:Z₂=>ψ h.1) fun zf zg hrel=>by
   have zk:zf⁻¹*zg∈Zsub:=(QuotientGroup.leftRel_apply).mp hrel;apply MonoidHom.ext;intro u;obtain ⟨x,rfl⟩:=Bi Zsub u;apply Ae;change zf.1*x.1*zf.1⁻¹*x.1⁻¹=zg.1*x.1*zg.1⁻¹*x.1⁻¹;have zF:zf.1⁻¹*zg.1∈Z:=zk;have hc:x.1*(zf.1⁻¹*zg.1)=(zf.1⁻¹*zg.1)*x.1:=Subgroup.mem_center_iff.mp zF x.1;have zL:zf.1*x.1*zf.1⁻¹=zg.1*x.1*zg.1⁻¹:=by
    calc zf.1*x.1*zf.1⁻¹=zf.1*((zf.1⁻¹*zg.1)*x.1*(zf.1⁻¹*zg.1)⁻¹)*zf.1⁻¹:=by
            rw[<-hc];group
          _ = zg.1*x.1*zg.1⁻¹:=by group
   rw[zL]
 have zD:Function.Injective Θ:=by
  intro zP zQ z2;obtain ⟨zf,rfl⟩:=Bi Zsub zP;obtain ⟨zg,rfl⟩:=Bi Zsub zQ;have zx:∀ x∈Z₂,(zf.1⁻¹*zg.1)*x=x*(zf.1⁻¹*zg.1):=by
   intro x hx;have h1:=Ah (fun f:E→*Z=>(f (QuotientGroup.mk' Zsub ⟨x,hx⟩)).1) z2;change zf.1*x*zf.1⁻¹*x⁻¹=zg.1*x*zg.1⁻¹*x⁻¹ at h1;have h2:zf.1*x*zf.1⁻¹=zg.1*x*zg.1⁻¹:=Cj h1
   calc (zf.1⁻¹*zg.1)*x=zf.1⁻¹*(zg.1*x*zg.1⁻¹)*zg.1:=by group
    _ = zf.1⁻¹*(zf.1*x*zf.1⁻¹)*zg.1:=by rw[<-h2]
    _ = x*(zf.1⁻¹*zg.1):=by group
  have zs:zf.1⁻¹*zg.1∈C₂:=Subgroup.mem_centralizer_iff.mpr fun x hx=>(zx x hx).symm;have zt:zf.1⁻¹*zg.1∈Z₂:=Z₂.mul_mem (Z₂.inv_mem zf.2) zg.2;have zm:zf.1⁻¹*zg.1∈Z:=(by change zf.1⁻¹*zg.1∈Subgroup.center R;rw[<-za];exact ⟨zt,zs⟩);have zN:QuotientGroup.mk' Zsub (zf⁻¹*zg)=1:=
   (Bs _).mpr zm
  rw[AF,C5] at zN;exact eq_of_inv_mul_eq_one zN
 have zy:Nat.card (E→*Z)=Nat.card E:=
  W8 zK zU ⟨zR,zq⟩
   (fun h=>zd (Ah Subtype.val h))
   (Ae zc)
   (fun u=>(zb u.1).mp u.2 |>.imp Ae Ae)
 have zz:Function.Surjective Θ:=(by haveI:Fintype E:=Fintype.ofFinite E;haveI:Finite (E→*Z):=Finite.of_injective (fun f:E→*Z=>(f:E->Z)) DFunLike.coe_injective;haveI:Fintype (E→*Z):=Fintype.ofFinite (E→*Z);have zX:Fintype.card E=Fintype.card (E→*Z):=(by rw[<-Au,<-Au,zy]);exact (Ci Θ).mpr ⟨zD,zX⟩ |>.2);have zp:∀ g:R,∃ h∈Z₂,∃ c∈C₂,g=h*c:=by
  intro g;obtain ⟨u,hu⟩:=zz (ψ g);obtain ⟨h,rfl⟩:=Bi Zsub u;refine ⟨h.1,h.2,h.1⁻¹*g,?_,by group⟩;rw[Cv];intro x hx;have h1:=Ah (fun f:E→*Z=>(f (QuotientGroup.mk' Zsub ⟨x,hx⟩)).1) hu;change h.1*x*h.1⁻¹*x⁻¹=g*x*g⁻¹*x⁻¹ at h1;have h2:h.1*x*h.1⁻¹=g*x*g⁻¹:=Cj h1
  calc x*(h.1⁻¹*g)=h.1⁻¹*(h.1*x*h.1⁻¹)*g:=by group
   _ = h.1⁻¹*(g*x*g⁻¹)*g:=by rw[h2]
   _ = (h.1⁻¹*g)*x:=by group
 have zu:C₂<=Z:=by
  by_contra hnot;let Cbar:Subgroup (R ⧸ Z):=C₂.map zi;have zA:Cbar≠⊥:=by
   have zY:∃ c∈C₂,c∉Z:=by by_contra hall;push Not at hall;exact hnot hall
   obtain ⟨c,zl,zH⟩:=zY;intro zS;have zG:zi c∈(⊥:Subgroup (R ⧸ Z)):=zS ▸ ⟨c,zl,rfl⟩;rw[CG] at zG;exact zH ((Bs c).mp zG)
  haveI:Nontrivial Cbar:=(CW Cbar).mpr zA;have zE:IsPGroup 2 Cbar:=(ze.to_quotient Z).to_subgroup Cbar;haveI:Nontrivial (Subgroup.center Cbar):=zE.center_nontrivial;obtain ⟨⟨u,hu_center⟩,hu_ne1⟩:=exists_ne (1:Subgroup.center Cbar);obtain ⟨c,zl,zO⟩:=u.2;have zB:c∉Z:=by intro zH;have zZ:u=1:=Ae (by rw[<-zO];exact (Bs c).mpr zH);exact hu_ne1 (Ae zZ)
  have zv:c∈Z₂:=by
   change zi c∈Subgroup.center (R ⧸ Z);rw[Bk];intro q;obtain ⟨g,rfl⟩:=Bi Z q;obtain ⟨h,zo,d,zI,rfl⟩:=zp g;have z0:h*c=c*h:=Subgroup.mem_centralizer_iff.mp zl h zo;have z1:zi d*zi c=zi c*zi d:=by have h1:=Subgroup.mem_center_iff.mp hu_center ⟨zi d,⟨d,zI,rfl⟩⟩;have h2:=Ah (fun v:Cbar=>v.1) h1;simpa[zO] using h2
   rw[AF,Ad,z1,<-Ad,<-AF,z0,AF,Ad]
  exact zB (by change c∈Subgroup.center R;rw[<-za];exact ⟨zv,zl⟩)
 intro g;obtain ⟨h,zo,c,zl,rfl⟩:=zp g;exact Z₂.mul_mem zo (zr (zu zl))
lemma Yj {p:ℕ} [Fact p.Prime] (zc:7<=p) {N:ℕ} {zb:0 < N} {zd:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zb zd ι) (za:∀ (A:Subgroup S.L),A.Normal->(∀ a b:A,a*b=b*a)-> ∀ a∈A,a.1=1\/a.1=Qd S.n p) : ∃ hzR:(⟨Qd S.n p,S.negOne_mem⟩:S.L)∈O2 S.L, Qn (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,hzR⟩:=by
 classical
 haveI:Fact (Nat.Prime 2):=⟨DI⟩;let zL:S.L:=⟨Qd S.n p,S.negOne_mem⟩;have zz:zL≠1:=by
  intro h1;have h0:=Ah (fun g:S.L=>g.1.val ⟨0,S.hn_pos⟩ ⟨0,S.hn_pos⟩) h1;simp only[zL,Qd,EP,Bh,BT,CH,Cn] at h0;have zO:(2:ZMod p)=0:=by linear_combination -h0
  have zK:p∣2:=(At 2 p).mp (by simpa using zO)
  have:=AP (by decide) zK;omega
 have zq:zL*zL=1:=(by apply Ae;apply A7;change (-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))*(-1)=1;simp);have zi:zL∈Subgroup.center S.L:=(by rw[Bk];intro g;apply Ae;apply A7;change g.1.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))=(-1)*g.1.val;simp);have hzR:zL∈O2 S.L:=by
  let Z1:Subgroup S.L:=Subgroup.zpowers zL
  have zu:Z1.Normal:=⟨fun x hx g=>by
   obtain ⟨k,rfl⟩:=hx;rw[Commute.zpow_right (Subgroup.mem_center_iff.mp zi g) k,DN]
   exact ⟨k,rfl⟩⟩
  have zG:IsPGroup 2 Z1:=(by intro ⟨x,hx⟩;obtain ⟨k,rfl⟩:=hx;refine ⟨1,?_⟩;apply Ae;change (zL ^ k) ^ 2=1;rw[<-Ee,<-zpow_mul,Bb,zpow_mul,show zL ^ ((2:ℕ):ℤ)=1 by rw[Ee,E6,zq],one_zpow]);exact YW zu zG (Co zL)
 refine ⟨hzR,?_⟩;let R:=O2 S.L;haveI hR_norm:R.Normal:=QI S.L;have zM:IsPGroup 2 R:=Wv S.L;let zR:R:=⟨zL,hzR⟩;have zr:zR≠1:=fun h=>zz (Ah Subtype.val h);have zn:zR*zR=1:=Ae zq;have zj:zR∈Subgroup.center R:=by rw[Bk];intro g;exact Ae (Subgroup.mem_center_iff.mp zi g.1)
 let ze (g:S.L):R≃*R:=
  {toFun:=fun r=>⟨g*r.1*g⁻¹,hR_norm.conj_mem r.1 r.2 g⟩
   invFun:=fun r=>⟨g⁻¹*r.1*g,by simpa using hR_norm.conj_mem r.1 r.2 g⁻¹⟩
   left_inv:=fun r=>Ae (by group)
   right_inv:=fun r=>Ae (by group)
   map_mul':=fun a b=>Ae (by
    change g*(a.1*b.1)*g⁻¹=(g*a.1*g⁻¹)*(g*b.1*g⁻¹);group) }
 let Z:Subgroup R:=Subgroup.center R
 have zv:(Z.map R.subtype).Normal:=⟨fun x hx g=>by
  obtain ⟨r,zD,rfl⟩:=hx;refine ⟨ze g r,?_,rfl⟩;change r∈Subgroup.center R at zD;change ze g r∈Subgroup.center R;rw[Bk] at zD ⊢;intro y;have h1:=zD ((ze g).symm y);have h2:=Ah (ze g) h1
  simpa[AF] using h2⟩
 have zA:∀ a b:Z.map R.subtype,a*b=b*a:=(by intro a b;obtain ⟨u,zV,zE⟩:=a.2;obtain ⟨v,zT,zF⟩:=b.2;apply Ae;change a.1*b.1=b.1*a.1;rw[<-zE,<-zF];exact Ah Subtype.val (Subgroup.mem_center_iff.mp zT u));have zg:∀ x:R,x∈Z↔x=1\/x=zR:=by
  intro x;constructor
  .
   intro zU;rcases za (Z.map R.subtype) zv zA x.1 ⟨x,zU,rfl⟩ with h1 | hz
   . left;exact Ae (Ae h1)
   . right;exact Ae (Ae hz)
  .
   rintro (rfl | rfl)
   . exact Z.one_mem
   . exact zj
 let zf:R→*R ⧸ Z:=QuotientGroup.mk' Z;let Z₂:Subgroup R:=(Subgroup.center (R ⧸ Z)).comap zf;let C₂:Subgroup R:=Subgroup.centralizer (Z₂:Set R);have zo:Z<=Z₂:=fun x hx=>by
  change zf x∈Subgroup.center (R ⧸ Z);have zB:zf x=1:=(Bs x).mpr hx;rw[zB];exact (Subgroup.center (R ⧸ Z)).one_mem
 have zk:∀ (g:S.L) (x:R),x∈Z₂->ze g x∈Z₂:=by
  intro g x hx;change zf (ze g x)∈Subgroup.center (R ⧸ Z);rw[Bk];intro q;obtain ⟨y,rfl⟩:=Bi Z q;have zh:zf ((ze g).symm y)*zf x=zf x*zf ((ze g).symm y):=
   Subgroup.mem_center_iff.mp hx (zf ((ze g).symm y))
  have zw:((ze g).symm y)*x*((ze g).symm y)⁻¹*x⁻¹∈Z:=(by rw[<-Bs];change zf (((ze g).symm y)*x*((ze g).symm y)⁻¹*x⁻¹)=1;simp only[AF,C5];rw[zh];group);have zH:y*ze g x*y⁻¹*(ze g x)⁻¹∈Z:=by
   have h1:ze g (((ze g).symm y)*x*((ze g).symm y)⁻¹*x⁻¹)=y*ze g x*y⁻¹*(ze g x)⁻¹:=(by simp only[AF,C5,MulEquiv.apply_symm_apply]);rw[<-h1];rcases (zg _).mp zw with h0 | hz
   . rw[h0,BI];exact Z.one_mem
   . rw[hz];have zP:ze g zR=zR:=(by apply Ae;change g*zL*g⁻¹=zL;rw[Subgroup.mem_center_iff.mp zi g];group);rw[zP];exact zj
  have h1:zf (y*ze g x*y⁻¹*(ze g x)⁻¹)=1:=
   (Bs _).mpr zH
  simp only[AF,C5] at h1
  calc zf y*zf (ze g x)=(zf y*zf (ze g x)*(zf y)⁻¹*(zf (ze g x))⁻¹)*(zf (ze g x)*zf y):=by group
   _ = zf (ze g x)*zf y:=by rw[h1,AA]
 have zp:∀ (g:S.L) (c:R),c∈C₂->ze g c∈C₂:=by
  intro g c hc;rw[Cv] at hc ⊢;intro x hx;have zQ:(ze g).symm x∈Z₂:=by
   have h1:=zk g⁻¹ x hx;have zS:(ze g).symm x=ze g⁻¹ x:=
    Ae (by change g⁻¹*x.1*g=g⁻¹*x.1*(g⁻¹)⁻¹;group)
   rwa[zS]
  have zh:=Ah (ze g) (hc ((ze g).symm x) zQ);simpa[AF] using zh
 have zm:Z₂ ⊓ C₂=Z:=by
  apply DP
  .
   have zC:((Z₂ ⊓ C₂).map R.subtype).Normal:=⟨fun y hy g=>by
    obtain ⟨x,⟨zB,hx2⟩,rfl⟩:=hy
    exact ⟨ze g x,⟨zk g x zB,zp g x hx2⟩,rfl⟩⟩
   have zN:∀ a b:(Z₂ ⊓ C₂).map R.subtype,a*b=b*a:=(by intro a b;obtain ⟨u,⟨hu1,_⟩,zE⟩:=a.2;obtain ⟨v,⟨_,hv2⟩,zF⟩:=b.2;apply Ae;change a.1*b.1=b.1*a.1;rw[<-zE,<-zF];exact Ah Subtype.val (Subgroup.mem_centralizer_iff.mp hv2 u hu1));intro x hx;rcases za ((Z₂ ⊓ C₂).map R.subtype) zC zN x.1 ⟨x,hx,rfl⟩ with h1 | hz
   . exact (zg x).mpr (Or.inl (Ae (Ae h1)))
   . exact (zg x).mpr (Or.inr (Ae (Ae hz)))
  . intro x hx;exact ⟨zo hx,Subgroup.mem_centralizer_iff.mpr fun y _=>Subgroup.mem_center_iff.mp hx y⟩
 have zs:∀ g:R,g∈Z₂:=
  WE zM zR zr zn zg zm
 have zl:∀ x y:R,x*y*x⁻¹*y⁻¹∈Z:=(by intro x y;rw[<-Bs];change zf (x*y*x⁻¹*y⁻¹)=1;simp only[AF,C5];have hc:zf x*zf y=zf y*zf x:=Subgroup.mem_center_iff.mp (zs y) (zf x);rw[hc];group);have zx:∀ x:R,x*x∈Z:=by
  intro x;rw[Bk];intro y;have zt:x*y*x⁻¹*y⁻¹∈Z:=zl x y;set c:=x*y*x⁻¹*y⁻¹;have zJ:x*y=c*(y*x):=by simp only[c];group
  have zy:∀ u:R,u*c=c*u:=fun u=>Subgroup.mem_center_iff.mp zt u;have zI:c*c=1:=by
   rcases (zg c).mp zt with h1 | hz
   . rw[h1,AK]
   . rw[hz,zn]
  calc y*(x*x)=(y*x)*x:=(Ad _ _ _).symm
   _ = (c*c)*((y*x)*x):=by rw[zI,AA]
   _ = c*(c*(y*x))*x:=by group
   _ = c*(x*y)*x:=by rw[<-zJ]
   _ = x*(c*(y*x)):=by rw[<-Ad,<-zy x,Ad,Ad]
   _ = x*(x*y):=by rw[<-zJ]
   _ = (x*x)*y:=(Ad _ _ _).symm
 exact {
  z_ne_one:=zr
  z_sq:=zn
  center_iff:=zg
  comm_mem:=fun x y=>(zg _).mp (zl x y)
  sq_mem:=fun x=>(zg _).mp (zx x)
  nonabelian:=YI zc S za
 }
end Section5Extraspecial
section Section6ExtraspecialRep
def Qb {M:Type*} [Monoid M]:∀ {m:ℕ},(Fin m->M)->M
 | 0,_=>1
 | _+1,f=>f 0*Qb (fun i=>f i.succ)
lemma Yt {M N:Type*} [Monoid M] [Monoid N] (φ:M→*N) : ∀ {m:ℕ} (f:Fin m->M),φ (Qb f)=Qb (fun i=>φ (f i))
 | 0,_=>BI φ
 | _+1,f=>by simp only[Qb,AF,Yt φ (fun i=>f i.succ)]
lemma Wc {M:Type*} [Monoid M] {m:ℕ} (c:M) (f:Fin m->M) (h:∀ i,c*f i=f i*c):c*Qb f=Qb f*c:=by
 induction m with
 | zero=>simp[Qb]
 | succ m ih=>
  simp only[Qb];rw[<-Ad,h 0,Ad,ih (fun i=>f i.succ) (fun i=>h i.succ),<-Ad]
lemma QL {M:Type*} [Monoid M] {m:ℕ} (f g:Fin m->M) (h:∀ i j,i≠j->f i*g j=g j*f i) : Qb f*Qb g=Qb (fun i=>f i*g i):=by
 induction m with
 | zero=>simp[Qb]
 | succ m ih=>
  simp only[Qb];have za:Qb (fun i=>f i.succ)*g 0=g 0*Qb (fun i=>f i.succ):=
   (Wc (g 0) (fun i=>f i.succ) fun i=>(h i.succ 0 (CJ i)).symm).symm
  calc f 0*Qb (fun i=>f i.succ)*(g 0*Qb (fun i=>g i.succ))
    = f 0*(Qb (fun i=>f i.succ)*g 0)*Qb (fun i=>g i.succ):=by simp only[Ad]
   _ = f 0*(g 0*Qb (fun i=>f i.succ))*Qb (fun i=>g i.succ):=by rw[za]
   _ = (f 0*g 0)*(Qb (fun i=>f i.succ)*Qb (fun i=>g i.succ)):=by simp only[Ad]
   _ = (f 0*g 0)*Qb (fun i=>f i.succ*g i.succ):=by rw[ih (fun i=>f i.succ) (fun i=>g i.succ) fun i j hij=>h i.succ j.succ (fun h'=>hij (D0 _ h'))]
lemma QB {M:Type*} [Monoid M] {m:ℕ} (f:Fin m->M) (hf:∀ i,f i=1) : Qb f=1:=by
 induction m with
 | zero=>rfl
 | succ m ih=>simp[Qb,hf 0,ih (fun i=>f i.succ) (fun i=>hf i.succ)]
lemma QN {M:Type*} [Monoid M] {m:ℕ} (g:Fin m->M) (j:Fin m) : Qb (fun i:Fin m=>if i=j then g i else 1)=g j:=by
 induction m with
 | zero=>exact Ez j
 | succ m ih=>
  refine Fin.cases ?_ ?_ j
  . simp only[Qb,↓reduceIte];rw[QB _ (fun i=>Aw (CJ i)),AK]
  .
   intro k;simp only[Qb,Aw (CJ k).symm,AA];have za:(fun i:Fin m=>if i.succ=k.succ then g i.succ else 1)=fun i=>if i=k then g i.succ else 1:=funext fun i=>by simp[Fin.succ_inj]
   rw[za,ih (fun i=>g i.succ) k]
lemma YL {R:Type*} [CommRing R] {n m:ℕ} : Qf (fun _:Fin m=>(1:Matrix (Fin n) (Fin n) R))=1:=by
 induction m with
 | zero=>rfl
 | succ m ih=>simp[Qf,ih]
lemma Q4 {M:Type*} [Monoid M] {m:ℕ} (g z:M) (f:Fin m->M) (za:Fin m) (hz:∀ a:M,z*a=a*z) (hf:∀ i,g*f i=(if i=za then z else 1)*f i*g) : g*Qb f=z*Qb f*g:=by
 induction m with
 | zero=>exact Ez za
 | succ m ih=>
  simp only[Qb];revert hf;refine Fin.cases ?_ ?_ za
  .
   intro hf;have h0:=hf 0;rw[Az rfl] at h0;have zb:g*Qb (fun i=>f i.succ)=Qb (fun i=>f i.succ)*g:=
    Wc g (fun i=>f i.succ) fun i=>by
     have hi:=hf i.succ;rw[Aw (CJ i),AA] at hi;exact hi
   calc g*(f 0*Qb (fun i=>f i.succ))
     = (g*f 0)*Qb (fun i=>f i.succ):=(Ad _ _ _).symm
    _ = (z*f 0*g)*Qb (fun i=>f i.succ):=by rw[h0]
    _ = z*f 0*(g*Qb (fun i=>f i.succ)):=by simp only[Ad]
    _ = z*(f 0*Qb (fun i=>f i.succ))*g:=by rw[zb];simp only[Ad]
  .
   intro k hf;have h0:=hf 0;rw[Aw (CJ k).symm,AA] at h0;have zb:=ih (fun i=>f i.succ) k fun i=>by
    have hi:=hf i.succ;by_cases h:i=k
    . subst h;rw[Az rfl] at hi;rw[Az rfl];exact hi
    . rw[Aw (fun h'=>h (D0 _ h'))] at hi;rw[Aw h];exact hi
   calc g*(f 0*Qb (fun i=>f i.succ))
     = (g*f 0)*Qb (fun i=>f i.succ):=(Ad _ _ _).symm
    _ = (f 0*g)*Qb (fun i=>f i.succ):=by rw[h0]
    _ = f 0*(g*Qb (fun i=>f i.succ)):=Ad _ _ _
    _ = f 0*(z*Qb (fun i=>f i.succ)*g):=by rw[zb]
    _ = (f 0*z)*Qb (fun i=>f i.succ)*g:=by simp only[Ad]
    _ = (z*f 0)*Qb (fun i=>f i.succ)*g:=by rw[hz (f 0)]
    _ = z*(f 0*Qb (fun i=>f i.succ))*g:=by simp only[Ad]
structure Qm (R:Type*) [Group R] [Finite R] (z:R) (m:ℕ) (eps:Bool) where
 hm:1<=m
 x:Fin m->R
 y:Fin m->R
 hxy_same:∀ i,x i*y i=z*(y i*x i)
 hxx:∀ i j,i≠j->x i*x j=x j*x i
 hxy:∀ i j,i≠j->x i*y j=y j*x i
 hyy:∀ i j,i≠j->y i*y j=y j*y i
 hsq_x:∀ i:Fin m,x i*x i=if i.val=0/\!eps then z else 1
 hsq_y:∀ i:Fin m,y i*y i=if i.val=0/\!eps then z else 1
 hcard:Nat.card R=2 ^ (1+2*m)
def Qc {M:Type*} [Monoid M] {m:ℕ} (z:M) (x y:Fin m->M) (c:Bool) (a b:Fin m->Bool):M:=
 (if c then z else 1)*Qb (fun i=>(if a i then x i else 1)*(if b i then y i else 1))
def Qt:∀ {m:ℕ},(Fin m->Bool)->Bool
 | 0,_=>false
 | _+1,f=>xor (f 0) (Qt (fun i=>f i.succ))
def QF {m:ℕ} (eps:Bool) (t₁ t₂:Bool×(Fin m->Bool)×(Fin m->Bool)) : Bool×(Fin m->Bool)×(Fin m->Bool):=
 let s:Fin m->Bool:=fun i=>
  xor (t₁.2.2 i&&t₂.2.1 i)
   (xor (decide (i.val=0)&&!eps&&t₁.2.1 i&&t₂.2.1 i) (decide (i.val=0)&&!eps&&t₁.2.2 i&&t₂.2.2 i))
 (xor (xor t₁.1 t₂.1) (Qt s),fun i=>xor (t₁.2.1 i) (t₂.2.1 i),fun i=>xor (t₁.2.2 i) (t₂.2.2 i))
lemma Yx {M:Type*} [Monoid M] {m:ℕ} (z:M) (za:∀ a:M,z*a=a*z) (zb:z*z=1) (s:Fin m->Bool) (f:Fin m->M) : Qb (fun i=>(if s i then z else 1)*f i)= (if Qt s then z else 1)*Qb f:=by
 induction m with
 | zero=>simp[Qb,Qt]
 | succ m ih=>
  simp only[Qb,Qt];rw[ih (fun i=>s i.succ) (fun i=>f i.succ)];have hc:f 0*(if Qt (fun i=>s i.succ) then z else 1)=(if Qt (fun i=>s i.succ) then z else 1)*f 0:=(by cases Qt (fun i=>s i.succ) <;> simp[za])
  calc (if s 0 then z else 1)*f 0*((if Qt (fun i=>s i.succ) then z else 1)*Qb (fun i=>f i.succ))
    = (if s 0 then z else 1)*(f 0*(if Qt (fun i=>s i.succ) then z else 1))*Qb (fun i=>f i.succ):=by simp only[Ad]
   _ = (if s 0 then z else 1)*(if Qt (fun i=>s i.succ) then z else 1)*(f 0*Qb (fun i=>f i.succ)):=by rw[hc];simp only[Ad]
   _ = (if xor (s 0) (Qt (fun i=>s i.succ)) then z else 1)*(f 0*Qb (fun i=>f i.succ)):=by cases s 0 <;> cases Qt (fun i=>s i.succ) <;> simp[zb]
lemma Wi {M:Type*} [Monoid M] {m:ℕ} (zc:Bool) (z:M) (x y:Fin m->M) (zd:∀ a:M,z*a=a*z) (ze:z*z=1) (hxy_same:∀ i,x i*y i=z*(y i*x i)) (hxx:∀ i j,i≠j->x i*x j=x j*x i) (hxy:∀ i j,i≠j->x i*y j=y j*x i) (hyy:∀ i j,i≠j->y i*y j=y j*y i) (hsq_x:∀ i:Fin m,x i*x i=if i.val=0/\!zc then z else 1) (hsq_y:∀ i:Fin m,y i*y i=if i.val=0/\!zc then z else 1) (za zb:Bool×(Fin m->Bool)×(Fin m->Bool)) : Qc z x y za.1 za.2.1 za.2.2*Qc z x y zb.1 zb.2.1 zb.2.2= Qc z x y (QF zc za zb).1 (QF zc za zb).2.1 (QF zc za zb).2.2:=by
 have zf:∀ i,y i*x i=z*(x i*y i):=fun i=>by
  rw[hxy_same i,<-Ad,ze,AA]
 have zj:∀ b₁ b₂:Bool,(if b₁ then z else 1)*(if b₂ then z else 1)=if xor b₁ b₂ then z else 1:=fun b₁ b₂=>by cases b₁ <;> cases b₂ <;> simp[ze]
 have zk:∀ i j,i≠j->((if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*((if zb.2.1 j then x j else 1)*(if zb.2.2 j then y j else 1))=((if zb.2.1 j then x j else 1)*(if zb.2.2 j then y j else 1))*((if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1)):=by
  intro i j zg;cases za.2.1 i <;> cases za.2.2 i <;> cases zb.2.1 j <;> cases zb.2.2 j <;>
   simp only[AE,Bg,Be,Bj,AA,AK]
  . exact hyy i j zg
  . exact (hxy j i zg.symm).symm
  .
   calc y i*(x j*y j)=(y i*x j)*y j:=(Ad _ _ _).symm
    _ = (x j*y i)*y j:=by rw[(hxy j i zg.symm).symm]
    _ = x j*(y j*y i):=by rw[Ad,hyy i j zg]
    _ = x j*y j*y i:=(Ad _ _ _).symm
  . exact hxy i j zg
  . exact hxx i j zg
  .
   calc x i*(x j*y j)=(x j*x i)*y j:=by rw[<-Ad,hxx i j zg]
    _ = x j*(y j*x i):=by rw[Ad,hxy i j zg]
    _ = x j*y j*x i:=(Ad _ _ _).symm
  .
   calc x i*y i*y j=x i*(y j*y i):=by rw[Ad,hyy i j zg]
    _ = (y j*x i)*y i:=by rw[<-Ad,hxy i j zg]
    _ = y j*(x i*y i):=Ad _ _ _
  .
   calc x i*y i*x j=x i*(x j*y i):=by rw[Ad,(hxy j i zg.symm).symm]
    _ = (x j*x i)*y i:=by rw[<-Ad,hxx i j zg]
    _ = x j*(x i*y i):=Ad _ _ _
  .
   calc x i*y i*(x j*y j)=x i*((y i*x j)*y j):=by simp only[Ad]
    _ = x i*((x j*y i)*y j):=by rw[(hxy j i zg.symm).symm]
    _ = (x i*x j)*(y i*y j):=by simp only[Ad]
    _ = (x j*x i)*(y j*y i):=by rw[hxx i j zg,hyy i j zg]
    _ = x j*((x i*y j)*y i):=by simp only[Ad]
    _ = x j*((y j*x i)*y i):=by rw[hxy i j zg]
    _ = x j*y j*(x i*y i):=by simp only[Ad]
 have zl:∀ i:Fin m,((if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*((if zb.2.1 i then x i else 1)*(if zb.2.2 i then y i else 1))=(if xor (za.2.2 i&&zb.2.1 i) (xor (decide (i.val=0)&&!zc&&za.2.1 i&&zb.2.1 i) (decide (i.val=0)&&!zc&&za.2.2 i&&zb.2.2 i)) then z else 1)*((if xor (za.2.1 i) (zb.2.1 i) then x i else 1)*(if xor (za.2.2 i) (zb.2.2 i) then y i else 1)):=by
  intro i;have zh:=hsq_x i;have zi:=hsq_y i;by_cases h0:i.val=0/\!zc
  .
   rw[Az h0] at zh zi;have zm:(decide (i.val=0)&&!zc)=true:=by simp[h0.1,h0.2]
   cases za.2.1 i <;> cases za.2.2 i <;> cases zb.2.1 i <;> cases zb.2.2 i <;>
    simp only[zm,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.xor_true,Ex,Bool.true_xor,Dz,Db,C3,AE,Bg,Be,Bj,AA,AK,zh,zi,zf]
   .
    calc y i*(x i*y i)=(y i*x i)*y i:=(Ad _ _ _).symm
     _ = z*x i*(y i*y i):=by rw[zf i];simp only[Ad]
     _ = z*(x i*z):=by rw[zi];simp only[Ad]
     _ = (z*z)*x i:=by rw[<-zd (x i)];simp only[Ad]
     _ = x i:=by rw[ze,AA]
   .
    calc x i*(x i*y i)=(x i*x i)*y i:=(Ad _ _ _).symm
     _ = z*y i:=by rw[zh]
   .
    calc x i*y i*y i=x i*(y i*y i):=Ad _ _ _
     _ = x i*z:=by rw[zi]
     _ = z*x i:=(zd (x i)).symm
   .
    calc x i*y i*x i=x i*(y i*x i):=Ad _ _ _
     _ = x i*(z*(x i*y i)):=by rw[zf i]
     _ = (x i*z)*x i*y i:=by simp only[Ad]
     _ = z*(x i*x i)*y i:=by rw[<-zd (x i)];simp only[Ad]
     _ = (z*z)*y i:=by rw[zh]
     _ = y i:=by rw[ze,AA]
   .
    calc x i*y i*(x i*y i)=x i*(y i*x i)*y i:=by simp only[Ad]
     _ = x i*(z*(x i*y i))*y i:=by rw[zf i]
     _ = (x i*z)*x i*(y i*y i):=by simp only[Ad]
     _ = z*(x i*x i)*z:=by rw[<-zd (x i),zi];simp only[Ad]
     _ = (z*z)*z:=by rw[zh]
     _ = z:=by rw[ze,AA]
  .
   rw[Aw h0] at zh zi;have zm:(decide (i.val=0)&&!zc)=false:=by
    by_cases zn:i.val=0
    .
     have zo:zc=true:=by
      cases he:zc
      . exfalso;exact h0 ⟨zn,by simp[he]⟩
      . rfl
     simp[zn,zo]
    . simp[zn]
   cases za.2.1 i <;> cases za.2.2 i <;> cases zb.2.1 i <;> cases zb.2.2 i <;>
    simp only[zm,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.xor_true,Ex,Bool.true_xor,Dz,Db,C3,AE,Bg,Be,Bj,AA,AK,zh,zi,zf]
   .
    calc y i*(x i*y i)=(y i*x i)*y i:=(Ad _ _ _).symm
     _ = z*x i*(y i*y i):=by rw[zf i];simp only[Ad]
     _ = z*x i:=by rw[zi,AK]
   .
    calc x i*(x i*y i)=(x i*x i)*y i:=(Ad _ _ _).symm
     _ = y i:=by rw[zh,AA]
   .
    calc x i*y i*y i=x i*(y i*y i):=Ad _ _ _
     _ = x i:=by rw[zi,AK]
   .
    calc x i*y i*x i=x i*(y i*x i):=Ad _ _ _
     _ = x i*(z*(x i*y i)):=by rw[zf i]
     _ = (x i*z)*x i*y i:=by simp only[Ad]
     _ = z*(x i*x i)*y i:=by rw[<-zd (x i)];simp only[Ad]
     _ = z*y i:=by rw[zh,AK]
   .
    calc x i*y i*(x i*y i)=x i*(y i*x i)*y i:=by simp only[Ad]
     _ = x i*(z*(x i*y i))*y i:=by rw[zf i]
     _ = (x i*z)*x i*(y i*y i):=by simp only[Ad]
     _ = z*(x i*x i):=by rw[<-zd (x i),zi,AK];simp only[Ad]
     _ = z:=by rw[zh,AK]
 dsimp only[Qc,QF];have zp:Qb (fun i=>(if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*(if zb.1 then z else 1)=(if zb.1 then z else 1)*Qb (fun i=>(if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1)):=(by cases zb.1 <;> simp[zd])
 calc (if za.1 then z else 1)*Qb (fun i=>(if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*((if zb.1 then z else 1)*Qb (fun i=>(if zb.2.1 i then x i else 1)*(if zb.2.2 i then y i else 1)))
   = (if za.1 then z else 1)*(if zb.1 then z else 1)*(Qb (fun i=>(if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*Qb (fun i=>(if zb.2.1 i then x i else 1)*(if zb.2.2 i then y i else 1))):=by rw[Ad,<-Ad (Qb _),zp];simp only[Ad]
  _ = (if xor za.1 zb.1 then z else 1)*Qb (fun i=>((if za.2.1 i then x i else 1)*(if za.2.2 i then y i else 1))*((if zb.2.1 i then x i else 1)*(if zb.2.2 i then y i else 1))):=by rw[zj,QL _ _ zk]
  _ = (if xor za.1 zb.1 then z else 1)*Qb (fun i=>(if xor (za.2.2 i&&zb.2.1 i) (xor (decide (i.val=0)&&!zc&&za.2.1 i&&zb.2.1 i) (decide (i.val=0)&&!zc&&za.2.2 i&&zb.2.2 i)) then z else 1)*((if xor (za.2.1 i) (zb.2.1 i) then x i else 1)*(if xor (za.2.2 i) (zb.2.2 i) then y i else 1))):=by congr 1;congr 1;funext i;exact zl i
  _ = _:=by rw[Yx z zd ze,<-Ad,zj]
noncomputable def Qe {R:Type*} [Group R] [Finite R] {z:R} {m:ℕ} {eps:Bool} (hES:Qn R z) (B:Qm R z m eps) : (Bool×(Fin m->Bool)×(Fin m->Bool)) ≃ R:=by
 classical
 haveI:Fintype R:=Fintype.ofFinite R;have zd:∀ a:R,z*a=a*z:=fun a=>
  (Subgroup.mem_center_iff.mp ((hES.center_iff z).mpr (Or.inr rfl)) a).symm
 let f:Bool×(Fin m->Bool)×(Fin m->Bool)->R:=
  fun t=>Qc z B.x B.y t.1 t.2.1 t.2.2
 have zl:Function.Injective f:=by
  intro zb za zh;have ha:∀ i:Fin m,zb.2.1 i=za.2.1 i:=by
   intro i;have zf:∀ t:Bool×(Fin m->Bool)×(Fin m->Bool),B.y i*f t=(if t.2.1 i then z else 1)*f t*B.y i:=by
    intro t;have h1:B.y i*Qb (fun j=>(if t.2.1 j then B.x j else 1)*(if t.2.2 j then B.y j else 1))=(if t.2.1 i then z else 1)*Qb (fun j=>(if t.2.1 j then B.x j else 1)*(if t.2.2 j then B.y j else 1))*B.y i:=by
     apply Q4 (B.y i) (if t.2.1 i then z else 1) _ i
     . intro a;cases t.2.1 i <;> simp[zd]
     .
      intro j;by_cases zc:j=i
      .
       subst zc;rw[Az rfl];cases t.2.1 j <;> cases t.2.2 j <;> simp
       .
        calc B.y j*B.x j=(z*z)*(B.y j*B.x j):=by rw[hES.z_sq,AA]
         _ = z*(B.x j*B.y j):=by rw[Ad,<-B.hxy_same j]
         _ = z*B.x j*B.y j:=(Ad _ _ _).symm
       .
        calc B.y j*(B.x j*B.y j)=(B.y j*B.x j)*B.y j:=(Ad _ _ _).symm
         _ = (z*(B.x j*B.y j))*B.y j:=by rw[B.hxy_same j,<-Ad,hES.z_sq,AA]
         _ = z*(B.x j*B.y j)*B.y j:=rfl
      .
       rw[Aw zc,AA];cases t.2.1 j <;> cases t.2.2 j <;> simp[B.hyy i j (Ne.symm zc),B.hxy j i zc]
       calc B.y i*(B.x j*B.y j)=(B.x j*B.y i)*B.y j:=by
               rw[<-Ad,(B.hxy j i zc).symm]
             _ = B.x j*(B.y j*B.y i):=by rw[Ad,B.hyy i j (Ne.symm zc)]
             _ = B.x j*B.y j*B.y i:=(Ad _ _ _).symm
    dsimp only[f,Qc];have ze:B.y i*(if t.1 then z else 1)=(if t.1 then z else 1)*B.y i:=(by cases t.1 <;> simp[zd]);have zi:(if t.1 then z else 1)*(if t.2.1 i then z else 1)=(if t.2.1 i then z else 1)*(if t.1 then z else 1):=(by cases t.1 <;> cases t.2.1 i <;> simp)
    calc B.y i*((if t.1 then z else 1)*Qb _)
      = (if t.1 then z else 1)*(B.y i*Qb _):=by rw[<-Ad,ze,Ad]
     _ = (if t.1 then z else 1)*((if t.2.1 i then z else 1)*Qb _*B.y i):=by rw[h1]
     _ = (if t.2.1 i then z else 1)*((if t.1 then z else 1)*Qb _)*B.y i:=by simp only[<-Ad,zi]
   have h1:=zf zb;have h2:=zf za;rw[zh] at h1;have h3:(if zb.2.1 i then z else 1)*(f za*B.y i)=(if za.2.1 i then z else 1)*(f za*B.y i):=(by simpa only[Ad] using h1.symm.trans h2);have h4:(if zb.2.1 i then z else 1)=(if za.2.1 i then z else 1):=Cj h3;cases zm:zb.2.1 i <;> cases zn:za.2.1 i <;> simp[zm,zn] at h4 ⊢
   . exact absurd h4.symm hES.z_ne_one
   . exact absurd h4 hES.z_ne_one
  have hb:∀ i:Fin m,zb.2.2 i=za.2.2 i:=by
   intro i;have zg:∀ t:Bool×(Fin m->Bool)×(Fin m->Bool),B.x i*f t=(if t.2.2 i then z else 1)*f t*B.x i:=by
    intro t;have h1:B.x i*Qb (fun j=>(if t.2.1 j then B.x j else 1)*(if t.2.2 j then B.y j else 1))=(if t.2.2 i then z else 1)*Qb (fun j=>(if t.2.1 j then B.x j else 1)*(if t.2.2 j then B.y j else 1))*B.x i:=by
     apply Q4 (B.x i) (if t.2.2 i then z else 1) _ i
     . intro a;cases t.2.2 i <;> simp[zd]
     .
      intro j;by_cases zc:j=i
      .
       subst zc;rw[Az rfl];cases t.2.1 j <;> cases t.2.2 j <;>
        simp only[AE,Bg,Be,Bj,AA,AK]
       . rw[B.hxy_same j,Ad]
       .
        calc B.x j*(B.x j*B.y j)=B.x j*(z*(B.y j*B.x j)):=by rw[B.hxy_same j]
         _ = (B.x j*z)*B.y j*B.x j:=by simp only[Ad]
         _ = z*(B.x j*B.y j)*B.x j:=by rw[<-zd (B.x j)];simp only[Ad]
      .
       rw[Aw zc,AA];cases t.2.1 j <;> cases t.2.2 j <;> simp[B.hxx i j (Ne.symm zc),B.hxy i j (Ne.symm zc)]
       calc B.x i*(B.x j*B.y j)=(B.x j*B.x i)*B.y j:=by
               rw[<-Ad,B.hxx i j (Ne.symm zc)]
             _ = B.x j*(B.y j*B.x i):=by rw[Ad,B.hxy i j (Ne.symm zc)]
             _ = B.x j*B.y j*B.x i:=(Ad _ _ _).symm
    dsimp only[f,Qc];have ze:B.x i*(if t.1 then z else 1)=(if t.1 then z else 1)*B.x i:=(by cases t.1 <;> simp[zd]);have zi:(if t.1 then z else 1)*(if t.2.2 i then z else 1)=(if t.2.2 i then z else 1)*(if t.1 then z else 1):=(by cases t.1 <;> cases t.2.2 i <;> simp)
    calc B.x i*((if t.1 then z else 1)*Qb _)
      = (if t.1 then z else 1)*(B.x i*Qb _):=by rw[<-Ad,ze,Ad]
     _ = (if t.1 then z else 1)*((if t.2.2 i then z else 1)*Qb _*B.x i):=by rw[h1]
     _ = (if t.2.2 i then z else 1)*((if t.1 then z else 1)*Qb _)*B.x i:=by simp only[<-Ad,zi]
   have h1:=zg zb;have h2:=zg za;rw[zh] at h1;have h3:(if zb.2.2 i then z else 1)*(f za*B.x i)=(if za.2.2 i then z else 1)*(f za*B.x i):=(by simpa only[Ad] using h1.symm.trans h2);have h4:(if zb.2.2 i then z else 1)=(if za.2.2 i then z else 1):=Cj h3;cases zm:zb.2.2 i <;> cases zn:za.2.2 i <;> simp[zm,zn] at h4 ⊢
   . exact absurd h4.symm hES.z_ne_one
   . exact absurd h4 hES.z_ne_one
  have zj:zb.2.1=za.2.1:=funext ha;have zk:zb.2.2=za.2.2:=funext hb;have hc:zb.1=za.1:=by
   dsimp only[f,Qc] at zh;rw[zj,zk] at zh;have h4:=Cj zh;cases zp:zb.1 <;> cases zq:za.1 <;> simp[zp,zq] at h4 ⊢
   . exact absurd h4.symm hES.z_ne_one
   . exact absurd h4 hES.z_ne_one
  exact Dr hc (Dr zj zk)
 have zo:Fintype.card (Bool×(Fin m->Bool)×(Fin m->Bool))=Fintype.card R:=(by rw[<-Au (α:=R),B.hcard];simp only[Fintype.card_prod,C6,Cl,AW];ring);exact Equiv.ofBijective f ((Ci f).mpr ⟨zl,zo⟩)
lemma Qs {R:Type*} [Group R] [Finite R] {z:R} {m:ℕ} {eps:Bool} (hES:Qn R z) (B:Qm R z m eps) (t:Bool×(Fin m->Bool)×(Fin m->Bool)) : Qe hES B t=Qc z B.x B.y t.1 t.2.1 t.2.2:=rfl
lemma WG {m:ℕ} (f:Fin m->Bool) (hf:∀ i,f i=false) : Qt f=false:=by
 induction m with
 | zero=>rfl
 | succ m ih=>simp only[Qt,hf 0,ih (fun i=>f i.succ) (fun i=>hf i.succ),Dz]
noncomputable def QA {R M:Type*} [Group R] [Finite R] [Monoid M]
  {z:R} {m:ℕ} {eps:Bool} (hES:Qn R z) (B:Qm R z m eps) (zM:M) (xM yM:Fin m->M) (hz_c:∀ a:M,zM*a=a*zM) (hz2:zM*zM=1) (hxy_same:∀ i,xM i*yM i=zM*(yM i*xM i)) (hxx:∀ i j,i≠j->xM i*xM j=xM j*xM i) (hxy:∀ i j,i≠j->xM i*yM j=yM j*xM i) (hyy:∀ i j,i≠j->yM i*yM j=yM j*yM i) (hsq_x:∀ i:Fin m,xM i*xM i=if i.val=0/\!eps then zM else 1) (hsq_y:∀ i:Fin m,yM i*yM i=if i.val=0/\!eps then zM else 1) : R→*M:=
 let eqv:=Qe hES B
 have hzR_c:∀ a:R,z*a=a*z:=fun a=>
  (Subgroup.mem_center_iff.mp ((hES.center_iff z).mpr (Or.inr rfl)) a).symm
 {toFun:=fun r=>
   let t:=eqv.symm r
   Qc zM xM yM t.1 t.2.1 t.2.2
  map_one':=by
   have h1:eqv (false,fun _=>false,fun _=>false)=1:=(by change Qc z B.x B.y false (fun _=>false) (fun _=>false)=1;simp only[Qc,AE,Bj,AA];exact QB _ (fun _=>rfl));have hs:eqv.symm 1=(false,fun _=>false,fun _=>false):=
    eqv.injective (by rw[AV,h1])
   simp only[hs,Qc,AE,Bj,AA];exact QB _ (fun _=>rfl)
  map_mul':=fun r₁ r₂=>by
   set za:=eqv.symm r₁;set t₂:=eqv.symm r₂;have zc:Qc z B.x B.y za.1 za.2.1 za.2.2=r₁:=eqv.apply_symm_apply r₁;have zd:Qc z B.x B.y t₂.1 t₂.2.1 t₂.2.2=r₂:=eqv.apply_symm_apply r₂;have zb:eqv (QF eps za t₂)=r₁*r₂:=by change Qc z B.x B.y (QF eps za t₂).1 (QF eps za t₂).2.1 (QF eps za t₂).2.2=r₁*r₂;rw[<-Wi eps z B.x B.y hzR_c hES.z_sq B.hxy_same B.hxx B.hxy B.hyy B.hsq_x B.hsq_y,zc,zd]
   have ze:eqv.symm (r₁*r₂)=QF eps za t₂:=
    eqv.injective (by rw[AV,zb])
   dsimp only;rw[ze]
   exact (Wi eps zM xM yM hz_c hz2 hxy_same hxx hxy hyy hsq_x hsq_y za t₂).symm }
lemma Yl {R M:Type*} [Group R] [Finite R] [Monoid M]
  {z:R} {m:ℕ} {zb:Bool} (za:Qn R z) (B:Qm R z m zb) (zM:M) (xM yM:Fin m->M) (zc:∀ a:M,zM*a=a*zM) (zd:zM*zM=1) (hxy_same:∀ i,xM i*yM i=zM*(yM i*xM i)) (hxx:∀ i j,i≠j->xM i*xM j=xM j*xM i) (hxy:∀ i j,i≠j->xM i*yM j=yM j*xM i) (hyy:∀ i j,i≠j->yM i*yM j=yM j*yM i) (hsq_x:∀ i:Fin m,xM i*xM i=if i.val=0/\!zb then zM else 1) (hsq_y:∀ i:Fin m,yM i*yM i=if i.val=0/\!zb then zM else 1) : QA za B zM xM yM zc zd hxy_same hxx hxy hyy hsq_x hsq_y z=zM:=by
 have h1:Qe za B (true,fun _=>false,fun _=>false)=z:=(by change Qc z B.x B.y true (fun _=>false) (fun _=>false)=z;simp only[Qc,AE,Bg,Be,Bj,AA];rw[QB _ (fun _=>rfl),AK]);have hs:(Qe za B).symm z=(true,fun _=>false,fun _=>false):=
  (Qe za B).injective (by rw[AV,h1])
 change Qc zM xM yM ((Qe za B).symm z).1 _ _=zM;rw[hs];simp only[Qc,AE,Bg,Be,Bj,AA];rw[QB _ (fun _=>rfl),AK]
lemma Q7 {R M:Type*} [Group R] [Finite R] [Monoid M]
  {z:R} {m:ℕ} {zc:Bool} (zb:Qn R z) (B:Qm R z m zc) (zM:M) (xM yM:Fin m->M) (zd:∀ a:M,zM*a=a*zM) (ze:zM*zM=1) (hxy_same:∀ i,xM i*yM i=zM*(yM i*xM i)) (hxx:∀ i j,i≠j->xM i*xM j=xM j*xM i) (hxy:∀ i j,i≠j->xM i*yM j=yM j*xM i) (hyy:∀ i j,i≠j->yM i*yM j=yM j*yM i) (hsq_x:∀ i:Fin m,xM i*xM i=if i.val=0/\!zc then zM else 1) (hsq_y:∀ i:Fin m,yM i*yM i=if i.val=0/\!zc then zM else 1) (za:Fin m) : QA zb B zM xM yM zd ze hxy_same hxx hxy hyy hsq_x hsq_y (B.x za)=xM za:=by
 have h1:Qe zb B (false,fun i=>decide (i=za),fun _=>false)=B.x za:=(by change Qc z B.x B.y false (fun i=>decide (i=za)) (fun _=>false)=B.x za;simp only[Qc,AE,Bj,AA,AK,D2];exact QN B.x za);have hs:(Qe zb B).symm (B.x za)=(false,fun i=>decide (i=za),fun _=>false):=
  (Qe zb B).injective (by rw[AV,h1])
 change Qc zM xM yM ((Qe zb B).symm (B.x za)).1 _ _=xM za;rw[hs];simp only[Qc,AE,Bj,AA,AK,D2];exact QN xM za
lemma Wd {R M:Type*} [Group R] [Finite R] [Monoid M]
  {z:R} {m:ℕ} {zc:Bool} (zb:Qn R z) (B:Qm R z m zc) (zM:M) (xM yM:Fin m->M) (zd:∀ a:M,zM*a=a*zM) (ze:zM*zM=1) (hxy_same:∀ i,xM i*yM i=zM*(yM i*xM i)) (hxx:∀ i j,i≠j->xM i*xM j=xM j*xM i) (hxy:∀ i j,i≠j->xM i*yM j=yM j*xM i) (hyy:∀ i j,i≠j->yM i*yM j=yM j*yM i) (hsq_x:∀ i:Fin m,xM i*xM i=if i.val=0/\!zc then zM else 1) (hsq_y:∀ i:Fin m,yM i*yM i=if i.val=0/\!zc then zM else 1) (za:Fin m) : QA zb B zM xM yM zd ze hxy_same hxx hxy hyy hsq_x hsq_y (B.y za)=yM za:=by
 have h1:Qe zb B (false,fun _=>false,fun i=>decide (i=za))=B.y za:=(by change Qc z B.x B.y false (fun _=>false) (fun i=>decide (i=za))=B.y za;simp only[Qc,AE,Bj,AA,D2];exact QN B.y za);have hs:(Qe zb B).symm (B.y za)=(false,fun _=>false,fun i=>decide (i=za)):=
  (Qe zb B).injective (by rw[AV,h1])
 change Qc zM xM yM ((Qe zb B).symm (B.y za)).1 _ _=yM za;rw[hs];simp only[Qc,AE,Bj,AA,D2];exact QN yM za
lemma WJ : ∀ (N:ℕ) (R:Type*) [Group R] [Finite R] (z:R), Nat.card R=N->Qn R z->∃ m eps,Nonempty (Qm R z m eps):=by
 intro N;induction N using Nat.strongRecOn with
 | ind N ih=>
  intro R _ _ z hcard za
  classical
  have zg:∀ a:R,z*a=a*z:=fun a=>
   (Subgroup.mem_center_iff.mp ((za.center_iff z).mpr (Or.inr rfl)) a).symm
  obtain ⟨a,b,zn⟩:=za.nonabelian;have zr:a*b=z*(b*a):=by
   rcases za.comm_mem a b with h1 | hz
   .
    exfalso;apply zn
    calc a*b=(a*b*a⁻¹*b⁻¹)*(b*a):=by group
     _ = b*a:=by rw[h1,AA]
   .
    calc a*b=(a*b*a⁻¹*b⁻¹)*(b*a):=by group
     _ = z*(b*a):=by rw[hz]
  have z1:(a*b)*(a*b)=z*(a*a)*(b*b):=by
   have vy:b*a=z*(a*b):=by rw[zr,<-Ad,za.z_sq,AA]
   calc (a*b)*(a*b)=a*(b*a)*b:=by simp only[Ad]
    _ = a*(z*(a*b))*b:=by rw[vy]
    _ = (a*z)*a*(b*b):=by simp only[Ad]
    _ = z*(a*a)*(b*b):=by rw[<-zg a];simp only[Ad]
  have z6:∃ (x₁ y₁:R) (zI:Bool),x₁*y₁=z*(y₁*x₁)/\x₁*x₁=(if zI then 1 else z)/\y₁*y₁=(if zI then 1 else z):=by
   rcases za.sq_mem a with ha1 | haz <;> rcases za.sq_mem b with hb1 | hbz
   . exact ⟨a,b,true,zr,ha1,hb1⟩
   .
    refine ⟨a,a*b,true,?_,by simp[ha1],by simp[z1,ha1,hbz,za.z_sq]⟩
    calc a*(a*b)=a*(z*(b*a)):=by rw[zr]
     _ = (a*z)*(b*a):=by simp only[Ad]
     _ = z*((a*b)*a):=by rw[<-zg a];simp only[Ad]
   .
    refine ⟨a*b,b,true,?_,by simp[z1,haz,hb1,za.z_sq],by simp[hb1]⟩
    calc (a*b)*b=(z*(b*a))*b:=by rw[zr]
     _ = z*(b*(a*b)):=by simp only[Ad]
   . exact ⟨a,b,false,zr,haz,hbz⟩
  obtain ⟨x₁,y₁,zI,zf,zh,ze⟩:=z6;let R':Subgroup R:=Subgroup.centralizer ({x₁,y₁}:Set R);have zi:∀ r:R,r∈R'↔x₁*r=r*x₁/\y₁*r=r*y₁:=by intro r;rw[Cv];simp only[Set.mem_insert_iff,Set.mem_singleton_iff,forall_eq_or_imp,forall_eq]
  have zB:z∈R':=(zi z).mpr ⟨(zg x₁).symm,(zg y₁).symm⟩;let φ:(Bool×Bool×R')->R:=fun p=>
   (if p.1 then x₁ else 1)*(if p.2.1 then y₁ else 1)*p.2.2.1
  have zT:Function.Bijective φ:=by
   constructor
   .
    intro zz zA z5;have zU:∀ p:Bool×Bool×R',x₁*φ p=(if p.2.1 then z else 1)*φ p*x₁:=by
     intro p;have hr:=((zi p.2.2.1).mp p.2.2.2).1;dsimp only[φ];cases p.1 <;> cases p.2.1 <;>
      simp only[AE,Bg,Be,Bj,AA,AK]
     . exact hr
     .
      calc x₁*(y₁*p.2.2.1)=(x₁*y₁)*p.2.2.1:=(Ad _ _ _).symm
       _ = z*y₁*(x₁*p.2.2.1):=by rw[zf];simp only[Ad]
       _ = z*(y₁*p.2.2.1)*x₁:=by rw[hr];simp only[Ad]
     .
      calc x₁*(x₁*p.2.2.1)=x₁*(p.2.2.1*x₁):=by rw[hr]
       _ = x₁*p.2.2.1*x₁:=(Ad _ _ _).symm
     .
      calc x₁*(x₁*y₁*p.2.2.1)=x₁*(z*(y₁*x₁))*p.2.2.1:=by rw[zf];simp only[Ad]
       _ = (x₁*z)*y₁*(x₁*p.2.2.1):=by simp only[Ad]
       _ = z*(x₁*y₁*p.2.2.1)*x₁:=by rw[<-zg x₁,hr];simp only[Ad]
    have zV:∀ p:Bool×Bool×R',y₁*φ p=(if p.1 then z else 1)*φ p*y₁:=by
     intro p;have hr:=((zi p.2.2.1).mp p.2.2.2).2;have zC:y₁*x₁=z*(x₁*y₁):=by rw[zf,<-Ad,za.z_sq,AA]
     dsimp only[φ];cases p.1 <;> cases p.2.1 <;>
      simp only[AE,Bg,Be,Bj,AA,AK]
     . exact hr
     .
      calc y₁*(y₁*p.2.2.1)=y₁*(p.2.2.1*y₁):=by rw[hr]
       _ = y₁*p.2.2.1*y₁:=(Ad _ _ _).symm
     .
      calc y₁*(x₁*p.2.2.1)=(y₁*x₁)*p.2.2.1:=(Ad _ _ _).symm
       _ = z*x₁*(y₁*p.2.2.1):=by rw[zC];simp only[Ad]
       _ = z*(x₁*p.2.2.1)*y₁:=by rw[hr];simp only[Ad]
     .
      calc y₁*(x₁*y₁*p.2.2.1)=(y₁*x₁)*(y₁*p.2.2.1):=by simp only[Ad]
       _ = z*(x₁*y₁)*(p.2.2.1*y₁):=by rw[zC,hr]
       _ = z*(x₁*y₁*p.2.2.1)*y₁:=by simp only[Ad]
    have hb:zz.2.1=zA.2.1:=by
     have h1:=zU zz;have h2:=zU zA;rw[z5] at h1;have h3:(if zz.2.1 then z else 1)=(if zA.2.1 then z else 1):=
      Cj (by simpa only[Ad] using h1.symm.trans h2)
     cases vC:zz.2.1 <;> cases vD:zA.2.1 <;> simp[vC,vD] at h3 ⊢
     . exact absurd h3.symm za.z_ne_one
     . exact absurd h3 za.z_ne_one
    have ha:zz.1=zA.1:=by
     have h1:=zV zz;have h2:=zV zA;rw[z5] at h1;have h3:(if zz.1 then z else 1)=(if zA.1 then z else 1):=
      Cj (by simpa only[Ad] using h1.symm.trans h2)
     cases vE:zz.1 <;> cases vF:zA.1 <;> simp[vE,vF] at h3 ⊢
     . exact absurd h3.symm za.z_ne_one
     . exact absurd h3 za.z_ne_one
    have hr:zz.2.2=zA.2.2:=(by dsimp only[φ] at z5;rw[ha,hb] at z5;exact Ae (E3 z5));exact Dr ha (Dr hb hr)
   .
    intro r;let cx:R:=x₁*r*x₁⁻¹*r⁻¹;let cy:R:=y₁*r*y₁⁻¹*r⁻¹;let u:Bool:=decide (cy=z);let v:Bool:=decide (cx=z);have zk:x₁*r=(if v then z else 1)*(r*x₁):=by
     rcases za.comm_mem x₁ r with h1 | hz
     .
      have hv:v=false:=by simp[v,cx,h1,za.z_ne_one.symm]
      rw[hv,Aw (by decide),AA]
      calc x₁*r=(x₁*r*x₁⁻¹*r⁻¹)*(r*x₁):=by group
       _ = r*x₁:=by rw[h1,AA]
     .
      have hv:v=true:=by simp[v,cx,hz]
      rw[hv,Az rfl]
      calc x₁*r=(x₁*r*x₁⁻¹*r⁻¹)*(r*x₁):=by group
       _ = z*(r*x₁):=by rw[hz]
    have zH:y₁*r=(if u then z else 1)*(r*y₁):=by
     rcases za.comm_mem y₁ r with h1 | hz
     .
      have hu:u=false:=by simp[u,cy,h1,za.z_ne_one.symm]
      rw[hu,Aw (by decide),AA]
      calc y₁*r=(y₁*r*y₁⁻¹*r⁻¹)*(r*y₁):=by group
       _ = r*y₁:=by rw[h1,AA]
     .
      have hu:u=true:=by simp[u,cy,hz]
      rw[hu,Az rfl]
      calc y₁*r=(y₁*r*y₁⁻¹*r⁻¹)*(r*y₁):=by group
       _ = z*(r*y₁):=by rw[hz]
    let g:R:=(if u then x₁ else 1)*(if v then y₁ else 1);let r':R:=g⁻¹*r;have vz:x₁*g=(if v then z else 1)*(g*x₁):=by
     dsimp only[g];cases u <;> cases v <;>
      simp only[AE,Bg,Be,Bj,AA,AK]
     . exact zf
     .
      calc x₁*(x₁*y₁)=x₁*(z*(y₁*x₁)):=by rw[zf]
       _ = (x₁*z)*y₁*x₁:=by simp only[Ad]
       _ = z*(x₁*y₁*x₁):=by rw[<-zg x₁];simp only[Ad]
    have vA:y₁*g=(if u then z else 1)*(g*y₁):=by
     have zC:y₁*x₁=z*(x₁*y₁):=by rw[zf,<-Ad,za.z_sq,AA]
     dsimp only[g];cases u <;> cases v <;>
      simp only[AE,Bg,Be,Bj,AA,AK]
     . exact zC
     .
      calc y₁*(x₁*y₁)=(y₁*x₁)*y₁:=(Ad _ _ _).symm
       _ = z*(x₁*y₁*y₁):=by rw[zC];simp only[Ad]
    have vf:r'∈R':=by
     rw[zi];constructor
     .
      have h1:x₁*g⁻¹=(if v then z else 1)*(g⁻¹*x₁):=by
       have z7:g⁻¹*(x₁*g)=g⁻¹*((if v then z else 1)*(g*x₁)):=Ah (g⁻¹*·) vz;have zQ:g⁻¹*(if v then z else 1)=(if v then z else 1)*g⁻¹:=by cases v <;> simp[zg]
       have h2:g⁻¹*x₁*g=(if v then z else 1)*x₁:=by
        calc g⁻¹*x₁*g=g⁻¹*(x₁*g):=Ad _ _ _
         _ = g⁻¹*(if v then z else 1)*(g*x₁):=by rw[z7];simp only[Ad]
         _ = (if v then z else 1)*(g⁻¹*g)*x₁:=by rw[zQ];simp only[Ad]
         _ = (if v then z else 1)*x₁:=by simp
       have h3:(if v then z else 1)*(if v then z else 1)=1:=by cases v <;> simp[za.z_sq]
       calc x₁*g⁻¹=(if v then z else 1)*((if v then z else 1)*x₁)*g⁻¹:=by
               rw[<-Ad,h3,AA]
             _ = (if v then z else 1)*(g⁻¹*x₁*g)*g⁻¹:=by rw[<-h2]
             _ = (if v then z else 1)*(g⁻¹*x₁):=by group
      have h3:(if v then z else 1)*(if v then z else 1)=1:=by cases v <;> simp[za.z_sq]
      have zQ:g⁻¹*(if v then z else 1)=(if v then z else 1)*g⁻¹:=by cases v <;> simp[zg]
      calc x₁*(g⁻¹*r)=(x₁*g⁻¹)*r:=(Ad _ _ _).symm
       _ = (if v then z else 1)*g⁻¹*(x₁*r):=by rw[h1];simp only[Ad]
       _ = (if v then z else 1)*(g⁻¹*(if v then z else 1))*(r*x₁):=by rw[zk];simp only[Ad]
       _ = ((if v then z else 1)*(if v then z else 1))*(g⁻¹*r*x₁):=by rw[zQ];simp only[Ad]
       _ = g⁻¹*r*x₁:=by rw[h3,AA]
     .
      have h1:y₁*g⁻¹=(if u then z else 1)*(g⁻¹*y₁):=by
       have z7:g⁻¹*(y₁*g)=g⁻¹*((if u then z else 1)*(g*y₁)):=Ah (g⁻¹*·) vA;have zQ:g⁻¹*(if u then z else 1)=(if u then z else 1)*g⁻¹:=by cases u <;> simp[zg]
       have h2:g⁻¹*y₁*g=(if u then z else 1)*y₁:=by
        calc g⁻¹*y₁*g=g⁻¹*(y₁*g):=Ad _ _ _
         _ = g⁻¹*(if u then z else 1)*(g*y₁):=by rw[z7];simp only[Ad]
         _ = (if u then z else 1)*(g⁻¹*g)*y₁:=by rw[zQ];simp only[Ad]
         _ = (if u then z else 1)*y₁:=by simp
       have h3:(if u then z else 1)*(if u then z else 1)=1:=by cases u <;> simp[za.z_sq]
       calc y₁*g⁻¹=(if u then z else 1)*((if u then z else 1)*y₁)*g⁻¹:=by
               rw[<-Ad,h3,AA]
             _ = (if u then z else 1)*(g⁻¹*y₁*g)*g⁻¹:=by rw[<-h2]
             _ = (if u then z else 1)*(g⁻¹*y₁):=by group
      have h3:(if u then z else 1)*(if u then z else 1)=1:=by cases u <;> simp[za.z_sq]
      have zQ:g⁻¹*(if u then z else 1)=(if u then z else 1)*g⁻¹:=by cases u <;> simp[zg]
      calc y₁*(g⁻¹*r)=(y₁*g⁻¹)*r:=(Ad _ _ _).symm
       _ = (if u then z else 1)*g⁻¹*(y₁*r):=by rw[h1];simp only[Ad]
       _ = (if u then z else 1)*(g⁻¹*(if u then z else 1))*(r*y₁):=by rw[zH];simp only[Ad]
       _ = ((if u then z else 1)*(if u then z else 1))*(g⁻¹*r*y₁):=by rw[zQ];simp only[Ad]
       _ = g⁻¹*r*y₁:=by rw[h3,AA]
    exact ⟨(u,v,⟨r',vf⟩),by change g*(g⁻¹*r)=r;group⟩
  have zR:Nat.card R=4*Nat.card R':=by
   have h1:=Bc (Equiv.ofBijective φ zT);rw[<-h1,EG,EG];have hb:Nat.card Bool=2:=by simp
   rw[hb];ring
  by_cases zE:∀ r':R',r'=1\/r'=⟨z,zB⟩;·
   have z2:Nat.card R'=2:=by
    let e2:Bool ≃ R':=
     {toFun:=fun b=>if b then ⟨z,zB⟩ else 1
      invFun:=fun r=>decide (r=⟨z,zB⟩)
      left_inv:=fun b=>by
       have vg:(⟨z,zB⟩:R')≠1:=fun h=>za.z_ne_one (Ah Subtype.val h);cases b <;> simp[vg,vg.symm]
      right_inv:=fun r=>by
       rcases zE r with rfl | rfl
       . simp[show (1:R')≠⟨z,zB⟩ from fun h=>za.z_ne_one (Ah Subtype.val h).symm]
       . simp }
    rw[<-Bc e2];simp
   refine ⟨1,zI,⟨{
    hm:=le_rfl
    x:=fun _=>x₁
    y:=fun _=>y₁
    hxy_same:=fun _=>zf
    hxx:=fun i j hij=>absurd (Subsingleton.elim i j) hij
    hxy:=fun i j hij=>absurd (Subsingleton.elim i j) hij
    hyy:=fun i j hij=>absurd (Subsingleton.elim i j) hij
    hsq_x:=fun i=>by cases zI <;> simp[CR i,zh]
    hsq_y:=fun i=>by cases zI <;> simp[CR i,ze]
    hcard:=by rw[zR,z2];norm_num }⟩⟩
  ·
   push Not at zE;obtain ⟨zJ,z3,z4⟩:=zE;have vs:Qn R' ⟨z,zB⟩:=by
    have vq:∀ c:R',c∈Subgroup.center R'↔c=1\/c=⟨z,zB⟩:=by
     intro c;constructor
     .
      intro vx;have vh:c.1∈Subgroup.center R:=by
       rw[Bk];intro g;obtain ⟨⟨u,v,s⟩,rfl⟩:=zT.2 g;have zk:=((zi c.1).mp c.2).1;have zH:=((zi c.1).mp c.2).2;have vb:s.1*c.1=c.1*s.1:=Ah Subtype.val (Subgroup.mem_center_iff.mp vx s);dsimp only[φ];cases u <;> cases v <;>
        simp only[AE,Bg,Be,Bj,AA,AK]
       . exact vb
       .
        calc y₁*s.1*c.1=y₁*(c.1*s.1):=by rw[Ad,vb]
         _ = c.1*(y₁*s.1):=by rw[<-Ad,zH,Ad]
       .
        calc x₁*s.1*c.1=x₁*(c.1*s.1):=by rw[Ad,vb]
         _ = c.1*(x₁*s.1):=by rw[<-Ad,zk,Ad]
       .
        calc x₁*y₁*s.1*c.1=x₁*y₁*(c.1*s.1):=by rw[Ad,vb]
         _ = x₁*(c.1*y₁)*s.1:=by rw[Ad x₁,<-Ad y₁,zH];simp only[Ad]
         _ = c.1*(x₁*y₁*s.1):=by rw[<-Ad x₁,zk];simp only[Ad]
      exact ((za.center_iff c.1).mp vh).imp Ae Ae
     .
      rintro (rfl | rfl)
      . exact (Subgroup.center R').one_mem
      . rw[Bk];intro g;exact Ae (zg g.1).symm
    exact {
     z_ne_one:=fun h=>za.z_ne_one (Ah Subtype.val h)
     z_sq:=Ae za.z_sq
     center_iff:=vq
     comm_mem:=fun u v=>(za.comm_mem u.1 v.1).imp Ae Ae
     sq_mem:=fun u=>(za.sq_mem u.1).imp Ae Ae
     nonabelian:=by
      by_contra hab';push Not at hab';have vt:zJ∈Subgroup.center R':=Subgroup.mem_center_iff.mpr fun g=>hab' g zJ;rcases (vq zJ).mp vt with h1 | hz
      . exact z3 h1
      . exact z4 hz }
   have vi:Nat.card R' < N:=(by have vG:0 < Nat.card R':=CD;omega);obtain ⟨m',eps',⟨B'⟩⟩:=ih (Nat.card R') vi R' ⟨z,zB⟩ rfl vs;have zD:Nat.card R=2 ^ (1+2*(m'+1)):=(by rw[zR,B'.hcard];ring);let x':Fin m'->R:=fun i=>(B'.x i).1;let y':Fin m'->R:=fun i=>(B'.y i).1;have zu:∀ i,x₁*x' i=x' i*x₁/\y₁*x' i=x' i*y₁:=fun i=>(zi _).mp (B'.x i).2;have zv:∀ i,x₁*y' i=y' i*x₁/\y₁*y' i=y' i*y₁:=fun i=>(zi _).mp (B'.y i).2;have zs:∀ i,x' i*y' i=z*(y' i*x' i):=fun i=>Ah Subtype.val (B'.hxy_same i);have zY:∀ i j,i≠j->x' i*x' j=x' j*x' i:=fun i j h=>Ah Subtype.val (B'.hxx i j h);have zw:∀ i j,i≠j->x' i*y' j=y' j*x' i:=fun i j h=>Ah Subtype.val (B'.hxy i j h);have zZ:∀ i j,i≠j->y' i*y' j=y' j*y' i:=fun i j h=>Ah Subtype.val (B'.hyy i j h);have zN:∀ i:Fin m',x' i*x' i=if i.val=0/\!eps' then z else 1:=fun i=>by
    have h:=Ah Subtype.val (B'.hsq_x i);split_ifs at h ⊢ <;> exact h
   have zO:∀ i:Fin m',y' i*y' i=if i.val=0/\!eps' then z else 1:=fun i=>by
    have h:=Ah Subtype.val (B'.hsq_y i);split_ifs at h ⊢ <;> exact h
   cases vr:zI;·
    rw[vr] at zh ze;simp only[AE,Bj] at zh ze;cases zP:eps';·
     let i0:Fin m':=⟨0,B'.hm⟩;let x0:=x' i0;let y0:=y' i0;have zF:x0*x0=z:=by simpa[x0,i0,zP] using zN i0
     have vc:y0*y0=z:=by simpa[y0,i0,zP] using zO i0
     have z8:x0*y0=z*(y0*x0):=zs i0;have z9:y0*x0=z*(x0*y0):=by rw[z8,<-Ad,za.z_sq,AA]
     have vj:y₁*x₁=z*(x₁*y₁):=by rw[zf,<-Ad,za.z_sq,AA]
     have zK:x₁*x0=x0*x₁:=(zu i0).1;have zy:y₁*x0=x0*y₁:=(zu i0).2;have z0:x₁*y0=y0*x₁:=(zv i0).1;have zG:y₁*y0=y0*y₁:=(zv i0).2;let a₀:=x₁*x0;let b₀:=x₁*y₁*x0;let zj:=y₁*y0;let b₁:=y₁*x0*y0;have vk:a₀*a₀=1:=by
      calc (x₁*x0)*(x₁*x0)=(x₁*(x0*x₁))*x0:=by simp only[Ad]
       _ = (x₁*x₁)*(x0*x0):=by rw[<-zK];simp only[Ad]
       _ = 1:=by rw[zh,zF,za.z_sq]
     have vl:b₀*b₀=1:=by
      have h1:(x₁*y₁)*(x₁*y₁)=z:=by
       calc (x₁*y₁)*(x₁*y₁)=x₁*(y₁*x₁)*y₁:=by simp only[Ad]
        _ = x₁*(z*(x₁*y₁))*y₁:=by rw[vj]
        _ = (x₁*z)*x₁*(y₁*y₁):=by simp only[Ad]
        _ = z*(x₁*x₁)*z:=by rw[<-zg x₁,ze];simp only[Ad]
        _ = z:=by rw[zh,za.z_sq,AA]
      have zo:(x₁*y₁)*x0=x0*(x₁*y₁):=(by rw[Ad,zy,<-Ad,zK,Ad])
      calc (x₁*y₁*x0)*(x₁*y₁*x0)=(x₁*y₁)*(x0*(x₁*y₁))*x0:=by simp only[Ad]
       _ = ((x₁*y₁)*(x₁*y₁))*(x0*x0):=by rw[<-zo];simp only[Ad]
       _ = 1:=by rw[h1,zF,za.z_sq]
     have vm:zj*zj=1:=by
      calc (y₁*y0)*(y₁*y0)=(y₁*(y0*y₁))*y0:=by simp only[Ad]
       _ = (y₁*y₁)*(y0*y0):=by rw[<-zG];simp only[Ad]
       _ = 1:=by rw[ze,vc,za.z_sq]
     have vn:b₁*b₁=1:=by
      have h1:(x0*y0)*(x0*y0)=z:=by
       calc (x0*y0)*(x0*y0)=x0*(y0*x0)*y0:=by simp only[Ad]
        _ = x0*(z*(x0*y0))*y0:=by rw[z9]
        _ = (x0*z)*x0*(y0*y0):=by simp only[Ad]
        _ = z*(x0*x0)*z:=by rw[<-zg x0,vc];simp only[Ad]
        _ = z:=by rw[zF,za.z_sq,AA]
      have va:y₁*(x0*y0)=(x0*y0)*y₁:=(by rw[<-Ad,zy,Ad,zG,<-Ad])
      calc (y₁*x0*y0)*(y₁*x0*y0)=y₁*((x0*y0)*y₁)*(x0*y0):=by simp only[Ad]
       _ = (y₁*y₁)*((x0*y0)*(x0*y0)):=by rw[<-va];simp only[Ad]
       _ = 1:=by rw[ze,h1,za.z_sq]
     have vu:a₀*b₀=z*(b₀*a₀):=by
      have zo:x0*(x₁*y₁)=(x₁*y₁)*x0:=(by rw[<-Ad,<-zK,Ad,<-zy,<-Ad])
      calc (x₁*x0)*(x₁*y₁*x0)=x₁*(x0*(x₁*y₁))*x0:=by simp only[Ad]
       _ = x₁*(x₁*y₁)*(x0*x0):=by rw[zo];simp only[Ad]
       _ = x₁*(z*(y₁*x₁))*(x0*x0):=by rw[zf]
       _ = (x₁*z)*y₁*(x₁*(x0*x0)):=by simp only[Ad]
       _ = z*(x₁*y₁*(x0*x₁*x0)):=by rw[<-zg x₁,<-Ad x₁ x0,zK];simp only[Ad]
       _ = z*((x₁*y₁*x0)*(x₁*x0)):=by simp only[Ad]
     have vv:zj*b₁=z*(b₁*zj):=by
      have va:y₁*(x0*y0)=(x0*y0)*y₁:=(by rw[<-Ad,zy,Ad,zG,<-Ad])
      calc (y₁*y0)*(y₁*x0*y0)=y₁*(y0*y₁)*(x0*y0):=by simp only[Ad]
       _ = (y₁*y₁)*(y0*x0*y0):=by rw[<-zG];simp only[Ad]
       _ = (y₁*y₁)*(z*(x0*y0)*y0):=by rw[z9]
       _ = ((y₁*y₁)*z)*(x0*y0*y0):=by simp only[Ad]
       _ = z*((y₁*(y₁*(x0*y0)))*y0):=by rw[<-zg (y₁*y₁)];simp only[Ad]
       _ = z*((y₁*((x0*y0)*y₁))*y0):=by rw[va]
       _ = z*((y₁*x0*y0)*(y₁*y0)):=by simp only[Ad]
     have vd:a₀*zj=zj*a₀:=by
      calc (x₁*x0)*(y₁*y0)=x₁*(x0*y₁)*y0:=by simp only[Ad]
       _ = (x₁*y₁)*(x0*y0):=by rw[<-zy];simp only[Ad]
       _ = (z*(y₁*x₁))*(z*(y0*x0)):=by rw[zf,z8]
       _ = (z*z)*(y₁*(x₁*y0)*x0):=by
             calc (z*(y₁*x₁))*(z*(y0*x0))=z*((y₁*x₁)*z)*(y0*x0):=by simp only[Ad]
              _ = (z*z)*(y₁*(x₁*y0)*x0):=by rw[<-zg (y₁*x₁)];simp only[Ad]
       _ = y₁*(y0*x₁)*x0:=by rw[za.z_sq,AA,z0]
       _ = (y₁*y0)*(x₁*x0):=by simp only[Ad]
     have zx:∀ (u₁ v₁ u₀ v₀:R),u₀*v₁=v₁*u₀->(u₁*u₀)*(v₁*v₀)=(u₁*v₁)*(u₀*v₀):=
      fun u₁ v₁ u₀ v₀ h=>by rw[Ad,<-Ad u₀,h];simp only[Ad]
     have zW:x0*y0*x0=y0:=by
      calc x0*y0*x0=x0*(z*(x0*y0)):=by rw[Ad,z9]
       _ = (x0*z)*x0*y0:=by simp only[Ad]
       _ = z*(x0*x0)*y0:=by rw[<-zg x0];simp only[Ad]
       _ = y0:=by rw[zF,za.z_sq,AA]
     have zX:y₁*(x₁*y₁)=x₁:=by
      calc y₁*(x₁*y₁)=(y₁*x₁)*y₁:=(Ad _ _ _).symm
       _ = z*x₁*(y₁*y₁):=by rw[vj];simp only[Ad]
       _ = z*(x₁*z):=by rw[ze];simp only[Ad]
       _ = (z*z)*x₁:=by rw[<-zg x₁];simp only[Ad]
       _ = x₁:=by rw[za.z_sq,AA]
     have zL:x0*y₁=y₁*x0:=zy.symm;have zt:(x0*y0)*x₁=x₁*(x0*y0):=(by rw[Ad,<-z0,<-Ad,<-zK,Ad]);have zS:(x0*y0)*(x₁*y₁)=(x₁*y₁)*(x0*y0):=(by rw[<-Ad,zt,Ad];have h1:(x0*y0)*y₁=y₁*(x0*y0):=(by rw[Ad,<-zG,<-Ad,<-zy,Ad]);rw[h1,<-Ad]);have vo:a₀*b₁=b₁*a₀:=by
      have hL:a₀*b₁=(x₁*y₁)*(x0*(x0*y0)):=(by dsimp only[a₀,b₁];rw[Ad y₁];exact zx x₁ y₁ x0 (x0*y0) zL);have hR:b₁*a₀=(y₁*x₁)*((x0*y0)*x0):=(by dsimp only[a₀,b₁];rw[Ad y₁];exact zx y₁ x₁ (x0*y0) x0 zt);rw[hL,hR,zf,<-Ad x0,zF,zW]
      calc z*(y₁*x₁)*(z*y0)=z*((y₁*x₁)*z)*y0:=by simp only[Ad]
       _ = (z*z)*(y₁*x₁)*y0:=by rw[<-zg (y₁*x₁)];simp only[Ad]
       _ = y₁*x₁*y0:=by rw[za.z_sq,AA]
     have vp:b₀*zj=zj*b₀:=by
      have hL:b₀*zj=((x₁*y₁)*y₁)*(x0*y0):=zx (x₁*y₁) y₁ x0 y0 zL;have hR:zj*b₀=(y₁*(x₁*y₁))*(y0*x0):=(by have vw:y0*(x₁*y₁)=(x₁*y₁)*y0:=(by rw[<-Ad,<-z0,Ad,<-zG,<-Ad]);exact zx y₁ (x₁*y₁) y0 x0 vw);rw[hL,hR,Ad x₁,ze,zX,z8]
      calc x₁*z*(z*(y0*x0))=x₁*(z*z)*(y0*x0):=by simp only[Ad]
       _ = x₁*(y0*x0):=by rw[za.z_sq,AK]
     have ve:b₀*b₁=b₁*b₀:=by
      have hL:b₀*b₁=((x₁*y₁)*y₁)*(x0*(x0*y0)):=(by dsimp only[b₀,b₁];rw[Ad y₁];exact zx (x₁*y₁) y₁ x0 (x0*y0) zL);have hR:b₁*b₀=(y₁*(x₁*y₁))*((x0*y0)*x0):=(by dsimp only[b₀,b₁];rw[Ad y₁];exact zx y₁ (x₁*y₁) (x0*y0) x0 zS);rw[hL,hR,Ad x₁,ze,<-Ad x0,zF,zX,zW]
      calc x₁*z*(z*y0)=x₁*(z*z)*y0:=by simp only[Ad]
       _ = x₁*y0:=by rw[za.z_sq,AK]
     let nx:Fin (m'+1)->R:=fun k=>
      if hk0:k.val=0 then a₀
      else if hk1:k.val=1 then zj
      else x' ⟨k.val - 1,by omega⟩
     let ny:Fin (m'+1)->R:=fun k=>
      if hk0:k.val=0 then b₀
      else if hk1:k.val=1 then b₁
      else y' ⟨k.val - 1,by omega⟩
     have zb:∀ (r:R),(x₁*r=r*x₁/\y₁*r=r*y₁/\x0*r=r*x0/\y0*r=r*y0)->a₀*r=r*a₀/\b₀*r=r*b₀/\zj*r=r*zj/\b₁*r=r*b₁:=by
      rintro r ⟨h1,h2,h3,h4⟩;refine ⟨?_,?_,?_,?_⟩
      . dsimp only[a₀];rw[Ad,h3,<-Ad,h1,Ad]
      .
       dsimp only[b₀]
       calc x₁*y₁*x0*r=x₁*y₁*(r*x0):=by rw[Ad,h3]
        _ = x₁*(r*y₁)*x0:=by rw[Ad x₁,<-Ad y₁,h2];simp only[Ad]
        _ = r*(x₁*y₁*x0):=by rw[<-Ad x₁,h1];simp only[Ad]
      . dsimp only[zj];rw[Ad,h4,<-Ad,h2,Ad]
      .
       dsimp only[b₁]
       calc y₁*x0*y0*r=y₁*x0*(r*y0):=by rw[Ad,h4]
        _ = y₁*(r*x0)*y0:=by rw[Ad y₁,<-Ad x0,h3];simp only[Ad]
        _ = r*(y₁*x0*y0):=by rw[<-Ad y₁,h2];simp only[Ad]
     have zp:∀ (k:Fin (m'+1)) (h0:k.val≠0) (h1:k.val≠1),x₁*x' ⟨k.val - 1,by omega⟩=x' ⟨k.val - 1,by omega⟩*x₁/\y₁*x' ⟨k.val - 1,by omega⟩=x' ⟨k.val - 1,by omega⟩*y₁/\x0*x' ⟨k.val - 1,by omega⟩=x' ⟨k.val - 1,by omega⟩*x0/\y0*x' ⟨k.val - 1,by omega⟩=x' ⟨k.val - 1,by omega⟩*y0:=by
      intro k h0 h1;have zM:i0≠⟨k.val - 1,by omega⟩:=fun h=>by
       have:=Ah Fin.val h;dsimp[i0] at this;omega
      exact ⟨(zu _).1,(zu _).2,zY i0 _ zM,(zw _ i0 zM.symm).symm⟩
     have zq:∀ (k:Fin (m'+1)) (h0:k.val≠0) (h1:k.val≠1),x₁*y' ⟨k.val - 1,by omega⟩=y' ⟨k.val - 1,by omega⟩*x₁/\y₁*y' ⟨k.val - 1,by omega⟩=y' ⟨k.val - 1,by omega⟩*y₁/\x0*y' ⟨k.val - 1,by omega⟩=y' ⟨k.val - 1,by omega⟩*x0/\y0*y' ⟨k.val - 1,by omega⟩=y' ⟨k.val - 1,by omega⟩*y0:=by
      intro k h0 h1;have zM:i0≠⟨k.val - 1,by omega⟩:=fun h=>by
       have:=Ah Fin.val h;dsimp[i0] at this;omega
      exact ⟨(zv _).1,(zv _).2,zw i0 _ zM,zZ i0 _ zM⟩
     refine ⟨m'+1,true,⟨{
      hm:=by omega
      x:=nx
      y:=ny
      hxy_same:=fun k=>by
       dsimp only[nx,ny];split_ifs with h0 h1
       . exact vu
       . exact vv
       . exact zs ⟨k.val - 1,by omega⟩
      hxx:=fun i j hij=>by
       dsimp only[nx];by_cases zl:i.val=0
       .
        rw[dif_pos zl];by_cases zc:j.val=0
        . exact absurd (A4 (zl.trans zc.symm)) hij
        .
         rw[dif_neg zc];by_cases zd:j.val=1
         . rw[dif_pos zd];exact vd
         . rw[dif_neg zd];exact (zb _ (zp j zc zd)).1
       .
        rw[dif_neg zl];by_cases zm:i.val=1
        .
         rw[dif_pos zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact vd.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . exact absurd (A4 (zm.trans zd.symm)) hij
          . rw[dif_neg zd];exact (zb _ (zp j zc zd)).2.2.1
        .
         rw[dif_neg zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact (zb _ (zp i zl zm)).1.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . rw[dif_pos zd];exact (zb _ (zp i zl zm)).2.2.1.symm
          . rw[dif_neg zd];exact zY _ _ (fun h=>hij (A4 (by have:=Ah Fin.val h;dsimp at this;omega)))
      hxy:=fun i j hij=>by
       dsimp only[nx,ny];by_cases zl:i.val=0
       .
        rw[dif_pos zl];by_cases zc:j.val=0
        . exact absurd (A4 (zl.trans zc.symm)) hij
        .
         rw[dif_neg zc];by_cases zd:j.val=1
         . rw[dif_pos zd];exact vo
         . rw[dif_neg zd];exact (zb _ (zq j zc zd)).1
       .
        rw[dif_neg zl];by_cases zm:i.val=1
        .
         rw[dif_pos zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact vp.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . exact absurd (A4 (zm.trans zd.symm)) hij
          . rw[dif_neg zd];exact (zb _ (zq j zc zd)).2.2.1
        .
         rw[dif_neg zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact (zb _ (zp i zl zm)).2.1.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . rw[dif_pos zd];exact (zb _ (zp i zl zm)).2.2.2.symm
          . rw[dif_neg zd];exact zw _ _ (fun h=>hij (A4 (by have:=Ah Fin.val h;dsimp at this;omega)))
      hyy:=fun i j hij=>by
       dsimp only[ny];by_cases zl:i.val=0
       .
        rw[dif_pos zl];by_cases zc:j.val=0
        . exact absurd (A4 (zl.trans zc.symm)) hij
        .
         rw[dif_neg zc];by_cases zd:j.val=1
         . rw[dif_pos zd];exact ve
         . rw[dif_neg zd];exact (zb _ (zq j zc zd)).2.1
       .
        rw[dif_neg zl];by_cases zm:i.val=1
        .
         rw[dif_pos zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact ve.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . exact absurd (A4 (zm.trans zd.symm)) hij
          . rw[dif_neg zd];exact (zb _ (zq j zc zd)).2.2.2
        .
         rw[dif_neg zm];by_cases zc:j.val=0
         . rw[dif_pos zc];exact (zb _ (zq i zl zm)).2.1.symm
         .
          rw[dif_neg zc];by_cases zd:j.val=1
          . rw[dif_pos zd];exact (zb _ (zq i zl zm)).2.2.2.symm
          . rw[dif_neg zd];exact zZ _ _ (fun h=>hij (A4 (by have:=Ah Fin.val h;dsimp at this;omega)))
      hsq_x:=fun k=>by
       simp only[C3,AE,and_false,↓reduceIte,nx];split_ifs with h0 h1
       . exact vk
       . exact vm
       . have h:=zN ⟨k.val - 1,by omega⟩;rw[Aw (by intro hc;dsimp at hc;omega)] at h;exact h
      hsq_y:=fun k=>by
       simp only[C3,AE,and_false,↓reduceIte,ny];split_ifs with h0 h1
       . exact vl
       . exact vn
       . have h:=zO ⟨k.val - 1,by omega⟩;rw[Aw (by intro hc;dsimp at hc;omega)] at h;exact h
      hcard:=zD }⟩⟩
    ·
     refine ⟨m'+1,false,⟨{
      hm:=by omega
      x:=Fin.cons x₁ x'
      y:=Fin.cons y₁ y'
      hxy_same:=fun k=>Fin.cases zf zs k
      hxx:=fun i j hij=>by
       refine Fin.cases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
       . refine Fin.cases (fun h=>absurd rfl h) (fun j' _=>(zu j').1) j hij
       . refine Fin.cases (fun _=>(zu i').1.symm) (fun j' h=>zY i' j' (fun h'=>h (Ah Fin.succ h'))) j hij
      hxy:=fun i j hij=>by
       refine Fin.cases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
       . refine Fin.cases (fun h=>absurd rfl h) (fun j' _=>(zv j').1) j hij
       . refine Fin.cases (fun _=>(zu i').2.symm) (fun j' h=>zw i' j' (fun h'=>h (Ah Fin.succ h'))) j hij
      hyy:=fun i j hij=>by
       refine Fin.cases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
       . refine Fin.cases (fun h=>absurd rfl h) (fun j' _=>(zv j').2) j hij
       . refine Fin.cases (fun _=>(zv i').2.symm) (fun j' h=>zZ i' j' (fun h'=>h (Ah Fin.succ h'))) j hij
      hsq_x:=fun k=>Fin.cases (by simp[zh]) (fun j=>by
       have h:=zN j;simp[zP] at h ⊢;exact h) k
      hsq_y:=fun k=>Fin.cases (by simp[ze]) (fun j=>by
       have h:=zO j;simp[zP] at h ⊢;exact h) k
      hcard:=zD }⟩⟩
   ·
    rw[vr] at zh ze;simp only[Bg,Be] at zh ze
    refine ⟨m'+1,eps',⟨{
     hm:=by omega
     x:=Fin.snoc x' x₁
     y:=Fin.snoc y' y₁
     hxy_same:=fun k=>Fin.lastCases (by simp only[CS];exact zf)
      (fun i=>by simp only[BL];exact zs i) k
     hxx:=fun i j hij=>by
      refine Fin.lastCases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
      .
       refine Fin.lastCases (fun h=>absurd rfl h) (fun j' _=>by
        simp only[CS,BL];exact (zu j').1) j hij
      .
       refine Fin.lastCases (fun _=>by
        simp only[CS,BL];exact (zu i').1.symm)
        (fun j' h=>by
         simp only[BL]
         exact zY i' j' (fun h'=>h (Ah Fin.castSucc h'))) j hij
     hxy:=fun i j hij=>by
      refine Fin.lastCases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
      .
       refine Fin.lastCases (fun h=>absurd rfl h) (fun j' _=>by
        simp only[CS,BL];exact (zv j').1) j hij
      .
       refine Fin.lastCases (fun _=>by
        simp only[CS,BL];exact (zu i').2.symm)
        (fun j' h=>by
         simp only[BL]
         exact zw i' j' (fun h'=>h (Ah Fin.castSucc h'))) j hij
     hyy:=fun i j hij=>by
      refine Fin.lastCases (fun j hij=>?_) (fun i' j hij=>?_) i j hij
      .
       refine Fin.lastCases (fun h=>absurd rfl h) (fun j' _=>by
        simp only[CS,BL];exact (zv j').2) j hij
      .
       refine Fin.lastCases (fun _=>by
        simp only[CS,BL];exact (zv i').2.symm)
        (fun j' h=>by
         simp only[BL]
         exact zZ i' j' (fun h'=>h (Ah Fin.castSucc h'))) j hij
     hsq_x:=fun k=>Fin.lastCases (by
      have vB:1<=m':=B'.hm
      simp[CS,show m'≠0 by omega,zh]) (fun j=>by
      simpa[BL] using zN j) k
     hsq_y:=fun k=>Fin.lastCases (by
      have vB:1<=m':=B'.hm
      simp[CS,show m'≠0 by omega,ze]) (fun j=>by
      simpa[BL] using zO j) k
     hcard:=zD }⟩⟩
lemma Ye (p:ℕ) [Fact p.Prime]:∃ ι4:Qa p,ι4*ι4=-1:=by
 let f:Polynomial (Qa p):=Polynomial.X ^ 2+1;have za:f.degree≠0:=by
  have:f.degree=2:=by
   dsimp only[f];rw[Polynomial.degree_add_eq_left_of_degree_lt]
   . simp
   . simp
  rw[this];decide
 obtain ⟨r,hr⟩:=IsAlgClosed.exists_root f za;refine ⟨r,?_⟩;simp only[f,Polynomial.IsRoot,Polynomial.eval_add,DW,D3,Polynomial.eval_one] at hr;rw[E6] at hr;linear_combination hr
noncomputable def Qk {p:ℕ} [Fact p.Prime] {m:ℕ} (eps:Bool) (ι4:Qa p) (i:Fin m) : Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
 Matrix.diagonal fun s=>
  if i.val=0/\!eps then (if s i then -ι4 else ι4) else (if s i then (-1:Qa p) else 1)
noncomputable def Ql {p:ℕ} [Fact p.Prime] {m:ℕ} (eps:Bool) (i:Fin m) : Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
 Matrix.of fun s t=>
  if t=Function.update s i (!s i) then
   (if i.val=0/\!eps then (if s i then (1:Qa p) else -1) else 1)
  else 0
noncomputable def QD {p:ℕ} [Fact p.Prime] {m:ℕ} (hm:1<=m) (eps:Bool) : Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
 Matrix.of fun s t=>
  if ∀ i:Fin m,1<=i.val->s i=t i then
   if eps then (if s ⟨0,hm⟩=t ⟨0,hm⟩ then (1:Qa p) else 0)
   else (if s ⟨0,hm⟩=!t ⟨0,hm⟩ then (if s ⟨0,hm⟩ then 1 else -1) else 0)
  else 0
lemma QJ {p:ℕ} [Fact p.Prime] {m:ℕ} (za:Bool) {zb:Qa p} (zc:zb*zb=-1) : (∀ i:Fin m,Qk za zb i*Ql (p:=p) za i=(-1)*(Ql (p:=p) za i*Qk za zb i))/\ (∀ i j:Fin m,i≠j->Qk za zb i*Qk za zb j=Qk za zb j*Qk za zb i)/\ (∀ i j:Fin m,i≠j->Qk za zb i*Ql (p:=p) za j=Ql (p:=p) za j*Qk za zb i)/\ (∀ i j:Fin m,i≠j->Ql (p:=p) za i*Ql (p:=p) za j=Ql (p:=p) za j*Ql (p:=p) za i)/\ (∀ i:Fin m,Qk za zb i*Qk za zb i=if i.val=0/\!za then -1 else 1)/\ (∀ i:Fin m,Ql (p:=p) za i*Ql (p:=p) za i=if i.val=0/\!za then -1 else 1):=by
 have zd:∀ (s:Fin m->Bool) (i:Fin m),Function.update (Function.update s i (!s i)) i (!(!s i))=s:=(by intro s i;funext k;by_cases h:k=i <;> simp[h]);have zi:∀ (s:Fin m->Bool) (i j:Fin m),i≠j->Function.update (Function.update s i (!s i)) j (!s j)=Function.update (Function.update s j (!s j)) i (!s i):=by
  intro s i j zh;funext k;by_cases h1:k=i
  . subst h1;simp[zh]
  .
   by_cases h2:k=j
   . subst h2;simp[h1]
   . simp[h1,h2]
 have zj:∀ (i:Fin m) (s t:Fin m->Bool),Function.update s i (!s i)=Function.update t i (!t i)->s=t:=(by intro i s t h;have h1:=Ah (fun u=>Function.update u i (!u i)) h;have ze:Function.update s i (!s i) i=!s i:=AD i _ s;have zk:Function.update t i (!t i) i=!t i:=AD i _ t;rw[ze,zk,zd,zd] at h1;exact h1);refine ⟨?_,?_,?_,?_,?_,?_⟩;·
  intro i;ext s t;simp only[Qk,Ql,Cy,CU,Cp,AC,Bh,Ak];by_cases ht:t=Function.update s i (!s i)
  . subst ht;rw[Az rfl,AD];cases zg:za <;> by_cases hi:i.val=0 <;> cases ze:s i <;> simp[zg,hi,ze]
  . simp[ht]
 ·
  intro i j _;ext s t;simp only[Qk,C0,Bb]
 ·
  intro i j zh;ext s t;simp only[Qk,Ql,Cy,CU,Ak];by_cases ht:t=Function.update s j (!s j)
  . subst ht;rw[Az rfl,Bu zh];ring
  . simp[ht]
 ·
  intro i j zh;ext s t;simp only[Ql,Av,Ak];have hL:∑ u:Fin m->Bool,(if u=Function.update s i (!s i) then (if i.val=0/\!za then (if s i then (1:Qa p) else -1) else 1) else 0)*(if t=Function.update u j (!u j) then (if j.val=0/\!za then (if u j then (1:Qa p) else -1) else 1) else 0)=(if t=Function.update (Function.update s i (!s i)) j (!s j) then (if i.val=0/\!za then (if s i then (1:Qa p) else -1) else 1)*(if j.val=0/\!za then (if s j then (1:Qa p) else -1) else 1) else 0):=by
   rw[Ay (Function.update s i (!s i))]
   . rw[Az rfl,Bu zh.symm];split_ifs <;> ring
   . intro u _ hu;rw[Aw hu,Bm]
   . intro h;exact absurd (Ai _) h
  have hR:∑ u:Fin m->Bool,(if u=Function.update s j (!s j) then (if j.val=0/\!za then (if s j then (1:Qa p) else -1) else 1) else 0)*(if t=Function.update u i (!u i) then (if i.val=0/\!za then (if u i then (1:Qa p) else -1) else 1) else 0)=(if t=Function.update (Function.update s j (!s j)) i (!s i) then (if j.val=0/\!za then (if s j then (1:Qa p) else -1) else 1)*(if i.val=0/\!za then (if s i then (1:Qa p) else -1) else 1) else 0):=by
   rw[Ay (Function.update s j (!s j))]
   . rw[Az rfl,Bu zh];split_ifs <;> ring
   . intro u _ hu;rw[Aw hu,Bm]
   . intro h;exact absurd (Ai _) h
  rw[hL,hR,zi s i j zh];split_ifs <;> ring
 ·
  intro i;ext s t;simp only[Qk,C0];by_cases zf:s=t
  .
   subst zf;cases zg:za <;> by_cases hi:i.val=0 <;> cases ze:s i <;>
    simp[zg,hi,ze,Matrix.diagonal_apply_eq,BT,zc]
  . split_ifs <;> simp[Df _ zf,AH zf]
 ·
  intro i;ext s t;simp only[Ql,Av,Ak];rw[Ay (Function.update s i (!s i))]
  .
   rw[Az rfl,AD,zd];by_cases zf:s=t
   .
    subst zf;rw[Az rfl];cases zg:za <;> by_cases hi:i.val=0 <;> cases ze:s i <;>
     simp[zg,hi,ze,BT]
   . rw[Aw (Ne.symm zf),AS];split_ifs <;> simp[AH zf]
  . intro u _ hu;rw[Aw hu,Bm]
  . intro h;exact absurd (Ai _) h
lemma Q5 {p:ℕ} [Fact p.Prime] (zf:7<=p) {m:ℕ} (zb:Bool) {za:Qa p} (zc:za*za=-1) (A:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p)) (zd:∀ i:Fin m,A*Qk zb za i=Qk zb za i*A) (ze:∀ i:Fin m,A*Ql zb i=Ql zb i*A) : ∃ c:Qa p,A=c•1:=by
 have zh:(2:Qa p)≠0:=by
  intro h2;have zr:(2:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[C2,Bn];exact h2);have zq:p∣2:=(At 2 p).mp (by simpa using zr)
  have:=AP (by decide) zq;omega
 have zg:za≠0:=(by intro h0;rw[h0,Bm] at zc;exact neg_ne_zero.mpr DL zc.symm);have zl:∀ s t:Fin m->Bool,s≠t->A s t=0:=by
  intro s t zi;have zs:∃ i,s i≠t i:=by by_contra hall;push Not at hall;exact zi (funext hall)
  obtain ⟨i,hi⟩:=zs;have h1:=An (An (zd i) s) t;simp only[Qk,CU,Cy] at h1;by_cases h0:i.val=0/\!zb
  .
   rw[Az h0,Az h0] at h1;cases hs:s i <;> cases ht:t i <;> simp[hs,ht] at hi h1
   .
    have:(2*za)*A s t=0:=by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left (DM zh zg)
   .
    have:(2*za)*A s t=0:=by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (DM zh zg)
  .
   rw[Aw h0,Aw h0] at h1;cases hs:s i <;> cases ht:t i <;> simp[hs,ht] at hi h1
   .
    have:(2:Qa p)*A s t=0:=by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left zh
   .
    have:(2:Qa p)*A s t=0:=by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left zh
 have zj:∀ (s:Fin m->Bool) (i:Fin m),A (Function.update s i (!s i)) (Function.update s i (!s i))=A s s:=by
  intro s i;have h1:=An (An (ze i) s) (Function.update s i (!s i));simp only[Ql,Av,Ak] at h1;have hL:∑ u:Fin m->Bool,A s u*(if Function.update s i (!s i)=Function.update u i (!u i) then (if i.val=0/\!zb then (if u i then (1:Qa p) else -1) else 1) else 0)=A s s*(if i.val=0/\!zb then (if s i then (1:Qa p) else -1) else 1):=by
   rw[Ay s]
   . rw[Az rfl]
   . intro u _ hu;rw[zl s u hu.symm,Bm]
   . intro h;exact absurd (Ai s) h
  have hR:∑ u:Fin m->Bool,(if u=Function.update s i (!s i) then (if i.val=0/\!zb then (if s i then (1:Qa p) else -1) else 1) else 0)*A u (Function.update s i (!s i))=(if i.val=0/\!zb then (if s i then (1:Qa p) else -1) else 1)*A (Function.update s i (!s i)) (Function.update s i (!s i)):=by
   rw[Ay (Function.update s i (!s i))]
   . rw[Az rfl]
   . intro u _ hu;rw[Aw hu,Bm]
   . intro h;exact absurd (Ai _) h
  rw[hL,hR] at h1;by_cases h0:i.val=0/\!zb
  . rw[Az h0] at h1;cases zn:s i <;> simp[zn] at h1 ⊢ <;> exact h1.symm
  . rw[Aw h0] at h1;simpa using h1.symm
 let s₀:Fin m->Bool:=fun _=>false;have zm:∀ s:Fin m->Bool,A s s=A s₀ s₀:=by
  suffices h:∀ k:ℕ,∀ s:Fin m->Bool,(Finset.univ.filter fun i:Fin m=>s i=true).card=k->A s s=A s₀ s₀ from fun s=>h _ s rfl;intro k;induction k with
  | zero=>
   intro s hs;have zt:s=s₀:=by funext i;have zp:i∉Finset.univ.filter (fun j:Fin m=>s j=true):=(by rw[Finset.card_eq_zero.mp hs];simp);simp only[AL,Ai,B3] at zp;exact Bool.eq_false_iff.mpr zp
   rw[zt]
  | succ k ih=>
   intro s hs;have zu:(Finset.univ.filter fun i:Fin m=>s i=true).Nonempty:=
    Finset.card_pos.mp (by omega)
   obtain ⟨i,hi⟩:=zu;have zn:s i=true:=(Finset.mem_filter.mp hi).2;let s':=Function.update s i (!s i);have zk:(Finset.univ.filter fun j:Fin m=>s' j=true).card=k:=by
    have zo:Finset.univ.filter (fun j:Fin m=>s' j=true)=(Finset.univ.filter fun j:Fin m=>s j=true).erase i:=by
     ext j;simp only[AL,Ai,B3,Finset.mem_erase,s'];by_cases hj:j=i
     . subst hj;simp[zn]
     . simp[hj]
    rw[zo,Finset.card_erase_of_mem hi,hs];omega
   rw[<-zj s i];exact ih s' zk
 refine ⟨A s₀ s₀,?_⟩;ext s t;by_cases zi:s=t
 . subst zi;simp[BT,zm s]
 . simp[AH zi,zl s t zi]
lemma YM {p:ℕ} [Fact p.Prime] {m:ℕ} (hm:1<=m) (za:Bool) {zb:Qa p} (zc:zb*zb=-1) : (QD (p:=p) hm za)ᵀ=(if za then QD (p:=p) hm za else -QD (p:=p) hm za)/\ (QD (p:=p) hm za)*(QD (p:=p) hm za)=(if za then 1 else -1)/\ (∀ i:Fin m,(Qk za zb i)ᵀ*QD (p:=p) hm za*Qk za zb i=QD (p:=p) hm za)/\ (∀ i:Fin m,(Ql (p:=p) za i)ᵀ*QD (p:=p) hm za*Ql (p:=p) za i=QD (p:=p) hm za):=by
 let i0:Fin m:=⟨0,hm⟩;have zf:∀ (s:Fin m->Bool) (i:Fin m),Function.update (Function.update s i (!s i)) i (!(!s i))=s:=(by intro s i;funext k;by_cases h:k=i <;> simp[h]);refine ⟨?_,?_,?_,?_⟩;·
  ext s t;cases za
  .
   simp only[QD,AM,Ak,AE,Bj,Bh];by_cases zd:∀ i:Fin m,1<=i.val->s i=t i
   . have zg:∀ i:Fin m,1<=i.val->t i=s i:=fun i hi=>(zd i hi).symm;rw[Az zg,Az zd];cases hs:s i0 <;> cases ht:t i0 <;> simp[i0,hs,ht]
   . have zg:¬ ∀ i:Fin m,1<=i.val->t i=s i:=fun h=>zd fun i hi=>(h i hi).symm;rw[Aw zg,Aw zd,neg_zero]
  .
   simp only[QD,AM,Ak,Bg,Be];by_cases zd:∀ i:Fin m,1<=i.val->s i=t i
   . have zg:∀ i:Fin m,1<=i.val->t i=s i:=fun i hi=>(zd i hi).symm;rw[Az zg,Az zd];cases hs:s i0 <;> cases ht:t i0 <;> simp[i0,hs,ht]
   . have zg:¬ ∀ i:Fin m,1<=i.val->t i=s i:=fun h=>zd fun i hi=>(h i hi).symm;rw[Aw zg,Aw zd]
 ·
  cases za
  .
   ext s t;simp only[QD,Av,Ak,AE,Bj,Bh];let zj:Fin m->Bool:=Function.update s i0 (!s i0);rw[Ay zj]
   .
    have h1:∀ i:Fin m,1<=i.val->s i=zj i:=fun i hi=>by
     have zh:i≠i0:=fun h=>by subst h;simp[i0] at hi
     simp[zj,zh]
    rw[Az h1,show zj i0=!s i0 from AD i0 _ s,Bool.not_not,Az rfl];by_cases zi:s=t
    . subst zi;have h2:∀ i:Fin m,1<=i.val->zj i=s i:=fun i hi=>(h1 i hi).symm;rw[Az h2,Az rfl,BT];cases hs:s i0 <;> simp[i0,hs]
    .
     rw[AH zi,neg_zero];by_cases h2:∀ i:Fin m,1<=i.val->zj i=t i
     .
      rw[Az h2];have zv:s i0≠t i0:=by
       intro zp;apply zi;funext i;by_cases hi:i.val=0
       . have:i=i0:=A4 hi;rw[this,zp]
       . exact (h1 i (by omega)).trans (h2 i (by omega))
      have zm:(!s i0)≠!t ⟨0,hm⟩:=(by change (!s i0)≠!t i0;cases hs:s i0 <;> cases ht:t i0 <;> simp[hs,ht] at zv ⊢);rw[Aw zm,AS]
     . rw[Aw h2,AS]
   .
    intro u _ hu;by_cases h1:∀ i:Fin m,1<=i.val->s i=u i
    .
     rw[Az h1];have zm:s i0≠!u i0:=by
      intro zp;apply hu;funext i;by_cases hi:i.val=0
      . have:i=i0:=A4 hi;subst this;rw[show zj i0=!s i0 from AD i0 _ s,zp,Bool.not_not]
      .
       have zh:i≠i0:=fun h=>by subst h;exact hi rfl
       rw[show zj i=s i from Bu zh _ s,h1 i (by omega)]
     rw[Aw zm,Bm]
    . rw[Aw h1,Bm]
   . intro h;exact absurd (Ai zj) h
  .
   ext s t;have h1:QD (p:=p) hm true=1:=by
    ext a b;simp only[QD,Ak,Bg,Be];by_cases zu:a=b
    . subst zu;simp[BT]
    .
     rw[AH zu];by_cases zd:∀ i:Fin m,1<=i.val->a i=b i
     .
      rw[Az zd];have h0:a i0≠b i0:=by
       intro zp;apply zu;funext i;by_cases hi:i.val=0
       . rw[show i=i0 from A4 hi,zp]
       . exact zd i (by omega)
      rw[Aw h0]
     . rw[Aw zd]
   simp[h1]
 ·
  intro i;ext s t;have zx:(Qk za zb i)ᵀ=Qk za zb i:=Matrix.diagonal_transpose _;rw[zx];simp only[Qk,Cy,CU,QD,Ak];by_cases zd:∀ j:Fin m,1<=j.val->s j=t j
  .
   rw[Az zd];cases zw:za
   .
    simp only[Db,Bg,AE,and_true,Be,Bj];by_cases zk:s i0=!t i0
    .
     rw[Az zk];by_cases zl:i.val=0
     .
      have zn:i=i0:=A4 zl;subst zn;simp only[show i0.val=0 from rfl,↓reduceIte];cases hs:s i0 <;> cases ht:t i0 <;> simp[hs,ht] at zk ⊢ <;>
       (try linear_combination zc) <;> (try linear_combination -zc)
     . simp only[zl,↓reduceIte];have zr:s i=t i:=zd i (by omega);rw[zr];cases t i <;> cases s i0 <;> simp
    . rw[Aw zk];simp
   .
    simp only[C3,AE,Bg,and_false,Be,Bj];by_cases zk:s i0=t i0
    .
     rw[Az zk];have zr:s i=t i:=by
      by_cases zl:i.val=0
      . rw[show i=i0 from A4 zl,zk]
      . exact zd i (by omega)
     rw[zr];cases t i <;> simp
    . rw[Aw zk];simp
  . rw[Aw zd];simp
 ·
  intro i;ext s t;simp only[Ql,Av,AM,Ak];have zs:∀ u:Fin m->Bool,(∑ v:Fin m->Bool,(if s=Function.update v i (!v i) then (if i.val=0/\!za then (if v i then (1:Qa p) else -1) else 1) else 0)*QD (p:=p) hm za v u)=(if i.val=0/\!za then (if !s i then (1:Qa p) else -1) else 1)*QD (p:=p) hm za (Function.update s i (!s i)) u:=by
   intro u;rw[Ay (Function.update s i (!s i))]
   . rw[AD,zf,Az rfl]
   .
    intro v _ hv;rw[Aw]
    . exact Bm _
    . intro hs;apply hv;rw[hs,AD,zf]
   . intro h;exact absurd (Ai _) h
  simp only[zs];rw[Ay (Function.update t i (!t i))]
  .
   rw[AD,zf,Az rfl];dsimp only[QD];simp only[Ak];by_cases zl:i.val=0
   .
    have zn:i=i0:=A4 zl;subst zn;have ze:(∀ j:Fin m,1<=j.val->Function.update s i0 (!s i0) j=Function.update t i0 (!t i0) j)↔(∀ j:Fin m,1<=j.val->s j=t j):=by
     constructor <;> intro h j hj <;>
      have zh:j≠i0:=fun hc=>by subst hc;simp[i0] at hj
     . simpa[zh] using h j hj
     . simpa[zh] using h j hj
    by_cases zd:∀ j:Fin m,1<=j.val->s j=t j
    .
     rw[Az (ze.mpr zd),Az zd,AD,AD];cases zw:za
     . simp only[Db,Bg,AE,and_true,Be,Bj,show i0.val=0 from rfl];cases hs:s i0 <;> cases ht:t i0 <;> simp
     . simp only[C3,AE,Bg,and_false,Be,Bj];cases hs:s i0 <;> cases ht:t i0 <;> simp
    . rw[Aw (mt ze.mp zd),Aw zd];ring
   .
    have zt:i≠i0:=fun hc=>zl (Ah Fin.val hc);have ze:(∀ j:Fin m,1<=j.val->Function.update s i (!s i) j=Function.update t i (!t i) j)↔(∀ j:Fin m,1<=j.val->s j=t j):=by
     constructor <;> intro h j hj
     .
      by_cases zo:j=i
      . subst zo;have h1:=h j hj;simp at h1;exact h1
      . simpa[zo] using h j hj
     .
      by_cases zo:j=i
      . subst zo;simp[h j hj]
      . simpa[zo] using h j hj
    by_cases zd:∀ j:Fin m,1<=j.val->s j=t j
    . have zq:¬ (i.val=0/\(!za)=true):=fun h=>zl h.1;rw[Az (ze.mpr zd),Az zd,Bu zt.symm,Bu zt.symm,Aw zq,Aw zq,AA,AK]
    . rw[Aw (mt ze.mp zd),Aw zd];ring
  . intro u _ hu;rw[Aw (show ¬ t=Function.update u i (!u i) from fun ht=>hu (by rw[ht,AD,zf]))];exact AS _
  . intro h;exact absurd (Ai _) h
lemma Wj {p:ℕ} [Fact p.Prime] (zf:7<=p)
  {R:Type*} [Group R] [Finite R] {z:R} {m:ℕ} {za:Bool} (ze:Qn R z) (B:Qm R z m za)
  {zb:Qa p} (zc:zb*zb=-1)
  {n:ℕ} (ρ:R→*Matrix (Fin n) (Fin n) (Qa p)) (zd:ρ z=-1) :
  let rels:=QJ (p:=p) (m:=m) za zc
  let ρX:R→*Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
   QA ze B (-1) (Qk za zb) (Ql za)
    (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2
  ∃ (k:ℕ) (e:(Fin n->Qa p)≃ₗ[Qa p] Matrix (Fin m->Bool) (Fin k) (Qa p)),∀ (r:R) (v:Fin n->Qa p),e (ρ r*ᵥv)=ρX r*e v:=by
 intro rels ρX;have zU:(2:Qa p)≠0:=by
  intro h2;have vn:(2:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[C2,Bn];exact h2);have vd:p∣2:=(At 2 p).mp (by simpa using vn)
  have:=AP (by decide) vd;omega
 have zP:zb≠0:=(by intro h0;rw[h0,Bm] at zc;exact neg_ne_zero.mpr DL zc.symm);let μ (i:Fin m) (b:Bool):Qa p:=
  if i.val=0/\!za then (if b then -zb else zb) else (if b then -1 else 1)
 have zV:∀ i b,μ i b*μ i b=if i.val=0/\!za then -1 else 1:=fun i b=>by
  dsimp only[μ];cases zn:za <;> by_cases hi:i.val=0 <;> cases b <;> simp[zn,hi,zc]
 have zi:∀ i b,μ i b≠0:=fun i b=>by
  dsimp only[μ];cases zn:za <;> by_cases hi:i.val=0 <;> cases b <;> simp[zn,hi,zP]
 have zq:∀ i b,μ i (!b)=-μ i b:=fun i b=>by
  dsimp only[μ];cases zn:za <;> by_cases hi:i.val=0 <;> cases b <;> simp[zn,hi]
 have zQ:∀ i:Fin m,ρ (B.x i)*ρ (B.x i)=if i.val=0/\!za then -1 else 1:=fun i=>by
  rw[<-AF,B.hsq_x i];split_ifs <;> simp[zd]
 have zR:∀ i:Fin m,ρ (B.y i)*ρ (B.y i)=if i.val=0/\!za then -1 else 1:=fun i=>by
  rw[<-AF,B.hsq_y i];split_ifs <;> simp[zd]
 have zN:∀ i j:Fin m,ρ (B.x i)*ρ (B.x j)=ρ (B.x j)*ρ (B.x i):=fun i j=>by
  by_cases h:i=j
  . subst h;rfl
  . rw[<-AF,B.hxx i j h,AF]
 have zz:∀ i:Fin m,ρ (B.x i)*ρ (B.y i)=-(ρ (B.y i)*ρ (B.x i)):=fun i=>by
  rw[<-AF,B.hxy_same i,AF,zd,AF];simp
 have zA:∀ i j:Fin m,i≠j->ρ (B.x i)*ρ (B.y j)=ρ (B.y j)*ρ (B.x i):=fun i j h=>by
  rw[<-AF,B.hxy i j h,AF]
 have zo:∀ i j:Fin m,i≠j->ρ (B.y i)*ρ (B.y j)=ρ (B.y j)*ρ (B.y i):=fun i j h=>by
  rw[<-AF,B.hyy i j h,AF]
 let E (i:Fin m) (b:Bool):Matrix (Fin n) (Fin n) (Qa p):=
  (2:Qa p)⁻¹•(1+(μ i b)⁻¹•ρ (B.x i))
 have zW:∀ i,∑ b:Bool,E i b=1:=fun i=>by
  rw[Ea];dsimp only[E];have vo:μ i true=-μ i false:=zq i false;rw[<-Eq,vo,inv_neg,neg_smul];have ve:(1+-((μ i false)⁻¹•ρ (B.x i)))+(1+(μ i false)⁻¹•ρ (B.x i))=(2:Qa p)•(1:Matrix (Fin n) (Fin n) (Qa p)):=(by ext a b;simp[EL];ring);rw[ve,AR,inv_mul_cancel₀ zU,Bx]
 have zX:∀ i b,ρ (B.x i)*E i b=μ i b•E i b:=fun i b=>by
  dsimp only[E];rw[Ao,BH,As,Ao,zQ i,smul_comm];congr 1;have vp:(μ i b)⁻¹•(if i.val=0/\!za then (-1:Matrix (Fin n) (Fin n) (Qa p)) else 1)=μ i b•(1:Matrix (Fin n) (Fin n) (Qa p)):=by
   have zY:=zV i b;have zH:(μ i b)⁻¹*(if i.val=0/\!za then (-1:Qa p) else 1)=μ i b:=(by rw[<-zY,<-Ad,inv_mul_cancel₀ (zi i b),AA]);split_ifs at zH ⊢
   . rw[<-neg_one_smul (Qa p) (1:Matrix (Fin n) (Fin n) (Qa p)),AR,zH]
   . simpa using Ah (·•(1:Matrix (Fin n) (Fin n) (Qa p))) zH
  rw[vp,Eq,AR,mul_inv_cancel₀ (zi i b),Bx,DQ]
 have zu:∀ i b₁ b₂,E i b₁*E i b₂=if b₁=b₂ then E i b₁ else 0:=fun i b₁ b₂=>by
  conv_lhs=>arg 1;dsimp only[E]
  rw[Ar,BQ,AC,Ar,zX i b₂,AR];have z6:E i b₂+((μ i b₁)⁻¹*μ i b₂)•E i b₂=(1+(μ i b₁)⁻¹*μ i b₂)•E i b₂:=(by rw[Fc,Bx]);rw[z6,AR];by_cases h:b₁=b₂
  . subst h;rw[Az rfl,inv_mul_cancel₀ (zi i b₁),show (1:Qa p)+1=2 by ring,inv_mul_cancel₀ zU,Bx]
  .
   rw[Aw h];have vf:b₂=!b₁:=by cases b₁ <;> cases b₂ <;> simp at h ⊢
   rw[vf,zq,mul_neg,inv_mul_cancel₀ (zi i b₁),add_neg_cancel,AS,Dl]
 have zv:∀ i j b₁ b₂,E i b₁*E j b₂=E j b₂*E i b₁:=fun i j b₁ b₂=>by
  dsimp only[E];rw[Ar,Ao,Ar,Ao];congr 1;congr 1;simp only[BQ,BH,AC,As,Ar,Ao,Eq,AR,zN i j,Bb];abel
 let P (s:Fin m->Bool):Matrix (Fin n) (Fin n) (Qa p):=Qf fun i=>E i (s i);have zZ:∑ s:Fin m->Bool,P s=1:=(by dsimp only[P];rw[WM];have h1:(fun i:Fin m=>∑ b:Bool,E i b)=fun _=>1:=funext zW;rw[h1];exact YL);have zw:∀ s t,P s*P t=if s=t then P s else 0:=fun s t=>by
  dsimp only[P];rw[QG _ _ (fun i j=>zv i j (s i) (t j))];by_cases h:s=t
  . subst h;rw[Az rfl];congr 1;funext i;rw[zu,Az rfl]
  .
   rw[Aw h];have vq:∃ i,s i≠t i:=by by_contra hall;push Not at hall;exact h (funext hall)
   obtain ⟨i₀,zr⟩:=vq;exact QS _ i₀ (by rw[zu,Aw zr])
 have vg:∀ (i:Fin m) (s:Fin m->Bool),ρ (B.x i)*P s=μ i (s i)•P s:=fun i s=>
  QV (ρ (B.x i)) _ (fun a b=>zv a b (s a) (s b))
   (fun j=>by
    dsimp only[E];simp only[Ao,Ar,BH,BQ,As,AC,zN i j])
   i _ (zX i (s i))
 have vh:∀ (i j:Fin m) (b:Bool),ρ (B.y i)*E j b=E j (if j=i then !b else b)*ρ (B.y i):=fun i j b=>by
  dsimp only[E];rw[Ao,Ar,BH,BQ,As,AC,Ao,Ar];congr 1;congr 1;by_cases zx:j=i
  . subst zx;rw[Az rfl,zq,inv_neg,neg_smul];have h1:ρ (B.y j)*ρ (B.x j)=-(ρ (B.x j)*ρ (B.y j)):=(by rw[zz j,Dp]);rw[h1,smul_neg]
  . rw[Aw zx,(zA j i zx).symm]
 have z0:∀ (i:Fin m) (s:Fin m->Bool),ρ (B.y i)*P s=P (Function.update s i (!s i))*ρ (B.y i):=by
  intro i s;have z1:∃ zt:Matrix (Fin n) (Fin n) (Qa p),ρ (B.y i)*zt=1/\zt*ρ (B.y i)=1:=
   ⟨ρ (B.y i)⁻¹,by rw[<-AF,By,BI],by rw[<-AF,CK,BI]⟩
  obtain ⟨zt,h1,h2⟩:=z1;suffices h:ρ (B.y i)*P s*zt=P (Function.update s i (!s i)) by
   calc ρ (B.y i)*P s=(ρ (B.y i)*P s*zt)*ρ (B.y i):=by rw[Af,h2,As]
    _ = P (Function.update s i (!s i))*ρ (B.y i):=by rw[h]
  dsimp only[P];rw[WD _ _ h1 h2];congr 1;funext j;rw[vh i j (s j),Af,h1,As];by_cases zx:j=i
  . subst zx;simp
  . simp[zx]
 let Yw (s:Fin m->Bool):Matrix (Fin n) (Fin n) (Qa p):=
  Qb fun i=>if s i then ρ (B.y i) else 1
 let zg (s:Fin m->Bool):Matrix (Fin n) (Fin n) (Qa p):=
  Qb fun i=>if s i then ρ (B.y i)⁻¹ else 1
 have zl:∀ s,Yw s*zg s=1:=fun s=>by
  dsimp only[Yw,zg];rw[QL]
  . exact QB _ (fun i=>by cases s i <;> simp[<-AF])
  .
   intro i j z4;cases s i <;> cases s j <;> simp;rw[<-AF,<-AF];congr 1;have zB:=B.hyy i j z4
   calc B.y i*(B.y j)⁻¹=(B.y j)⁻¹*(B.y j*B.y i)*(B.y j)⁻¹:=by group
    _ = (B.y j)⁻¹*(B.y i*B.y j)*(B.y j)⁻¹:=by rw[zB]
    _ = (B.y j)⁻¹*B.y i:=by group
 have zm:∀ s,zg s*Yw s=1:=fun s=>by
  dsimp only[Yw,zg];rw[QL]
  . exact QB _ (fun i=>by cases s i <;> simp[<-AF])
  .
   intro i j z4;cases s i <;> cases s j <;> simp;rw[<-AF,<-AF];congr 1;have zB:=B.hyy j i z4.symm
   calc (B.y i)⁻¹*B.y j=(B.y i)⁻¹*(B.y j*B.y i)*(B.y i)⁻¹:=by group
    _ = (B.y i)⁻¹*(B.y i*B.y j)*(B.y i)⁻¹:=by rw[zB]
    _ = B.y j*(B.y i)⁻¹:=by group
 let s₀:Fin m->Bool:=fun _=>false;have zp:∀ s:Fin m->Bool,Yw s*P s₀=P s*Yw s:=by
  intro s;have vu:∀ (t:Fin m->Bool) (i:Fin m) (b:Bool),(if b then ρ (B.y i) else 1)*P t=P (if b then Function.update t i (!t i) else t)*(if b then ρ (B.y i) else 1):=(by intro t i b;cases b <;> simp[z0]);have vi:∀ (s:Fin m->Bool) (t:Fin m->Bool),Yw s*P t=P (fun i=>xor (s i) (t i))*Yw s:=by
   intro s;suffices h:∀ k:ℕ,∀ s:Fin m->Bool,(Finset.univ.filter fun i:Fin m=>s i=true).card=k->∀ t,Yw s*P t=P (fun i=>xor (s i) (t i))*Yw s from fun t=>h _ s rfl t;intro k;induction k with
   | zero=>
    intro s hs t;have vr:s=s₀:=by funext i;have vb:i∉Finset.univ.filter (fun j:Fin m=>s j=true):=(by rw[Finset.card_eq_zero.mp hs];simp);simp only[AL,Ai,B3] at vb;exact Bool.eq_false_iff.mpr vb
    subst vr;have h1:Yw s₀=1:=QB _ (fun _=>by simp[s₀]);rw[h1,AC,As];congr 1;funext i;simp[s₀]
   | succ k ih=>
    intro s hs t;obtain ⟨i₀,zr⟩:=Finset.card_pos.mp (show 0 < (Finset.univ.filter fun i:Fin m=>s i=true).card by omega);have z2:s i₀=true:=(Finset.mem_filter.mp zr).2;let s':=Function.update s i₀ false;have zI:(Finset.univ.filter fun j:Fin m=>s' j=true).card=k:=by
     have hf:Finset.univ.filter (fun j:Fin m=>s' j=true)=(Finset.univ.filter fun j:Fin m=>s j=true).erase i₀:=by
      ext j;simp only[AL,Ai,B3,Finset.mem_erase,s'];by_cases h:j=i₀
      . subst h;simp
      . simp[h]
     rw[hf,Finset.card_erase_of_mem zr,hs];omega
    have zG:Yw s=ρ (B.y i₀)*Yw s':=by
     dsimp only[Yw];have zs:(fun i:Fin m=>if s i then ρ (B.y i) else 1)=fun i=>(if i=i₀ then ρ (B.y i₀) else 1)*(if s' i then ρ (B.y i) else 1):=by
      funext i;by_cases h:i=i₀
      . subst h;simp[z2,s']
      . simp[h,s']
     rw[zs,<-QL]
     . congr 1;exact QN (fun _=>ρ (B.y i₀)) i₀
     .
      intro a b z5;by_cases ha:a=i₀
      . subst ha;rw[Az rfl];cases s' b <;> simp[zo a b z5]
      . rw[Aw ha,AC,As]
    rw[zG,Af,ih s' zI t,<-Af,z0,Af];congr 2;funext j;by_cases h:j=i₀
    . subst h;simp[z2,s']
    . simp[h,s']
  simpa[s₀] using vi s s₀
 let HW:Submodule (Qa p) (Fin n->Qa p):=LinearMap.range (Matrix.toLin' (P s₀));let k:=Module.finrank (Qa p) HW;let zh:Module.Basis (Fin k) (Qa p) HW:=Module.finBasis (Qa p) HW;have zk:∀ x:HW,P s₀*ᵥx.1=x.1:=fun x=>by
  obtain ⟨u,hu⟩:=x.2;rw[<-hu,Aj,Ac,zw s₀ s₀,Az rfl]
 let Ψ:Matrix (Fin m->Bool) (Fin k) (Qa p)→ₗ[Qa p] (Fin n->Qa p):=
  {toFun:=fun A=>∑ s:Fin m->Bool,∑ j:Fin k,A s j•(Yw s*ᵥ(zh j).1)
   map_add':=fun A₁ A₂=>by
    simp only[EY,Fc,Bt]
   map_smul':=fun c A=>by
    simp only[A2,Am,DE,BC,AR] }
 let Φ:(Fin n->Qa p)→ₗ[Qa p] Matrix (Fin m->Bool) (Fin k) (Qa p):=
  {toFun:=fun v=>Matrix.of fun s j=>zh.equivFun ⟨P s₀*ᵥ(zg s*ᵥv),⟨zg s*ᵥv,rfl⟩⟩ j
   map_add':=fun u v=>by
    ext s j;have h1:(⟨P s₀*ᵥ(zg s*ᵥ(u+v)),⟨_,rfl⟩⟩:HW)=
      ⟨P s₀*ᵥ(zg s*ᵥu),⟨_,rfl⟩⟩+⟨P s₀*ᵥ(zg s*ᵥv),⟨_,rfl⟩⟩:=
     Ae (by simp[A3])
    simp only[Ak,EY];rw[h1,EN];rfl
   map_smul':=fun c v=>by
    ext s j;have h1:(⟨P s₀*ᵥ(zg s*ᵥ(c•v)),⟨_,rfl⟩⟩:HW)=c•⟨P s₀*ᵥ(zg s*ᵥv),⟨_,rfl⟩⟩:=
     Ae (by simp[Al])
    simp only[Ak,A2,Am,DE];rw[h1,Bd];rfl }
 have zC:∀ v:Fin n->Qa p,Ψ (Φ v)=v:=by
  intro v;change ∑ s:Fin m->Bool,∑ j:Fin k,(zh.equivFun ⟨P s₀*ᵥ(zg s*ᵥv),⟨zg s*ᵥv,rfl⟩⟩ j)•(Yw s*ᵥ(zh j).1)=v;have z7:∀ s:Fin m->Bool,∑ j:Fin k,(zh.equivFun ⟨P s₀*ᵥ(zg s*ᵥv),⟨zg s*ᵥv,rfl⟩⟩ j)•(Yw s*ᵥ(zh j).1)=P s*ᵥv:=by
   intro s;have zD:=Ah Subtype.val (zh.sum_repr ⟨P s₀*ᵥ(zg s*ᵥv),⟨zg s*ᵥv,rfl⟩⟩);rw[B4] at zD;simp only[Bp] at zD
   calc ∑ j:Fin k,(zh.equivFun ⟨P s₀*ᵥ(zg s*ᵥv),_⟩ j)•(Yw s*ᵥ(zh j).1)
     = Yw s*ᵥ(∑ j:Fin k,(zh.equivFun ⟨P s₀*ᵥ(zg s*ᵥv),_⟩ j)•(zh j).1):=by rw[AJ];refine Ag rfl fun j _=>(Al _ _ _).symm
    _ = Yw s*ᵥ(P s₀*ᵥ(zg s*ᵥv)):=by simp only[Module.Basis.equivFun_apply];rw[zD]
    _ = (Yw s*P s₀*zg s)*ᵥv:=by simp only[Ac,Af]
    _ = P s*ᵥv:=by rw[zp s,Af,zl s,As]
  calc ∑ s:Fin m->Bool,∑ j:Fin k,_=∑ s:Fin m->Bool,P s*ᵥv:=
     Ag rfl fun s _=>z7 s
   _ = (∑ s:Fin m->Bool,P s)*ᵥv:=by funext r;simp only[AQ,Matrix.mulVec,dotProduct,BR,Bo];exact AY
   _ = v:=by rw[zZ,AN]
 have z3:∀ A:Matrix (Fin m->Bool) (Fin k) (Qa p),Φ (Ψ A)=A:=by
  intro A;ext s j;dsimp only[Φ,Ψ,LinearMap.coe_mk,AddHom.coe_mk];simp only[Ak];have vj:P s₀*ᵥ(zg s*ᵥ∑ t:Fin m->Bool,∑ r:Fin k,A t r•(Yw t*ᵥ(zh r).1))=∑ r:Fin k,A s r•(zh r).1:=by
   rw[AJ,AJ,Ay s]
   . rw[AJ,AJ];refine Ag rfl fun r _=>?_;rw[Al,Al,Ac,Ac,Af,zm s,As,zk]
   .
    intro t _ vt;rw[AJ,AJ];refine A1 fun r _=>?_;rw[Al,Al,<-zk (zh r),Ac,Ac,Ac,Af (P s₀*zg s),zp t];have h0:P s₀*zg s*(P t*Yw t)=0:=by
     have zS:P s₀*zg s=zg s*P s:=by
      calc P s₀*zg s=(zg s*Yw s)*P s₀*zg s:=by rw[zm s,AC]
       _ = zg s*(Yw s*P s₀)*zg s:=by simp only[Af]
       _ = zg s*P s*(Yw s*zg s):=by rw[zp s];simp only[Af]
       _ = zg s*P s:=by rw[zl s,As]
     calc P s₀*zg s*(P t*Yw t)=zg s*(P s*P t)*Yw t:=by
             rw[zS];simp only[Af]
           _ = 0:=by rw[zw s t,Aw (Ne.symm vt),CZ,Ce]
    rw[h0,BF,smul_zero]
   . intro h;exact absurd (Ai s) h
  have vk:(⟨P s₀*ᵥ(zg s*ᵥ∑ t,∑ r,A t r•(Yw t*ᵥ(zh r).1)),⟨_,rfl⟩⟩:HW)=∑ r:Fin k,A s r•zh r:=Ae (by simpa[B4,Bp] using vj);rw[vk,Ba];simp only[AQ,Bd,AX,Am,Module.Basis.equivFun_self,DS,Ca,AK,AS,A8,Ai,↓reduceIte]
 let e:(Fin n->Qa p)≃ₗ[Qa p] Matrix (Fin m->Bool) (Fin k) (Qa p):=
  {toLinearMap:=Φ
   invFun:=Ψ
   left_inv:=zC
   right_inv:=z3 }
 have zE:∀ (r:R),(∀ A,ρ r*ᵥΨ A=Ψ (ρX r*A))->∀ v,e (ρ r*ᵥv)=ρX r*e v:=fun r hA v=>by
  apply e.symm.injective;change Ψ (Φ (ρ r*ᵥv))=Ψ (ρX r*Φ v);rw[zC,<-hA (Φ v),zC]
 have zJ:∀ A,ρ z*ᵥΨ A=Ψ (ρX z*A):=fun A=>by
  rw[zd,Yl];simp[Ψ,BJ,Cp,Bh,Dy]
 have zK:∀ i A,ρ (B.x i)*ᵥΨ A=Ψ (ρX (B.x i)*A):=fun i A=>by
  rw[Q7];change ρ (B.x i)*ᵥ∑ s,∑ j,A s j•(Yw s*ᵥ(zh j).1)=∑ s,∑ j,(Qk za zb i*A) s j•(Yw s*ᵥ(zh j).1);rw[AJ];refine Ag rfl fun s _=>?_;rw[AJ];refine Ag rfl fun j _=>?_;rw[Al,<-zk (zh j),Ac,Ac,Af (ρ (B.x i)),zp s,<-Af,vg i s,Ar,Bv,AR,<- zp s,<-Ac,zk];congr 1;simp only[Qk,Cy,μ];ring
 have zL:∀ i A,ρ (B.y i)*ᵥΨ A=Ψ (ρX (B.y i)*A):=fun i A=>by
  rw[Wd];change ρ (B.y i)*ᵥ∑ s,∑ j,A s j•(Yw s*ᵥ(zh j).1)=∑ s,∑ j,(Ql (p:=p) za i*A) s j•(Yw s*ᵥ(zh j).1);rw[AJ];let zj:(Fin m->Bool) ≃ (Fin m->Bool):=
   {toFun:=fun s=>Function.update s i (!s i)
    invFun:=fun s=>Function.update s i (!s i)
    left_inv:=fun s=>by funext r;by_cases h:r=i <;> simp[h]
    right_inv:=fun s=>by funext r;by_cases h:r=i <;> simp[h] }
  rw[<-AO zj _ _ (fun _=>rfl)];refine Ag rfl fun s _=>?_;rw[AJ];refine Ag rfl fun j _=>?_;rw[Al,Ac];let u:Fin m->Bool:=zj s;have vs:Function.update u i (!u i)=s:=zj.left_inv s;have z8:ρ (B.y i)*Yw u=(if u i then (if i.val=0/\!za then (-1:Qa p) else 1) else 1)•Yw s:=by
   dsimp only[Yw];have zT:ρ (B.y i)=Qb (fun r:Fin m=>if r=i then ρ (B.y i) else 1):=
    (QN (fun _=>ρ (B.y i)) i).symm
   rw[zT,QL]
   .
    have vl:(fun r:Fin m=>(if r=i then ρ (B.y i) else 1)*(if u r then ρ (B.y r) else 1))=fun r=>(if r=i then (if u i then (if i.val=0/\!za then (-1:Qa p) else 1) else 1) else 1)•(if Function.update u i (!u i) r then ρ (B.y r) else 1):=by
     funext r;by_cases zO:r=i
     .
      subst zO;simp only[↓reduceIte,AD];cases vc:u r
      . simp
      . simp only[↓reduceIte,C3,AE,Bj,zR r];split_ifs <;> simp
     . simp[zO]
    rw[vl,vs];have z9:∀ {q:ℕ} (c:Fin q->Qa p) (M:Fin q->Matrix (Fin n) (Fin n) (Qa p)) (j:Fin q),(∀ r,r≠j->c r=1)->Qb (fun r=>c r•M r)=c j•Qb M:=by
     intro q c M j hc;induction q with
     | zero=>exact Ez j
     | succ q ihq=>
      revert hc;refine Fin.cases ?_ ?_ j
      .
       intro hc;simp only[Qb];have va:(fun r:Fin q=>c r.succ•M r.succ)=fun r=>M r.succ:=
        funext fun r=>by rw[hc r.succ (CJ r),Bx]
       rw[va,Ar]
      . intro j' hc;simp only[Qb,hc 0 (CJ j').symm,Bx,ihq (fun r=>c r.succ) (fun r=>M r.succ) j' (fun r hr=>hc r.succ (fun h=>hr (D0 _ h))),Ao]
    rw[z9 _ _ i (fun r hr=>Aw hr),Az rfl]
   .
    intro a b z5;by_cases ha:a=i
    . subst ha;rw[Az rfl];cases u b <;> simp[zo a b z5]
    . rw[Aw ha,AC,As]
  change A u j•(ρ (B.y i)*Yw u)*ᵥ↑(zh j)=(Ql (p:=p) za i*A) s j•Yw s*ᵥ↑(zh j);rw[z8,Bv,AR];congr 1;have zM:(Ql (p:=p) za i*A) s j=(if u i then (if i.val=0/\!za then (-1:Qa p) else 1) else 1)*A u j:=by
   simp only[Ql,Av,Ak];rw[Ay u]
   . have vc:u i=!s i:=AD i _ s;change (if u=u then (if i.val=0/\!za then (if s i then (1:Qa p) else -1) else 1) else 0)*A u j=_;rw[Az rfl,vc];cases zn:za <;> by_cases hi:i.val=0 <;> cases zy:s i <;> simp[zn,hi,zy]
   . intro t _ ht;change (if t=u then _ else 0)*A t j=0;rw[Aw ht,Bm]
   . intro h;exact absurd (Ai u) h
  rw[zM,Bb]
 have zF:∀ r:R,∀ A,ρ r*ᵥΨ A=Ψ (ρX r*A):=by
  have zs:∀ r₁ r₂:R,(∀ A,ρ r₁*ᵥΨ A=Ψ (ρX r₁*A))->(∀ A,ρ r₂*ᵥΨ A=Ψ (ρX r₂*A))->∀ A,ρ (r₁*r₂)*ᵥΨ A=Ψ (ρX (r₁*r₂)*A):=fun r₁ r₂ h1 h2 A=>by
   rw[AF,AF,<-Ac,h2,h1,Af]
  have h1:∀ A,ρ (1:R)*ᵥΨ A=Ψ (ρX 1*A):=fun A=>by simp
  have vm:∀ {q:ℕ} (f:Fin q->R),(∀ i A,ρ (f i)*ᵥΨ A=Ψ (ρX (f i)*A))->∀ A,ρ (Qb f)*ᵥΨ A=Ψ (ρX (Qb f)*A):=by
   intro q f hf;induction q with
   | zero=>exact h1
   | succ q ih=>exact zs _ _ (hf 0) (ih (fun i=>f i.succ) (fun i=>hf i.succ))
  intro r;obtain ⟨⟨c,a,b⟩,hr⟩:=(Qe ze B).surjective r;rw[<-hr];change ∀ A,ρ (Qc z B.x B.y c a b)*ᵥΨ A=Ψ (ρX (Qc z B.x B.y c a b)*A);dsimp only[Qc];refine zs _ _ (by cases c;exacts [h1,zJ]) (vm _ fun i=>zs _ _ ?_ ?_)
  . cases a i;exacts [h1,zK i]
  . cases b i;exacts [h1,zL i]
 exact ⟨k,e,fun r v=>zE r (zF r) v⟩
set_option maxHeartbeats 800000 in
lemma Wk {p:ℕ} [Fact p.Prime] (zc:7<=p)
  {N:ℕ} {zd:0 < N} {zf:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zd zf ι) (ze:(⟨Qd S.n p,S.negOne_mem⟩:S.L)∈O2 S.L) (zb:Qn (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,ze⟩)
  {m:ℕ} {za:Bool} (B:Qm (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,ze⟩ m za) : za=false/\S.n=2 ^ m/\ (∀ g:S.L,(∀ r∈O2 S.L,g*r=r*g)->g.1=1\/g.1=Qd S.n p)/\ (∃ (ι4:Qa p) (hι4:ι4*ι4=-1) (e:(Fin S.n->Qa p)≃ₗ[Qa p] ((Fin m->Bool)->Qa p)) (c₀:Qa p), c₀≠0/\ (∀ (r:O2 S.L) (v:Fin S.n->Qa p), e ((r.1.1.val.map (algebraMap (ZMod p) (Qa p)))*ᵥv)=
        let rels:=QJ (p:=p) (m:=m) za hι4
        QA zb B (-1) (Qk za ι4) (Ql za)
          (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥe v)/\
    (∀ u v:Fin S.n->Qa p,dotProduct u ((S.B.map (algebraMap (ZMod p) (Qa p)))*ᵥv)=c₀*dotProduct (e u) (QD B.hm za*ᵥe v))):=by
 classical
 let zk:=algebraMap (ZMod p) (Qa p);let R:=O2 S.L;haveI hR_norm:R.Normal:=QI S.L;let zR:R:=⟨⟨Qd S.n p,S.negOne_mem⟩,ze⟩;obtain ⟨ι4,hι4⟩:=Ye p;let rels:=QJ (p:=p) (m:=m) za hι4;let zg:R→*Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
  QA zb B (-1) (Qk za ι4) (Ql za)
   (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2
 have va:zg zR=-1:=Yl zb B (-1) (Qk za ι4) (Ql za)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2
 have vD:∀ i:Fin m,zg (B.x i)=Qk za ι4 i:=fun i=>Q7 zb B (-1) (Qk za ι4) (Ql za)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 i
 have vE:∀ i:Fin m,zg (B.y i)=Ql za i:=fun i=>Wd zb B (-1) (Qk za ι4) (Ql za)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 i
 let ρ:R→*Matrix (Fin S.n) (Fin S.n) (Qa p):=
  {toFun:=fun r=>r.1.1.val.map zk
   map_one':=by ext a b;simp[BG]
   map_mul':=fun r₁ r₂=>Aq }
 have vS:ρ zR=-1:=by
  ext a b;by_cases h:a=b
  . subst h;simp[ρ,zR,Qd]
  . simp[ρ,zR,Qd,AH h]
 obtain ⟨k,e,zr⟩:=Wj zc zb B hι4 ρ vS;have zZ:S.n=2 ^ m*k:=by have h1:=e.finrank_eq;rw[CQ,AW] at h1;have h2:Module.finrank (Qa p) (Matrix (Fin m->Bool) (Fin k) (Qa p))=2 ^ m*k:=(by simp only[Ep,Cl,C6,AW,DX,AK]);exact h1.trans h2
 have v3:1<=k:=by
  have hn:=S.hn_pos;by_contra h0;have v4:k=0:=by omega
  rw[v4,AS] at zZ;omega
 let bX:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=QD B.hm za;have zp:=YM (p:=p) B.hm za hι4;have zJ:∀ r:R,(zg r)ᵀ*bX*zg r=bX:=by
  have z2:∀ r₁ r₂:R,(zg r₁)ᵀ*bX*zg r₁=bX->(zg r₂)ᵀ*bX*zg r₂=bX->(zg (r₁*r₂))ᵀ*bX*zg (r₁*r₂)=bX:=fun r₁ r₂ h1 h2=>by
   rw[AF,AT]
   calc (zg r₂)ᵀ*(zg r₁)ᵀ*bX*(zg r₁*zg r₂)
       = (zg r₂)ᵀ*((zg r₁)ᵀ*bX*zg r₁)*zg r₂:=by simp only[Af]
     _ = bX:=by rw[h1,h2]
  have h1:(zg 1)ᵀ*bX*zg 1=bX:=by simp
  have vT:∀ {q:ℕ} (f:Fin q->R),(∀ i,(zg (f i))ᵀ*bX*zg (f i)=bX)->(zg (Qb f))ᵀ*bX*zg (Qb f)=bX:=by
   intro q f hf;induction q with
   | zero=>exact h1
   | succ q ih=>exact z2 _ _ (hf 0) (ih (fun i=>f i.succ) (fun i=>hf i.succ))
  intro r;obtain ⟨⟨c,a,b⟩,hr⟩:=(Qe zb B).surjective r;rw[<-hr];change (zg (Qc zR B.x B.y c a b))ᵀ*bX*zg (Qc zR B.x B.y c a b)=bX;dsimp only[Qc];refine z2 _ _ (by cases c;exacts [h1,by simp only[Be,va];simp])
   (vT _ fun i=>z2 _ _ ?_ ?_)
  . cases a i;exacts [h1,by simp only[Be,vD];exact zp.2.2.1 i]
  . cases b i;exacts [h1,by simp only[Be,vE];exact zp.2.2.2 i]
 have zS:∃ bXinv:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p),bX*bXinv=1/\bXinv*bX=1:=by
  cases zs:za
  .
   refine ⟨-bX,?_,?_⟩
   . rw[CN,show bX*bX=-1 by simpa[bX,zs] using zp.2.1,Dp]
   . rw[Cp,show bX*bX=-1 by simpa[bX,zs] using zp.2.1,Dp]
  . refine ⟨bX,?_,?_⟩ <;> simpa[bX,zs] using zp.2.1
 obtain ⟨bXinv,zD,vO⟩:=zS;have ve:bX.det≠0:=by intro h0;have h1:=Ah Matrix.det zD;rw[Cq,h0,Bm,Dv] at h1;exact CX h1
 have zt:∀ M:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p),(∀ r:R,M*zg r=zg r*M)->∃ c:Qa p,M=c•1:=fun M hM=>
  Q5 zc za hι4 M
   (fun i=>by have h:=hM (B.x i);dsimp only[zg] at h;rwa[Q7] at h)
   (fun i=>by have h:=hM (B.y i);dsimp only[zg] at h;rwa[Wd] at h)
 have zz:∀ F:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p),(∀ r:R,(zg r)ᵀ*F*zg r=F)->∃ c:Qa p,F=c•bX:=by
  intro F hF;have zE:∀ r:R,(bXinv*F)*zg r=zg r*(bXinv*F):=by
   intro r;have zT:zg r*zg r⁻¹=1/\zg r⁻¹*zg r=1:=
     ⟨by
       rw[<-AF,By,BI],by rw[<-AF,CK,BI]⟩
   have zU:(zg r)ᵀ*(zg r⁻¹)ᵀ=1/\(zg r⁻¹)ᵀ*(zg r)ᵀ=1:=
     ⟨by
       rw[<-AT,zT.2,BM],
      by rw[<-AT,zT.1,BM]⟩
   have vf:zg r*bXinv=bXinv*(zg r⁻¹)ᵀ:=by
     have h1:bX*zg r=(zg r⁻¹)ᵀ*bX:=by
       calc bX*zg r=((zg r⁻¹)ᵀ*(zg r)ᵀ)*(bX*zg r):=by rw[zU.2,AC]
         _ = (zg r⁻¹)ᵀ*((zg r)ᵀ*bX*zg r):=by simp only[Af]
         _ = (zg r⁻¹)ᵀ*bX:=by rw[zJ r]
     calc zg r*bXinv=(bXinv*bX)*zg r*bXinv:=by rw[vO,AC]
       _ = bXinv*(bX*zg r)*bXinv:=by simp only[Af]
       _ = bXinv*((zg r⁻¹)ᵀ*bX)*bXinv:=by rw[h1]
       _ = bXinv*(zg r⁻¹)ᵀ:=by rw[Af,Af,zD,As]
   have vg:F*zg r=(zg r⁻¹)ᵀ*F:=by
     calc F*zg r=((zg r⁻¹)ᵀ*(zg r)ᵀ)*(F*zg r):=by rw[zU.2,AC]
       _ = (zg r⁻¹)ᵀ*((zg r)ᵀ*F*zg r):=by simp only[Af]
       _ = (zg r⁻¹)ᵀ*F:=by rw[hF r]
   calc (bXinv*F)*zg r=bXinv*(F*zg r):=Af _ _ _
     _ = (bXinv*(zg r⁻¹)ᵀ)*F:=by rw[vg,<-Af]
     _ = zg r*(bXinv*F):=by rw[<-vf,Af]
  obtain ⟨c,hc⟩:=zt (bXinv*F) zE;refine ⟨c,?_⟩
  calc F=(bX*bXinv)*F:=by rw[zD,AC]
   _ = bX*(bXinv*F):=Af _ _ _
   _ = c•bX:=by rw[hc,Ao,As]
 let BK:Matrix (Fin S.n) (Fin S.n) (Qa p):=S.B.map zk;have vh:BKᵀ=-BK:=by ext a b;have:=An (An S.B_alt a) b;simpa[BK] using Ah zk this
 have zV:BK.det≠0:=(by have:BK.det=zk S.B.det:=(DT zk S.B).symm;rw[this];intro h;exact S.B_det (zk.injective (by rwa[Bn])));have zI:∀ g∈S.L,(g.val.map zk)ᵀ*BK*(g.val.map zk)=BK:=fun g hg=>by
  have h:=Ah (Matrix.map · zk) (S.B_inv g hg);have zK:(g.valᵀ).map zk=(g.val.map zk)ᵀ:=by ext a b;rfl
  rwa[Aq,Aq,zK] at h
 let zh (s:Fin m->Bool) (j:Fin k):Matrix (Fin m->Bool) (Fin k) (Qa p):=
  Matrix.of fun s' j'=>if s'=s/\j'=j then 1 else 0
 have zA:∀ (r:R) (s:Fin m->Bool) (j:Fin k),zg r*zh s j=∑ u:Fin m->Bool,zg r u s•zh u j:=by
  intro r s j;ext a b;simp only[Av,zh,Ak,BR,A2,Am];by_cases hb:b=j
  . subst hb;simp only[and_true,Ca,AK,AS,A8,Ai,↓reduceIte,Bq]
  . simp[hb]
 have vp:∀ j₁ j₂:Fin k,
   let F:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
     Matrix.of fun s t=>dotProduct (e.symm (zh s j₁)) (BK*ᵥe.symm (zh t j₂))
   ∀ r:R,(zg r)ᵀ*F*zg r=F:=by
  intro j₁ j₂ F r;ext s t;have z3:((zg r)ᵀ*F*zg r) s t=dotProduct (e.symm (zg r*zh s j₁)) (BK*ᵥe.symm (zg r*zh t j₂)):=by rw[zA r s j₁,zA r t j₂,Ba,Ba,AJ,sum_dotProduct];simp only[Av,AM,F,Ak,Bo];rw[AY];refine Ag rfl fun u _=>?_;rw[Bd,smul_dotProduct,dotProduct_sum,BC];refine Ag rfl fun v _=>?_;rw[Bd,Al,dotProduct_smul,Am,Am];ring
  rw[z3];have v5:e.symm (zg r*zh s j₁)=ρ r*ᵥe.symm (zh s j₁):=(by apply e.injective;rw[e.apply_symm_apply,zr,e.apply_symm_apply]);have v6:e.symm (zg r*zh t j₂)=ρ r*ᵥe.symm (zh t j₂):=(by apply e.injective;rw[e.apply_symm_apply,zr,e.apply_symm_apply]);rw[v5,v6]
  calc dotProduct (ρ r*ᵥe.symm (zh s j₁)) (BK*ᵥ(ρ r*ᵥe.symm (zh t j₂)))
     = dotProduct (Matrix.vecMul (e.symm (zh s j₁)) (ρ r)ᵀ) (BK*ᵥ(ρ r*ᵥe.symm (zh t j₂))):=by rw[AI]
   _ = dotProduct (e.symm (zh s j₁)) (((ρ r)ᵀ*BK*ρ r)*ᵥe.symm (zh t j₂)):=by rw[<-AB];simp only[Ac,Af]
   _ = F s t:=by change dotProduct (e.symm (zh s j₁)) (((r.1.1.val.map zk)ᵀ*BK*(r.1.1.val.map zk))*ᵥe.symm (zh t j₂))=F s t;rw[zI r.1.1 r.1.2];rfl
 have vF:∀ j₁ j₂:Fin k,∃ cval:Qa p,Matrix.of (fun s t=>dotProduct (e.symm (zh s j₁)) (BK*ᵥe.symm (zh t j₂)))=cval•bX:=
  fun j₁ j₂=>zz _ (vp j₁ j₂)
 choose cmat hcmat using vF;let c:Matrix (Fin k) (Fin k) (Qa p):=Matrix.of cmat;have zu:∀ zl zi:Matrix (Fin m->Bool) (Fin k) (Qa p),dotProduct (e.symm zl) (BK*ᵥe.symm zi)=Matrix.trace (zlᵀ*bX*zi*cᵀ):=by
  intro zl zi;have zC:∀ A:Matrix (Fin m->Bool) (Fin k) (Qa p),A=∑ s:Fin m->Bool,∑ j:Fin k,A s j•zh s j:=fun A=>by
   ext a b;simp only[BR,A2,Am,zh,Ak,Ca,AK,AS];rw[Ay a]
   .
     rw[Ay b]
     . simp
     . intro j _ hj;rw[Aw (fun h=>hj h.2.symm)]
     . intro h;exact absurd (Ai b) h
   . intro s _ hs;exact A1 fun j _=>Aw (fun h=>hs h.1.symm)
   . intro h;exact absurd (Ai a) h
  conv_lhs=>rw[zC zl,zC zi]
  simp only[Ba,Bd,AJ,sum_dotProduct,dotProduct_sum,smul_dotProduct,Al,dotProduct_smul,Am];have vG:∀ s j₁ t j₂,dotProduct (e.symm (zh s j₁)) (BK*ᵥe.symm (zh t j₂))=c j₁ j₂*bX s t:=fun s j₁ t j₂=>by
   have h:=An (An (hcmat j₁ j₂) s) t;simpa[c,Ak,A2,Am] using h
  simp only[vG];simp only[Matrix.trace,Matrix.diag,Av,AM,A6,Bo]
  calc ∑ t,∑ j₂,∑ s,∑ j₁,zi t j₂*(zl s j₁*(c j₁ j₂*bX s t))
     = ∑ j₂,∑ t,∑ s,∑ j₁,zl s j₁*bX s t*zi t j₂*c j₁ j₂:=by
           rw[AY];refine Ag rfl fun j₂ _=>Ag rfl fun t _=>
             Ag rfl fun s _=>Ag rfl fun j₁ _=>by ring
   _ = ∑ j₂,∑ t,∑ j₁,∑ s,zl s j₁*bX s t*zi t j₂*c j₁ j₂:=by refine Ag rfl fun j₂ _=>Ag rfl fun t _=>AY
   _ = ∑ j₂,∑ j₁,∑ t,∑ s,zl s j₁*bX s t*zi t j₂*c j₁ j₂:=by refine Ag rfl fun j₂ _=>AY
   _ = ∑ j₁,∑ j₂,∑ t,∑ s,zl s j₁*bX s t*zi t j₂*c j₁ j₂:=AY
 have zN:cᵀ=if za then -c else c:=by
  have zO:∃ s t,bX s t≠0:=by
   by_contra hall;push Not at hall;have v7:bX=0:=by ext s t;exact hall s t
   have h1:=zD;rw[v7,Ce] at h1;have v8:=An (An h1 (fun _=>false)) (fun _=>false);simp at v8
  obtain ⟨s,t,zY⟩:=zO;ext j₁ j₂;have h1:=An (An (hcmat j₂ j₁) t) s;have h2:=An (An (hcmat j₁ j₂) s) t;have vH:dotProduct (e.symm (zh t j₂)) (BK*ᵥe.symm (zh s j₁))=-dotProduct (e.symm (zh s j₁)) (BK*ᵥe.symm (zh t j₂)):=by
   calc dotProduct (e.symm (zh t j₂)) (BK*ᵥe.symm (zh s j₁))
       = dotProduct (BK*ᵥe.symm (zh s j₁)) (e.symm (zh t j₂)):=dotProduct_comm _ _
     _ = dotProduct (Matrix.vecMul (e.symm (zh s j₁)) BKᵀ) (e.symm (zh t j₂)):=by rw[AI]
     _ = dotProduct (e.symm (zh s j₁)) (BKᵀ*ᵥe.symm (zh t j₂)):=(AB _ _ _).symm
     _ = -dotProduct (e.symm (zh s j₁)) (BK*ᵥe.symm (zh t j₂)):=by rw[vh,BJ,dotProduct_neg]
  simp only[Ak,A2,Am] at h1 h2;rw[vH,h2] at h1;have v9:bX t s=(if za then bX s t else -bX s t):=by have zK:=An (An zp.1 s) t;cases za <;> simpa[bX] using zK
  rw[v9] at h1;cases za
  .
   simp only[AE,Bj,AM,c,Ak] at h1 ⊢;have h3:(cmat j₂ j₁ - cmat j₁ j₂)*bX s t=0:=by linear_combination h1
   exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right zY)
  .
   simp only[Be,AM,Bh,c,Ak] at h1 ⊢;have h3:(cmat j₂ j₁+cmat j₁ j₂)*bX s t=0:=by linear_combination -h1
   have:=(mul_eq_zero.mp h3).resolve_right zY
   linear_combination this
 have zF:c.det≠0:=by
  intro h0;obtain ⟨u,vP,uf⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr h0;let zi:Matrix (Fin m->Bool) (Fin k) (Qa p):=Matrix.of fun s j=>if s=(fun _=>false) then u j else 0;have z4:zi≠0:=by
   intro ug;apply vP;funext j
   have:=An (An ug (fun _=>false)) j
   simpa[zi] using this
  have vI:e.symm zi≠0:=fun h=>z4 (e.symm.injective (h.trans (Bn e.symm).symm));have vJ:BK*ᵥe.symm zi=0:=by
   funext r;have vK:∀ w:Fin S.n->Qa p,dotProduct w (BK*ᵥe.symm zi)=0:=fun w=>by
     rw[<-e.symm_apply_apply w,zu];have vU:zi*cᵀ=0:=by
       ext s j₁;simp only[Av,AM,zi,Ak,ES];by_cases hs:s=fun _=>false
       . simp only[hs,↓reduceIte];have h1:=An uf j₁;simpa[Matrix.mulVec,dotProduct,Bb] using h1
       . simp[hs]
     rw[Af,vU,CZ,Matrix.trace_zero]
   have:=vK (Pi.single r 1)
   simpa[dotProduct,AG] using this
  exact zV (Matrix.exists_mulVec_eq_zero_iff.mp ⟨e.symm zi,vI,vJ⟩)
 have vi:k=1:=by
  by_contra hk_ne1;have vq:2<=k:=by omega
  let eB:Fin (2 ^ m) ≃ (Fin m->Bool):=Fintype.equivOfCardEq (by simp);let b':Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa p):=Matrix.of fun i j=>bX (eB i) (eB j);let e':(Fin S.n->Qa p)≃ₗ[Qa p] Matrix (Fin (2 ^ m)) (Fin k) (Qa p):=
   e.trans
     { toFun:=fun A=>Matrix.of fun i j=>A (eB i) j
       invFun:=fun A=>Matrix.of fun s j=>A (eB.symm s) j
       left_inv:=fun A=>by ext s j;simp
       right_inv:=fun A=>by ext i j;simp
       map_add':=fun _ _=>rfl
       map_smul':=fun _ _=>rfl }
  have vj:(b'ᵀ=b'/\cᵀ=-c)\/(b'ᵀ=-b'/\cᵀ=c):=by
   cases zs:za
   . right;refine ⟨?_,by simpa[zs] using zN⟩;ext i j;have h:=An (An zp.1 (eB i)) (eB j);simpa[b',bX,zs] using h
   . left;refine ⟨?_,by simpa[zs] using zN⟩;ext i j;have h:=An (An zp.1 (eB i)) (eB j);simpa[b',bX,zs] using h
  have vk:b'.det≠0:=by
   have z5:b'*Matrix.of (fun i j=>bXinv (eB i) (eB j))=1:=by
     ext i j;simp only[b',Av,Ak];have vV:=AO eB (fun r=>bX (eB i) (eB r)*bXinv (eB r) (eB j))
       (fun u=>bX (eB i) u*bXinv u (eB j)) (fun _=>rfl)
     rw[vV];have h1:=An (An zD (eB i)) (eB j);simp only[Av] at h1;rw[h1];by_cases h:i=j
     . subst h;simp
     . simp[AH h,AH (fun h'=>h (eB.injective h'))]
   intro h0
   have:=Ah Matrix.det z5
   rw[Cq,h0,Bm,Dv] at this;exact CX this
  have vr:2<=2 ^ m:=by
   have:=B.hm
   calc 2=2 ^ 1:=by norm_num
     _<=2 ^ m:=Nat.pow_le_pow_right (by omega) this
  have vW:∀ g∈S.L,∃ (s:Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa p))
       (t:Matrix (Fin k) (Fin k) (Qa p)) (α:Qa p),
       α≠0/\s.det≠0/\t.det≠0/\
       (∀ v:Fin S.n->Qa p,e' ((g.val.map zk)*ᵥv)=s*e' v*tᵀ)/\
       sᵀ*b'*s=α•b'/\tᵀ*c*t=α⁻¹•c:=by
   intro g vd;let gL:S.L:=⟨g,vd⟩;let zo:R→*R:=
     { toFun:=fun r=>⟨gL*r.1*gL⁻¹,hR_norm.conj_mem r.1 r.2 gL⟩
       map_one':=Ae (by simp)
       map_mul':=fun a b=>Ae (by
         change gL*(a.1*b.1)*gL⁻¹=(gL*a.1*gL⁻¹)*(gL*b.1*gL⁻¹);group) }
   let zw:R→*Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa p):=
     { toFun:=fun r=>Matrix.of fun i j=>zg (zo r) (eB i) (eB j)
       map_one':=by
         ext i j;simp only[BI,Ak];by_cases h:i=j
         . subst h;simp
         . simp[AH h,AH (fun h'=>h (eB.injective h'))]
       map_mul':=fun a b=>by
         ext i j;simp only[AF,Av,Ak]
         exact (AO eB _ _ (fun _=>rfl)).symm }
   have z6:zw zR=-1:=by
     have ua:zo zR=zR:=(by apply Ae;apply Ae;apply A7;change g.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))*g.inv=-1;simp);ext i j;simp only[zw,MonoidHom.coe_mk,OneHom.coe_mk,Ak,ua,va,Bh];by_cases h:i=j
     . subst h;simp
     . simp[AH h,AH (fun h'=>h (eB.injective h'))]
   obtain ⟨k',zj,vQ⟩:=Wj zc zb B hι4 zw z6;have vs:k'=1:=by have h1:=zj.finrank_eq;simp only[CQ,Ep,Cl,C6,AW,DX,AK] at h1;have uh:0 < 2 ^ m:=El m;nlinarith
   subst vs;let zm:((Fin m->Bool)->Qa p)≃ₗ[Qa p] ((Fin m->Bool)->Qa p):=
     { toFun:=fun v s=>zj (fun i=>v (eB i)) s 0
       invFun:=fun v s=>zj.symm (Matrix.of fun u _=>v u) (eB.symm s)
       left_inv:=fun v=>by
         funext s;dsimp only;have h1:(Matrix.of fun u (_:Fin 1)=>zj (fun i=>v (eB i)) u 0)=zj (fun i=>v (eB i)):=(by ext u j;rw[CR j];rfl);rw[h1,zj.symm_apply_apply];simp
       right_inv:=fun v=>by
         funext s;dsimp only;have h1:(fun i:Fin (2 ^ m)=>zj.symm (Matrix.of fun u (_:Fin 1)=>v u) (eB.symm (eB i)))=zj.symm (Matrix.of fun u (_:Fin 1)=>v u):=by funext i;simp
         rw[h1,zj.apply_symm_apply];rfl
       map_add':=fun u v=>by
         funext s;have h1:(fun i=>(u+v) (eB i))=(fun i=>u (eB i))+(fun i=>v (eB i)):=rfl;rw[h1,EN];rfl
       map_smul':=fun r v=>by
         funext s;have h1:(fun i=>(r•v) (eB i))=r•(fun i=>v (eB i)):=rfl
         rw[h1,Bd];rfl }
   let sM:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
     LinearMap.toMatrix' zm.symm.toLinearMap
   let sMinv:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
     LinearMap.toMatrix' zm.toLinearMap
   have zx:sM*sMinv=1:=(by rw[<-Dh];change LinearMap.toMatrix' (zm.symm.toLinearMap.comp zm.toLinearMap)=1;have hc:zm.symm.toLinearMap.comp zm.toLinearMap=LinearMap.id:=Ap fun v=>zm.symm_apply_apply v;rw[hc,Dw]);have z7:sMinv*sM=1:=(by rw[<-Dh];change LinearMap.toMatrix' (zm.toLinearMap.comp zm.symm.toLinearMap)=1;have hc:zm.toLinearMap.comp zm.symm.toLinearMap=LinearMap.id:=Ap fun v=>zm.apply_symm_apply v;rw[hc,Dw]);have zL:∀ r:R,zg (zo r)*sM=sM*zg r:=by
     intro r;apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];have vb:∀ w,sM*ᵥw=zm.symm w:=fun w=>CO zm.symm.toLinearMap w;rw[vb,vb];apply zm.injective;rw[zm.apply_symm_apply];funext s;have ub:=An (An (vQ r (fun i=>(zm.symm v) (eB i))) s) 0;have z3:(fun i=>(zg (zo r)*ᵥzm.symm v) (eB i))=zw r*ᵥ(fun i=>(zm.symm v) (eB i)):=by funext i;simp only[Matrix.mulVec,dotProduct,zw,MonoidHom.coe_mk,OneHom.coe_mk,Ak];exact (AO eB _ _ (fun _=>rfl)).symm
     change zj (fun i=>(zg (zo r)*ᵥzm.symm v) (eB i)) s 0=(zg r*ᵥv) s;rw[z3,ub];simp only[Av,Matrix.mulVec,dotProduct];refine Ag rfl fun u _=>?_;congr 1;have h2:zj (fun i=>(zm.symm v) (eB i)) u 0=zm (zm.symm v) u:=rfl;rw[h2,zm.apply_symm_apply]
   have vt:∃ α:Qa p,sMᵀ*bX*sM=α•bX:=by
     apply zz;intro r
     calc (zg r)ᵀ*(sMᵀ*bX*sM)*zg r
         = (sM*zg r)ᵀ*bX*(sM*zg r):=by rw[AT];simp only[Af]
       _ = (zg (zo r)*sM)ᵀ*bX*(zg (zo r)*sM):=by rw[zL r]
       _ = sMᵀ*((zg (zo r))ᵀ*bX*zg (zo r))*sM:=by rw[AT];simp only[Af]
       _ = sMᵀ*bX*sM:=by rw[zJ (zo r)]
   obtain ⟨α,zG⟩:=vt;have zW:sM.det≠0:=by intro h0;have:=Ah Matrix.det zx;rw[Cq,h0,Bm,Dv] at this;exact CX this
   have zP:α≠0:=(by intro h0;rw[h0,Dl] at zG;have h1:=Ah Matrix.det zG;rw[Cq,Cq,Eu,Di] at h1;exact DM (DM zW ve) zW h1);let zv:Matrix (Fin m->Bool) (Fin k) (Qa p)→ₗ[Qa p] Matrix (Fin m->Bool) (Fin k) (Qa p):=
     { toFun:=fun A=>sMinv*e ((g.val.map zk)*ᵥe.symm A)
       map_add':=fun zl zi=>by simp[A3,BH]
       map_smul':=fun r A=>by simp[Al,Ao] }
   have z0:∀ (r:R) (A:Matrix (Fin m->Bool) (Fin k) (Qa p)),zv (zg r*A)=zg r*zv A:=by
     intro r A;dsimp only[zv,LinearMap.coe_mk,AddHom.coe_mk];have h1:e.symm (zg r*A)=ρ r*ᵥe.symm A:=(by apply e.injective;rw[e.apply_symm_apply,zr,e.apply_symm_apply]);have vu:(g.val.map zk)*ρ r=ρ (zo r)*(g.val.map zk):=by dsimp only[ρ,MonoidHom.coe_mk,OneHom.coe_mk,zo];rw[<-Aq,<-Aq];congr 1;change g.val*r.1.1.val=(g.val*r.1.1.val*g.inv)*g.val;rw[Af,g.inv_val,As]
     rw[h1,Ac,vu,<-Ac,zr (zo r)];have h2:sMinv*zg (zo r)=zg r*sMinv:=by
       calc sMinv*zg (zo r)=sMinv*(zg (zo r)*sM)*sMinv:=by
                 rw[Af,Af,zx,As]
              _ = (sMinv*sM)*zg r*sMinv:=by rw[zL r];simp only[Af]
              _ = zg r*sMinv:=by rw[z7,AC]
     rw[<-Af,h2,Af]
   have vL:∀ j₁ j₂:Fin k,∃ tval:Qa p,Matrix.of (fun u s=>zv (zh s j₂) u j₁)=tval•1:=by
     intro j₁ j₂;apply zt;intro r;ext u s;have h1:=An (An (z0 r (zh s j₂)) u) j₁;rw[zA r s j₂,Ba] at h1;simp only[Av,Ak,BR,Bd,A2,Am] at h1 ⊢
     calc ∑ v,zv (zh v j₂) u j₁*zg r v s
         = ∑ v,zg r v s*zv (zh v j₂) u j₁:=Ag rfl fun v _=>Bb _ _
       _ = ∑ v,zg r u v*zv (zh s j₂) v j₁:=h1
   choose tmat htmat using vL;let t:Matrix (Fin k) (Fin k) (Qa p):=Matrix.of tmat;have vl:∀ A:Matrix (Fin m->Bool) (Fin k) (Qa p),zv A=A*tᵀ:=by
     intro A;have zC:A=∑ s:Fin m->Bool,∑ j₂:Fin k,A s j₂•zh s j₂:=by
       ext a b;simp only[BR,A2,Am,zh,Ak,Ca,AK,AS];rw[Ay a]
       .
         rw[Ay b]
         . simp
         . intro j _ hj;rw[Aw (fun h=>hj h.2.symm)]
         . intro h;exact absurd (Ai b) h
       . intro s _ hs;exact A1 fun j _=>Aw (fun h=>hs h.1.symm)
       . intro h;exact absurd (Ai a) h
     ext u j₁
     conv_lhs=>rw[zC]
     simp only[Ba,Bd,BR,A2,Am,Av,AM,t,Ak];rw[AY];refine Ag rfl fun j₂ _=>?_;have vX:∀ s,zv (zh s j₂) u j₁=if u=s then tmat j₁ j₂ else 0:=fun s=>by
       have h:=An (An (htmat j₁ j₂) u) s;by_cases vC:u=s
       . subst vC;simpa using h
       . simp only[Aw vC];simpa[AH vC] using h
     simp only[vX,Ca,AS,Bq,Ai,↓reduceIte]
   have z8:∀ v:Fin S.n->Qa p,e ((g.val.map zk)*ᵥv)=sM*e v*tᵀ:=fun v=>by
     have h1:=vl (e v);dsimp only[zv,LinearMap.coe_mk,AddHom.coe_mk] at h1;rw[e.symm_apply_apply] at h1
     calc e ((g.val.map zk)*ᵥv)=(sM*sMinv)*e ((g.val.map zk)*ᵥv):=by rw[zx,AC]
       _ = sM*(sMinv*e ((g.val.map zk)*ᵥv)):=Af _ _ _
       _ = sM*e v*tᵀ:=by rw[h1,Af]
   have vv:tᵀ*c*t=α⁻¹•c:=by
     have vw:∀ zl zi:Matrix (Fin m->Bool) (Fin k) (Qa p),Matrix.trace (zlᵀ*bX*zi*(α•(tᵀ*c*t))ᵀ)=Matrix.trace (zlᵀ*bX*zi*cᵀ):=by
       intro zl zi;have h1:dotProduct (e.symm zl) (BK*ᵥe.symm zi)=dotProduct ((g.val.map zk)*ᵥe.symm zl) (BK*ᵥ((g.val.map zk)*ᵥe.symm zi)):=by
         calc dotProduct (e.symm zl) (BK*ᵥe.symm zi)
            = dotProduct (e.symm zl) (((g.val.map zk)ᵀ*BK*(g.val.map zk))*ᵥe.symm zi):=by rw[zI g vd]
           _ = dotProduct (e.symm zl) ((g.val.map zk)ᵀ*ᵥ(BK*ᵥ((g.val.map zk)*ᵥe.symm zi))):=by simp only[Ac,Af]
           _ = dotProduct (Matrix.vecMul (e.symm zl) (g.val.map zk)ᵀ) (BK*ᵥ((g.val.map zk)*ᵥe.symm zi)):=
             AB _ _ _
           _ = dotProduct ((g.val.map zk)*ᵥe.symm zl) (BK*ᵥ((g.val.map zk)*ᵥe.symm zi)):=by rw[AI]
       have h2:e ((g.val.map zk)*ᵥe.symm zl)=sM*zl*tᵀ:=by rw[z8,e.apply_symm_apply]
       have h3:e ((g.val.map zk)*ᵥe.symm zi)=sM*zi*tᵀ:=by rw[z8,e.apply_symm_apply]
       rw[<-e.symm_apply_apply ((g.val.map zk)*ᵥe.symm zl),<- e.symm_apply_apply ((g.val.map zk)*ᵥe.symm zi),h2,h3,zu,zu] at h1;rw[h1];have vY:Matrix.trace ((sM*zl*tᵀ)ᵀ*bX*(sM*zi*tᵀ)*cᵀ)=Matrix.trace (zlᵀ*bX*zi*(α•(tᵀ*c*t))ᵀ):=by
         rw[AT,AT,Cc]
         calc Matrix.trace (t*(zlᵀ*sMᵀ)*bX*(sM*zi*tᵀ)*cᵀ)
            = Matrix.trace ((t*(zlᵀ*(sMᵀ*bX*sM)*zi*tᵀ))*cᵀ):=by simp only[Af]
           _ = Matrix.trace (t*((zlᵀ*(α•bX)*zi*tᵀ)*cᵀ)):=by rw[zG];simp only[Af]
           _ = Matrix.trace ((zlᵀ*(α•bX)*zi*tᵀ*cᵀ)*t):=by rw[Matrix.trace_mul_comm]
           _ = Matrix.trace (zlᵀ*bX*zi*(α•(tᵀ*c*t))ᵀ):=by simp only[Ch,AT,Cc,Ao,Ar,Af]
       exact vY.symm
     have zO:∃ zy zB,bX zy zB≠0:=by
       by_contra hall;push Not at hall;have h0:bX=0:=by ext a b;exact hall a b
       have h1:=zD;rw[h0,Ce] at h1
       have:=An (An h1 (fun _=>false)) (fun _=>false);simp at this
     obtain ⟨zy,zB,zY⟩:=zO;have vm:α•(tᵀ*c*t)=c:=by
       ext j₁ j₂;have h:=vw (zh zy j₁) (zh zB j₂);have vc:∀ D:Matrix (Fin k) (Fin k) (Qa p),Matrix.trace ((zh zy j₁)ᵀ*bX*zh zB j₂*Dᵀ)=bX zy zB*D j₁ j₂:=fun D=>by
         simp only[Matrix.trace,Matrix.diag,Av,AM,zh,Ak];rw[Ay j₁]
         .
           rw[Ay j₂]
           .
            rw[Ay zB]
            .
             rw[Ay zy]
             . simp
             . intro s _ hs;simp[hs]
             . intro hm;exact absurd (Ai zy) hm
            . intro t _ ht;simp[ht]
            . intro hm;exact absurd (Ai zB) hm
           . intro j _ hj;simp[hj]
           . intro hm;exact absurd (Ai j₂) hm
         .
           intro j _ hj;refine A1 fun r _=>?_;have:(∑ t,(∑ s,(if s=zy/\j=j₁ then (1:Qa p) else 0)*bX s t)*if t=zB/\r=j₂ then 1 else 0)=0:=by
            refine A1 fun t _=>?_;have:(∑ s,(if s=zy/\j=j₁ then (1:Qa p) else 0)*bX s t)=0:=
             A1 fun s _=>by simp[hj]
            rw[this,Bm]
           rw[this,Bm]
         . intro hm;exact absurd (Ai j₁) hm
       rw[vc,vc] at h;exact Ck zY h
     calc tᵀ*c*t=α⁻¹•(α•(tᵀ*c*t)):=by rw[AR,inv_mul_cancel₀ zP,Bx]
       _ = α⁻¹•c:=by rw[vm]
   have vx:t.det≠0:=(by intro h0;have h1:=Ah Matrix.det vv;rw[Cq,Cq,Eu,h0,AS,Matrix.det_smul,AW] at h1;exact DM (pow_ne_zero _ (inv_ne_zero zP)) zF h1.symm);let s':Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa p):=Matrix.of fun i j=>sM (eB i) (eB j);have vn:s'.det≠0:=by
     have z5:s'*Matrix.of (fun i j=>sMinv (eB i) (eB j))=1:=by
       ext i j;simp only[s',Av,Ak];rw[AO eB _ (fun u=>sM (eB i) u*sMinv u (eB j)) (fun _=>rfl)];have h1:=An (An zx (eB i)) (eB j);simp only[Av] at h1;rw[h1];by_cases h:i=j
       . subst h;simp
       . simp[AH h,AH (fun h'=>h (eB.injective h'))]
     intro h0;have:=Ah Matrix.det z5;rw[Cq,h0,Bm,Dv] at this;exact CX this
   refine ⟨s',t,α,zP,vn,vx,?_,?_,vv⟩
   . intro v;ext i j;have h1:=An (An (z8 v) (eB i)) j;simp only[Av] at h1;change e ((g.val.map zk)*ᵥv) (eB i) j=∑ r,(∑ u,sM (eB i) (eB u)*e v (eB u) r)*tᵀ r j;rw[h1];refine Ag rfl fun r _=>?_;congr 1;exact (AO eB _ _ (fun _=>rfl)).symm
   . ext i j;have h1:=An (An zG (eB i)) (eB j);simp only[s',b',Av,AM,Ak,A2,Am] at h1 ⊢;rw[<-h1];rw[AO eB _ (fun u=>(∑ r,sM (eB r) (eB i)*bX (eB r) u)*sM u (eB j)) (fun _=>rfl)];refine Ag rfl fun u _=>?_;congr 1;exact AO eB _ (fun v=>sM v (eB i)*bX v u) (fun _=>rfl)
  exact YC zc vr vq S.L S.SF e' b' vk c zF vj
   (fun g vd=>let ⟨s,t,α,hα,hs,_,he,hsb,htc⟩:=vW g vd;⟨s,t,α,hα,hs,hsb,htc,he⟩)
 have zX:za=false:=by
  by_contra hne;have z1:za=true:=B6 hne;have vM:cᵀ=-c:=by simpa[z1] using zN
  have uc:c ⟨0,by omega⟩ ⟨0,by omega⟩=-c ⟨0,by omega⟩ ⟨0,by omega⟩:=by
   have:=An (An vM ⟨0,by omega⟩) ⟨0,by omega⟩
   simpa using this
  have vZ:(2:Qa p)≠0:=by
   intro h2;have ud:(2:ZMod p)=0:=(algebraMap (ZMod p) (Qa p)).injective (by rw[C2,Bn];exact h2);have v0:p∣2:=(At 2 p).mp (by simpa using ud)
   have:=AP (by decide) v0;omega
  have v1:c ⟨0,by omega⟩ ⟨0,by omega⟩=0:=by
   have h2:(2:Qa p)*c ⟨0,by omega⟩ ⟨0,by omega⟩=0:=by linear_combination uc
   exact (mul_eq_zero.mp h2).resolve_left vZ
  have zQ:c=0:=(by ext i j;have hi:i=⟨0,by omega⟩:=A4 (by omega);have hj:j=⟨0,by omega⟩:=A4 (by omega);rw[hi,hj,v1];rfl);haveI:Nonempty (Fin k):=⟨⟨0,by omega⟩⟩;apply zF;rw[zQ];exact Di
 subst zX;have vy:S.n=2 ^ m:=by rw[zZ,vi,AK]
 let j0:Fin k:=⟨0,by omega⟩;let zn:(Fin S.n->Qa p)≃ₗ[Qa p] ((Fin m->Bool)->Qa p):=
  e.trans
   { toFun:=fun A s=>A s j0
     invFun:=fun v=>Matrix.of fun s _=>v s
     left_inv:=fun A=>by ext s j;rw[show j=j0 from A4 (by omega)];rfl
     right_inv:=fun v=>by funext s;rfl
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
 have zq:∀ w s,zn w s=e w s j0:=fun _ _=>rfl;have vz:c j0 j0≠0:=(by intro h0;apply zF;have zQ:c=0:=(by ext i j;rw[show i=j0 from A4 (by omega),show j=j0 from A4 (by omega),h0];rfl);haveI:Nonempty (Fin k):=⟨j0⟩;rw[zQ];exact Di);have ue:∀ g:S.L,(∀ r∈O2 S.L,g*r=r*g)->g.1=1\/g.1=Qd S.n p:=by
  intro g hg;let Gmat:Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
   LinearMap.toMatrix' (zn.toLinearMap∘ₗMatrix.toLin' (g.1.val.map zk)∘ₗzn.symm.toLinearMap)
  have zM:∀ v,Gmat*ᵥv=zn ((g.1.val.map zk)*ᵥzn.symm v):=fun v=>
   CO _ v
  have vo:∀ r:R,Gmat*zg r=zg r*Gmat:=by
   intro r;apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac,zM];have h1:zn.symm (zg r*ᵥv)=ρ r*ᵥzn.symm v:=by apply zn.injective;rw[zn.apply_symm_apply];funext s;symm;have h:=An (An (zr r (zn.symm v)) s) j0;rw[zq,h];simp only[Av,Matrix.mulVec,dotProduct];refine Ag rfl fun u _=>?_;congr 1;have h2:=An (An (e.apply_symm_apply (Matrix.of fun a (_:Fin k)=>v a)) u) j0;simpa[zn] using h2
   rw[h1,Ac];have vu:(g.1.val.map zk)*ρ r=ρ r*(g.1.val.map zk):=by dsimp only[ρ,MonoidHom.coe_mk,OneHom.coe_mk];rw[<-Aq,<-Aq];exact Ah (Matrix.map · zk) (Ah (fun x:S.L=>x.1.val) (hg r.1 r.2))
   rw[vu,<-Ac];funext s;have h:=An (An (zr r ((g.1.val.map zk)*ᵥzn.symm v)) s) j0;rw[zq,h];simp only[Av,Matrix.mulVec,dotProduct,zq];rfl
  obtain ⟨zH,z9⟩:=zt Gmat vo;have vA:g.1.val.map zk=zH•1:=by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,Bv,AN];apply zn.injective;have h1:=zM (zn v);rw[zn.symm_apply_apply,z9,Bv,AN] at h1;rw[<-h1,Bd]
  have vN:zH*zH=1:=by
   have h1:=zI g.1 g.2;rw[vA,Ch,BM,Ar,AC,Ao,As,AR] at h1;have v2:(zH*zH - 1)•BK=0:=by rw[DJ,Bx,h1,Cx]
   have vB:BK≠0:=(by haveI:Nonempty (Fin S.n):=⟨⟨0,S.hn_pos⟩⟩;intro h0;apply zV;rw[h0];exact Di);exact sub_eq_zero.mp ((smul_eq_zero.mp v2).resolve_right vB)
  rcases mul_self_eq_one_iff.mp vN with rfl | rfl
  . left;apply A7;ext a b;apply zk.injective;have h:=An (An vA a) b;simpa[AZ,BG] using h
  .
   right;apply A7;ext a b;apply zk.injective;have h:=An (An vA a) b;by_cases vR:a=b
   . subst vR;simpa[AZ,Qd] using h
   . simpa[AZ,Qd,AH vR] using h
 refine ⟨rfl,vy,ue,ι4,hι4,zn,c j0 j0,vz,?_,?_⟩
 . intro r v;funext s;have h:=An (An (zr r v) s) j0;rw[zq];change e (ρ r*ᵥv) s j0=_;rw[h];simp only[Av,Matrix.mulVec,dotProduct,zq]
 .
  intro u v;have h:=zu (e u) (e v);rw[e.symm_apply_apply,e.symm_apply_apply] at h;rw[h];simp only[Matrix.trace,Matrix.diag,Av,AM];rw[Ay j0]
  .
   rw[Ay j0]
   . simp only[dotProduct,Matrix.mulVec,zq,A6,Bo];rw[AY];refine Ag rfl fun s _=>Ag rfl fun t _=>by ring
   . intro j _ hj;exact absurd (A4 (by omega)) hj
   . intro hm;exact absurd (Ai j0) hm
  . intro j _ hj;exact absurd (A4 (by omega)) hj
  . intro hm;exact absurd (Ai j0) hm
end Section6ExtraspecialRep
section Section6bKillCases
lemma W9 {p:ℕ} [Fact p.Prime]
  {N:ℕ} {zc:0 < N} {zd:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zc zd ι) (zb:(⟨Qd S.n p,S.negOne_mem⟩:S.L)∈O2 S.L) (za:Qn (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,zb⟩)
  {m:ℕ} {ze:Bool} (B:Qm (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,zb⟩ m ze) (zf:∀ g:S.L,(∀ r∈O2 S.L,g*r=r*g)->g.1=1\/g.1=Qd S.n p) (g:S.L) (zg:∀ i:Fin m,g*(B.x i).1*g⁻¹=(B.x i).1\/g*(B.x i).1*g⁻¹=⟨Qd S.n p,S.negOne_mem⟩*(B.x i).1) (zh:∀ i:Fin m,g*(B.y i).1*g⁻¹=(B.y i).1\/g*(B.y i).1*g⁻¹=⟨Qd S.n p,S.negOne_mem⟩*(B.y i).1) : g∈O2 S.L:=by
 classical
 let R:=O2 S.L;let zL:S.L:=⟨Qd S.n p,S.negOne_mem⟩;let zR:R:=⟨zL,zb⟩;have zj:∀ r:R,zR*r=r*zR:=fun r=>
  (Subgroup.mem_center_iff.mp ((za.center_iff zR).mpr (Or.inr rfl)) r).symm
 let α:Fin m->Bool:=fun i=>decide (g*(B.x i).1*g⁻¹≠(B.x i).1);let β:Fin m->Bool:=fun i=>decide (g*(B.y i).1*g⁻¹≠(B.y i).1);let h:R:=Qc zR B.x B.y false β α;have zk:h=Qb (fun j=>(if β j then B.x j else 1)*(if α j then B.y j else 1)):=(by simp[h,Qc]);have zx:∀ i:Fin m,h*B.x i=(if α i then zR else 1)*(B.x i*h):=by
  intro i;have h1:B.x i*Qb (fun j=>(if β j then B.x j else 1)*(if α j then B.y j else 1))=(if α i then zR else 1)*Qb (fun j=>(if β j then B.x j else 1)*(if α j then B.y j else 1))*B.x i:=by
   apply Q4 (B.x i) (if α i then zR else 1) _ i
   . intro a;cases α i <;> simp[zj]
   .
    intro j;by_cases zi:j=i
    .
     subst zi;rw[Az rfl];cases β j <;> cases α j <;> simp
     . rw[B.hxy_same j,Ad]
     .
      calc B.x j*(B.x j*B.y j)=B.x j*(zR*(B.y j*B.x j)):=by rw[B.hxy_same j]
       _ = zR*(B.x j*B.y j)*B.x j:=by rw[<-Ad,<-zj (B.x j)];simp only[Ad]
    .
     rw[Aw zi,AA];cases β j <;> cases α j <;> simp[B.hxx i j (Ne.symm zi),B.hxy i j (Ne.symm zi)]
     calc B.x i*(B.x j*B.y j)=(B.x j*B.x i)*B.y j:=by rw[<-Ad,B.hxx i j (Ne.symm zi)]
      _ = B.x j*(B.y j*B.x i):=by rw[Ad,B.hxy i j (Ne.symm zi)]
      _ = B.x j*B.y j*B.x i:=(Ad _ _ _).symm
  rw[<-zk] at h1;have zC:∀ a:R,(if α i then zR else 1)*a=a*(if α i then zR else 1):=fun a=>by
   cases α i <;> simp[zj]
  have zp:(if α i then zR else 1)*(if α i then zR else 1)=1:=(by cases α i;exacts [by simp,by simpa only[Be] using za.z_sq])
  calc h*B.x i=((if α i then zR else 1)*(if α i then zR else 1))*(h*B.x i):=by rw[zp,AA]
   _ = (if α i then zR else 1)*((if α i then zR else 1)*h*B.x i):=by simp only[Ad]
   _ = (if α i then zR else 1)*(B.x i*h):=by rw[<-h1]
 have zy:∀ i:Fin m,h*B.y i=(if β i then zR else 1)*(B.y i*h):=by
  intro i;have h1:B.y i*Qb (fun j=>(if β j then B.x j else 1)*(if α j then B.y j else 1))=(if β i then zR else 1)*Qb (fun j=>(if β j then B.x j else 1)*(if α j then B.y j else 1))*B.y i:=by
   apply Q4 (B.y i) (if β i then zR else 1) _ i
   . intro a;cases β i <;> simp[zj]
   .
    intro j;by_cases zi:j=i
    .
     subst zi;rw[Az rfl];cases β j <;> cases α j <;> simp
     .
      calc B.y j*B.x j=(zR*zR)*(B.y j*B.x j):=by rw[za.z_sq,AA]
       _ = zR*(B.x j*B.y j):=by rw[Ad,<-B.hxy_same j]
       _ = zR*B.x j*B.y j:=(Ad _ _ _).symm
     .
      calc B.y j*(B.x j*B.y j)=(B.y j*B.x j)*B.y j:=(Ad _ _ _).symm
       _ = (zR*(B.x j*B.y j))*B.y j:=by rw[B.hxy_same j,<-Ad,za.z_sq,AA]
       _ = zR*(B.x j*B.y j)*B.y j:=rfl
    .
     rw[Aw zi,AA];cases β j <;> cases α j <;> simp[B.hyy i j (Ne.symm zi),B.hxy j i zi]
     calc B.y i*(B.x j*B.y j)=(B.x j*B.y i)*B.y j:=by rw[<-Ad,(B.hxy j i zi).symm]
      _ = B.x j*(B.y j*B.y i):=by rw[Ad,B.hyy i j (Ne.symm zi)]
      _ = B.x j*B.y j*B.y i:=(Ad _ _ _).symm
  rw[<-zk] at h1;have zp:(if β i then zR else 1)*(if β i then zR else 1)=1:=(by cases β i;exacts [by simp,by simpa only[Be] using za.z_sq])
  calc h*B.y i=((if β i then zR else 1)*(if β i then zR else 1))*(h*B.y i):=by rw[zp,AA]
   _ = (if β i then zR else 1)*((if β i then zR else 1)*h*B.y i):=by simp only[Ad]
   _ = (if β i then zR else 1)*(B.y i*h):=by rw[<-h1]
 let g':S.L:=h.1⁻¹*g;have zz:∀ i:Fin m,g'*(B.x i).1=(B.x i).1*g':=fun i=>by
  have h1:g*(B.x i).1*g⁻¹=(if α i then zL else 1)*(B.x i).1:=by
   rcases zg i with heq | heq
   . simp[α,heq]
   .
    by_cases zl:g*(B.x i).1*g⁻¹=(B.x i).1
    . simp[α,zl]
    .
     have zu:α i=true:=by simp[α,zl]
     rw[zu,Az rfl];exact heq
  have h2:h.1*(B.x i).1=(if α i then zL else 1)*((B.x i).1*h.1):=by
   have:=Ah Subtype.val (zx i)
   cases zq:α i <;> simpa[zq,zR] using this
  calc g'*(B.x i).1=h.1⁻¹*(g*(B.x i).1*g⁻¹)*g:=by dsimp[g'];group
   _ = h.1⁻¹*((if α i then zL else 1)*(B.x i).1)*g:=by rw[h1]
   _ = h.1⁻¹*((if α i then zL else 1)*((B.x i).1*h.1))*(h.1⁻¹*g):=by group
   _ = h.1⁻¹*(h.1*(B.x i).1)*g':=by rw[<-h2]
   _ = (B.x i).1*g':=by group
 have zA:∀ i:Fin m,g'*(B.y i).1=(B.y i).1*g':=fun i=>by
  have h1:g*(B.y i).1*g⁻¹=(if β i then zL else 1)*(B.y i).1:=by
   rcases zh i with heq | heq
   . simp[β,heq]
   .
    by_cases zl:g*(B.y i).1*g⁻¹=(B.y i).1
    . simp[β,zl]
    .
     have zv:β i=true:=by simp[β,zl]
     rw[zv,Az rfl];exact heq
  have h2:h.1*(B.y i).1=(if β i then zL else 1)*((B.y i).1*h.1):=by
   have:=Ah Subtype.val (zy i)
   cases zr:β i <;> simpa[zr,zR] using this
  calc g'*(B.y i).1=h.1⁻¹*(g*(B.y i).1*g⁻¹)*g:=by dsimp[g'];group
   _ = h.1⁻¹*((if β i then zL else 1)*(B.y i).1)*g:=by rw[h1]
   _ = h.1⁻¹*((if β i then zL else 1)*((B.y i).1*h.1))*(h.1⁻¹*g):=by group
   _ = h.1⁻¹*(h.1*(B.y i).1)*g':=by rw[<-h2]
   _ = (B.y i).1*g':=by group
 have zB:g'*zL=zL*g':=(by apply Ae;apply A7;change g'.1.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))=(-1)*g'.1.val;simp);have zm:∀ r∈O2 S.L,g'*r=r*g':=by
  have zn:∀ r₁ r₂:R,g'*r₁.1=r₁.1*g'->g'*r₂.1=r₂.1*g'->g'*(r₁*r₂).1=(r₁*r₂).1*g':=fun r₁ r₂ h1 h2=>by
   change g'*(r₁.1*r₂.1)=(r₁.1*r₂.1)*g';rw[<-Ad,h1,Ad,h2,<-Ad]
  have zw:∀ {q:ℕ} (f:Fin q->R),(∀ i,g'*(f i).1=(f i).1*g')->g'*(Qb f).1=(Qb f).1*g':=by
   intro q f hf;induction q with
   | zero=>simp[Qb]
   | succ q ih=>exact zn _ _ (hf 0) (ih (fun i=>f i.succ) (fun i=>hf i.succ))
  intro r hr;obtain ⟨⟨c,a,b⟩,hcab⟩:=(Qe za B).surjective ⟨r,hr⟩;have zs:(⟨r,hr⟩:R)=Qc zR B.x B.y c a b:=hcab.symm;change g'*(⟨r,hr⟩:R).1=(⟨r,hr⟩:R).1*g';rw[zs];dsimp only[Qc];refine zn _ _ (by cases c;exacts [by simp,by simpa using zB]) (zw _ fun i=>zn _ _ ?_ ?_)
  . cases a i;exacts [by simp,by simpa using zz i]
  . cases b i;exacts [by simp,by simpa using zA i]
 have zo:g'∈O2 S.L:=by
  rcases zf g' zm with h1 | hz
  . have:g'=1:=Ae h1;rw[this];exact (O2 S.L).one_mem
  . have:g'=zL:=Ae hz;rw[this];exact zb
 have zt:g=h.1*g':=by dsimp[g'];group
 rw[zt];exact (O2 S.L).mul_mem h.2 zo
set_option maxHeartbeats 800000 in
lemma YN {p:ℕ} [Fact p.Prime] (zj:11<=p)
  {N:ℕ} {zg:0 < N} {zl:¬ p∣N}
  {ι:Ab N (Qa p)≃*Ab N ℂ} (S:Qg p N zg zl ι) (zh:(⟨Qd S.n p,S.negOne_mem⟩:S.L)∈O2 S.L) (zd:Qn (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,zh⟩)
  {m:ℕ} (B:Qm (O2 S.L) ⟨⟨Qd S.n p,S.negOne_mem⟩,zh⟩ m false) (za:Qa p) (ze:za*za=-1) (zc:(Fin S.n->Qa p)≃ₗ[Qa p] ((Fin m->Bool)->Qa p)) (zb:Qa p) (zi:zb≠0) (zf:∀ (r:O2 S.L) (v:Fin S.n->Qa p), zc ((r.1.1.val.map (algebraMap (ZMod p) (Qa p)))*ᵥv)=
    let rels:=QJ (p:=p) (m:=m) false ze
    QA zd B (-1) (Qk false za) (Ql false)
     (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥzc v)
  (zk:∀ u v:Fin S.n->Qa p,dotProduct u ((S.B.map (algebraMap (ZMod p) (Qa p)))*ᵥv)=zb*dotProduct (zc u) (QD B.hm false*ᵥzc v)) :
  False:=by
 classical
 let ιK:=algebraMap (ZMod p) (Qa p);let R:=O2 S.L;have zz:R.Normal:=QI S.L;haveI:Fintype R:=Fintype.ofFinite R;let zR:R:=⟨⟨Qd S.n p,S.negOne_mem⟩,zh⟩;let BK:Matrix (Fin S.n) (Fin S.n) (Qa p):=S.B.map ιK;let rels:=QJ (p:=p) (m:=m) false ze;let zq:R→*Matrix (Fin m->Bool) (Fin m->Bool) (Qa p):=
  QA zd B (-1) (Qk false za) (Ql false)
   (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2
 have zP:zq zR=-1:=Yl zd B (-1) (Qk false za) (Ql false)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2
 have zQ:∀ i,zq (B.x i)=Qk false za i:=fun i=>Q7 zd B (-1) (Qk false za) (Ql false)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 i
 have zS:∀ i,zq (B.y i)=Ql false i:=fun i=>Wd zd B (-1) (Qk false za) (Ql false)
  (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 i
 let S4:Finset R:=Finset.univ.filter fun r=>r*r=zR;let F:MvPolynomial (Fin S.n) (Qa p):=
  ∑ r∈S4,(QH (BK*r.1.1.val.map ιK)) ^ 4
 have zM:F.IsHomogeneous 8:=(by refine MvPolynomial.IsHomogeneous.sum _ _ 8 fun r _=>?_;simpa using (Q8 (BK*r.1.1.val.map ιK)).pow 4);have zJ:∀ g∈S.L,(g.val.map ιK)ᵀ*BK*(g.val.map ιK)=BK:=fun g hg=>by
  have h:=Ah (Matrix.map · ιK) (S.B_inv g hg);have vg:(g.valᵀ).map ιK=(g.val.map ιK)ᵀ:=by ext a b;rfl
  rwa[Aq,Aq,vg] at h
 have zN:∀ g∈S.L,∀ v:Fin S.n->Qa p,MvPolynomial.eval ((g.val.map ιK)*ᵥv) F=MvPolynomial.eval v F:=by
  intro g z5 v;let gL:S.L:=⟨g,z5⟩;let zn:R≃*R:=
   {toFun:=fun r=>⟨gL⁻¹*r.1*gL,by simpa using zz.conj_mem r.1 r.2 gL⁻¹⟩
    invFun:=fun r=>⟨gL*r.1*gL⁻¹,zz.conj_mem r.1 r.2 gL⟩
    left_inv:=fun r=>Ae (by group)
    right_inv:=fun r=>Ae (by group)
    map_mul':=fun a b=>Ae (by
     change gL⁻¹*(a.1*b.1)*gL=(gL⁻¹*a.1*gL)*(gL⁻¹*b.1*gL);group) }
  have z3:zn zR=zR:=(by apply Ae;apply Ae;apply A7;change g.inv*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod p))*g.val=-1;simp);simp only[F,Ba,Dc,WC];refine Finset.sum_nbij' (fun r=>zn r) (fun r=>zn.symm r) ?_ ?_ ?_ ?_ ?_
  . intro r hr;simp only[S4,AL,Ai,B3] at hr ⊢;rw[<-AF,hr,z3]
  . intro r hr;simp only[S4,AL,Ai,B3] at hr ⊢;apply zn.injective;rw[AF,zn.apply_symm_apply,hr,z3]
  . intro r _;exact zn.symm_apply_apply r
  . intro r _;exact zn.apply_symm_apply r
  .
   intro r _;refine Ah (· ^ 4) ?_;have z6:(g.val.map ιK)ᵀ*(BK*r.1.1.val.map ιK)*(g.val.map ιK)=BK*(zn r).1.1.val.map ιK:=by
    have vh:(zn r).1.1.val.map ιK=g.inv.map ιK*r.1.1.val.map ιK*g.val.map ιK:=(by change (g.inv*r.1.1.val*g.val).map ιK=_;simp only[Aq]);have zT:g.val.map ιK*g.inv.map ιK=1:=by
     rw[<-Aq,g.val_inv];ext a b;by_cases h:a=b
     . subst h;simp
     . simp[AH h]
    calc (g.val.map ιK)ᵀ*(BK*r.1.1.val.map ιK)*(g.val.map ιK)
      = ((g.val.map ιK)ᵀ*BK*(g.val.map ιK))*(g.inv.map ιK*r.1.1.val.map ιK*g.val.map ιK):=by simp only[Af];rw[<-Af (g.val.map ιK) (g.inv.map ιK),zT,AC]
     _ = BK*(zn r).1.1.val.map ιK:=by rw[zJ g z5,vh]
   calc dotProduct ((g.val.map ιK)*ᵥv) ((BK*r.1.1.val.map ιK)*ᵥ((g.val.map ιK)*ᵥv))
     = dotProduct (Matrix.vecMul v (g.val.map ιK)ᵀ) ((BK*r.1.1.val.map ιK)*ᵥ((g.val.map ιK)*ᵥv)):=by rw[AI]
    _ = dotProduct v (((g.val.map ιK)ᵀ*(BK*r.1.1.val.map ιK)*(g.val.map ιK))*ᵥv):=by rw[<-AB];simp only[Ac,Af]
    _ = dotProduct v ((BK*(zn r).1.1.val.map ιK)*ᵥv):=by rw[z6]
 have vi:F=0:=Yh zj S.L S.SF F zM zN;let zs:Fin m->Bool:=fun _=>false;let zm:Fin m->Bool:=fun i=>decide (i.val=0);let zx:Fin S.n->Qa p:=zc.symm (Pi.single zs 1);have zA:∀ (c:Bool) (a b:Fin m->Bool) (s:Fin m->Bool),∃ zr:Qa p,zr ^ 4=1/\zq (Qc zR B.x B.y c a b)*ᵥPi.single s 1=zr•Pi.single (fun i=>xor (s i) (b i)) 1:=by
  have vj:∀ (s:Fin m->Bool),∃ zr:Qa p,zr ^ 4=1/\zq zR*ᵥPi.single s 1=zr•Pi.single s 1:=fun s=>
   ⟨-1,by ring,by rw[zP,BJ,AN,neg_one_smul]⟩
  have hxx:∀ (i:Fin m) (s:Fin m->Bool),∃ zr:Qa p,zr ^ 4=1/\zq (B.x i)*ᵥPi.single s 1=zr•Pi.single s 1:=fun i s=>by
   rw[zQ i];refine ⟨if i.val=0/\!false then (if s i then -za else za) else (if s i then -1 else 1),?_,?_⟩
   .
    have h4:za ^ 4=1:=by
     calc za ^ 4=(za*za)*(za*za):=by ring
      _ = 1:=by rw[ze];ring
    have vk:(-za) ^ 4=1:=by
     calc (-za) ^ 4=za ^ 4:=by ring
      _ = 1:=h4
    by_cases hi:i.val=0 <;> cases zD:s i <;> simp[hi,zD,h4,vk] <;> ring
   .
    funext t;simp only[Qk,BO,AX,Am,AG];by_cases ht:t=s
    . subst ht;simp
    . simp[ht]
  have hyy:∀ (i:Fin m) (s:Fin m->Bool),∃ zr:Qa p,zr ^ 4=1/\zq (B.y i)*ᵥPi.single s 1=zr•Pi.single (Function.update s i (!s i)) 1:=fun i s=>by
   rw[zS i];refine ⟨if i.val=0 then (if s i then -1 else 1) else 1,?_,?_⟩
   . by_cases hi:i.val=0 <;> cases zD:s i <;> simp[hi,zD] <;> ring
   .
    funext t;simp only[Ql,Matrix.mulVec,dotProduct,Ak,AG,Ca,AK,AS,A8,Ai,↓reduceIte,AX,Am];have zy:s=Function.update t i (!t i)↔t=Function.update s i (!s i):=(by constructor <;> intro h <;> subst h <;> funext k <;> by_cases hk:k=i <;> simp[hk]);by_cases ht:t=Function.update s i (!s i)
    . rw[Az (zy.mpr ht),Az ht,ht,AD];by_cases hi:i.val=0 <;> cases zD:s i <;> simp[hi,zD]
    . rw[Aw (fun h=>ht (zy.mp h)),Aw ht]
  have zU:∀ {q:ℕ} (f:Fin q->Fin m) (a b:Fin q->Bool) (s:Fin m->Bool),Function.Injective f->∃ zr:Qa p,zr ^ 4=1/\zq (Qb (fun i=>(if a i then B.x (f i) else 1)*(if b i then B.y (f i) else 1)))*ᵥPi.single s 1=zr•Pi.single (fun k=>if h:∃ i,f i=k then xor (s k) (b (Classical.choose h)) else s k) 1:=by
   intro q f a b s zv;induction q generalizing s with
   | zero=>
    refine ⟨1,B8 4,?_⟩;simp only[Qb,BI,AN,Bx];refine Ah (Pi.single · (1:Qa p)) (funext fun k=>?_);rw[dif_neg (fun h:∃ i:Fin 0,f i=k=>Ez h.choose)]
   | succ q ih=>
    have zO:Function.Injective (fun i:Fin q=>f i.succ):=fun i j h=>D0 _ (zv h);obtain ⟨l1,zI,zu⟩:=ih (fun i=>f i.succ) (fun i=>a i.succ) (fun i=>b i.succ) s zO;let s1:Fin m->Bool:=fun k=>
     if h:∃ i:Fin q,f i.succ=k then xor (s k) (b (Classical.choose h).succ) else s k
    have vl:∃ l2:Qa p,l2 ^ 4=1/\zq (if b 0 then B.y (f 0) else 1)*ᵥPi.single s1 1=l2•Pi.single (if b 0 then Function.update s1 (f 0) (!s1 (f 0)) else s1) 1:=by
     cases zw:b 0
     . exact ⟨1,B8 4,by simp only[Bj,AE,BI,AN,Bx]⟩
     . simpa using hyy (f 0) s1
    obtain ⟨l2,vo,zZ⟩:=vl;let s2:Fin m->Bool:=if b 0 then Function.update s1 (f 0) (!s1 (f 0)) else s1;have vm:∃ l3:Qa p,l3 ^ 4=1/\zq (if a 0 then B.x (f 0) else 1)*ᵥPi.single s2 1=l3•Pi.single s2 1:=by
     cases vr:a 0
     . exact ⟨1,B8 4,by simp only[Bj,AE,BI,AN,Bx]⟩
     . simpa using hxx (f 0) s2
    obtain ⟨l3,vp,z0⟩:=vm;refine ⟨l3*l2*l1,by rw[CC,CC,vp,vo,zI];ring,?_⟩;simp only[Qb,AF,<-Ac];rw[zu,Al,Al,zZ,Al,z0,AR,AR];congr 1
    . ring
    .
     congr 1;funext k;by_cases hk:k=f 0
     . subst hk;have zE:¬ ∃ i:Fin q,f i.succ=f 0:=fun ⟨i,hi⟩=>CJ i (zv hi);have zF:∃ i:Fin (q+1),f i=f 0:=⟨0,rfl⟩;have zB:Classical.choose zF=0:=zv (Classical.choose_spec zF);rw[dif_pos zF,zB];cases zw:b 0 <;> simp[s2,s1,zE,zw]
     .
      have zy:(∃ i:Fin (q+1),f i=k)↔(∃ i:Fin q,f i.succ=k):=by
       constructor
       . rintro ⟨i,hi⟩;refine Fin.cases (fun h0=>absurd h0.symm hk) (fun j hj=>⟨j,hj⟩) i hi
       . rintro ⟨i,hi⟩;exact ⟨i.succ,hi⟩
      by_cases zp:∃ i:Fin q,f i.succ=k
      .
       have zG:∃ i:Fin (q+1),f i=k:=zy.mpr zp;have zB:Classical.choose zG=(Classical.choose zp).succ:=
        zv ((Classical.choose_spec zG).trans (Classical.choose_spec zp).symm)
       rw[dif_pos zG,zB];cases zw:b 0 <;> simp[s2,s1,zp,hk,zw]
      . have zV:¬ ∃ i:Fin (q+1),f i=k:=fun h=>zp (zy.mp h);rw[dif_neg zV];cases zw:b 0 <;> simp[s2,s1,zp,hk,zw]
  intro c a b s;obtain ⟨l1,zI,zu⟩:=zU id a b s Function.injective_id;have zW:(fun k=>if h:∃ i:Fin m,id i=k then xor (s k) (b (Classical.choose h)) else s k)=fun i=>xor (s i) (b i):=by funext k;have zp:∃ i:Fin m,id i=k:=⟨k,rfl⟩;rw[dif_pos zp];have zB:Classical.choose zp=k:=Classical.choose_spec zp;rw[zB]
  rw[zW] at zu;dsimp only[id] at zu;dsimp only[Qc];cases hc:c
  . refine ⟨l1,zI,?_⟩;simpa[hc] using zu
  . obtain ⟨l0,vq,z1⟩:=vj (fun i=>xor (s i) (b i));refine ⟨l0*l1,by rw[CC,vq,zI,AA],?_⟩;simp only[hc,Be,AF,<-Ac];rw[zu,Al,z1,AR,Bb]
 have zK:∀ (c:Bool) (a b:Fin m->Bool),(MvPolynomial.eval zx (QH (BK*(Qc zR B.x B.y c a b).1.1.val.map ιK))) ^ 4=if b=zm then zb ^ 4 else 0:=by
  intro c a b;rw[WC,<-Ac,zk,zc.apply_symm_apply,zf,zc.apply_symm_apply];obtain ⟨zr,z2,zo⟩:=zA c a b zs;have zX:(fun i=>xor (zs i) (b i))=b:=funext fun i=>by simp[zs]
  rw[zX] at zo;change (zb*dotProduct (Pi.single zs 1) (QD B.hm false*ᵥ(zq (Qc zR B.x B.y c a b)*ᵥPi.single zs 1))) ^ 4=_;rw[zo,Al,dotProduct_smul,Am];have z7:dotProduct (Pi.single zs 1) (QD (p:=p) B.hm false*ᵥPi.single b 1)=if b=zm then -1 else 0:=by
   simp only[dotProduct,Matrix.mulVec,AG,Ca,AK,AS,A8,Ai,↓reduceIte,ite_mul,AA,Bm,Bq];simp only[QD,Ak,AE,Bj,zs];by_cases zt:b=zm
   .
    subst zt;have h1:∀ i:Fin m,1<=i.val->false=zm i:=fun i hi=>by
     simp[zm];omega
    rw[Az h1,show zm ⟨0,B.hm⟩=true by simp[zm],C3,Az rfl,Az rfl]
   .
    rw[Aw zt];by_cases h1:∀ i:Fin m,1<=i.val->false=b i
    .
     rw[Az h1];have z8:b ⟨0,B.hm⟩=false:=by
      by_contra hne;apply zt;funext i;by_cases hi:i.val=0
      . have:i=⟨0,B.hm⟩:=A4 hi;rw[this,B6 hne];simp[zm,hi]
      . rw[<-h1 i (by omega)];simp[zm,hi]
     rw[z8,Db,Aw (by decide)]
    . rw[Aw h1]
  rw[z7];by_cases zt:b=zm
  . rw[Az zt,Az zt];rw[CC,CC,z2];ring
  . rw[Aw zt,Aw zt];ring
 have zC:∀ (c:Bool) (a:Fin m->Bool),Qc zR B.x B.y c a zm∈S4:=by
  intro c a;simp only[S4,AL,Ai,B3];have z9:∀ r:R,zR*r=r*zR:=fun r=>
   (Subgroup.mem_center_iff.mp ((zd.center_iff zR).mpr (Or.inr rfl)) r).symm
  have va:=Wi false zR B.x B.y z9 zd.z_sq B.hxy_same B.hxx B.hxy B.hyy B.hsq_x B.hsq_y (c,a,zm) (c,a,zm);rw[va];have vb:(fun i=>xor (a i) (a i))=fun _=>false:=funext fun i=>B9 (a i);have vc:(fun i=>xor (zm i) (zm i))=fun _=>false:=funext fun i=>B9 (zm i);have vd:(QF false (c,a,zm) (c,a,zm)).1=true:=by
   dsimp only[QF];rw[B9,Dz];obtain ⟨q,hq⟩:∃ q,m=q+1:=⟨m - 1,by have:=B.hm;omega⟩;subst hq;simp only[Qt]
   have h0:xor (zm 0&&a 0) (xor (decide ((0:Fin (q+1)).val=0)&&!false&&a 0&&a 0)
     (decide ((0:Fin (q+1)).val=0)&&!false&&zm 0&&zm 0))=true:=by
    cases a 0 <;> simp[zm]
   rw[h0,WG _ (fun i=>by simp[zm]),Ex]
  dsimp only[Qc];have h1:(QF false (c,a,zm) (c,a,zm)).2.1=fun _=>false:=vb;have h2:(QF false (c,a,zm) (c,a,zm)).2.2=fun _=>false:=vc;rw[vd,h1,h2,Az rfl];have zY:Qb (fun i:Fin m=>(if false=true then B.x i else 1)*(if false=true then B.y i else 1))=1:=
   QB _ fun _=>by simp
  rw[zY,AK]
 have zL:MvPolynomial.eval zx F=(2 ^ (m+1):Qa p)*zb ^ 4:=by
  simp only[F,Ba,Dc];have zH:∑ r:R,(if r*r=zR then (MvPolynomial.eval zx (QH (BK*r.1.1.val.map ιK))) ^ 4 else 0)=∑ t:Bool×(Fin m->Bool)×(Fin m->Bool),if t.2.2=zm then zb ^ 4 else 0:=by
   rw[<-AO (Qe zd B) _ _ (fun _=>rfl)];refine Ag rfl fun ⟨c,a,b⟩ _=>?_;change (if Qc zR B.x B.y c a b*Qc zR B.x B.y c a b=zR then (MvPolynomial.eval zx (QH (BK*(Qc zR B.x B.y c a b).1.1.val.map ιK))) ^ 4 else 0)=if b=zm then zb ^ 4 else 0;rw[zK c a b];by_cases zt:b=zm
   . subst zt;have z4:=zC c a;simp only[S4,AL,Ai,B3] at z4;simp[z4]
   . simp[zt]
  change (∑ r∈Finset.univ.filter (fun r:R=>r*r=zR),(MvPolynomial.eval zx (QH (BK*r.1.1.val.map ιK))) ^ 4)=_;rw[Finset.sum_filter,zH];simp_rw[C4];simp only[A8,Ai,↓reduceIte,Cm,BS,Cl,C6,AW,nsmul_eq_mul];push_cast;ring
 have h0:MvPolynomial.eval zx F=0:=by rw[vi,Bn]
 rw[zL] at h0;have ve:(2:Qa p)≠0:=by
  intro h2;have vn:(2:ZMod p)=0:=ιK.injective (by rw[C2,Bn];exact h2);have vf:p∣2:=(At 2 p).mp (by simpa using vn)
  have:=AP (by decide) vf;omega
 exact DM (pow_ne_zero (m+1) ve) (pow_ne_zero 4 zi) h0
def Qu {m:ℕ} (i:Fin m):Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7):=
 if i.val=0 then
  Matrix.of fun s t=>
   if ∀ k:Fin m,1<=k.val->s k=t k then
    if s i then (if t i then (4:ZMod 7) else 2) else (if t i then 2 else 3)
   else 0
 else
  Matrix.diagonal fun s=>if s i then (-1:ZMod 7) else 1
def Qv {m:ℕ} (i:Fin m):Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7):=
 Matrix.of fun s t=>
  if t=Function.update s i (!s i) then
   if i.val=0 then (if s i then (1:ZMod 7) else -1) else 1
  else 0
def Qp {m:ℕ} (hm:1<=m):Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7):=
 Qv ⟨0,hm⟩
lemma YO {m:ℕ} : (∀ i:Fin m,Qu i*Qv i=(-1)*(Qv i*Qu i))/\ (∀ i j:Fin m,i≠j->Qu i*Qu j=Qu j*Qu i)/\ (∀ i j:Fin m,i≠j->Qu i*Qv j=Qv j*Qu i)/\ (∀ i j:Fin m,i≠j->Qv i*Qv j=Qv j*Qv i)/\ (∀ i:Fin m,Qu i*Qu i=if i.val=0/\!false then -1 else 1)/\ (∀ i:Fin m,Qv i*Qv i=if i.val=0/\!false then -1 else 1):=by
 have zb:∀ (s:Fin m->Bool) (i:Fin m),Function.update (Function.update s i (!s i)) i (!(!s i))=s:=(by intro s i;funext k;by_cases h:k=i <;> simp[h]);have zi:∀ (s:Fin m->Bool) (i j:Fin m),i≠j->Function.update (Function.update s i (!s i)) j (!s j)=Function.update (Function.update s j (!s j)) i (!s i):=by
  intro s i j zf;funext k;by_cases h1:k=i
  . subst h1;simp[zf]
  .
   by_cases h2:k=j
   . subst h2;simp[h1]
   . simp[h1,h2]
 have zo:∀ (i:Fin m) (s t:Fin m->Bool),Function.update s i (!s i)=Function.update t i (!t i)->s=t:=(by intro i s t h;have h1:=Ah (fun u=>Function.update u i (!u i)) h;rw[AD,AD,zb,zb] at h1;exact h1);have zm:∀ (i:Fin m) (hi:i.val=0) (s:Fin m->Bool) (f:(Fin m->Bool)->ZMod 7),∑ u:Fin m->Bool,Qu i s u*f u=(if s i then (4:ZMod 7) else 3)*f s+2*f (Function.update s i (!s i)):=by
  intro i hi s f;let s':=Function.update s i (!s i);have zj:s≠s':=fun h=>by
   have:=An h i;simp[s'] at this
  rw[Finset.sum_eq_add s s' zj (fun u _ ⟨hu1,hu2⟩=>by
   simp only[Qu,Az hi,Ak];have zq:¬ ∀ k:Fin m,1<=k.val->s k=u k:=by
    intro za;by_cases zp:u i=s i
    .
     apply hu1;funext k;by_cases hk:k=i
     . subst hk;exact zp
     .
      have zn:1<=k.val:=by have:k.val≠0:=fun h0=>hk (A4 (by omega));omega
      exact (za k zn).symm
    .
     apply hu2;funext k;by_cases hk:k=i
     . subst hk;simp only[s',AD];cases hs:s k <;> cases hu:u k <;> simp[hs,hu] at zp ⊢
     .
      have zn:1<=k.val:=by have:k.val≠0:=fun h0=>hk (A4 (by omega));omega
      simp only[s',Bu hk];exact (za k zn).symm
   rw[Aw zq,Bm]) (fun h=>absurd (Ai s) h) (fun h=>absurd (Ai s') h)]
  simp only[Qu,Az hi,Ak];have h1:∀ k:Fin m,1<=k.val->s k=s k:=fun _ _=>rfl;have h2:∀ k:Fin m,1<=k.val->s k=s' k:=fun k hk=>by
   have zh:k≠i:=fun h=>by subst h;omega
   simp[s',zh]
  rw[Az (fun _ _=>trivial),Az h2,show s' i=!s i from AD i _ s];cases hs:s i <;> simp[s',hs]
 have zg:∀ (i:Fin m) (M:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) (s t:Fin m->Bool),(Qv i*M) s t=(if i.val=0 then (if s i then (1:ZMod 7) else -1) else 1)*M (Function.update s i (!s i)) t:=by
  intro i M s t;simp only[Qv,Av,Ak];rw[Ay (Function.update s i (!s i))]
  . rw[Az rfl]
  . intro u _ hu;rw[Aw hu,Bm]
  . intro h;exact absurd (Ai _) h
 have zk:∀ (i:Fin m) (M:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) (s t:Fin m->Bool),(M*Qv i) s t=M s (Function.update t i (!t i))*(if i.val=0 then (if t i then (-1:ZMod 7) else 1) else 1):=by
  intro i M s t;simp only[Qv,Av,Ak];rw[Ay (Function.update t i (!t i))]
  . have h1:t=Function.update (Function.update t i (!t i)) i (!Function.update t i (!t i) i):=(by rw[AD,zb]);rw[Az h1,AD];by_cases hi:i.val=0 <;> cases ht:t i <;> simp[hi,ht]
  .
   intro u _ hu
   have zj:t≠Function.update u i (!u i):=fun ze=>hu (by
    have h1:=Ah (fun w=>Function.update w i (!w i)) ze
    rw[AD,zb] at h1;exact h1.symm)
   rw[Aw zj,AS]
  . intro h;exact absurd (Ai _) h
 refine ⟨?_,?_,?_,?_,?_,?_⟩;·
  intro i;ext s t;simp only[Cp,AC,Bh,zk,zg];by_cases hi:i.val=0
  .
   simp only[Qu,Az hi,Ak];have zc:(∀ k:Fin m,1<=k.val->s k=Function.update t i (!t i) k)↔(∀ k:Fin m,1<=k.val->Function.update s i (!s i) k=t k):=by
    constructor <;> intro za k hk
    .
     have zh:k≠i:=fun h=>by subst h;omega
     simpa[zh] using za k hk
    .
     have zh:k≠i:=fun h=>by subst h;omega
     simpa[zh] using za k hk
   by_cases za:∀ k:Fin m,1<=k.val->Function.update s i (!s i) k=t k
   . rw[Az (zc.mpr za),Az za,AD,AD];cases hs:s i <;> cases ht:t i <;> simp[hi,hs,ht] <;> decide
   . rw[Aw (fun h=>za (zc.mp h)),Aw za];simp
  .
   simp only[Qu,Aw hi,Matrix.diagonal_apply,Aw hi,AK,AA];have zc:s=Function.update t i (!t i)↔Function.update s i (!s i)=t:=(by constructor <;> intro h <;> subst h <;> exact (by rw[AD,zb]));by_cases ze:Function.update s i (!s i)=t
   . rw[Az (zc.mpr ze),Az ze,AD];cases s i <;> simp
   . rw[Aw (fun h=>ze (zc.mp h)),Aw ze,neg_zero]
 ·
  intro i j zf;ext s t;by_cases hi:i.val=0
  .
   have hj:j.val≠0:=fun h0=>zf (A4 (by omega));simp only[Qu,Aw hj,CU,Cy];simp only[Qu,Az hi,Ak];by_cases za:∀ k:Fin m,1<=k.val->s k=t k
   .
    have zt:1<=j.val:=by omega
    rw[Az za,za j zt];ring
   . rw[Aw za,Bm,AS]
  .
   by_cases hj:j.val=0
   .
    simp only[Qu,Aw hi,CU,Cy];simp only[Qu,Az hj,Ak];by_cases za:∀ k:Fin m,1<=k.val->s k=t k
    .
     have zu:1<=i.val:=by omega
     rw[Az za,za i zu];ring
    . rw[Aw za,Bm,AS]
   . simp only[Qu,Aw hi,Aw hj,C0,Bb]
 ·
  intro i j zf;ext s t;rw[zk,zg];by_cases hi:i.val=0
  .
   have hj:j.val≠0:=fun h0=>zf (A4 (by omega));simp only[Aw hj,AK,AA,Qu,Az hi,Ak,Bu zf,Bu zf.symm];have zc:(∀ k:Fin m,1<=k.val->s k=Function.update t j (!t j) k)↔(∀ k:Fin m,1<=k.val->Function.update s j (!s j) k=t k):=by
    constructor <;> intro za k hk
    .
     by_cases zl:k=j
     . subst zl;have:=za k hk;simp only[AD] at this ⊢;cases hs:s k <;> cases ht:t k <;> simp[hs,ht] at this ⊢
     . simpa[zl] using za k hk
    .
     by_cases zl:k=j
     . subst zl;have:=za k hk;simp only[AD] at this ⊢;cases hs:s k <;> cases ht:t k <;> simp[hs,ht] at this ⊢
     . simpa[zl] using za k hk
   by_cases za:∀ k:Fin m,1<=k.val->Function.update s j (!s j) k=t k
   . rw[Az (zc.mpr za),Az za]
   . rw[Aw (fun h=>za (zc.mp h)),Aw za]
  .
   simp only[Qu,Aw hi,Matrix.diagonal_apply];have zc:s=Function.update t j (!t j)↔Function.update s j (!s j)=t:=(by constructor <;> intro h <;> subst h <;> exact (by rw[AD,zb]));by_cases ze:Function.update s j (!s j)=t
   .
    rw[Az (zc.mpr ze),Az ze,Bu zf];have zd:t j=!s j:=by rw[<-ze,AD]
    rw[zd];by_cases hj:j.val=0 <;> cases zv:s j <;> cases zw:s i <;> simp[hj,zv,zw]
   . rw[Aw (fun h=>ze (zc.mp h)),Aw ze,Bm,AS]
 ·
  intro i j zf;ext s t;rw[zg,zg];simp only[Qv,Ak,Bu zf,Bu zf.symm];rw[zi s i j zf];have zc:t=Function.update (Function.update s j (!s j)) i (!s i)↔t=Function.update (Function.update s j (!s j)) i (!s i):=Iff.rfl;split_ifs <;> ring
 ·
  intro i;ext s t;by_cases hi:i.val=0
  .
   simp only[hi,Db,and_self,Be,Av,Bh];rw[zm i hi s (fun u=>Qu i u t)];simp only[Qu,Az hi,Ak];have zc:(∀ k:Fin m,1<=k.val->Function.update s i (!s i) k=t k)↔(∀ k:Fin m,1<=k.val->s k=t k):=by
    constructor <;> intro za k hk <;> have zh:k≠i:=fun h=>by subst h;omega
    . simpa[zh] using za k hk
    . simpa[zh] using za k hk
   by_cases za:∀ k:Fin m,1<=k.val->s k=t k
   .
    rw[Az za,Az (zc.mpr za),AD];by_cases zd:s=t
    . subst zd;rw[BT];cases hs:s i <;> simp[hs] <;> decide
    .
     rw[AH zd,neg_zero]
     have zr:s i≠t i:=fun ze=>zd (funext fun k=>by
      by_cases hk:k=i;· subst hk;exact ze
      . exact za k (by have:k.val≠0:=fun h0=>hk (A4 (by omega));omega))
     cases hs:s i <;> cases ht:t i <;> simp[hs,ht] at zr ⊢ <;> decide
   . rw[Aw za,Aw (fun h=>za (zc.mp h)),AS,AS,D8];have zd:s≠t:=fun h=>za (fun k _=>by rw[h]);rw[AH zd,neg_zero]
  .
   simp only[hi,Db,false_and,Bj,Qu,Aw hi,C0];by_cases zd:s=t
   . subst zd;simp only[Matrix.diagonal_apply_eq,BT];cases s i <;> simp
   . simp[Df _ zd,AH zd]
 ·
  intro i;ext s t;rw[zg];simp only[Qv,Ak,AD,zb];by_cases zd:t=s
  . subst zd;by_cases hi:i.val=0 <;> cases ht:t i <;> simp[hi,ht]
  . have zs:s≠t:=Ne.symm zd;by_cases hi:i.val=0 <;> simp[hi,zd,AH zs]
lemma YJ {m:ℕ} (hm:1<=m) : (Qp hm)ᵀ=-Qp hm/\ Qp hm*Qp hm=-1/\ (∀ i:Fin m,(Qu i)ᵀ*Qp hm*Qu i=Qp hm)/\ (∀ i:Fin m,(Qv i)ᵀ*Qp hm*Qv i=Qp hm):=by
 have za:=YO (m:=m);let i0:Fin m:=⟨0,hm⟩;have zd:(Qv i0)ᵀ=-Qv i0:=by
  ext s t;simp only[Qv,AM,Bh,Ak,show i0.val=0 from rfl,Be];have zb:s=Function.update t i0 (!t i0)↔t=Function.update s i0 (!s i0):=(by constructor <;> intro h <;> subst h <;> funext k <;> by_cases hk:k=i0 <;> simp[hk]);by_cases ht:t=Function.update s i0 (!s i0)
  . rw[Az (zb.mpr ht),Az ht,ht,AD];cases s i0 <;> simp
  . rw[Aw (fun h=>ht (zb.mp h)),Aw ht,neg_zero]
 have zg:∀ i:Fin m,(Qu i)ᵀ=Qu i:=fun i=>by
  ext s t;by_cases hi:i.val=0
  .
   simp only[Qu,Az hi,AM,Ak];have zb:(∀ k:Fin m,1<=k.val->t k=s k)↔(∀ k:Fin m,1<=k.val->s k=t k):=
    ⟨fun h k hk=>(h k hk).symm,fun h k hk=>(h k hk).symm⟩
   by_cases h:∀ k:Fin m,1<=k.val->s k=t k
   . rw[Az (zb.mpr h),Az h];cases s i <;> cases t i <;> simp
   . rw[Aw (fun h'=>h (zb.mp h')),Aw h]
  .
   by_cases zf:s=t
   . subst zf;simp[Qu,hi]
   . simp[Qu,hi,Df _ zf,Df _ (Ne.symm zf)]
 have zh:∀ i:Fin m,i≠i0->(Qv i)ᵀ=Qv i:=fun i hi=>by
  have ze:i.val≠0:=fun h0=>hi (A4 h0);ext s t;simp only[Qv,AM,Ak,Aw ze];have zb:s=Function.update t i (!t i)↔t=Function.update s i (!s i):=(by constructor <;> intro h <;> subst h <;> funext k <;> by_cases hk:k=i <;> simp[hk]);by_cases ht:t=Function.update s i (!s i)
  . rw[Az (zb.mpr ht),Az ht]
  . rw[Aw (fun h=>ht (zb.mp h)),Aw ht]
 refine ⟨zd,?_,?_,?_⟩
 . simpa[Qp,i0] using za.2.2.2.2.2 i0
 .
  intro i;rw[zg i];change Qu i*Qv i0*Qu i=Qv i0;by_cases hi:i=i0
  .
   subst hi;rw[za.1 i0,Cp,AC,Cp,Af];have zc:Qu i0*Qu i0=-1:=by simpa[i0] using za.2.2.2.2.1 i0
   rw[zc,CN,As,Dp]
  .
   rw[za.2.2.1 i i0 hi,Af];have ze:i.val≠0:=fun h0=>hi (A4 h0);have zc:Qu i*Qu i=1:=by simpa[ze] using za.2.2.2.2.1 i
   rw[zc,As]
 .
  intro i;change (Qv i)ᵀ*Qv i0*Qv i=Qv i0;by_cases hi:i=i0
  .
   subst hi;rw[zd,Cp];have zc:Qv i0*Qv i0=-1:=by simpa[i0] using za.2.2.2.2.2 i0
   rw[zc,Dp,AC]
  .
   rw[zh i hi,za.2.2.2.1 i i0 hi,Af];have ze:i.val≠0:=fun h0=>hi (A4 h0);have zc:Qv i*Qv i=1:=by simpa[ze] using za.2.2.2.2.2 i
   rw[zc,As]
abbrev QM := ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7
def Ym:QM->QM
 | (a,b,c,d,e,f,g,h)=>(3*a+2*e,3*b+2*f,3*c+2*g,3*d+2*h, 2*a+4*e,2*b+4*f,2*c+4*g,2*d+4*h)
def QY:QM->QM
 | (a,b,c,d,e,f,g,h)=>(-e,-f,-g,-h,a,b,c,d)
def Yn:QM->QM
 | (a,b,c,d,e,f,g,h)=>(a,b,-c,-d,e,f,-g,-h)
def Yo:QM->QM
 | (a,b,c,d,e,f,g,h)=>(c,d,a,b,g,h,e,f)
def Yp:QM->QM
 | (a,b,c,d,e,f,g,h)=>(a,-b,c,-d,e,-f,g,-h)
def Yq:QM->QM
 | (a,b,c,d,e,f,g,h)=>(b,a,d,c,f,e,h,g)
def WW:QM->QM->ZMod 7
 | (a1,b1,c1,d1,e1,f1,g1,h1),(a2,b2,c2,d2,e2,f2,g2,h2)=> a1*a2+b1*b2+c1*c2+d1*d2+e1*e2+f1*f2+g1*g2+h1*h2
def Q0:QM:=(1,1,1,1,1,0,0,0)
def Wb (a0 b0 a1 b1 a2 b2:Bool) (v:QM):QM:=
 let v1:=if b2 then Yq v else v
 let v2:=if a2 then Yp v1 else v1
 let v3:=if b1 then Yo v2 else v2
 let v4:=if a1 then Yn v3 else v3
 let v5:=if b0 then QY v4 else v4
 if a0 then Ym v5 else v5
def WR (a0 b0 a1 b1 a2 b2:Bool):Bool:=
 xor (xor (xor (b0&&a0) (xor a0 b0)) (b1&&a1)) (b2&&a2)
def WK (f:Bool->ℕ):ℕ:=f false+f true
def Ww:ℕ:=
 WK fun a0=>WK fun b0=>WK fun a1=>WK fun b1=>
  WK fun a2=>WK fun b2=>
   if WR a0 b0 a1 b1 a2 b2&&decide (WW Q0 (QY (Wb a0 b0 a1 b1 a2 b2 Q0))≠0)
   then 1 else 0
lemma YD:Ww=32:=by decide
private lemma QZ:(0:ZMod 7).val=0/\(1:ZMod 7).val=1/\(2:ZMod 7).val=2/\ (3:ZMod 7).val=3/\(4:ZMod 7).val=4/\(5:ZMod 7).val=5/\(6:ZMod 7).val=6:=by decide
private lemma YV (y:ZMod 7) (hy:y≠0) : y=1\/y=2\/y=3\/y=4\/y=5\/y=6:=by
 have zc:=y.val_lt;have zb:y.val≠0:=fun h0=>hy (by rw[<-CP y,h0];rfl);have za:y=(y.val:ZMod 7):=(CP y).symm;interval_cases y.val
 . exact absurd rfl zb
 . exact Or.inl (by simpa using za)
 . exact Or.inr (Or.inl (by simpa using za))
 . exact Or.inr (Or.inr (Or.inl (by simpa using za)))
 . exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using za))))
 . exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using za)))))
 . exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using za)))))
private lemma Yk:(2:ZMod 7)*2=4:=by decide
private lemma YX:(2:ZMod 7)*6=5:=by decide
private lemma YY:(2:ZMod 7)*5=3:=by decide
private lemma Yz:(4:ZMod 7)*2=1:=by decide
private lemma YA:(2:ZMod 7) ^ 3=1:=by decide
private lemma YZ:(8:ZMod 7)=1:=by decide
private lemma YH:(2:ZMod 7) ^ 1≠1:=by decide
private lemma Yu:(2:ZMod 7) ^ 2≠1:=by decide
set_option maxHeartbeats 800000 in
lemma YE [Fact (Nat.Prime 7)] {m:ℕ} (zm:3<=m)
  {N:ℕ} {zh:0 < N} {zj:¬ 7∣N}
  {ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N zh zj ι) (zi:(⟨Qd S.n 7,S.negOne_mem⟩:S.L)∈O2 S.L) (za:Qn (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zi⟩) (B:Qm (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zi⟩ m false) (zb:S.n=2 ^ m) (zd:Qa 7) (ze:zd*zd=-1) (zc:(Fin S.n->Qa 7)≃ₗ[Qa 7] ((Fin m->Bool)->Qa 7)) (zf:Qa 7) (zk:zf≠0) (zg:∀ (r:O2 S.L) (v:Fin S.n->Qa 7), zc ((r.1.1.val.map (algebraMap (ZMod 7) (Qa 7)))*ᵥv)=
    let rels:=QJ (p:=7) (m:=m) false ze
    QA za B (-1) (Qk false zd) (Ql false)
      (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥzc v)
  (zl:∀ u v:Fin S.n->Qa 7,dotProduct u ((S.B.map (algebraMap (ZMod 7) (Qa 7)))*ᵥv)=zf*dotProduct (zc u) (QD B.hm false*ᵥzc v)) :
  False:=by
 classical
 let ιK:=algebraMap (ZMod 7) (Qa 7);let R:=O2 S.L;have vo:R.Normal:=QI S.L;haveI:Fintype R:=Fintype.ofFinite R;let zR:R:=⟨⟨Qd S.n 7,S.negOne_mem⟩,zi⟩;let zs:=YO (m:=m);let zo:R→*Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7):=
  QA za B (-1) Qu Qv
   (fun A=>by simp) (by simp) zs.1 zs.2.1 zs.2.2.1 zs.2.2.2.1 zs.2.2.2.2.1 zs.2.2.2.2.2
 have vx:zo zR=-1:=Yl za B (-1) Qu Qv
  (fun A=>by simp) (by simp) zs.1 zs.2.1 zs.2.2.1 zs.2.2.2.1 zs.2.2.2.2.1 zs.2.2.2.2.2
 have uf:∀ i,zo (B.x i)=Qu i:=fun i=>Q7 za B (-1) Qu Qv
  (fun A=>by simp) (by simp) zs.1 zs.2.1 zs.2.2.1 zs.2.2.2.1 zs.2.2.2.2.1 zs.2.2.2.2.2 i
 have ug:∀ i,zo (B.y i)=Qv i:=fun i=>Wd za B (-1) Qu Qv
  (fun A=>by simp) (by simp) zs.1 zs.2.1 zs.2.2.1 zs.2.2.2.1 zs.2.2.2.2.1 zs.2.2.2.2.2 i
 let eB:Fin (2 ^ m) ≃ (Fin m->Bool):=Fintype.equivOfCardEq (by simp);let zu:R→*Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (ZMod 7):=
  {toFun:=fun r=>Matrix.of fun i j=>zo r (eB i) (eB j)
   map_one':=by
    ext i j;simp only[BI,Ak];by_cases h:i=j
    . subst h;simp
    . simp[AH h,AH (fun h'=>h (eB.injective h'))]
   map_mul':=fun a b=>by
    ext i j;simp only[AF,Av,Ak]
    exact (AO eB _ _ (fun _=>rfl)).symm }
 let b7':Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (ZMod 7):=Matrix.of fun i j=>Qp B.hm (eB i) (eB j);have zP:=YJ B.hm;have vK:∀ r:R,(zo r)ᵀ*Qp B.hm*zo r=Qp B.hm:=by
  have vV:∀ r₁ r₂:R,(zo r₁)ᵀ*Qp B.hm*zo r₁=Qp B.hm->(zo r₂)ᵀ*Qp B.hm*zo r₂=Qp B.hm->(zo (r₁*r₂))ᵀ*Qp B.hm*zo (r₁*r₂)=Qp B.hm:=fun r₁ r₂ h1 h2=>by
   rw[AF,AT]
   calc (zo r₂)ᵀ*(zo r₁)ᵀ*Qp B.hm*(zo r₁*zo r₂)
      = (zo r₂)ᵀ*((zo r₁)ᵀ*Qp B.hm*zo r₁)*zo r₂:=by simp only[Af]
    _ = Qp B.hm:=by rw[h1,h2]
  have h1:(zo 1)ᵀ*Qp B.hm*zo 1=Qp B.hm:=by simp
  have u1:∀ {q:ℕ} (f:Fin q->R),(∀ i,(zo (f i))ᵀ*Qp B.hm*zo (f i)=Qp B.hm)->(zo (Qb f))ᵀ*Qp B.hm*zo (Qb f)=Qp B.hm:=by
   intro q f hf;induction q with
   | zero=>exact h1
   | succ q ih=>exact vV _ _ (hf 0) (ih (fun i=>f i.succ) (fun i=>hf i.succ))
  intro r;obtain ⟨⟨c,a,b⟩,hr⟩:=(Qe za B).surjective r;rw[<-hr];change (zo (Qc zR B.x B.y c a b))ᵀ*Qp B.hm*zo (Qc zR B.x B.y c a b)=Qp B.hm;dsimp only[Qc];refine vV _ _ (by cases c;exacts [h1,by simp only[Be,vx];simp]) (u1 _ fun i=>vV _ _ ?_ ?_)
  . cases a i;exacts [h1,by simp only[Be,uf];exact zP.2.2.1 i]
  . cases b i;exacts [h1,by simp only[Be,ug];exact zP.2.2.2 i]
 have vy:∀ r:R,(zu r)ᵀ*b7'*zu r=b7':=fun r=>by
  ext i j;have h:=An (An (vK r) (eB i)) (eB j);simp only[zu,b7',MonoidHom.coe_mk,OneHom.coe_mk,Av,AM,Ak] at h ⊢;rw[<-h,AO eB _ (fun u=>(∑ v,zo r (eB v) (eB i)*Qp B.hm (eB v) u)*zo r u (eB j)) (fun _=>rfl)];refine Ag rfl fun u _=>?_;congr 1;exact AO eB _ (fun v=>zo r v (eB i)*Qp B.hm v u) (fun _=>rfl)
 let zU:=QJ (p:=7) (m:=m) false ze;let zq:R→*Matrix (Fin m->Bool) (Fin m->Bool) (Qa 7):=
  QA za B (-1) (Qk false zd) (Ql false)
   (fun A=>by simp) (by simp) zU.1 zU.2.1 zU.2.2.1 zU.2.2.2.1 zU.2.2.2.2.1 zU.2.2.2.2.2
 let zt:R→*Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa 7):=
  {toFun:=fun r=>(zu r).map ιK
   map_one':=by
    rw[BI];ext i j;by_cases h:i=j
    . subst h;simp
    . simp[AH h]
   map_mul':=fun a b=>by rw[AF,Aq] }
 have uv:zt zR=-1:=by
  ext i j;simp only[zt,zu,MonoidHom.coe_mk,OneHom.coe_mk,AZ,Ak,vx,Bh];by_cases h:i=j
  . subst h;simp
  . simp[AH h,AH (fun h'=>h (eB.injective h'))]
 obtain ⟨k7,zS,uu⟩:=Wj (by decide) za B ze zt uv;have hk7:k7=1:=by have h1:=zS.finrank_eq;simp only[CQ,Ep,Cl,C6,AW,DX,AK] at h1;have zav:0 < 2 ^ m:=El m;nlinarith
 subst hk7;let e7:(Fin (2 ^ m)->Qa 7)≃ₗ[Qa 7] ((Fin m->Bool)->Qa 7):=
  zS.trans
   {toFun:=fun A s=>A s 0
    invFun:=fun v=>Matrix.of fun s _=>v s
    left_inv:=fun A=>by ext s j;rw[CR j];rfl
    right_inv:=fun v=>by funext s;rfl
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
 have z5:∀ w s,e7 w s=zS w s 0:=fun _ _=>rfl;have zG:∀ (r:R) (v:Fin (2 ^ m)->Qa 7),e7 (zt r*ᵥv)=zq r*ᵥe7 v:=fun r v=>by
  funext s;rw[z5];have h:=An (An (uu r v) s) 0;rw[h];simp only[Av,Matrix.mulVec,dotProduct,z5];rfl
 let zF:(Fin S.n->Qa 7)≃ₗ[Qa 7] (Fin (2 ^ m)->Qa 7):=zc.trans e7.symm;let TK:Matrix (Fin (2 ^ m)) (Fin S.n) (Qa 7):=LinearMap.toMatrix' zF.toLinearMap;let TKinv:Matrix (Fin S.n) (Fin (2 ^ m)) (Qa 7):=LinearMap.toMatrix' zF.symm.toLinearMap;have zJ:TK*TKinv=1:=(by rw[<-Dh];have:zF.toLinearMap.comp zF.symm.toLinearMap=LinearMap.id:=Ap fun v=>zF.apply_symm_apply v;rw[this,Dw]);have vb:TKinv*TK=1:=(by rw[<-Dh];have:zF.symm.toLinearMap.comp zF.toLinearMap=LinearMap.id:=Ap fun v=>zF.symm_apply_apply v;rw[this,Dw]);have uw:TK≠0:=(by intro h0;rw[h0,Ce] at zJ;have h:=An (An zJ ⟨0,El m⟩) ⟨0,El m⟩;simp at h);have z6:∀ r:R,TK*(r.1.1.val.map ιK)=(zu r).map ιK*TK:=fun r=>by
  apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac];have uU:∀ w,TK*ᵥw=e7.symm (zc w):=fun w=>CO zF.toLinearMap w;rw[uU,uU];apply e7.injective;rw[e7.apply_symm_apply];change zc ((r.1.1.val.map ιK)*ᵥv)=e7 (zt r*ᵥe7.symm (zc v));rw[zG,e7.apply_symm_apply,zg]
 obtain ⟨T₀,ud,zH⟩:=
  Wy (fun r:R=>zu r) (fun r:R=>r.1.1.val) TK uw z6
 have vc:∃ zB:Qa 7,zB≠0/\T₀.map ιK=zB•TK:=by
  let M:Matrix (Fin m->Bool) (Fin m->Bool) (Qa 7):=
   LinearMap.toMatrix' (e7.toLinearMap∘ₗMatrix.toLin' (T₀.map ιK*TKinv)∘ₗe7.symm.toLinearMap)
  have uh:∀ v,M*ᵥv=e7 ((T₀.map ιK*TKinv)*ᵥe7.symm v):=fun v=>CO _ v;have vp:∀ r:R,M*zq r=zq r*M:=fun r=>by
   apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac,uh];have h1:e7.symm (zq r*ᵥv)=zt r*ᵥe7.symm v:=(by apply e7.injective;rw[e7.apply_symm_apply,zG,e7.apply_symm_apply]);have vz:(T₀.map ιK*TKinv)*zt r=zt r*(T₀.map ιK*TKinv):=by
    have u2:T₀.map ιK*r.1.1.val.map ιK=zt r*T₀.map ιK:=(by have h:=Ah (Matrix.map · ιK) (zH r);simpa[Aq,zt] using h);have vd:TKinv*zt r=r.1.1.val.map ιK*TKinv:=by
      calc TKinv*zt r=TKinv*((zu r).map ιK*TK)*TKinv:=by
              change TKinv*(zu r).map ιK=_;rw[Af,Af,zJ,As]
            _ = (TKinv*TK)*r.1.1.val.map ιK*TKinv:=by rw[<-z6 r];simp only[Af]
            _ = r.1.1.val.map ιK*TKinv:=by rw[vb,AC]
    calc (T₀.map ιK*TKinv)*zt r=T₀.map ιK*(TKinv*zt r):=Af _ _ _
      _ = (T₀.map ιK*r.1.1.val.map ιK)*TKinv:=by rw[vd,Af]
      _ = zt r*(T₀.map ιK*TKinv):=by rw[u2,Af]
   rw[h1,Ac (zt r*ᵥe7.symm v) (T₀.map ιK) TKinv,Ac (e7.symm v) (T₀.map ιK*TKinv) (zt r),vz,<-Ac,zG,<-Ac]
  obtain ⟨zB,vl⟩:=Q5 (by decide) false ze M
   (fun i=>by have h:=vp (B.x i);dsimp only[zq] at h;rwa[Q7] at h)
   (fun i=>by have h:=vp (B.y i);dsimp only[zq] at h;rwa[Wd] at h)
  have hMT:T₀.map ιK*TKinv=zB•1:=(by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,Bv,AN];apply e7.injective;have h1:=uh (e7 v);rw[e7.symm_apply_apply,vl,Bv,AN] at h1;rw[<-h1,Bd]);have vA:T₀.map ιK=zB•TK:=by
   calc T₀.map ιK=(T₀.map ιK*TKinv)*TK:=by rw[Af,vb,As]
    _ = zB•TK:=by rw[hMT,Ar,AC]
  have z1:zB≠0:=(by intro h0;rw[h0,Dl] at vA;apply ud;ext a b;apply ιK.injective;simpa using An (An vA a) b);exact ⟨zB,z1,vA⟩
 obtain ⟨zB,z1,vU⟩:=vc;let zx:Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (ZMod 7):=Matrix.of fun i j=>T₀ i (Fin.cast zb.symm j);have zV:zx.det≠0:=by
  have uL:(zx.map ιK)*Matrix.of (fun i j=>(zB⁻¹•TKinv) (Fin.cast zb.symm i) j)=1:=by
   ext i j;simp only[Av,AZ,zx,Ak,A2,Am];have h1:=An (An zJ i) j;simp only[Av] at h1;have zQ:∑ r:Fin (2 ^ m),ιK (T₀ i (Fin.cast zb.symm r))*(zB⁻¹*TKinv (Fin.cast zb.symm r) j)=∑ r:Fin S.n,TK i r*TKinv r j:=by
    rw[AO (finCongr zb.symm) _ (fun r:Fin S.n=>ιK (T₀ i r)*(zB⁻¹*TKinv r j)) (fun r=>by rfl)];refine Ag rfl fun r _=>?_;have zO:=An (An vU i) r;simp only[AZ,A2,Am] at zO;rw[zO];calc zB*TK i r*(zB⁻¹*TKinv r j)=(zB*zB⁻¹)*(TK i r*TKinv r j):=by ring
      _ = TK i r*TKinv r j:=by rw[mul_inv_cancel₀ z1,AA]
   rw[zQ,h1]
  intro h0;have h0K:(zx.map ιK).det=0:=by have vW:(zx.map ιK).det=ιK zx.det:=(DT ιK zx).symm;rw[vW,h0,Bn]
  have h1:=Ah Matrix.det uL;rw[Cq,h0K,Bm,Dv] at h1;exact CX h1
 let T₀inv:Matrix (Fin S.n) (Fin (2 ^ m)) (ZMod 7):=Matrix.of fun i j=>zx⁻¹ (Fin.cast zb i) j;have zK:T₀*T₀inv=1:=by
  ext i j;have h1:=An (An (B0 zx (isUnit_iff_ne_zero.mpr zV)) i) j;simp only[Av,T₀inv,Ak] at h1 ⊢;rw[<-h1];exact AO (finCongr zb) _ _ fun r=>by simp[zx]
 have zL:T₀inv*T₀=1:=by
  ext i j;have h1:=An (An (Du zx (isUnit_iff_ne_zero.mpr zV)) (Fin.cast zb i)) (Fin.cast zb j);have hcc:Fin.cast zb.symm (Fin.cast zb j)=j:=A4 rfl;simp only[Av,T₀inv,zx,Ak,hcc] at h1 ⊢;rw[h1];by_cases zE:i=j
  . subst zE;simp
  . have zD:Fin.cast zb i≠Fin.cast zb j:=fun h=>zE (A4 (by simpa using Ah Fin.val h));simp[AH zE,AH zD]
 have vX:∃ zv:ZMod 7,zv≠0/\T₀invᵀ*S.B*T₀inv=zv•b7':=by
  let B1:Matrix (Fin m->Bool) (Fin m->Bool) (Qa 7):=
   Matrix.of fun s t=>dotProduct (e7.symm (Pi.single s 1)) (((T₀invᵀ*S.B*T₀inv).map ιK)*ᵥe7.symm (Pi.single t 1))
  let B2:Matrix (Fin m->Bool) (Fin m->Bool) (Qa 7):=
   Matrix.of fun s t=>dotProduct (e7.symm (Pi.single s 1)) ((b7'.map ιK)*ᵥe7.symm (Pi.single t 1))
  have z2:B2.det≠0:=by
   have zW:b7'*(-b7')=1:=by
    rw[CN];ext i j;simp only[Bh,Av,b7',Ak];rw[AO eB _ (fun u=>Qp B.hm (eB i) u*Qp B.hm u (eB j)) (fun _=>rfl)];have h:=An (An zP.2.1 (eB i)) (eB j);simp only[Av,Bh] at h;rw[h,Dp];by_cases zE:i=j
    . subst zE;simp
    . simp[AH zE,AH (fun h'=>zE (eB.injective h'))]
   have vY:b7'.det≠0:=fun h0=>by
    have:=Ah Matrix.det zW;rw[Cq,h0,Bm,Dv] at this;exact CX this
   intro h0;obtain ⟨v,vI,vO⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr h0;let w:Fin (2 ^ m)->Qa 7:=e7.symm v;have vB:w≠0:=fun h=>vI (e7.symm.injective (h.trans (Bn e7.symm).symm));have hbw:b7'.map ιK*ᵥw=0:=by
    funext i;have uM:∀ u:Fin (2 ^ m)->Qa 7,dotProduct u (b7'.map ιK*ᵥw)=0:=fun u=>by
      have hu:u=∑ s:Fin m->Bool,e7 u s•e7.symm (Pi.single s 1):=(by apply e7.injective;rw[Ba];funext t;simp only[AQ,Bd,AX,e7.apply_symm_apply,AG,Am,Ca,AK,AS,Bq,A8,Ai,↓reduceIte]);have hwv:w=∑ t:Fin m->Bool,v t•e7.symm (Pi.single t 1):=(by apply e7.injective;rw[e7.apply_symm_apply,Ba];funext t;simp only[AQ,Bd,AX,e7.apply_symm_apply,AG,Am,Ca,AK,AS,Bq,A8,Ai,↓reduceIte]);rw[hu,hwv,AJ,sum_dotProduct];refine A1 fun s _=>?_;rw[smul_dotProduct,dotProduct_sum];have uV:=An vO s;simp only[Matrix.mulVec,dotProduct,B2,Ak,EE] at uV;have ve:∑ t,dotProduct (e7.symm (Pi.single s 1)) (b7'.map ιK*ᵥ(v t•e7.symm (Pi.single t 1)))=0:=by rw[<-uV];refine Ag rfl fun t _=>?_;simp only[Al,dotProduct_smul,Am];exact Bb _ _
      rw[ve,smul_zero]
    have:=uM (Pi.single i 1);simpa[dotProduct,AG] using this
   have vZ:(b7'.map ιK).det≠0:=(by have vW:(b7'.map ιK).det=ιK b7'.det:=(DT ιK b7').symm;rw[vW];intro h;exact vY (ιK.injective (by rwa[Bn])));exact vZ (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w,vB,hbw⟩)
  have zY:∀ (M:Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Qa 7)),(∀ r:R,(zt r)ᵀ*M*zt r=M)->∀ r:R,(zq r)ᵀ*Matrix.of (fun s t=>dotProduct (e7.symm (Pi.single s 1)) (M*ᵥe7.symm (Pi.single t 1)))*zq r=Matrix.of (fun s t=>dotProduct (e7.symm (Pi.single s 1)) (M*ᵥe7.symm (Pi.single t 1))):=by
   intro M hM r;ext s t;have h1:∀ u:Fin m->Bool,e7.symm (zq r*ᵥPi.single u 1)=zt r*ᵥe7.symm (Pi.single u 1):=fun u=>by
    apply e7.injective;rw[e7.apply_symm_apply,zG,e7.apply_symm_apply]
   have h2:∀ u:Fin m->Bool,zq r*ᵥPi.single u 1=∑ a,zq r a u•Pi.single a 1:=fun u=>by
    funext a;simp[Matrix.mulVec,dotProduct,AQ,AG]
   have u3:((zq r)ᵀ*Matrix.of (fun s' t'=>dotProduct (e7.symm (Pi.single s' 1)) (M*ᵥe7.symm (Pi.single t' 1)))*zq r) s t=dotProduct (e7.symm (zq r*ᵥPi.single s 1)) (M*ᵥe7.symm (zq r*ᵥPi.single t 1)):=(by rw[h2 s,h2 t,Ba,Ba,AJ,sum_dotProduct];simp only[Av,AM,Ak,Bo];rw[AY];refine Ag rfl fun a _=>?_;rw[Bd,smul_dotProduct,dotProduct_sum,BC];refine Ag rfl fun b _=>?_;rw[Bd,Al,dotProduct_smul,Am,Am];ring);rw[u3,h1 s,h1 t]
   calc dotProduct (zt r*ᵥe7.symm (Pi.single s 1)) (M*ᵥ(zt r*ᵥe7.symm (Pi.single t 1)))
      = dotProduct (Matrix.vecMul (e7.symm (Pi.single s 1)) (zt r)ᵀ) (M*ᵥ(zt r*ᵥe7.symm (Pi.single t 1))):=by rw[AI]
    _ = dotProduct (e7.symm (Pi.single s 1)) (((zt r)ᵀ*M*zt r)*ᵥe7.symm (Pi.single t 1)):=by rw[<-AB];simp only[Ac,Af]
    _ = _:=by rw[hM r];rfl
  have um:∀ r:R,(zq r)ᵀ*B1*zq r=B1:=by
   apply zY;intro r;have h1:(zu r)ᵀ*(T₀invᵀ*S.B*T₀inv)*zu r=T₀invᵀ*S.B*T₀inv:=by
    have vf:r.1.1.val*T₀inv=T₀inv*zu r:=by
      calc r.1.1.val*T₀inv=(T₀inv*T₀)*r.1.1.val*T₀inv:=by rw[zL,AC]
       _ = T₀inv*(zu r*T₀)*T₀inv:=by rw[Af T₀inv,zH r]
       _ = T₀inv*zu r:=by rw[Af,Af,zK,As]
    calc (zu r)ᵀ*(T₀invᵀ*S.B*T₀inv)*zu r
       = (T₀inv*zu r)ᵀ*S.B*(T₀inv*zu r):=by rw[AT];simp only[Af]
      _ = (r.1.1.val*T₀inv)ᵀ*S.B*(r.1.1.val*T₀inv):=by rw[vf]
      _ = T₀invᵀ*(r.1.1.valᵀ*S.B*r.1.1.val)*T₀inv:=by rw[AT];simp only[Af]
      _ = T₀invᵀ*S.B*T₀inv:=by rw[S.B_inv r.1.1 r.1.2]
   have h:=Ah (Matrix.map · ιK) h1;have zO:((zu r)ᵀ).map ιK=(zt r)ᵀ:=by ext a b;rfl
   simpa[Aq,zO,zt] using h
  have un:∀ r:R,(zq r)ᵀ*B2*zq r=B2:=by
   apply zY;intro r;have h:=Ah (Matrix.map · ιK) (vy r);have zO:((zu r)ᵀ).map ιK=(zt r)ᵀ:=by ext a b;rfl
   simpa[Aq,zO,zt] using h
  have zZ:∀ r:R,(B2⁻¹*B1)*zq r=zq r*(B2⁻¹*B1):=fun r=>by
   have uN:B2*B2⁻¹=1:=B0 B2 (isUnit_iff_ne_zero.mpr z2);have uO:B2⁻¹*B2=1:=Du B2 (isUnit_iff_ne_zero.mpr z2);have vq:zq r*zq r⁻¹=1/\zq r⁻¹*zq r=1:=
    ⟨by
      rw[<-AF,By,BI],by rw[<-AF,CK,BI]⟩
   have vr:(zq r)ᵀ*(zq r⁻¹)ᵀ=1/\(zq r⁻¹)ᵀ*(zq r)ᵀ=1:=
    ⟨by
      rw[<-AT,vq.2,BM],
     by rw[<-AT,vq.1,BM]⟩
   have h1:B1*zq r=(zq r⁻¹)ᵀ*B1:=by
    calc B1*zq r=((zq r⁻¹)ᵀ*(zq r)ᵀ)*(B1*zq r):=by rw[vr.2,AC]
      _ = (zq r⁻¹)ᵀ*((zq r)ᵀ*B1*zq r):=by simp only[Af]
      _ = (zq r⁻¹)ᵀ*B1:=by rw[um r]
   have h2:zq r*B2⁻¹=B2⁻¹*(zq r⁻¹)ᵀ:=by
    have h2':B2*zq r=(zq r⁻¹)ᵀ*B2:=by
      calc B2*zq r=((zq r⁻¹)ᵀ*(zq r)ᵀ)*(B2*zq r):=by rw[vr.2,AC]
       _ = (zq r⁻¹)ᵀ*((zq r)ᵀ*B2*zq r):=by simp only[Af]
       _ = (zq r⁻¹)ᵀ*B2:=by rw[un r]
    calc zq r*B2⁻¹=(B2⁻¹*B2)*zq r*B2⁻¹:=by rw[uO,AC]
      _ = B2⁻¹*(B2*zq r)*B2⁻¹:=by simp only[Af]
      _ = B2⁻¹*((zq r⁻¹)ᵀ*B2)*B2⁻¹:=by rw[h2']
      _ = B2⁻¹*(zq r⁻¹)ᵀ:=by rw[Af,Af,uN,As]
   calc (B2⁻¹*B1)*zq r=B2⁻¹*(B1*zq r):=Af _ _ _
    _ = (B2⁻¹*(zq r⁻¹)ᵀ)*B1:=by rw[h1,<-Af]
    _ = zq r*(B2⁻¹*B1):=by rw[<-h2,Af]
  obtain ⟨c₂K,uK⟩:=Q5 (by decide) false ze (B2⁻¹*B1)
   (fun i=>by have h:=zZ (B.x i);dsimp only[zq] at h;rwa[Q7] at h)
   (fun i=>by have h:=zZ (B.y i);dsimp only[zq] at h;rwa[Wd] at h)
  have ux:B1=c₂K•B2:=by
   calc B1=(B2*B2⁻¹)*B1:=by rw[B0 B2 (isUnit_iff_ne_zero.mpr z2),AC]
    _ = B2*(B2⁻¹*B1):=Af _ _ _
    _ = c₂K•B2:=by rw[uK,Ao,As]
  have ui:(T₀invᵀ*S.B*T₀inv).map ιK=c₂K•b7'.map ιK:=by
   ext i j;have vg:∀ u v:Fin (2 ^ m)->Qa 7,dotProduct u (((T₀invᵀ*S.B*T₀inv).map ιK)*ᵥv)=c₂K*dotProduct u ((b7'.map ιK)*ᵥv):=by
    intro u v;have vC:∀ w:Fin (2 ^ m)->Qa 7,w=∑ s:Fin m->Bool,e7 w s•e7.symm (Pi.single s 1):=by intro w;apply e7.injective;rw[Ba];funext t;simp only[AQ,Bd,AX,e7.apply_symm_apply,AG,Am,Ca,AK,AS,Bq,A8,Ai,↓reduceIte]
    conv_lhs=>rw[vC u,vC v]
    conv_rhs=>rw[vC u,vC v]
    simp only[AJ,sum_dotProduct,dotProduct_sum,smul_dotProduct,Al,dotProduct_smul,Am,A6];refine Ag rfl fun s _=>Ag rfl fun t _=>?_;have uj:=An (An ux t) s;simp only[B1,B2,Ak,A2,Am] at uj;rw[uj];ring
   have h:=vg (Pi.single i 1) (Pi.single j 1);simpa[dotProduct,Matrix.mulVec,AG] using h
  let s0:Fin m->Bool:=fun _=>false;let t0:Fin m->Bool:=Function.update s0 ⟨0,B.hm⟩ true;let vD:=eB.symm s0;let vE:=eB.symm t0;have uy:b7' vD vE=-1:=(by simp[b7',vD,vE,Qp,Qv,s0,t0]);let zv:ZMod 7:=-(T₀invᵀ*S.B*T₀inv) vD vE;have vL:ιK zv=c₂K:=(by have h:=An (An ui vD) vE;simp only[AZ,A2,Am,uy,map_neg,BI,mul_neg,AK] at h;simp only[zv,map_neg,h,Dp]);have vF:T₀invᵀ*S.B*T₀inv=zv•b7':=(by ext i j;apply ιK.injective;have h:=An (An ui i) j;simpa[AZ,A2,Am,vL] using h);have zX:zv≠0:=by
   intro h0;rw[h0,Dl] at vF;have hB0:S.B=0:=by
    calc S.B=(T₀ᵀ*T₀invᵀ)*S.B*(T₀inv*T₀):=by
             rw[<-AT,zL,BM,AC,As]
           _ = T₀ᵀ*(T₀invᵀ*S.B*T₀inv)*T₀:=by simp only[Af]
           _ = 0:=by rw[vF,CZ,Ce]
   haveI:Nonempty (Fin S.n):=⟨⟨0,S.hn_pos⟩⟩;exact S.B_det (by rw[hB0];exact Di)
  exact ⟨zv,zX,vF⟩
 obtain ⟨zv,zX,ue⟩:=vX;let S4:Finset R:=Finset.univ.filter fun r=>r*r=zR;let f (v:(Fin m->Bool)->ZMod 7) (r:R):ZMod 7:=dotProduct v (Qp B.hm*ᵥ(zo r*ᵥv));let d (v:(Fin m->Bool)->ZMod 7):ℕ:=(S4.filter fun r=>f v r≠0).card;have z0:∀ v:(Fin m->Bool)->ZMod 7,v≠0->3∣d v:=by
  intro v vI;let u:Fin (2 ^ m)->ZMod 7:=fun i=>v (eB i);let w:Fin S.n->ZMod 7:=T₀inv*ᵥu;have vB:w≠0:=by
   intro hw0;apply vI;funext s;have h1:T₀*ᵥw=u:=by rw[Ac,zK,AN]
   rw[hw0,DZ] at h1;have h2:=An h1 (eB.symm s);simpa[u] using h2.symm
  obtain ⟨g,u0,hgw⟩:=S.SF w vB (Units.mk0 (3:ZMod 7) (fun e=>by
   have h:=Ah ZMod.val e;simp only[QZ] at h;omega))
  let gL:S.L:=⟨g,u0⟩;let zw:R≃*R:=
   {toFun:=fun r=>⟨gL⁻¹*r.1*gL,by simpa using vo.conj_mem r.1 r.2 gL⁻¹⟩
    invFun:=fun r=>⟨gL*r.1*gL⁻¹,vo.conj_mem r.1 r.2 gL⟩
    left_inv:=fun r=>Ae (by group)
    right_inv:=fun r=>Ae (by group)
    map_mul':=fun a b=>Ae (by
      change gL⁻¹*(a.1*b.1)*gL=(gL⁻¹*a.1*gL)*(gL⁻¹*b.1*gL);group) }
  have uW:zw zR=zR:=(by apply Ae;apply Ae;apply A7;change g.inv*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*g.val=-1;simp);have vM:∀ r:R,zv*f v r=dotProduct w (S.B*ᵥ(r.1.1.val*ᵥw)):=fun r=>by
   have h1:dotProduct w (S.B*ᵥ(r.1.1.val*ᵥw))=dotProduct u ((T₀invᵀ*S.B*T₀inv)*ᵥ(zu r*ᵥu)):=by
    have vf:r.1.1.val*T₀inv=T₀inv*zu r:=by
      calc r.1.1.val*T₀inv=(T₀inv*T₀)*r.1.1.val*T₀inv:=by rw[zL,AC]
       _ = T₀inv*(zu r*T₀)*T₀inv:=by rw[Af T₀inv,zH r]
       _ = T₀inv*zu r:=by rw[Af,Af,zK,As]
    calc dotProduct (T₀inv*ᵥu) (S.B*ᵥ(r.1.1.val*ᵥ(T₀inv*ᵥu)))
       = dotProduct (Matrix.vecMul u T₀invᵀ) (S.B*ᵥ((T₀inv*zu r)*ᵥu)):=by rw[AI];congr 2;rw[Ac,vf]
      _ = dotProduct u ((T₀invᵀ*S.B*T₀inv)*ᵥ(zu r*ᵥu)):=by rw[<-AB];simp only[Ac,Af]
   rw[h1,ue,Bv,dotProduct_smul,Am];congr 1;simp only[f,dotProduct,Matrix.mulVec,u,b7',zu,MonoidHom.coe_mk,OneHom.coe_mk,Ak];rw[<-AO eB _ _ (fun _=>rfl)];refine Ag rfl fun i _=>?_;congr 1;rw[<-AO eB _ _ (fun _=>rfl)];refine Ag rfl fun j _=>?_;congr 1;exact (AO eB _ _ (fun _=>rfl)).symm
  have vs:∀ r:R,f v (zw r)=2*f v r:=fun r=>by
   apply Ck zX;rw[vM (zw r),<-Ad,Bb zv 2,Ad,vM r];have hcr:(zw r).1.1.val=g.inv*r.1.1.val*g.val:=rfl
   calc dotProduct w (S.B*ᵥ((zw r).1.1.val*ᵥw))
      = dotProduct w (((g.valᵀ*S.B*g.val)*(g.inv*r.1.1.val*g.val))*ᵥw):=by rw[S.B_inv g u0,hcr,Ac]
    _ = dotProduct w ((g.valᵀ*S.B*r.1.1.val*g.val)*ᵥw):=by simp only[Af,<-Af g.val g.inv,g.val_inv,AC]
    _ = dotProduct (Matrix.vecMul w g.valᵀ) (S.B*ᵥ(r.1.1.val*ᵥ(g.val*ᵥw))):=by rw[<-AB];simp only[Ac,Af]
    _ = dotProduct (g.val*ᵥw) (S.B*ᵥ(r.1.1.val*ᵥ(g.val*ᵥw))):=by rw[AI]
    _ = dotProduct ((3:ZMod 7)•w) (S.B*ᵥ(r.1.1.val*ᵥ((3:ZMod 7)•w))):=by rw[hgw];rfl
    _ = (3*3:ZMod 7)*dotProduct w (S.B*ᵥ(r.1.1.val*ᵥw)):=by simp only[Al,smul_dotProduct,dotProduct_smul,Am];ring
    _ = 2*dotProduct w (S.B*ᵥ(r.1.1.val*ᵥw)):=by congr 1
  let E (a:ZMod 7):Finset R:=S4.filter fun r=>f v r=a;have va:∀ a:ZMod 7,(E a).card=(E (2*a)).card:=fun a=>by
   refine Finset.card_nbij' (fun r=>zw r) (fun r=>zw.symm r) ?_ ?_ ?_ ?_
   . intro r hr;simp only[Finset.mem_coe,E,S4,AL,Ai,B3] at hr ⊢;exact ⟨by rw[<-AF,hr.1,uW],by rw[vs,hr.2]⟩
   .
    intro r hr;simp only[Finset.mem_coe,E,S4,AL,Ai,B3] at hr ⊢;refine ⟨by apply zw.injective;rw[AF,zw.apply_symm_apply,hr.1,uW],?_⟩;have h1:=vs (zw.symm r);rw[zw.apply_symm_apply,hr.2] at h1;have u4:(2:ZMod 7)≠0:=fun e=>by have h:=Ah ZMod.val e;simp only[QZ] at h;omega
    exact Ck u4 h1.symm
   . intro r _;exact zw.symm_apply_apply r
   . intro r _;exact zw.apply_symm_apply r
  have uP:(S4.filter fun r=>f v r≠0)=E 1∪E 2∪E 3∪E 4∪E 5∪E 6:=by
   ext r;simp only[E,Finset.mem_union,AL];constructor
   . rintro ⟨hr,zD⟩;rcases YV (f v r) zD with h | h | h | h | h | h <;> simp[hr,h]
   .
    rintro (((((⟨hr,h⟩ | ⟨hr,h⟩) | ⟨hr,h⟩) | ⟨hr,h⟩) | ⟨hr,h⟩) | ⟨hr,h⟩) <;>
      exact ⟨hr,fun e=>by rw[h] at e;have hv:=Ah ZMod.val e;simp only[QZ] at hv;omega⟩
  have uQ:∀ a b:ZMod 7,a≠b->Disjoint (E a) (E b):=fun a b hab=>
   Finset.disjoint_left.mpr fun r hra hrb=>hab ((Finset.mem_filter.mp hra).2.symm.trans (Finset.mem_filter.mp hrb).2)
  have zah:d v=(E 1).card+(E 2).card+(E 3).card+(E 4).card+(E 5).card+(E 6).card:=by
   dsimp only[d];rw[uP];rw[BN,BN,BN,BN,BN]
   all_goals
    try simp only[Finset.disjoint_union_left]
    repeat constructor
    all_goals apply uQ;intro e;have hv:=Ah ZMod.val e;simp only[QZ] at hv;omega
  have h12:(E 1).card=(E 2).card:=by simpa using va 1
  have h24:(E 2).card=(E 4).card:=by simpa[Yk] using va 2
  have h65:(E 6).card=(E 5).card:=by simpa[YX] using va 6
  have h53:(E 5).card=(E 3).card:=by simpa[YY] using va 5
  refine ⟨(E 1).card+(E 6).card,?_⟩;omega
 let i0:Fin m:=⟨0,by omega⟩;let i1:Fin m:=⟨1,by omega⟩;let i2:Fin m:=⟨2,by omega⟩;let v_m:(Fin m->Bool)->ZMod 7:=fun s=>
  if (∀ i:Fin m,3<=i.val->s i=false)/\(s i0=false\/(s i1=false/\s i2=false)) then 1 else 0
 have uz:v_m≠0:=fun h=>by
  have h0:=An h (fun _=>false);simp[v_m] at h0
 have z7:3∣d v_m:=z0 v_m uz;let zn (b0 b1 b2:Bool):Fin m->Bool:=fun i=>
  if i.val=0 then b0 else if i.val=1 then b1 else if i.val=2 then b2 else false
 let zr (w:(Fin m->Bool)->ZMod 7):QM:=
  (w (zn false false false),w (zn false false true),w (zn false true false),w (zn false true true),w (zn true false false),w (zn true false true),w (zn true true false),w (zn true true true))
 have zA:∀ (i:Fin m) (w:(Fin m->Bool)->ZMod 7) (b0 b1 b2:Bool),(Qv i*ᵥw) (zn b0 b1 b2)=(if i.val=0 then (if zn b0 b1 b2 i then (1:ZMod 7) else -1) else 1)*w (Function.update (zn b0 b1 b2) i (!zn b0 b1 b2 i)):=by
  intro i w b0 b1 b2;simp only[Matrix.mulVec,dotProduct,Qv,Ak];rw[Ay (Function.update (zn b0 b1 b2) i (!zn b0 b1 b2 i))]
  . rw[Az rfl]
  . intro u _ hu;rw[Aw hu,Bm]
  . intro h;exact absurd (Ai _) h
 have v0:∀ w:(Fin m->Bool)->ZMod 7,zr (Qu i0*ᵥw)=Ym (zr w):=by
  intro w;have u5:∀ b0 b1 b2:Bool,(Qu i0*ᵥw) (zn b0 b1 b2)=if b0 then 2*w (zn false b1 b2)+4*w (zn true b1 b2)
    else 3*w (zn false b1 b2)+2*w (zn true b1 b2):=by
   intro b0 b1 b2;simp only[Matrix.mulVec,dotProduct];let sF:=zn false b1 b2;let sT:=zn true b1 b2;have zD:sF≠sT:=fun h=>by have:=An h i0;simp[sF,sT,zn,i0] at this
   rw[Finset.sum_eq_add sF sT zD (fun u _ ⟨huF,huT⟩=>by
    simp only[Qu,show i0.val=0 from rfl,Be,Ak];have v1:¬ ∀ k:Fin m,1<=k.val->zn b0 b1 b2 k=u k:=by
      intro zM;cases uZ:u i0
      .
       apply huF;funext k;by_cases zC:k.val=0
       . have:k=i0:=A4 zC;rw[this,uZ];simp[sF,zn,i0]
       . rw[<-zM k (by omega)];simp[sF,zn,zC]
      .
       apply huT;funext k;by_cases zC:k.val=0
       . have:k=i0:=A4 zC;rw[this,uZ];simp[sT,zn,i0]
       . rw[<-zM k (by omega)];simp[sT,zn,zC]
    rw[Aw v1,Bm]) (fun h=>absurd (Ai sF) h) (fun h=>absurd (Ai sT) h)]
   have hF:∀ k:Fin m,1<=k.val->zn b0 b1 b2 k=sF k:=fun k hk=>by
    have zC:k.val≠0:=by omega
    simp[sF,zn,zC]
   have hT:∀ k:Fin m,1<=k.val->zn b0 b1 b2 k=sT k:=fun k hk=>by
    have zC:k.val≠0:=by omega
    simp[sT,zn,zC]
   simp only[Qu,show i0.val=0 from rfl,Be,Ak,Az hF,Az hT,show sF i0=false by simp[sF,zn,i0],show sT i0=true by simp[sT,zn,i0],show zn b0 b1 b2 i0=b0 by simp[zn,i0]];cases b0 <;> simp[sF,sT]
  simp only[zr,Ym,u5];rfl
 have vh:∀ w:(Fin m->Bool)->ZMod 7,zr (Qv i0*ᵥw)=QY (zr w):=by
  intro w;have vi:∀ b0 b1 b2,Function.update (zn b0 b1 b2) i0 (!zn b0 b1 b2 i0)=zn (!b0) b1 b2:=by
   intro b0 b1 b2;funext k;by_cases zC:k.val=0
   . have:k=i0:=A4 zC;subst this;simp[zn,i0]
   . have zD:k≠i0:=fun h=>zC (Ah Fin.val h);simp[zn,zC,zD]
  have uA:∀ b0 b1 b2,zn b0 b1 b2 i0=b0:=fun _ _ _=>by simp[zn,i0]
  simp only[zr,QY,zA,vi,show i0.val=0 from rfl,Be];simp only[uA];simp
 have v2:∀ w:(Fin m->Bool)->ZMod 7,zr (Qu i1*ᵥw)=Yn (zr w):=by
  intro w;have h1:i1.val≠0:=by dsimp[i1];omega
  simp only[zr,Yn,Qu,Aw h1,BO,show ∀ b0 b1 b2,zn b0 b1 b2 i1=b1 from fun b0 b1 b2=>by simp[zn,i1]];simp
 have v3:∀ w:(Fin m->Bool)->ZMod 7,zr (Qv i1*ᵥw)=Yo (zr w):=by
  intro w;have h1:i1.val≠0:=by dsimp[i1];omega
  have vi:∀ b0 b1 b2,Function.update (zn b0 b1 b2) i1 (!zn b0 b1 b2 i1)=zn b0 (!b1) b2:=by
   intro b0 b1 b2;funext k;by_cases vT:k.val=1
   . have:k=i1:=A4 vT;subst this;simp[zn,i1]
   . have zD:k≠i1:=fun h=>vT (Ah Fin.val h);by_cases zC:k.val=0 <;> simp[zn,zC,vT,zD]
  simp only[zr,Yo,zA,vi,Aw h1];simp
 have v4:∀ w:(Fin m->Bool)->ZMod 7,zr (Qu i2*ᵥw)=Yp (zr w):=by
  intro w;have h2:i2.val≠0:=by dsimp[i2];omega
  simp only[zr,Yp,Qu,Aw h2,BO,show ∀ b0 b1 b2,zn b0 b1 b2 i2=b2 from fun b0 b1 b2=>by simp[zn,i2]];simp
 have v5:∀ w:(Fin m->Bool)->ZMod 7,zr (Qv i2*ᵥw)=Yq (zr w):=by
  intro w;have h2:i2.val≠0:=by dsimp[i2];omega
  have vi:∀ b0 b1 b2,Function.update (zn b0 b1 b2) i2 (!zn b0 b1 b2 i2)=zn b0 b1 (!b2):=by
   intro b0 b1 b2;funext k;by_cases uJ:k.val=2
   . have:k=i2:=A4 uJ;subst this;simp[zn,i2]
   . have zD:k≠i2:=fun h=>uJ (Ah Fin.val h);by_cases zC:k.val=0 <;> by_cases vT:k.val=1 <;> simp[zn,zC,vT,uJ,zD]
  simp only[zr,Yq,zA,vi,Aw h2];simp
 have vN:∀ b0 b1 b2,v_m (zn b0 b1 b2)=if b0=false\/(b1=false/\b2=false) then 1 else 0:=by
  intro b0 b1 b2;have zM:∀ i:Fin m,3<=i.val->zn b0 b1 b2 i=false:=fun i hi=>by
   have h0:i.val≠0:=by omega
   have h1:i.val≠1:=by omega
   have h2:i.val≠2:=by omega
   simp[zn,h0,h1,h2]
  dsimp only[v_m];have v6:((∀ i:Fin m,3<=i.val->zn b0 b1 b2 i=false)/\(zn b0 b1 b2 i0=false\/zn b0 b1 b2 i1=false/\zn b0 b1 b2 i2=false))↔(b0=false\/b1=false/\b2=false):=by
   have h0:zn b0 b1 b2 i0=b0:=by simp[zn,i0]
   have h1:zn b0 b1 b2 i1=b1:=by simp[zn,i1]
   have h2:zn b0 b1 b2 i2=b2:=by simp[zn,i2]
   rw[h0,h1,h2];exact and_iff_right zM
  exact if_congr v6 rfl rfl
 have uo:zr v_m=Q0:=(by simp only[zr,Q0,vN];simp);have up:∀ w:(Fin m->Bool)->ZMod 7,dotProduct v_m w=WW Q0 (zr w):=by
  intro w;let vG:Finset (Fin m->Bool):=
   {zn false false false,zn false false true,zn false true false,zn false true true,zn true false false,zn true false true,zn true true false,zn true true true}
  have v7:dotProduct v_m w=∑ s∈vG,v_m s*w s:=by
   simp only[dotProduct];symm;refine D6 (Finset.subset_univ _) fun s _ hs=>?_;have v1:¬ ∀ i:Fin m,3<=i.val->s i=false:=by
    intro zM;apply hs;have u6:s=zn (s i0) (s i1) (s i2):=by
      funext k;by_cases h0:k.val=0
      . have:k=i0:=A4 h0;rw[this];simp[zn,i0]
      .
       by_cases h1:k.val=1
       . have:k=i1:=A4 h1;rw[this];simp[zn,i1]
       .
        by_cases h2:k.val=2
        . have:k=i2:=A4 h2;rw[this];simp[zn,i2]
        . rw[zM k (by omega)];simp[zn,h0,h1,h2]
    rw[u6];cases s i0 <;> cases s i1 <;> cases s i2 <;> simp[vG]
   simp[v_m,v1]
  rw[v7];have zD:∀ a0 a1 a2 b0 b1 b2:Bool,(a0≠b0\/a1≠b1\/a2≠b2)->zn a0 a1 a2≠zn b0 b1 b2:=by
   intro a0 a1 a2 b0 b1 b2 h zQ;rcases h with h | h | h
   . exact h (by simpa[zn,i0] using An zQ i0)
   . exact h (by simpa[zn,i1] using An zQ i1)
   . exact h (by simpa[zn,i2] using An zQ i2)
  dsimp only[vG]
  repeat' rw[C7 (by simp[zD])]
  simp only[Finset.sum_singleton,WW,Q0,zr,vN];simp;ring
 have vt:∀ (c:Bool) (a b:Fin m->Bool),f v_m (Qc zR B.x B.y c a b)=if ∀ i:Fin m,3<=i.val->b i=false then
      (if c then (-1:ZMod 7) else 1)*WW Q0 (QY (Wb (a i0) (b i0) (a i1) (b i1) (a i2) (b i2) Q0))
    else 0:=by
  intro c a b;let F_mat (i:Fin m):Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7):=
   (if a i then Qu i else 1)*(if b i then Qv i else 1)
  have vu:∀ i j:Fin m,i≠j->F_mat i*F_mat j=F_mat j*F_mat i:=fun i j zE=>by
   dsimp only[F_mat];have v8:∀ (P Q R S:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)),P*R=R*P->P*S=S*P->Q*R=R*Q->Q*S=S*Q->(P*Q)*(R*S)=(R*S)*(P*Q):=fun P Q R S hPR hPS hQR hQS=>by
    calc P*Q*(R*S)=P*(Q*R)*S:=by simp only[Af]
      _ = P*(R*Q)*S:=by rw[hQR]
      _ = (P*R)*(Q*S):=by simp only[Af]
      _ = (R*P)*(S*Q):=by rw[hPR,hQS]
      _ = R*(P*S)*Q:=by simp only[Af]
      _ = R*(S*P)*Q:=by rw[hPS]
      _ = R*S*(P*Q):=by simp only[Af]
   apply v8
   . cases a i <;> cases a j <;> simp[zs.2.1 i j zE]
   . cases a i <;> cases b j <;> simp[zs.2.2.1 i j zE]
   . cases b i <;> cases a j <;> simp[(zs.2.2.1 j i zE.symm).symm]
   . cases b i <;> cases b j <;> simp[zs.2.2.2.1 i j zE]
  have z8:zo (Qc zR B.x B.y c a b)=(if c then (-1:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) else 1)*(F_mat i0*F_mat i1*F_mat i2)*Qb (fun i:Fin m=>if 3<=i.val then F_mat i else 1):=by
   dsimp only[Qc];rw[AF,Yt];have uq:(fun i:Fin m=>zo ((if a i then B.x i else 1)*(if b i then B.y i else 1)))=F_mat:=(by funext i;rw[AF];cases ha:a i <;> cases hb:b i <;> simp[F_mat,ha,hb,uf,ug]);rw[uq];have vj:Qb F_mat=Qb (fun i:Fin m=>if i.val < 3 then F_mat i else 1)*Qb (fun i:Fin m=>if 3<=i.val then F_mat i else 1):=by
    rw[QL]
    .
      congr 1;funext i;by_cases hi:i.val < 3
      . rw[Az hi,Aw (by omega),As]
      . rw[Aw hi,Az (by omega),AC]
    . intro i j zE;by_cases hi:i.val < 3 <;> by_cases hj:3<=j.val <;> simp[hi,hj,vu i j zE]
   have hlo:Qb (fun i:Fin m=>if i.val < 3 then F_mat i else 1)=F_mat i0*F_mat i1*F_mat i2:=by
    obtain ⟨r,hr⟩:∃ r,m=r+3:=⟨m - 3,by omega⟩;subst hr;simp only[Qb];have h0:(0:Fin (r+3))=i0:=A4 rfl;have h1:(Fin.succ 0:Fin (r+3))=i1:=A4 rfl;have h2:(Fin.succ (Fin.succ 0):Fin (r+3))=i2:=A4 rfl;rw[h0,h1,h2,Az (by simp[i0]),Az (by simp[i1]),Az (by simp[i2])];have uB:Qb (fun j:Fin r=>if (Fin.succ (Fin.succ (Fin.succ j))).val < 3 then F_mat (Fin.succ (Fin.succ (Fin.succ j))) else 1)=1:=
      QB _ fun j=>Aw (by simp)
    rw[uB,As,<-Af]
   have uR:zo (if c then zR else 1)=if c then -1 else 1:=by cases c <;> simp[vx]
   rw[uR,vj,hlo];simp only[Af]
  let vk:=Qb (fun i:Fin m=>if 3<=i.val then F_mat i else 1);by_cases zz:∀ i:Fin m,3<=i.val->b i=false
  .
   rw[Az zz];have v9:vk*ᵥv_m=v_m:=by
    have u7:∀ {q:ℕ} (g:Fin q->Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)),(∀ j,g j*ᵥv_m=v_m)->Qb g*ᵥv_m=v_m:=by
      intro q g hg;induction q with
      | zero=>simp[Qb]
      | succ q ih=>simp only[Qb,<-Ac];rw[ih _ (fun j=>hg j.succ),hg 0]
    apply u7;intro i;by_cases uk:3<=i.val
    .
      rw[Az uk];dsimp only[F_mat];rw[zz i uk,Aw Bz,As];cases a i
      . simp
      .
       simp only[Be];funext s;have z9:i.val≠0:=by omega
       simp only[Qu,Aw z9,BO];by_cases ul:s i=false
       . simp[ul]
       . have u8:s i=true:=B6 ul;have vO:v_m s=0:=(by simp only[v_m];rw[Aw (fun h=>by have:=h.1 i uk;rw[u8] at this;exact Bz this.symm)]);rw[vO,AS]
    . rw[Aw uk,AN]
   dsimp only[f];rw[z8,<-Ac,v9,<-Ac];have ur:((if c then (-1:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) else 1)*ᵥ((F_mat i0*F_mat i1*F_mat i2)*ᵥv_m))=(if c then (-1:ZMod 7) else 1)•((F_mat i0*F_mat i1*F_mat i2)*ᵥv_m):=(by cases c <;> simp[BJ]);rw[ur,Al,dotProduct_smul,Am];congr 1;rw[up];change WW Q0 (zr (Qv i0*ᵥ((F_mat i0*F_mat i1*F_mat i2)*ᵥv_m)))=_;rw[vh];congr 2;simp only[F_mat,<-Ac];have zI:∀ (vJ:Bool) (M:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) (g8:QM->QM),(∀ w,zr (M*ᵥw)=g8 (zr w))->∀ w,zr ((if vJ then M else 1)*ᵥw)=if vJ then g8 (zr w) else zr w:=(by intro vJ M g8 hM w;cases vJ <;> simp[hM]);rw[zI (a i0) (Qu i0) Ym v0,zI (b i0) (Qv i0) QY vh,zI (a i1) (Qu i1) Yn v2,zI (b i1) (Qv i1) Yo v3,zI (a i2) (Qu i2) Yp v4,zI (b i2) (Qv i2) Yq v5,uo];rfl
  .
   rw[Aw zz];push Not at zz;obtain ⟨zp,zT,vm⟩:=zz;have us:b zp=true:=B6 vm;have vP:∀ s:Fin m->Bool,s zp=false->(vk*ᵥv_m) s=0:=by
    have ua:vk=(if 3<=zp.val then F_mat zp else 1)*Qb (fun i:Fin m=>if i≠zp/\3<=i.val then F_mat i else 1):=by
      have h1:(if 3<=zp.val then F_mat zp else 1)=Qb (fun i:Fin m=>if i=zp then (if 3<=i.val then F_mat i else 1) else 1):=
       (QN (fun i=>if 3<=i.val then F_mat i else 1) zp).symm
      dsimp only[vk];rw[h1,QL]
      .
       congr 1;funext i;by_cases uX:i=zp
       . subst uX;simp[zT]
       . simp[uX]
      .
       intro i j zE;by_cases hi:i=zp
       . subst hi;by_cases hj:j≠i/\3<=j.val <;> simp[hj,zT,vu i j zE]
       . simp[hi]
    have vH:∀ s:Fin m->Bool,s zp=true->(Qb (fun i:Fin m=>if i≠zp/\3<=i.val then F_mat i else 1)*ᵥv_m) s=0:=by
      have uC:∀ {q:ℕ} (M:Fin q->Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)),(∀ j w,(∀ s,s zp=true->w s=0)->∀ s,s zp=true->(M j*ᵥw) s=0)->∀ w,(∀ s,s zp=true->w s=0)->∀ s,s zp=true->(Qb M*ᵥw) s=0:=by
       intro q M hM w hw;induction q with
       | zero=>intro s hs;simpa[Qb] using hw s hs
       | succ q ih=>
        intro s hs;simp only[Qb,<-Ac];exact hM 0 _ (ih (fun j=>M j.succ) (fun j=>hM j.succ)) s hs
      apply uC
      .
       intro i w hw s hs;by_cases hi:i≠zp/\3<=i.val
       .
        rw[Az hi];dsimp only[F_mat];rw[<-Ac];have u9:i.val≠0:=by omega
        have hY:∀ u,u zp=true->((if b i then Qv i else 1)*ᵥw) u=0:=by
         intro u hu;cases b i
         . simpa using hw u hu
         .
          simp only[Be,Matrix.mulVec,dotProduct,Qv,Ak];refine A1 fun t _=>?_;by_cases ht:t=Function.update u i (!u i)
          . subst ht;rw[hw _ (by simp[hi.1.symm,hu]),AS]
          . rw[Aw ht,Bm]
        cases a i
        . simpa using hY s hs
        . simp only[Be,Qu,Aw u9,BO,hY s hs,AS]
       . rw[Aw hi,AN];exact hw s hs
      . intro s hs;simp only[v_m];rw[Aw (fun h=>by have:=h.1 zp zT;rw[hs] at this;exact Bz this.symm)]
    intro s vw;rw[ua,Az zT,<-Ac];change (((if a zp then Qu zp else 1)*(if b zp then Qv zp else 1))*ᵥ(Qb (fun i:Fin m=>if i≠zp/\3<=i.val then F_mat i else 1)*ᵥv_m)) s=0;rw[us];simp only[Be];rw[<-Ac];have ut:zp.val≠0:=by omega
    have hY:(Qv zp*ᵥ(Qb (fun i:Fin m=>if i≠zp/\3<=i.val then F_mat i else 1)*ᵥv_m)) s=0:=by
      change ∑ t:Fin m->Bool,Qv zp s t*(Qb (fun i:Fin m=>if i≠zp/\3<=i.val then F_mat i else 1)*ᵥv_m) t=0;refine A1 fun t _=>?_;by_cases ht:t=Function.update s zp (!s zp)
      . subst ht;rw[vH (Function.update s zp (!s zp)) (by simp[vw]),AS]
      . simp only[Qv,Ak,Aw ht,Bm]
    cases a zp
    . rw[Aw Bz,AN];exact hY
    . rw[Az rfl];simp only[Qu,Aw ut,BO,hY,AS]
   have z3:∀ (w:(Fin m->Bool)->ZMod 7),(∀ s,s zp=false->w s=0)->∀ (i:Fin m),i.val < 3->(∀ s,s zp=false->(Qu i*ᵥw) s=0)/\(∀ s,s zp=false->(Qv i*ᵥw) s=0):=by
    intro w hw i hi;have hki:zp≠i:=fun h=>by subst h;omega
    constructor
    .
      intro s vw;by_cases z9:i.val=0
      .
       simp only[Matrix.mulVec,dotProduct,Qu,Az z9,Ak];refine A1 fun u _=>?_;by_cases zM:∀ r:Fin m,1<=r.val->s r=u r
       . rw[hw u ((zM zp (by omega)).symm.trans vw),AS]
       . rw[Aw zM,Bm]
      . simp only[Qu,Aw z9,BO,hw s vw,AS]
    .
      intro s vw;simp only[Matrix.mulVec,dotProduct,Qv,Ak];refine A1 fun u _=>?_;by_cases hu:u=Function.update s i (!s i)
      . subst hu;rw[hw _ (by simp[hki,vw]),AS]
      . rw[Aw hu,Bm]
   have z4:∀ (i:Fin m),i.val < 3->∀ w,(∀ s,s zp=false->w s=0)->∀ s,s zp=false->(F_mat i*ᵥw) s=0:=by
    intro i hi w hw;dsimp only[F_mat];rw[<-Ac];have hY:∀ s,s zp=false->((if b i then Qv i else 1)*ᵥw) s=0:=by
      cases b i;· exact fun s hs=>by simpa using hw s hs
      . exact (z3 w hw i hi).2
    cases a i;· exact fun s hs=>by simpa using hY s hs
    . exact (z3 _ hY i hi).1
   have vn:∀ s,s zp=false->(Qp B.hm*ᵥ(zo (Qc zR B.x B.y c a b)*ᵥv_m)) s=0:=by
    rw[z8,<-Ac,<-Ac,<-Ac,<-Ac];have h1:=z4 i2 (by simp[i2]) _ vP;have h2:=z4 i1 (by simp[i1]) _ h1;have h3:=z4 i0 (by simp[i0]) _ h2;have h4:∀ s,s zp=false->((if c then (-1:Matrix (Fin m->Bool) (Fin m->Bool) (ZMod 7)) else 1)*ᵥ(F_mat i0*ᵥF_mat i1*ᵥF_mat i2*ᵥvk*ᵥv_m)) s=0:=by
      cases c <;> intro s hs
      . rw[Aw Bz,AN];exact h3 s hs
      . rw[Az rfl,BJ,AN,Pi.neg_apply,h3 s hs,neg_zero]
    exact (z3 _ h4 i0 (by simp[i0])).2
   dsimp only[f,dotProduct];refine A1 fun s _=>?_;by_cases uY:s zp=false
   . rw[vn s uY,AS]
   . have zaa:s zp=true:=B6 uY;have vO:v_m s=0:=(by simp only[v_m];rw[Aw (fun h=>by have:=h.1 zp zT;rw[zaa] at this;exact Bz this.symm)]);rw[vO,Bm]
 have ub:∀ (c:Bool) (a b:Fin m->Bool),(∀ i:Fin m,3<=i.val->b i=false)->(Qc zR B.x B.y c a b∈S4↔WR (a i0) (b i0) (a i1) (b i1) (a i2) (b i2)=true):=by
  intro c a b zz;simp only[S4,AL,Ai,B3];have zab:∀ r:R,zR*r=r*zR:=fun r=>
   (Subgroup.mem_center_iff.mp ((za.center_iff zR).mpr (Or.inr rfl)) r).symm
  rw[Wi false zR B.x B.y zab za.z_sq B.hxy_same B.hxx B.hxy B.hyy B.hsq_x B.hsq_y (c,a,b) (c,a,b)];have zac:(fun i=>xor (a i) (a i))=fun _=>false:=funext fun i=>B9 (a i);have zad:(fun i=>xor (b i) (b i))=fun _=>false:=funext fun i=>B9 (b i);have vv:zR=Qc zR B.x B.y true (fun _=>false) (fun _=>false):=(by simp[Qc,QB]);have v6:Qc zR B.x B.y (QF false (c,a,b) (c,a,b)).1 (QF false (c,a,b) (c,a,b)).2.1
    (QF false (c,a,b) (c,a,b)).2.2=zR↔(QF false (c,a,b) (c,a,b)).1=true:=by
   constructor
   . intro zQ;have zae:(Qe za B) (QF false (c,a,b) (c,a,b))=(Qe za B) (true,fun _=>false,fun _=>false):=(by rw[Qs,Qs,<-vv];exact zQ);exact Ah Prod.fst ((Qe za B).injective zae)
   . intro zO;dsimp only[QF] at zO ⊢;rw[zO,zac,zad];exact vv.symm
  rw[v6];dsimp only[QF];rw[B9,Dz];let zy (i:Fin m):Bool:=
   xor (b i&&a i) (xor (decide (i.val=0)&&!false&&a i&&a i) (decide (i.val=0)&&!false&&b i&&b i))
  have vQ:∀ i:Fin m,3<=i.val->zy i=false:=fun i hi=>by
   have z9:i.val≠0:=by omega
   simp[zy,zz i hi,z9]
  have uD:zy i0=xor (b i0&&a i0) (xor (a i0) (b i0)):=(by cases ha:a i0 <;> cases hb:b i0 <;> simp[zy,i0,ha,hb]);have uE:zy i1=(b i1&&a i1):=by
   have h1:i1.val≠0:=by dsimp[i1];omega
   simp[zy,h1]
  have uF:zy i2=(b i2&&a i2):=by
   have h2:i2.val≠0:=by dsimp[i2];omega
   simp[zy,h2]
  have uc:Qt zy=xor (xor (zy i0) (zy i1)) (zy i2):=(by obtain ⟨r,hr⟩:∃ r,m=r+3:=⟨m - 3,by omega⟩;subst hr;simp only[Qt];have h0:(0:Fin (r+3))=i0:=A4 rfl;have h1:(Fin.succ 0:Fin (r+3))=i1:=A4 rfl;have h2:(Fin.succ (Fin.succ 0):Fin (r+3))=i2:=A4 rfl;rw[h0,h1,h2,WG _ (fun j=>vQ _ (by simp)),Ex,<-Bool.xor_assoc]);change Qt zy=true↔_;rw[uc,uD,uE,uF];rfl
 have uG:d v_m=2 ^ (m - 3)*64:=by
  dsimp only[d];rw[Finset.card_eq_sum_ones];have uS:∑ r∈S4.filter (fun r=>f v_m r≠0),(1:ℕ)=∑ r:R,if r∈S4/\f v_m r≠0 then 1 else 0:=(by rw[<-Finset.sum_filter];congr 1;ext r;simp[and_comm]);rw[uS,<-AO (Qe za B) _ _ (fun _=>rfl)];simp_rw[Qs];have uT:∑ t:Bool×(Fin m->Bool)×(Fin m->Bool),(if Qc zR B.x B.y t.1 t.2.1 t.2.2∈S4/\f v_m (Qc zR B.x B.y t.1 t.2.1 t.2.2)≠0 then 1 else 0)=∑ c:Bool,∑ a:Fin m->Bool,∑ b:Fin m->Bool,if (∀ i:Fin m,3<=i.val->b i=false)/\WR (a i0) (b i0) (a i1) (b i1) (a i2) (b i2)=true/\WW Q0 (QY (Wb (a i0) (b i0) (a i1) (b i1) (a i2) (b i2) Q0))≠0
      then 1 else 0:=by
   simp_rw[C4];refine Ag rfl fun c _=>Ag rfl fun a _=>Ag rfl fun b _=>?_;change (if Qc zR B.x B.y c a b∈S4/\f v_m (Qc zR B.x B.y c a b)≠0 then 1 else 0)=_;refine if_congr ?_ rfl rfl;by_cases zz:∀ i:Fin m,3<=i.val->b i=false
   .
    have vR:=vt c a b;rw[Az zz] at vR;rw[vR,ub c a b zz];have zaf:(if c then (-1:ZMod 7) else 1)≠0:=by
      cases c
      . exact DL
      . exact neg_ne_zero.mpr DL
    rw[mul_ne_zero_iff];exact ⟨fun ⟨h1,_,h2⟩=>⟨zz,h1,h2⟩,fun ⟨_,h1,h2⟩=>⟨h1,zaf,h2⟩⟩
   . have vR:=vt c a b;rw[Aw zz] at vR;simp[zz,vR]
  change (∑ t:Bool×(Fin m->Bool)×(Fin m->Bool),if Qc zR B.x B.y t.1 t.2.1 t.2.2∈S4/\f v_m (Qc zR B.x B.y t.1 t.2.1 t.2.2)≠0 then 1 else 0)=_;rw[uT];let zN:(Fin m->Bool) ≃ ((Bool×Bool×Bool)×(Fin (m - 3)->Bool)):=
   {toFun:=fun g=>((g i0,g i1,g i2),fun j=>g ⟨j.val+3,by have:=j.isLt;omega⟩)
    invFun:=fun p k=>
      if h0:k.val=0 then p.1.1
      else if h1:k.val=1 then p.1.2.1
      else if h2:k.val=2 then p.1.2.2
      else p.2 ⟨k.val - 3,by have:=k.isLt;omega⟩
    left_inv:=fun g=>by
      funext k;dsimp only;by_cases h0:k.val=0
      . rw[dif_pos h0];congr 1;exact A4 h0.symm
      .
       rw[dif_neg h0];by_cases h1:k.val=1
       . rw[dif_pos h1];congr 1;exact A4 h1.symm
       .
        rw[dif_neg h1];by_cases h2:k.val=2
        . rw[dif_pos h2];congr 1;exact A4 h2.symm
        . rw[dif_neg h2];congr 1;exact A4 (by dsimp;omega)
    right_inv:=fun ⟨⟨x0,x1,x2⟩,rest⟩=>by
      refine Dr (Dr ?_ (Dr ?_ ?_)) (funext fun j=>?_)
      . simp[i0]
      . simp[i1]
      . simp[i2]
      .
       have h0:j.val+3≠0:=by omega
       have h1:j.val+3≠1:=by omega
       have h2:j.val+3≠2:=by omega
       simp only[h0,h1,h2,dite_false]
       exact Ah rest (A4 (by dsimp;omega)) }
  have vS:∀ b:Fin m->Bool,(∀ i:Fin m,3<=i.val->b i=false)↔(zN b).2=fun _=>false:=by
   intro b;constructor
   . intro h;funext j;exact h ⟨j.val+3,by have:=j.isLt;omega⟩ (by dsimp;omega)
   .
    intro h i hi
    have:=An h ⟨i.val - 3,by have:=i.isLt;omega⟩
    have zQ:(⟨(⟨i.val - 3,by have:=i.isLt;omega⟩:Fin (m - 3)).val+3,by have:=i.isLt;omega⟩:Fin m)=i:=A4 (by dsimp;omega);simpa[zN,zQ] using this
  have uH:∀ c:Bool,∑ a:Fin m->Bool,∑ b:Fin m->Bool,(if (∀ i:Fin m,3<=i.val->b i=false)/\WR (a i0) (b i0) (a i1) (b i1) (a i2) (b i2)=true/\WW Q0 (QY (Wb (a i0) (b i0) (a i1) (b i1) (a i2) (b i2) Q0))≠0 then 1 else 0)=2 ^ (m - 3)*Ww:=by
   intro _;rw[AO zN _ (fun pa=>∑ pb:(Bool×Bool×Bool)×(Fin (m - 3)->Bool),if pb.2=(fun _=>false)/\WR pa.1.1 pb.1.1 pa.1.2.1 pb.1.2.1 pa.1.2.2 pb.1.2.2=true/\WW Q0 (QY (Wb pa.1.1 pb.1.1 pa.1.2.1 pb.1.2.1 pa.1.2.2 pb.1.2.2 Q0))≠0 then 1 else 0) (fun a=>AO zN _ _ (fun b=>if_congr (by rw[vS b];rfl) rfl rfl))];rw[C4];dsimp only;have uI:∀ pa1:Bool×Bool×Bool,∀ pa2:Fin (m - 3)->Bool,∑ pb:(Bool×Bool×Bool)×(Fin (m - 3)->Bool),(if pb.2=(fun _=>false)/\WR pa1.1 pb.1.1 pa1.2.1 pb.1.2.1 pa1.2.2 pb.1.2.2=true/\WW Q0 (QY (Wb pa1.1 pb.1.1 pa1.2.1 pb.1.2.1 pa1.2.2 pb.1.2.2 Q0))≠0 then 1 else 0)=∑ pb1:Bool×Bool×Bool,if WR pa1.1 pb1.1 pa1.2.1 pb1.2.1 pa1.2.2 pb1.2.2=true/\WW Q0 (QY (Wb pa1.1 pb1.1 pa1.2.1 pb1.2.1 pa1.2.2 pb1.2.2 Q0))≠0
       then 1 else 0:=fun pa1 _=>by
    rw[C4];dsimp only;refine Ag rfl fun pb1 _=>?_;rw[Ay (fun _:Fin (m - 3)=>false)]
    . simp
    . intro pb2 _ zD;simp[zD]
    . intro h;exact absurd (Ai _) h
   refine (Ag rfl fun pa1 _=>Ag rfl fun pa2 _=>uI pa1 pa2).trans ?_;simp only[Cm,BS,Cl,C6,AW,Am];rw[<-A6];congr 1
  simp_rw[uH true];rw[Ea,YD];ring
 rw[uG] at z7;have zag:Nat.Coprime 3 (2 ^ (m - 3)*64):=
  Nat.Coprime.mul_right (Eo _ (by decide)) (by decide)
 have h1:3∣1:=by
  have:=DR (EO 3) z7
  rwa[zag.gcd_eq_one] at this
 omega
set_option maxHeartbeats 800000 in
lemma YU [Fact (Nat.Prime 7)]
  {N:ℕ} {zc:0 < N} {ze:¬ 7∣N}
  {ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N zc ze ι) (zb:(⟨Qd S.n 7,S.negOne_mem⟩:S.L)∈O2 S.L) (za:Qn (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zb⟩) (B:Qm (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zb⟩ 2 false) (zf:S.n=2 ^ 2) (zd:∀ g:S.L,(∀ r∈O2 S.L,g*r=r*g)->g.1=1\/g.1=Qd S.n 7) : False:=by
 classical
 let R:=O2 S.L;have vj:R.Normal:=QI S.L;haveI:Fintype S.L:=Fintype.ofFinite S.L;haveI:Fintype R:=Fintype.ofFinite R;let zL:S.L:=⟨Qd S.n 7,S.negOne_mem⟩;let zR:R:=⟨zL,zb⟩;have zY:Nat.card R=32:=by simpa using B.hcard
 have z9:∀ r:R,zR*r=r*zR:=fun r=>
  (Subgroup.mem_center_iff.mp ((za.center_iff zR).mpr (Or.inr rfl)) r).symm
 let zi (g:S.L):R≃*R:=
  {toFun:=fun r=>⟨g*r.1*g⁻¹,vj.conj_mem r.1 r.2 g⟩
   invFun:=fun r=>⟨g⁻¹*r.1*g,by simpa using vj.conj_mem r.1 r.2 g⁻¹⟩
   left_inv:=fun r=>Ae (by group)
   right_inv:=fun r=>Ae (by group)
   map_mul':=fun a b=>Ae (by
    change g*(a.1*b.1)*g⁻¹=(g*a.1*g⁻¹)*(g*b.1*g⁻¹);group) }
 have v4:∀ g:S.L,zi g zR=zR:=fun g=>by
  apply Ae;apply Ae;apply A7;change g.1.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*g.1.inv=-1;simp
 let zF (a0 b0 a1 b1:Bool):R:=
  Qc zR B.x B.y false (fun i=>if i=0 then a0 else a1) (fun i=>if i=0 then b0 else b1)
 let u:Fin 5->R:=![zF false false false true,zF false false true false,zF false true true true,zF true false true true,zF true true true true];have vw:∀ c1 c2 a1 b1 a2 b2,Qc zR B.x B.y c1 a1 b1*Qc zR B.x B.y c2 a2 b2=
    let vk:=QF false (c1,a1,b1) (c2,a2,b2);Qc zR B.x B.y vk.1 vk.2.1 vk.2.2:=
  fun c1 c2 a1 b1 a2 b2=>
   Wi false zR B.x B.y z9 za.z_sq B.hxy_same B.hxx B.hxy B.hyy B.hsq_x B.hsq_y (c1,a1,b1) (c2,a2,b2)
 have zS:zR*zR=1:=za.z_sq;have va:∀ (c:Bool) (a b:Fin 2->Bool),Qc zR B.x B.y c a b*Qc zR B.x B.y c a b=1↔xor (xor (b 0&&a 0) (xor (a 0) (b 0))) (b 1&&a 1)=false:=by
  intro c a b;rw[vw];have vq:(1:R)=Qc zR B.x B.y false (fun _=>false) (fun _=>false):=by simp[Qc,QB]
  have uY:Qc zR B.x B.y (QF false (c,a,b) (c,a,b)).1 (QF false (c,a,b) (c,a,b)).2.1
    (QF false (c,a,b) (c,a,b)).2.2=1↔(QF false (c,a,b) (c,a,b)).1=false:=by
   constructor
   . intro h;have h':(Qe za B) (QF false (c,a,b) (c,a,b))=(Qe za B) (false,fun _=>false,fun _=>false):=(by rw[Qs,Qs,<-vq];exact h);exact Ah Prod.fst ((Qe za B).injective h')
   . intro hf;dsimp only[QF] at hf ⊢;rw[hf,show (fun i=>xor (a i) (a i))=fun _=>false from funext fun i=>B9 (a i),show (fun i=>xor (b i) (b i))=fun _=>false from funext fun i=>B9 (b i),vq]
  rw[uY];dsimp only[QF];have h1:(Fin.succ 0:Fin 2)=1:=rfl;simp only[Qt,h1,B9,Dz];cases a 0 <;> cases b 0 <;> cases a 1 <;> cases b 1 <;> simp
 have zm:∀ k:Fin 5,u k≠1/\u k≠zR/\u k*u k=1:=by
  have v5:∀ (a0 b0 a1 b1:Bool),(a0||b0||a1||b1)=true->zF a0 b0 a1 b1≠1/\zF a0 b0 a1 b1≠zR:=by
   intro a0 b0 a1 b1 uo;have vq:(1:R)=Qc zR B.x B.y false (fun _=>false) (fun _=>false):=by simp[Qc,QB]
   have uZ:zR=Qc zR B.x B.y true (fun _=>false) (fun _=>false):=by simp[Qc,QB]
   constructor
   . intro h;have h':(Qe za B) (false,fun i=>if i=0 then a0 else a1,fun i=>if i=0 then b0 else b1)=(Qe za B) (false,fun _=>false,fun _=>false):=(by rw[Qs,Qs,<-vq];exact h);have zn:=(Qe za B).injective h';have zt:=An (Ah (fun t=>t.2.1) zn) 0;have zu:=An (Ah (fun t=>t.2.1) zn) 1;have zv:=An (Ah (fun t=>t.2.2) zn) 0;have zw:=An (Ah (fun t=>t.2.2) zn) 1;simp at zt zu zv zw;simp[zt,zu,zv,zw] at uo
   . intro h;have h':(Qe za B) (false,fun i=>if i=0 then a0 else a1,fun i=>if i=0 then b0 else b1)=(Qe za B) (true,fun _=>false,fun _=>false):=(by rw[Qs,Qs,<-uZ];exact h);exact Bz (Ah Prod.fst ((Qe za B).injective h'))
  intro k;fin_cases k <;> refine ⟨(v5 _ _ _ _ (by decide)).1,(v5 _ _ _ _ (by decide)).2,(va _ _ _).mpr (by decide)⟩
 have z4:∀ r:R,r≠1/\r≠zR/\r*r=1->∃! k:Fin 5,r=u k\/r=zR*u k:=by
  intro r ⟨vo,hrz,hrsq⟩;obtain ⟨⟨c,a,b⟩,hr⟩:=(Qe za B).surjective r;have un:r=Qc zR B.x B.y c a b:=hr.symm;rw[un] at vo hrz hrsq;have hq:=(va c a b).mp hrsq;have vL:∀ a' b',zR*Qc zR B.x B.y false a' b'=Qc zR B.x B.y true a' b':=fun a' b'=>by
   simp[Qc]
  have zr:∀ k:Fin 5,(r=u k\/r=zR*u k)↔(a 0=(if k=3\/k=4 then true else false)/\b 0=(if k=2\/k=4 then true else false)/\a 1=(if k=0 then false else true)/\b 1=(if k=1 then false else true)):=by
   intro k;have uE:∀ a0 b0 a1 b1,(Qc zR B.x B.y c a b=zF a0 b0 a1 b1\/Qc zR B.x B.y c a b=zR*zF a0 b0 a1 b1)↔(a 0=a0/\b 0=b0/\a 1=a1/\b 1=b1):=by
    intro a0 b0 a1 b1;rw[vL];constructor
    .
     rintro (h | h)
     . have h':(Qe za B) (c,a,b)=(Qe za B) (false,fun i=>if i=0 then a0 else a1,fun i=>if i=0 then b0 else b1):=(by rw[Qs,Qs];exact h);have zn:=(Qe za B).injective h';exact ⟨by simpa using An (Ah (fun t=>t.2.1) zn) 0,by simpa using An (Ah (fun t=>t.2.2) zn) 0,by simpa using An (Ah (fun t=>t.2.1) zn) 1,by simpa using An (Ah (fun t=>t.2.2) zn) 1⟩
     . have h':(Qe za B) (c,a,b)=(Qe za B) (true,fun i=>if i=0 then a0 else a1,fun i=>if i=0 then b0 else b1):=(by rw[Qs,Qs];exact h);have zn:=(Qe za B).injective h';exact ⟨by simpa using An (Ah (fun t=>t.2.1) zn) 0,by simpa using An (Ah (fun t=>t.2.2) zn) 0,by simpa using An (Ah (fun t=>t.2.1) zn) 1,by simpa using An (Ah (fun t=>t.2.2) zn) 1⟩
    .
     rintro ⟨zt,zv,zu,zw⟩;have vx:a=fun i=>if i=0 then a0 else a1:=funext fun i=>by fin_cases i <;> simp[zt,zu]
     have vy:b=fun i=>if i=0 then b0 else b1:=funext fun i=>by fin_cases i <;> simp[zv,zw]
     cases c
     . left;rw[vx,vy]
     . right;rw[vx,vy]
   rw[un];fin_cases k <;> simpa[u] using uE _ _ _ _
  have uo:¬ (a 0=false/\b 0=false/\a 1=false/\b 1=false):=by
   rintro ⟨zt,zv,zu,zw⟩;have vx:a=fun _=>false:=funext fun i=>by fin_cases i <;> simp[zt,zu]
   have vy:b=fun _=>false:=funext fun i=>by fin_cases i <;> simp[zv,zw]
   cases c
   . exact vo (by rw[vx,vy];simp[Qc,QB])
   . exact hrz (by rw[vx,vy];simp[Qc,QB])
  cases zt:a 0 <;> cases zv:b 0 <;> cases zu:a 1 <;> cases zw:b 1
  all_goals simp[zt,zv,zu,zw] at hq uo
  .
   refine ⟨0,(zr 0).mpr (by simp[zt,zv,zu,zw]),fun k hk=>?_⟩
   have:=(zr k).mp hk;fin_cases k <;> simp[zt,zv,zu,zw] at this ⊢
  .
   refine ⟨1,(zr 1).mpr (by simp[zt,zv,zu,zw]),fun k hk=>?_⟩
   have:=(zr k).mp hk;fin_cases k <;> simp[zt,zv,zu,zw] at this ⊢
  .
   refine ⟨2,(zr 2).mpr (by simp[zt,zv,zu,zw]),fun k hk=>?_⟩
   have:=(zr k).mp hk;fin_cases k <;> simp[zt,zv,zu,zw] at this ⊢
  .
   refine ⟨3,(zr 3).mpr (by simp[zt,zv,zu,zw]),fun k hk=>?_⟩
   have:=(zr k).mp hk;fin_cases k <;> simp[zt,zv,zu,zw] at this ⊢
  .
   refine ⟨4,(zr 4).mpr (by simp[zt,zv,zu,zw]),fun k hk=>?_⟩
   have:=(zr k).mp hk;fin_cases k <;> simp[zt,zv,zu,zw] at this ⊢
 have zZ:∀ (g:S.L) (k:Fin 5),∃! j:Fin 5,zi g (u k)=u j\/zi g (u k)=zR*u j:=fun g k=>by
  apply z4 (zi g (u k));have hk:=zm k;refine ⟨fun h=>hk.1 ((zi g).injective (h.trans (BI _).symm)),fun h=>hk.2.1 ((zi g).injective (h.trans (v4 g).symm)),by rw[<-AF,hk.2.2,BI]⟩
 let zj (g:S.L) (k:Fin 5):Fin 5:=Classical.choose (zZ g k).exists;have zq:∀ g k,zi g (u k)=u (zj g k)\/zi g (u k)=zR*u (zj g k):=
  fun g k=>Classical.choose_spec (zZ g k).exists
 have zJ:∀ g k j,(zi g (u k)=u j\/zi g (u k)=zR*u j)->j=zj g k:=
  fun g k j hj=>(zZ g k).unique hj (zq g k)
 have zO:∀ g₁ g₂ k,zj (g₁*g₂) k=zj g₁ (zj g₂ k):=fun g₁ g₂ k=>by
  symm;apply zJ
  have up:zi (g₁*g₂) (u k)=zi g₁ (zi g₂ (u k)):=Ae (by
   change (g₁*g₂)*(u k).1*(g₁*g₂)⁻¹=g₁*(g₂*(u k).1*g₂⁻¹)*g₁⁻¹;group)
  rw[up];rcases zq g₂ k with h2 | h2 <;> rw[h2]
  . exact zq g₁ (zj g₂ k)
  .
   rw[AF,v4 g₁];rcases zq g₁ (zj g₂ k) with h1 | h1 <;> rw[h1]
   . right;rfl
   . left;rw[<-Ad,za.z_sq,AA]
 have zP:∀ k,zj 1 k=k:=fun k=>by
  symm;apply zJ;left;exact Ae (by simp[zi])
 let ψ:S.L→*Equiv.Perm (Fin 5):=
  {toFun:=fun g=>
    {toFun:=zj g
     invFun:=zj g⁻¹
     left_inv:=fun k=>by rw[<-zO,CK,zP]
     right_inv:=fun k=>by rw[<-zO,By,zP] }
   map_one':=Ec zP
   map_mul':=fun g₁ g₂=>Ec (zO g₁ g₂) }
 have zG:ψ.ker=R:=by
  apply DP
  .
   intro g hg;rw[Bw] at hg;have zK:∀ k:Fin 5,zi g (u k)=u k\/zi g (u k)=zR*u k:=fun k=>by
    have h1:zj g k=k:=DV hg k;simpa[h1] using zq g k
   have zM:∀ zg r₂:R,(zi g zg=zg\/zi g zg=zR*zg)->(zi g r₂=r₂\/zi g r₂=zR*r₂)->zi g (zg*r₂)=zg*r₂\/zi g (zg*r₂)=zR*(zg*r₂):=fun zg r₂ h1 h2=>by
    rw[AF];rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw[h1,h2]
    . left;rfl
    . right;rw[<-Ad,<-z9 zg,Ad]
    . right;rw[Ad]
    . left;rw[Ad,<-Ad zg,<-z9 zg,<-Ad zR,<-Ad zR zR,zS,AA]
   have vM:B.y 1=u 0:=by simp[u,zF,Qc,Qb]
   have vN:B.x 1=u 1:=by simp[u,zF,Qc,Qb]
   have u0:B.y 0=u 2*(u 0*u 1):=by
    have h1:u 2=B.y 0*(B.x 1*B.y 1):=by simp[u,zF,Qc,Qb,Ad]
    rw[h1,<-vM,<-vN];have vr:B.x 1*B.x 1=1:=by simpa using B.hsq_x 1
    have vs:B.y 1*B.y 1=1:=by simpa using B.hsq_y 1
    calc B.y 0=B.y 0*(B.x 1*(B.y 1*B.y 1)*B.x 1):=by rw[vs,AK,vr,AK]
     _ = B.y 0*(B.x 1*B.y 1)*(B.y 1*B.x 1):=by simp only[Ad]
   have u1:B.x 0=u 3*(u 0*u 1):=by
    have h1:u 3=B.x 0*(B.x 1*B.y 1):=by simp[u,zF,Qc,Qb,Ad]
    rw[h1,<-vM,<-vN];have vr:B.x 1*B.x 1=1:=by simpa using B.hsq_x 1
    have vs:B.y 1*B.y 1=1:=by simpa using B.hsq_y 1
    calc B.x 0=B.x 0*(B.x 1*(B.y 1*B.y 1)*B.x 1):=by rw[vs,AK,vr,AK]
     _ = B.x 0*(B.x 1*B.y 1)*(B.y 1*B.x 1):=by simp only[Ad]
   have hfx:∀ i:Fin 2,g*(B.x i).1*g⁻¹=(B.x i).1\/g*(B.x i).1*g⁻¹=zL*(B.x i).1:=fun i=>by
    fin_cases i
    . have h:=zM _ _ (zK 3) (zM _ _ (zK 0) (zK 1));rw[<-u1] at h;exact h.imp (Ah Subtype.val) (Ah Subtype.val)
    . have h:=zK 1;rw[<-vN] at h;exact h.imp (Ah Subtype.val) (Ah Subtype.val)
   have hfy:∀ i:Fin 2,g*(B.y i).1*g⁻¹=(B.y i).1\/g*(B.y i).1*g⁻¹=zL*(B.y i).1:=fun i=>by
    fin_cases i
    . have h:=zM _ _ (zK 2) (zM _ _ (zK 0) (zK 1));rw[<-u0] at h;exact h.imp (Ah Subtype.val) (Ah Subtype.val)
    . have h:=zK 0;rw[<-vM] at h;exact h.imp (Ah Subtype.val) (Ah Subtype.val)
   exact W9 S zb za B zd g hfx hfy
  .
   intro r hr;rw[Bw];apply Ec;intro k;change zj r k=k;symm;apply zJ;have zs:=za.comm_mem ⟨r,hr⟩ (u k)
   have zz:zi r (u k)=(⟨r,hr⟩*u k*(⟨r,hr⟩:R)⁻¹*(u k)⁻¹)*u k:=Ae (by
    change r*(u k).1*r⁻¹=r*(u k).1*r⁻¹*(u k).1⁻¹*(u k).1;group)
   rcases zs with h1 | hz
   . left;rw[zz,h1,AA]
   . right;rw[zz,hz]
 have ub:Nat.card S.L=32*Nat.card ψ.range:=by
  have h1:=BX ψ.ker;have h2:Nat.card (S.L ⧸ ψ.ker)=Nat.card ψ.range:=
   Bc (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  change Nat.card ψ.ker*Nat.card (S.L ⧸ ψ.ker)=Nat.card S.L at h1;rw[h2,zG,zY] at h1;exact h1.symm
 have vt:Nat.card ψ.range∣120:=(by have h1:=Cf ψ.range;have h2:Nat.card (Equiv.Perm (Fin 5))=120:=(by rw[Au,D5,AW];decide);rwa[h2] at h1);have vz:¬ 9∣Nat.card S.L:=by
  intro h9;have z0:Nat.card S.L∣32*120:=by rw[ub];exact Nat.mul_dvd_mul_left 32 vt
  have h9':9∣32*120:=h9.trans z0;omega
 let T3:Finset S.L:=Finset.univ.filter fun h=>orderOf h=3;have uq:∀ v:Fin S.n->ZMod 7,v≠0->∃ h∈T3,h.1.val*ᵥv=(2:ZMod 7)•v:=by
  intro v hv
  obtain ⟨g,hgL,hgv⟩:=S.SF v hv (Units.mk0 (2:ZMod 7) (fun e=>by
   have h:=Ah ZMod.val e;simp only[QZ] at h;omega))
  let gL:S.L:=⟨g,hgL⟩;have vb:∀ k:ℕ,(gL ^ k).1.val*ᵥv=((2:ZMod 7) ^ k)•v:=fun k=>by
   induction k with
   | zero=>simp
   | succ k ih=>
    rw[BA];change (g.val*(gL ^ k).1.val)*ᵥv=_;rw[<-Ac,ih,Al,hgv,DG,AR,BA,Bb]
  have vu:3∣orderOf gL:=by
   have h1:=vb (orderOf gL);rw[BE] at h1;simp only[OneMemClass.coe_one,Cn,AN] at h1;have h2:((2:ZMod 7) ^ orderOf gL - 1)•v=0:=(by rw[DJ,Bx,CE];exact h1.symm);have v6:(2:ZMod 7) ^ orderOf gL=1:=sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv);have zV:(2:ZMod 7) ^ (orderOf gL % 3)=1:=(by have u2:=Cd (orderOf gL) 3;rw[<-u2,CT,Cz,YA,B8,AA] at v6;exact v6);have hlt:=DF (orderOf gL) (by decide:0 < 3);have h0:orderOf gL % 3=0:=by
    interval_cases hm:orderOf gL % 3
    . rfl
    . exact absurd zV YH
    . exact absurd zV Yu
   exact Eg h0
  obtain ⟨k,hk⟩:=vu;have vA:¬ 3∣k:=fun h3k=>by
   obtain ⟨j,rfl⟩:=h3k;have vc:orderOf gL∣Nat.card S.L:=Dd gL;rw[hk] at vc;exact vz (dvd_trans ⟨j,by ring⟩ vc)
  have vB:k≠0:=fun h0=>by rw[h0,AS] at hk;exact absurd hk (orderOf_pos gL).ne'
  have vl:orderOf (gL ^ k)=3:=(by rw[orderOf_pow' gL vB,hk,Nat.gcd_eq_right (dvd_mul_left k 3),Nat.mul_div_cancel _ (CM vB)]);have ur:k % 3=1\/k % 3=2:=by
   have:=DF k (by decide:0 < 3)
   have zaw:k % 3≠0:=fun h=>vA (Eg h);omega
  rcases ur with hk1 | hk2
  . refine ⟨gL ^ k,Finset.mem_filter.mpr ⟨Ai _,vl⟩,?_⟩;rw[vb k];have us:(2:ZMod 7) ^ k=2:=(by rw[<-Cd k 3,hk1,CT,Cz,YA,B8,AA,pow_one]);rw[us]
  .
   refine ⟨(gL ^ k) ^ 2,Finset.mem_filter.mpr ⟨Ai _,?_⟩,?_⟩
   . rw[orderOf_pow' (gL ^ k) (by decide),vl];decide
   .
    rw[<-Cz,vb (k*2)];have us:(2:ZMod 7) ^ (k*2)=2:=by
     have hm:(k*2) % 3=1:=by omega
     rw[<-Cd (k*2) 3,hm,CT,Cz,YA,B8,AA,pow_one]
    rw[us]
 have vC:∀ h∈T3,(Finset.univ.filter fun v:Fin S.n->ZMod 7=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v).card<=48:=by
  intro h _;let E2:Submodule (ZMod 7) (Fin S.n->ZMod 7):=
   LinearMap.ker (Matrix.toLin' h.1.val - (2:ZMod 7)•LinearMap.id)
  have z1:∀ v,v∈E2↔h.1.val*ᵥv=(2:ZMod 7)•v:=fun v=>by
   simp[E2,Bf,CE]
  have u3:∀ u∈E2,∀ v∈E2,dotProduct u (S.B*ᵥv)=0:=fun u hu v hv=>by
   have h1:dotProduct u (S.B*ᵥv)=dotProduct (h.1.val*ᵥu) (S.B*ᵥ(h.1.val*ᵥv)):=by
    calc dotProduct u (S.B*ᵥv)=dotProduct u ((h.1.valᵀ*S.B*h.1.val)*ᵥv):=by rw[S.B_inv h.1 h.2]
     _ = dotProduct (Matrix.vecMul u h.1.valᵀ) (S.B*ᵥ(h.1.val*ᵥv)):=by rw[<-AB];simp only[Ac,Af]
     _ = dotProduct (h.1.val*ᵥu) (S.B*ᵥ(h.1.val*ᵥv)):=by rw[AI]
   rw[(z1 u).mp hu,(z1 v).mp hv,Al,smul_dotProduct,dotProduct_smul,Am] at h1;have h3:(3:ZMod 7)*dotProduct u (S.B*ᵥv)=0:=by linear_combination -h1
   exact (mul_eq_zero.mp h3).resolve_left (fun e=>by have hv:=Ah ZMod.val e;simp only[QZ] at hv;omega)
  let φ:E2→ₗ[ZMod 7] Module.Dual (ZMod 7) ((Fin S.n->ZMod 7) ⧸ E2):=
   {toFun:=fun u=>Submodule.liftQ E2
     {toFun:=fun v=>dotProduct u.1 (S.B*ᵥv)
      map_add':=fun v₁ v₂=>by rw[A3,dotProduct_add]
      map_smul':=fun c v=>by rw[Al,dotProduct_smul,Am];rfl }
     (fun v hv=>by change dotProduct u.1 (S.B*ᵥv)=0;exact u3 u.1 u.2 v hv)
    map_add':=fun zx zy=>by
     apply Submodule.linearMap_qext;apply Ap;intro v;change dotProduct (zx.1+zy.1) (S.B*ᵥv)=dotProduct zx.1 (S.B*ᵥv)+dotProduct zy.1 (S.B*ᵥv);exact add_dotProduct _ _ _
    map_smul':=fun c u=>by
     apply Submodule.linearMap_qext;apply Ap;intro v;change dotProduct (c•u.1) (S.B*ᵥv)=c*dotProduct u.1 (S.B*ᵥv)
     rw[smul_dotProduct,Am] }
  have uc:Function.Injective φ:=by
   intro zx zy zA;apply Ae;have h0:∀ v:Fin S.n->ZMod 7,dotProduct (zx.1 - zy.1) (S.B*ᵥv)=0:=fun v=>by
    have h1:=BV zA (Submodule.Quotient.mk v);change dotProduct zx.1 (S.B*ᵥv)=dotProduct zy.1 (S.B*ᵥv) at h1;rw[sub_dotProduct,h1,Cx]
   have hBv:S.B*ᵥ(zx.1 - zy.1)=0:=by
    funext i;have h1:=h0 (Pi.single i 1);have uF:dotProduct (zx.1 - zy.1) (S.B*ᵥPi.single i 1)=-dotProduct (Pi.single i 1) (S.B*ᵥ(zx.1 - zy.1)):=by
     calc dotProduct (zx.1 - zy.1) (S.B*ᵥPi.single i 1)
        = dotProduct (Matrix.vecMul (zx.1 - zy.1) S.B) (Pi.single i 1):=AB _ _ _
      _ = dotProduct (Pi.single i 1) (S.Bᵀ*ᵥ(zx.1 - zy.1)):=by rw[dotProduct_comm,Matrix.mulVec_transpose]
      _ = -dotProduct (Pi.single i 1) (S.B*ᵥ(zx.1 - zy.1)):=by rw[S.B_alt,BJ,dotProduct_neg]
    rw[uF] at h1;simpa[dotProduct,AG] using neg_eq_zero.mp h1
   by_contra zB;exact S.B_det (Matrix.exists_mulVec_eq_zero_iff.mp ⟨zx.1 - zy.1,sub_ne_zero.mpr zB,hBv⟩)
  have ud:Module.finrank (ZMod 7) E2<=2:=by
   have h1:Module.finrank (ZMod 7) E2<=Module.finrank (ZMod 7) (Module.Dual (ZMod 7) ((Fin S.n->ZMod 7) ⧸ E2)):=
    LinearMap.finrank_le_finrank_of_injective uc
   have h2:Module.finrank (ZMod 7) (Module.Dual (ZMod 7) ((Fin S.n->ZMod 7) ⧸ E2))=Module.finrank (ZMod 7) ((Fin S.n->ZMod 7) ⧸ E2):=Subspace.dual_finrank_eq;have h3:=Submodule.finrank_quotient_add_finrank E2;rw[CQ,AW] at h3;omega
  have vd:Nat.card E2<=49:=by
   have h1:Nat.card E2=7 ^ Module.finrank (ZMod 7) E2:=(by have eE:=(Module.finBasis (ZMod 7) E2).equivFun.toEquiv;rw[Bc eE,Au,Cl,AW,Ey]);rw[h1]
   calc 7 ^ Module.finrank (ZMod 7) E2<=7 ^ 2:=Nat.pow_le_pow_right (by decide) ud
    _ = 49:=by decide
  have ut:(Finset.univ.filter fun v:Fin S.n->ZMod 7=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v).card+1<=Nat.card E2:=by
   have vD:(Finset.univ.filter fun v:Fin S.n->ZMod 7=>v∈E2).card=Nat.card E2:=(by rw[Au];exact (Ev _).symm);rw[<-vD];have vO:insert (0:Fin S.n->ZMod 7) (Finset.univ.filter fun v:Fin S.n->ZMod 7=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v)⊆
     Finset.univ.filter fun v=>v∈E2:=by
    intro v hv;simp only[Cu,AL,Ai,B3] at hv ⊢;rcases hv with rfl | ⟨_,zA⟩
    . exact E2.zero_mem
    . exact (z1 v).mpr zA
   have uG:(0:Fin S.n->ZMod 7)∉Finset.univ.filter (fun v:Fin S.n->ZMod 7=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v):=(by simp);have zU:=ED vO;rwa[C1 uG] at zU
  omega
 let P3:Finset (Equiv.Perm (Fin 5)):=Finset.univ.filter fun σ=>σ∈ψ.range/\orderOf σ=3;have vE:∀ σ∈P3,(T3.filter fun h=>ψ h=σ).card<=4:=by
  intro σ zk;by_cases vJ:(T3.filter fun h=>ψ h=σ).Nonempty
  .
   obtain ⟨h₀,zT⟩:=vJ;simp only[T3,AL,Ai,B3] at zT;obtain ⟨z3,zI⟩:=zT;have zp:orderOf σ=3:=(Finset.mem_filter.mp zk).2.2;have ue:∃ zh k₂:Fin 5,zh≠k₂/\σ zh=zh/\σ k₂=k₂:=by
    let Mv:Finset (Fin 5):=Finset.univ.filter fun k=>σ k≠k;have vP:σ ^ 3=1:=zp ▸ BE σ;have zl:∀ k,σ (σ (σ k))=k:=fun k=>by
     have:=DV vP k;simpa[DK,Equiv.Perm.mul_apply] using this
    have zal:Mv.card<=3:=by
     by_contra hgt;push Not at hgt;have zB:Mv.Nonempty:=Finset.card_pos.mp (by omega);obtain ⟨a,ha⟩:=zB;have z7:σ a≠a:=(Finset.mem_filter.mp ha).2;have vF:σ (σ a)≠a:=fun h=>z7 (by have:=Ah σ h;rw[zl] at this;exact this.symm);have uu:σ (σ a)≠σ a:=fun h=>z7 (σ.injective h);let O1:Finset (Fin 5):={a,σ a,σ (σ a)};have vQ:O1.card=3:=(by simp[O1,z7.symm,vF.symm,uu.symm]);have vm:O1⊆Mv:=by
      intro x hx;simp only[O1,Cu,Da] at hx;simp only[Mv,AL,Ai,B3];rcases hx with rfl | rfl | rfl
      . exact z7
      . exact uu
      . rw[zl];exact vF.symm
     have uH:(Mv \ O1).Nonempty:=Finset.card_pos.mp (by
      rw[Finset.card_sdiff,Finset.inter_eq_left.mpr vm];omega)
     obtain ⟨b,hb⟩:=uH;have z8:σ b≠b:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2;have uv:b∉O1:=(Finset.mem_sdiff.mp hb).2;have vG:σ (σ b)≠b:=fun h=>z8 (by have:=Ah σ h;rw[zl] at this;exact this.symm);have uw:σ (σ b)≠σ b:=fun h=>z8 (σ.injective h);let O2:Finset (Fin 5):={b,σ b,σ (σ b)};have vR:O2.card=3:=by simp[O2,z8.symm,vG.symm,uw.symm]
     have uf:O2⊆Mv:=by
      intro x hx;simp only[O2,Cu,Da] at hx;simp only[Mv,AL,Ai,B3];rcases hx with rfl | rfl | rfl
      . exact z8
      . exact uw
      . rw[zl];exact vG.symm
     have uI:Disjoint O1 O2:=by
      rw[Ew];intro x vp uX;apply uv;simp only[O1,O2,Cu,Da] at vp uX ⊢;rcases vp with rfl | rfl | rfl <;> rcases uX with h | h | h
      all_goals
        try exact Or.inl h.symm
        try exact Or.inr (Or.inl h.symm)
        try exact Or.inr (Or.inr h.symm)
      . have:=Ah (fun t=>σ (σ t)) h;rw[zl] at this;exact Or.inr (Or.inr this.symm)
      . have:=Ah σ h;rw[zl] at this;exact Or.inr (Or.inl this.symm)
      . have:=Ah (fun t=>σ (σ t)) h;rw[zl,zl] at this;exact Or.inl this.symm
      . have:=Ah σ h;rw[zl] at this;exact Or.inr (Or.inr this.symm)
      . have:=Ah (fun t=>σ (σ t)) h;rw[zl,zl] at this;exact Or.inr (Or.inl this.symm)
      . have:=Ah σ h;rw[zl,zl] at this;exact Or.inl this.symm
     have zU:=ED (Finset.union_subset vm uf);rw[BN uI,vQ,vR] at zU;have h5:Mv.card<=5:=(Finset.card_le_univ Mv).trans (by simp);omega
    have uW:2<=(Finset.univ.filter fun k:Fin 5=>σ k=k).card:=by
     have zax:(Finset.univ.filter fun k:Fin 5=>σ k=k).card+Mv.card=5:=by
      have hu:(Finset.univ.filter fun k:Fin 5=>σ k=k)∪Mv=Finset.univ:=(by ext k;simp only[Mv,Finset.mem_union,AL,Ai,B3,iff_true];exact em _);have hd:Disjoint (Finset.univ.filter fun k:Fin 5=>σ k=k) Mv:=
        Finset.disjoint_left.mpr fun k h1 h2=>(Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw[<-BN hd,hu,BS,AW]
     omega
    obtain ⟨zh,uU,k₂,uV,zB⟩:=Finset.one_lt_card.mp (by omega:1 < (Finset.univ.filter fun k:Fin 5=>σ k=k).card);exact ⟨zh,k₂,zB,(Finset.mem_filter.mp uU).2,(Finset.mem_filter.mp uV).2⟩
   obtain ⟨zh,k₂,zae,ul,um⟩:=ue;have z5:∀ k:Fin 5,σ k=k->zi h₀ (u k)=u k:=fun k hσk=>by
    have h1:zj h₀ k=k:=by change (ψ h₀) k=k;rw[zI,hσk]
    have h2:=zq h₀ k;rw[h1] at h2;rcases h2 with zA | zA
    . exact zA
    .
     exfalso;have h3:(zi h₀) ((zi h₀) ((zi h₀) (u k)))=u k:=by
      apply Ae;change h₀*(h₀*(h₀*(u k).1*h₀⁻¹)*h₀⁻¹)*h₀⁻¹=(u k).1;have hc:h₀ ^ 3=1:=z3 ▸ BE h₀
      calc h₀*(h₀*(h₀*(u k).1*h₀⁻¹)*h₀⁻¹)*h₀⁻¹
         = (h₀*h₀*h₀)*(u k).1*(h₀*h₀*h₀)⁻¹:=by group
        _ = h₀ ^ 3*(u k).1*(h₀ ^ 3)⁻¹:=by rw[DK,E6]
        _ = (u k).1:=by rw[hc];simp
     simp only[zA,AF,v4 h₀,<-Ad,zS,AA] at h3;exact za.z_ne_one (Cj (h3.trans (AA (u k)).symm))
   let CR0:Subgroup R:=
    {carrier:={r | zi h₀ r=r}
     mul_mem':=fun {a b} ha hb=>by change zi h₀ (a*b)=a*b;rw[AF,ha,hb]
     one_mem':=BI _
     inv_mem':=fun {a} ha=>by change zi h₀ a⁻¹=a⁻¹;rw[C5,ha] }
   have u4:8<=Nat.card CR0:=by
    let φ8:Bool×Bool×Bool->CR0:=fun ⟨c,a,b⟩=>
     ⟨(if c then zR else 1)*(if a then u zh else 1)*(if b then u k₂ else 1),CR0.mul_mem (CR0.mul_mem (by cases c;exacts [CR0.one_mem,v4 h₀])
       (by cases a;exacts [CR0.one_mem,z5 zh ul]))
       (by cases b;exacts [CR0.one_mem,z5 k₂ um])⟩
    have vS:Function.Injective φ8:=by
     intro ⟨c1,a1,b1⟩ ⟨c2,a2,b2⟩ zA;have hr:(if c1 then zR else 1)*(if a1 then u zh else 1)*(if b1 then u k₂ else 1)=(if c2 then zR else 1)*(if a2 then u zh else 1)*(if b2 then u k₂ else 1):=
      Ah Subtype.val zA
     have vv:∀ zg r₂:R,(zg=u zh\/zg=zR*u zh)->(r₂=u k₂\/r₂=zR*u k₂)->zg≠r₂:=by
      intro zg r₂ h1 h2 up;subst up
      have uJ:=z4 zg (by
        rcases h1 with rfl | rfl
        . exact zm zh
        .
         refine ⟨fun h=>(zm zh).2.1 (by calc u zh=zR*(zR*u zh):=by rw[<-Ad,zS,AA]
           _ = zR:=by rw[h,AK]),
          fun h=>(zm zh).1 (E3 (h.trans (AK zR).symm)),
          by rw[Ad,<-Ad (u zh),<-z9 (u zh),<-Ad zR,<-Ad zR zR,zS,AA,(zm zh).2.2]⟩)
      exact zae (uJ.unique h1 h2)
     have ux:∀ x y:Bool,(if x then zR else 1)*(if y then zR else 1)=if xor x y then zR else 1:=
      fun x y=>by cases x <;> cases y <;> simp[zS]
     have v7:∀ x y:Bool,(if x then u zh else 1)*(if y then u zh else 1)=if xor x y then u zh else 1:=
      fun x y=>by cases x <;> cases y <;> simp[(zm zh).2.2]
     have v8:∀ x y:Bool,(if x then u k₂ else 1)*(if y then u k₂ else 1)=if xor x y then u k₂ else 1:=
      fun x y=>by cases x <;> cases y <;> simp[(zm k₂).2.2]
     have uK:∀ (x:Bool) (r:R),(if x then zR else 1)*r=r*(if x then zR else 1):=
      fun x r=>by cases x <;> simp[z9]
     have zE:(if xor c2 c1 then zR else 1)*(if xor b1 b2 then u k₂ else 1)=if xor a1 a2 then u zh else 1:=by
      calc (if xor c2 c1 then zR else 1)*(if xor b1 b2 then u k₂ else 1)
         = (if a1 then u zh else 1)*((if c2 then zR else 1)*((if c1 then zR else 1)*(if a1 then u zh else 1)*(if b1 then u k₂ else 1))*(if b2 then u k₂ else 1)):=by simp only[Ad];rw[<-Ad (if c2 then zR else 1) (if c1 then zR else 1),ux,v8,<- Ad (if a1 then u zh else 1) (if xor c2 c1 then zR else 1),<-uK (xor c2 c1),Ad (if xor c2 c1 then zR else 1),<-Ad (if a1 then u zh else 1),v7,B9,Aw Bz,AA]
        _ = (if a1 then u zh else 1)*((if c2 then zR else 1)*((if c2 then zR else 1)*(if a2 then u zh else 1)*(if b2 then u k₂ else 1))*(if b2 then u k₂ else 1)):=by rw[hr]
        _ = if xor a1 a2 then u zh else 1:=by simp only[Ad];rw[<-Ad (if c2 then zR else 1) (if c2 then zR else 1),ux,B9,Aw Bz,AA,v8,B9,Aw Bz,AK,v7]
     cases ha:xor a1 a2 <;> cases hb:xor b1 b2 <;>
      simp only[ha,hb,Be,AE,Bj,AA,AK] at zE
     .
      have hc:xor c2 c1=false:=by
        cases vK:xor c2 c1
        . rfl
        . rw[vK,Az rfl] at zE;exact absurd zE za.z_ne_one
      refine Dr ?_ (Dr ?_ ?_)
      . cases c1 <;> cases c2 <;> simp at hc ⊢
      . cases a1 <;> cases a2 <;> simp at ha ⊢
      . cases b1 <;> cases b2 <;> simp at hb ⊢
     .
      exfalso;cases vK:xor c2 c1 <;> simp only[vK,Be,AE,Bj,AA] at zE
      . exact (zm k₂).1 zE
      .
        exact (zm k₂).2.1 (by calc u k₂=zR*(zR*u k₂):=by rw[<-Ad,zS,AA]
         _ = zR:=by rw[zE,AK])
     .
      exfalso;cases vK:xor c2 c1 <;> simp only[vK,Be,AE,Bj] at zE
      . exact (zm zh).1 zE.symm
      . exact (zm zh).2.1 zE.symm
     . exfalso;exact vv _ _ (Or.inl rfl) (by cases xor c2 c1 <;> simp) zE.symm
    haveI:Fintype CR0:=Fintype.ofFinite CR0;have zU:=Cw φ8 vS;rw[Au];simpa using zU
   let M:Subgroup S.L:=(Subgroup.zpowers σ).comap ψ;have ug:Nat.card M=96:=by
    let ψM:M→*Subgroup.zpowers σ:=
     {toFun:=fun m=>⟨ψ m.1,m.2⟩
      map_one':=Ae (BI ψ)
      map_mul':=fun a b=>Ae (AF ψ a.1 b.1) }
    have uL:Function.Surjective ψM:=(by rintro ⟨τ,hτ⟩;obtain ⟨k,rfl⟩:=Subgroup.mem_zpowers_iff.mp hτ;refine ⟨⟨h₀ ^ k,by change ψ (h₀ ^ k)∈Subgroup.zpowers σ;rw[map_zpow,zI];exact Subgroup.zpow_mem _ (Co σ) k⟩,Ae (by change ψ (h₀ ^ k)=σ ^ k;rw[map_zpow,zI])⟩);have uM:Nat.card ψM.ker=32:=by
     let eK:ψM.ker ≃ R:=
      { toFun:=fun x=>⟨x.1.1,by
         rw[<-zG,Bw];exact Ah Subtype.val (MonoidHom.mem_ker.mp x.2)⟩
        invFun:=fun r=>
         have hr:r.1∈ψ.ker:=by rw[zG];exact r.2
         ⟨⟨r.1,by change ψ r.1∈Subgroup.zpowers σ;rw[MonoidHom.mem_ker.mp hr];exact Subgroup.one_mem _⟩,MonoidHom.mem_ker.mpr (Ae (MonoidHom.mem_ker.mp hr))⟩
        left_inv:=fun x=>rfl
        right_inv:=fun r=>rfl }
     rw[Bc eK,zY]
    have h1:=BX ψM.ker;have h2:Nat.card (M ⧸ ψM.ker)=Nat.card (Subgroup.zpowers σ):=
     Bc (QuotientGroup.quotientKerEquivOfSurjective ψM uL).toEquiv
    change Nat.card ψM.ker*Nat.card (M ⧸ ψM.ker)=Nat.card M at h1;rw[uM,h2,EX,zp] at h1;omega
   have zH:∀ h∈T3.filter (fun h=>ψ h=σ),∃ r:R,r.1*h₀*r.1⁻¹=h:=by
    intro h hh;simp only[T3,AL,Ai,B3] at hh;obtain ⟨uB,uC⟩:=hh;have ve:h₀∈M:=by change ψ h₀∈Subgroup.zpowers σ;rw[zI];exact Co σ
    have z6:h∈M:=by change ψ h∈Subgroup.zpowers σ;rw[uC];exact Co σ
    let P0:Subgroup M:=Subgroup.zpowers ⟨h₀,ve⟩;let P1:Subgroup M:=Subgroup.zpowers ⟨h,z6⟩;have vT:Nat.card P0=3:=(by rw[EX,<-orderOf_injective M.subtype Subtype.val_injective ⟨h₀,ve⟩];exact z3);have vU:Nat.card P1=3:=(by rw[EX,<-orderOf_injective M.subtype Subtype.val_injective ⟨h,z6⟩];exact uB);haveI:Fact (Nat.Prime 3):=⟨by decide⟩;have vV:(Nat.card M).factorization 3=1:=(by rw[ug,show (96:ℕ)=3 ^ 1*32 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,Nat.Prime.factorization_pow (by decide),Finsupp.single_eq_same,Nat.factorization_eq_zero_of_not_dvd (by decide)]);have uh:Nat.card P0=3 ^ (Nat.card M).factorization 3:=by rw[vT,vV];simp
    have ui:Nat.card P1=3 ^ (Nat.card M).factorization 3:=by rw[vU,vV];simp
    let S0:Sylow 3 M:=Sylow.ofCard P0 uh;let S1:Sylow 3 M:=Sylow.ofCard P1 ui;obtain ⟨m,hm⟩:=MulAction.exists_smul_eq M S0 S1;have vn:(⟨h,z6⟩:M)∈(S1:Subgroup M):=Co _;rw[<-hm] at vn;have vW:m⁻¹*⟨h,z6⟩*m∈P0:=by
     obtain ⟨y,hy,zaf⟩:=vn;have:m⁻¹*⟨h,z6⟩*m=y:=by
      have hy':m*y*m⁻¹=⟨h,z6⟩:=zaf
      calc m⁻¹*⟨h,z6⟩*m=m⁻¹*(m*y*m⁻¹)*m:=by rw[hy']
        _ = y:=by group
     rwa[this]
    obtain ⟨j,hj⟩:=Subgroup.mem_zpowers_iff.mp vW;have z2:m.1*h₀ ^ j*m.1⁻¹=h:=by
     have h1:(⟨h₀,ve⟩:M) ^ j=m⁻¹*⟨h,z6⟩*m:=hj;have h2:h₀ ^ j=m.1⁻¹*h*m.1:=by simpa using Ah Subtype.val h1
     calc m.1*h₀ ^ j*m.1⁻¹=m.1*(m.1⁻¹*h*m.1)*m.1⁻¹:=by rw[h2]
      _ = h:=by group
    have u5:σ ^ j=σ:=(by have h1:=Ah ψ z2;rw[AF,AF,map_zpow,C5,zI,uC] at h1;obtain ⟨a,ha⟩:=Subgroup.mem_zpowers_iff.mp m.2;rw[<-ha,<-Do,<-zpow_neg,<-Do] at h1;simpa[DQ,add_left_comm,add_assoc] using h1);have uN:h₀ ^ j=h₀:=by
     have uO:(3:ℤ)∣j - 1:=by
      have h1:σ ^ (j - 1)=1:=by rw[zpow_sub,zpow_one,u5,By]
      rw[show (3:ℤ)=(orderOf σ:ℤ) by exact_mod_cast zp.symm,orderOf_dvd_iff_zpow_eq_one];exact h1
     obtain ⟨q,hq⟩:=uO;have u6:j=1+3*q:=by omega
     have uP:h₀ ^ (3:ℤ)=1:=(by rw[show (3:ℤ)=((3:ℕ):ℤ) from rfl,Ee,<-z3,BE]);rw[u6,Do,zpow_one,zpow_mul,uP,one_zpow,AK]
    rw[uN] at z2;obtain ⟨a,ha⟩:=Subgroup.mem_zpowers_iff.mp m.2;have uy:m.1*(h₀ ^ a)⁻¹∈R:=(by rw[<-zG,Bw,AF,C5,map_zpow,zI,ha,By]);refine ⟨⟨m.1*(h₀ ^ a)⁻¹,uy⟩,?_⟩;have uj:(h₀ ^ a)⁻¹*h₀*h₀ ^ a=h₀:=by
     calc (h₀ ^ a)⁻¹*h₀*h₀ ^ a=h₀ ^ (-a)*h₀ ^ (1:ℤ)*h₀ ^ a:=by rw[zpow_neg,zpow_one]
      _ = h₀ ^ (-a+1+a):=by rw[<-Do,<-Do]
      _ = h₀:=by rw[show -a+1+a=1 by omega,zpow_one]
    calc (m.1*(h₀ ^ a)⁻¹)*h₀*(m.1*(h₀ ^ a)⁻¹)⁻¹
      = m.1*((h₀ ^ a)⁻¹*h₀*h₀ ^ a)*m.1⁻¹:=by group
     _ = m.1*h₀*m.1⁻¹:=by rw[uj]
     _ = h:=z2
   let toCoset:{h // h∈T3.filter fun h=>ψ h=σ}->R ⧸ CR0:=
    fun h=>QuotientGroup.mk (Classical.choose (zH h.1 h.2))
   have vf:Function.Injective toCoset:=by
    intro vg vh zA;apply Ae;set zg:=Classical.choose (zH vg.1 vg.2);set r₂:=Classical.choose (zH vh.1 vh.2);have vo:zg.1*h₀*zg.1⁻¹=vg.1:=Classical.choose_spec (zH vg.1 vg.2);have hr2:r₂.1*h₀*r₂.1⁻¹=vh.1:=Classical.choose_spec (zH vh.1 vh.2);have zN:zg⁻¹*r₂∈CR0:=QuotientGroup.eq.mp zA;have zs:h₀*(zg⁻¹*r₂).1*h₀⁻¹=(zg⁻¹*r₂).1:=Ah Subtype.val zN;have u7:zg.1*h₀*zg.1⁻¹=r₂.1*h₀*r₂.1⁻¹:=by
     change h₀*(zg.1⁻¹*r₂.1)*h₀⁻¹=zg.1⁻¹*r₂.1 at zs;have h1:h₀*(zg.1⁻¹*r₂.1)=(zg.1⁻¹*r₂.1)*h₀:=by
      calc h₀*(zg.1⁻¹*r₂.1)=(h₀*(zg.1⁻¹*r₂.1)*h₀⁻¹)*h₀:=by group
        _ = (zg.1⁻¹*r₂.1)*h₀:=by rw[zs]
     calc zg.1*h₀*zg.1⁻¹=zg.1*(h₀*(zg.1⁻¹*r₂.1))*r₂.1⁻¹:=by group
      _ = zg.1*((zg.1⁻¹*r₂.1)*h₀)*r₂.1⁻¹:=by rw[h1]
      _ = r₂.1*h₀*r₂.1⁻¹:=by group
    rw[<-vo,<-hr2,u7]
   have vX:(T3.filter fun h=>ψ h=σ).card<=Nat.card (R ⧸ CR0):=(by haveI:Fintype (R ⧸ CR0):=Fintype.ofFinite (R ⧸ CR0);have h1:=Cw toCoset vf;rw[Au,<-Fintype.card_coe];exact h1);have uQ:Nat.card (R ⧸ CR0)<=4:=(by have h1:=BX CR0;rw[zY] at h1;change Nat.card CR0*Nat.card (R ⧸ CR0)=32 at h1;nlinarith);exact vX.trans uQ
  . rw[Finset.not_nonempty_iff_eq_empty.mp vJ];simp
 have u8:2400<=48*T3.card:=by
  let NZ:Finset (Fin S.n->ZMod 7):=Finset.univ.filter fun v=>v≠0;have vY:NZ.card=2400:=by
   have h1:NZ.card+1=Fintype.card (Fin S.n->ZMod 7):=(by have vO:insert (0:Fin S.n->ZMod 7) NZ=Finset.univ:=(by ext v;simp only[NZ,Cu,AL,Ai,B3,iff_true];exact eq_or_ne v 0);rw[<-BS,<-vO,C1 (by simp[NZ])]);rw[Cl,AW,Ey] at h1;have zW:7 ^ S.n=2401:=by rw[zf];decide
   rw[zW] at h1;omega
  have ut:NZ⊆T3.biUnion fun h=>Finset.univ.filter fun v=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v:=(by intro v hv;obtain ⟨h,hh,hhv⟩:=uq v (Finset.mem_filter.mp hv).2;exact Finset.mem_biUnion.mpr ⟨h,hh,Finset.mem_filter.mpr ⟨Ai _,(Finset.mem_filter.mp hv).2,hhv⟩⟩)
  calc 2400=NZ.card:=vY.symm
   _<=(T3.biUnion fun h=>Finset.univ.filter fun v=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v).card:=
     ED ut
   _<=∑ h∈T3,(Finset.univ.filter fun v=>v≠0/\h.1.val*ᵥv=(2:ZMod 7)•v).card:=
     Finset.card_biUnion_le
   _<=∑ _h∈T3,48:=Finset.sum_le_sum vC
   _ = 48*T3.card:=by rw[Cm,Am,Bb]
 have zao:T3.card<=4*P3.card:=by
  have uR:∀ h∈T3,ψ h∈P3:=fun h hh=>by
   have v9:orderOf h=3:=(Finset.mem_filter.mp hh).2;have u9:ψ h≠1:=fun h1=>by
    have hr:h∈R:=zG ▸ MonoidHom.mem_ker.mpr h1;have h2g:IsPGroup 2 R:=Wv S.L;obtain ⟨k,hk⟩:=h2g ⟨h,hr⟩;have zW:h ^ (2 ^ k)=1:=Ah Subtype.val hk;have z0:3∣2 ^ k:=v9 ▸ Bl zW;have zaa:Nat.Coprime 3 (2 ^ k):=Eo k (by decide);have:3∣1:=by have:=DR (EO 3) z0;rwa[zaa.gcd_eq_one] at this
    omega
   have uz:orderOf (ψ h)=3:=by
    have z0:orderOf (ψ h)∣3:=v9 ▸ orderOf_map_dvd ψ h;have zay:1 < orderOf (ψ h):=Nat.one_lt_iff_ne_zero_and_ne_one.mpr
     ⟨(orderOf_pos _).ne',fun h1=>u9 (orderOf_eq_one_iff.mp h1)⟩
    have zU:=AP (by decide) z0;have zaz:orderOf (ψ h)≠2:=fun h2=>by rw[h2] at z0;omega
    omega
   exact Finset.mem_filter.mpr ⟨Ai _,⟨h,rfl⟩,uz⟩
  calc T3.card=∑ σ∈P3,(T3.filter fun h=>ψ h=σ).card:=
     Finset.card_eq_sum_card_fiberwise uR
   _<=∑ _σ∈P3,4:=Finset.sum_le_sum vE
   _ = 4*P3.card:=by rw[Cm,Am,Bb]
 have zab:13<=P3.card:=by omega
 let A5:=alternatingGroup (Fin 5);haveI:IsSimpleGroup A5:=alternatingGroup.isSimpleGroup (by simp);let Q:Subgroup A5:=ψ.range.comap A5.subtype;have zag:14<=Nat.card Q:=by
  have zQ:∀ σ∈P3,σ∈A5:=fun σ zk=>by
   have h3:σ ^ 3=1:=(Finset.mem_filter.mp zk).2.2 ▸ BE σ;have hs:(Equiv.Perm.sign σ) ^ 3=1:=by rw[<-Dc,h3,BI]
   change Equiv.Perm.sign σ=1;rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hm1
   . exact h1
   . rw[hm1] at hs;exact absurd hs (by decide)
  let ua:Finset A5:=insert 1 (P3.attach.image fun σ=>⟨σ.1,zQ σ.1 σ.2⟩);have vZ:ua.card=P3.card+1:=by
   have uS:(1:A5)∉P3.attach.image (fun σ=>(⟨σ.1,zQ σ.1 σ.2⟩:A5)):=(by intro zN;obtain ⟨⟨σ,zk⟩,_,zA⟩:=Finset.mem_image.mp zN;have zac:σ=1:=Ah Subtype.val zA;have zo:=(Finset.mem_filter.mp zk).2.2;rw[zac,orderOf_one] at zo;omega);have zn:Function.Injective (fun σ:{x // x∈P3}=>(⟨σ.1,zQ σ.1 σ.2⟩:A5)):=
    fun a b h=>Ae (Ah (fun x:A5=>x.1) h)
   rw[C1 uS,E0 P3.attach zn,Finset.card_attach]
  have uk:∀ x∈ua,x∈Q:=fun x hx=>by
   simp only[ua,Cu,Eb,Finset.mem_attach,B3] at hx;rcases hx with rfl | ⟨⟨σ,zk⟩,rfl⟩
   . exact Q.one_mem
   . exact (Finset.mem_filter.mp zk).2.1
  let emb:{x // x∈ua}->Q:=fun x=>⟨x.1,uk x.1 x.2⟩;have v0:Function.Injective emb:=fun a b h=>Ae (Ah (fun x:Q=>x.1) h);haveI:Fintype Q:=Fintype.ofFinite Q;have zU:=Cw emb v0;rw[Fintype.card_coe,vZ,<-Au] at zU;omega
 have zX:Nat.card A5=60:=(by rw[nat_card_alternatingGroup,Au,AW];decide);have zaq:Q.index<=4:=(by have h1:=BX Q;rw[zX] at h1;nlinarith);have uA:Q=⊤:=(by let f:=MulAction.toPermHom A5 (A5 ⧸ Q);have vi:f.ker≠⊥:=(by intro v3;have zn:Function.Injective f:=(MonoidHom.ker_eq_bot_iff f).mp v3;haveI:Fintype A5:=Fintype.ofFinite A5;haveI:Fintype (A5 ⧸ Q):=Fintype.ofFinite (A5 ⧸ Q);have zU:Nat.card A5<=Nat.card (Equiv.Perm (A5 ⧸ Q)):=(by rw[Au,Au];exact Cw f zn);have uT:Nat.card (Equiv.Perm (A5 ⧸ Q))=Q.index.factorial:=(by rw[Au,D5,<-Au];rfl);rw[zX,uT] at zU;have zah:Q.index.factorial<=24:=(by interval_cases Q.index <;> decide);omega);have v1:f.ker=⊤:=(IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker f.normal_ker).resolve_left vi;have vH:f.ker<=Q:=(by rw[<-Subgroup.normalCore_eq_ker Q];exact Subgroup.normalCore_le Q);exact top_unique (v1 ▸ vH));haveI:Group.IsSolvable S.L:=S.solvable;have uD:Group.IsSolvable ψ.range:=by have eR:S.L ⧸ ψ.ker≃*ψ.range:=QuotientGroup.quotientKerEquivRange ψ;exact Group.isSolvable_of_isSolvable_injective (f:=eR.symm.toMonoidHom) eR.symm.injective
 let zad:A5→*ψ.range:=
  {toFun:=fun x=>⟨x.1,by have:x∈Q:=uA ▸ D9 x;exact this⟩
   map_one':=rfl
   map_mul':=fun _ _=>rfl }
 have v2:Group.IsSolvable A5:=
  Group.isSolvable_of_isSolvable_injective (f:=zad) (fun a b h=>Ae (Ah (fun x:ψ.range=>x.1) h))
 have vI:¬ ∀ a b:A5,a*b=b*a:=by
  intro hab;let zC:Equiv.Perm (Fin 5):=Equiv.swap 0 1*Equiv.swap 1 2;let zD:Equiv.Perm (Fin 5):=Equiv.swap 0 1*Equiv.swap 1 3;have h1:zC∈A5:=by change Equiv.Perm.sign zC=1;simp[zC,Equiv.Perm.sign_swap (by decide:(0:Fin 5)≠1),Equiv.Perm.sign_swap (by decide:(1:Fin 5)≠2)]
  have h2:zD∈A5:=(by change Equiv.Perm.sign zD=1;simp[zD,Equiv.Perm.sign_swap (by decide:(0:Fin 5)≠1),Equiv.Perm.sign_swap (by decide:(1:Fin 5)≠3)]);have zs:=Ah Subtype.val (hab ⟨zC,h1⟩ ⟨zD,h2⟩);change zC*zD=zD*zC at zs;have zB:(zC*zD) 0≠(zD*zC) 0:=by decide
  exact zB (DV zs 0)
 rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator A5) (DY ⊤ ⊤) with v3 | htop
 .
  apply vI;intro a b;have zN:a*b*a⁻¹*b⁻¹∈commutator A5:=Dj (D9 a) (D9 b);rw[v3,CG] at zN
  calc a*b=(a*b*a⁻¹*b⁻¹)*(b*a):=by group
   _ = b*a:=by rw[zN,AA]
 .
  have hds:∀ k:ℕ,derivedSeries A5 k=⊤:=fun k=>by
   induction k with
   | zero=>exact derivedSeries_zero A5
   | succ k ih=>rw[derivedSeries_succ,ih];exact htop
  obtain ⟨k,hk⟩:=v2.solvable;rw[hds k] at hk;haveI:Nontrivial A5:=Finite.one_lt_card_iff_nontrivial.mp (by rw[zX];decide);exact Fa hk
set_option maxHeartbeats 800000 in
lemma W5 [Fact (Nat.Prime 7)]
  {N:ℕ} {zb:0 < N} {zd:¬ 7∣N}
  {ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N zb zd ι) (zk:(⟨Qd S.n 7,S.negOne_mem⟩:S.L)∈O2 S.L) (zi:Qn (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zk⟩) (B:Qm (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zk⟩ 1 false) (za:Qa 7) (ze:za*za=-1) (zc:(Fin S.n->Qa 7)≃ₗ[Qa 7] ((Fin 1->Bool)->Qa 7)) (zh:∀ (r:O2 S.L) (v:Fin S.n->Qa 7), zc ((r.1.1.val.map (algebraMap (ZMod 7) (Qa 7)))*ᵥv)=
    let rels:=QJ (p:=7) (m:=1) false ze
    QA zi B (-1) (Qk false za) (Ql false)
     (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥzc v)
  (zf:Aa (Fin S.n) (ZMod 7)) (zg:zf∈S.L)
  (zj:zf.val=(2:ZMod 7)•(1+(B.x 0).1.1.val)) :
  False:=by
 classical
 let zw:=algebraMap (ZMod 7) (Qa 7);let R:=O2 S.L;let xR:R:=B.x 0;have zF:Nat.card R=8:=by simpa using B.hcard
 let zo:=QJ (p:=7) (m:=1) false ze;let HK:Matrix (Fin S.n) (Fin S.n) (Qa 7):=zf.val.map zw;have zM:HK=(2:Qa 7)•(1+xR.1.1.val.map zw):=by
  ext a b;simp only[HK,zj,xR,AZ,A2,EY,Am,AF,EN,C2];by_cases h:a=b
  . subst h;simp
  . simp[AH h]
 let D:Matrix (Fin 1->Bool) (Fin 1->Bool) (Qa 7):=
  Matrix.diagonal fun s=>(2:Qa 7)*(1+if s 0 then -za else za)
 have zG:zc.toLinearMap∘ₗMatrix.toLin' HK∘ₗzc.symm.toLinearMap=Matrix.toLin' D:=by
  apply Ap;intro v;funext s;rw[BZ,BZ,LinearEquiv.coe_coe,LinearEquiv.coe_coe,Aj,Aj,zM,Bv,Matrix.add_mulVec,AN,Bd,EN,zc.apply_symm_apply];have zD:=zh xR (zc.symm v);rw[zc.apply_symm_apply] at zD;dsimp only at zD
  have zW:(QA zi B (-1) (Qk false za) (Ql false)
   (fun A=>by simp) (by simp) zo.1 zo.2.1 zo.2.2.1 zo.2.2.2.1 zo.2.2.2.2.1 zo.2.2.2.2.2) xR=Qk false za 0:=Q7 zi B (-1) (Qk false za) (Ql false) _ _ _ _ _ _ _ _ 0
  rw[zW] at zD;change ((2:Qa 7)•(v+zc ((xR.1.1.val.map zw)*ᵥzc.symm v))) s=(D*ᵥv) s;rw[zD];simp only[AX,Pi.add_apply,Am,Qk,D,BO];cases s 0 <;> simp;all_goals ring
 have zx:Qr zb zd ι (Fin S.n->Qa 7) (Matrix.toLin' HK)=Qr zb zd ι ((Fin 1->Bool)->Qa 7) (Matrix.toLin' D):=(by rw[<-zG,Wz]);let lam1:Qa 7:=(2:Qa 7)*(1+za);let lam2:Qa 7:=(2:Qa 7)*(1 - za);have zs:(8:Qa 7)=1:=(by have h:=Ah zw YZ;rwa[C2,BI] at h);have zy:lam1*lam1=za:=by
  dsimp only[lam1]
  calc (2*(1+za))*(2*(1+za))=4*(1+2*za+za*za):=by ring
   _ = 8*za:=by rw[ze];ring
   _ = za:=by rw[zs,AA]
 have zt:lam1 ^ 4=-1:=by
  calc lam1 ^ 4=(lam1*lam1)*(lam1*lam1):=by ring
   _ = -1:=by rw[zy,ze]
 have zu:lam1 ^ 8=1:=by
  calc lam1 ^ 8=(lam1 ^ 4) ^ 2:=by ring
   _ = 1:=by rw[zt];ring
 have zp:lam1*lam2=1:=by
  dsimp only[lam1,lam2]
  calc (2*(1+za))*(2*(1 - za))=4*(1 - za*za):=by ring
   _ = 8:=by rw[ze];ring
   _ = 1:=zs
 have zz:8∣N:=(zF ▸ Cf R).trans S.card_dvd;obtain ⟨k8,z4⟩:=zz;have zH:lam1 ^ N=1:=by rw[z4,Cz,zu,B8]
 let u1:(Qa 7)ˣ:=Units.mkOfMulEqOne lam1 lam2 zp
 let zl:Ab N (Qa 7):=⟨u1,by
  rw[mem_rootsOfUnity];apply A7;simp[u1,zH]⟩
 have zm:((zl:(Qa 7)ˣ):Qa 7)=lam1:=rfl;have zr:(((zl⁻¹:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)=lam2:=by
  have h1:(((zl:(Qa 7)ˣ):Qa 7))*(((zl⁻¹:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)=1:=(by rw[<-De,<-BB,By];rfl);rw[zm] at h1;have zn:lam1≠0:=fun h0=>by rw[h0,Bm] at zp;exact CX zp
  exact Ck zn (h1.trans zp.symm)
 have zq:∀ ω:Ab N (Qa 7),Qr zb zd ι (Qa 7) (((ω:(Qa 7)ˣ):Qa 7)•LinearMap.id)=((ι ω:ℂˣ):ℂ):=by
  intro ω;letI:Fintype (Ab N (Qa 7)):=Qx zb zd;unfold Qr;rw[Ay ω]
  .
   have zA:LinearMap.ker (((ω:(Qa 7)ˣ):Qa 7)•(LinearMap.id:Module.End (Qa 7) (Qa 7)) -
     ((ω:(Qa 7)ˣ):Qa 7)•LinearMap.id)=⊤:=by
    rw[Cg];intro x;simp only[Bf,Cx,LinearMap.zero_apply]
   rw[zA,finrank_top,DX,Nat.cast_one,AA]
  .
   intro ζ _ z5;have zn:((ω:(Qa 7)ˣ):Qa 7) - ((ζ:(Qa 7)ˣ):Qa 7)≠0:=(by intro h0;apply z5;apply Ae;apply A7;exact (sub_eq_zero.mp h0).symm)
   have zA:LinearMap.ker (((ω:(Qa 7)ˣ):Qa 7)•(LinearMap.id:Module.End (Qa 7) (Qa 7)) -
     ((ζ:(Qa 7)ˣ):Qa 7)•LinearMap.id)=⊥:=by
    rw[BY];intro x hx;simp only[Bf,BU,AU,Br,Am] at hx;have:(((ω:(Qa 7)ˣ):Qa 7) - ((ζ:(Qa 7)ˣ):Qa 7))*x=0:=by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left zn
   rw[zA,Module.finrank_eq_zero_of_subsingleton,Nat.cast_zero,Bm]
  . intro h;exact absurd (Ai ω) h
 have zI:Qr zb zd ι ((Fin 1->Bool)->Qa 7) (Matrix.toLin' D)=((ι zl:ℂˣ):ℂ)+((ι zl⁻¹:ℂˣ):ℂ):=by
  have z1:=YS zb zd ι (W:=fun _:Fin 1->Bool=>Qa 7)
   (fun s=>(((if s 0 then zl⁻¹ else zl:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)•LinearMap.id)
  have zP:Matrix.toLin' D=
    {toFun:=fun f s=>((((if s 0 then zl⁻¹ else zl:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)•(LinearMap.id:Module.End (Qa 7) (Qa 7))) (f s)
     map_add':=fun _ _=>by funext s;simp only[Pi.add_apply,AU,Br,Am,EM]
     map_smul':=fun _ _=>by funext s;simp only[AX,AU,Br,DE,Am];ring }:=by
   apply Ap;intro f;funext s;simp only[Aj,D,BO,LinearMap.coe_mk,AddHom.coe_mk,AU,Br,Am];cases hs:s 0
   . simp only[AE,Bj,zm,lam1]
   . simp only[Be,zr,lam2];ring
  rw[zP,z1];let e1:(Fin 1->Bool) ≃ Bool:=
   {toFun:=fun s=>s 0,invFun:=fun b _=>b,
    left_inv:=fun s=>funext fun i=>by rw[CR i],
    right_inv:=fun _=>rfl }
  rw[AO e1 (fun i:Fin 1->Bool=>Qr zb zd ι (Qa 7) ((((if i 0 then zl⁻¹ else zl:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)•LinearMap.id)) (fun b:Bool=>Qr zb zd ι (Qa 7) ((((if b then zl⁻¹ else zl:Ab N (Qa 7)):(Qa 7)ˣ):Qa 7)•LinearMap.id)) (fun _=>rfl)];rw[Ea,Az rfl,Aw (by decide),zq,zq,DQ]
 let zC:ℂ:=((ι zl:ℂˣ):ℂ);have zJ:((ι zl⁻¹:ℂˣ):ℂ)=zC⁻¹:=(by have h1:zC*((ι zl⁻¹:ℂˣ):ℂ)=1:=(by dsimp only[zC];rw[<-De,<-BB,<-AF,By,BI];rfl);have zn:zC≠0:=DH _;exact Ck zn (h1.trans (mul_inv_cancel₀ zn).symm));have zQ:zC ^ 4=-1:=by
  have zX:zl ^ 4≠1:=by
   intro h1;have zN:lam1 ^ 4=1:=by
    have:=Ah (fun x:Ab N (Qa 7)=>((x:(Qa 7)ˣ):Qa 7)) h1
    simpa[zm] using this
   rw[zt] at zN
   have h2:(2:ZMod 7)=0:=zw.injective (by
    rw[C2,Bn];linear_combination -zN)
   have hv:=Ah ZMod.val h2;simp only[QZ] at hv;omega
  have zY:(zl ^ 4) ^ 2=1:=(by apply Ae;apply A7;simpa[zm,<-Cz] using zu)
  have zO:zC ^ 4≠1:=fun h1=>zX (ι.injective (Ae (A7 (by
   simpa[zC,Dc] using h1))))
  have zR:(zC ^ 4)*(zC ^ 4)=1:=(by have h:=Ah (fun x:Ab N ℂ=>((x:ℂˣ):ℂ)) (Ah ι zY);simpa[zC,E6] using h);exact (mul_self_eq_one_iff.mp zR).resolve_left zO
 have zZ:(zC+zC⁻¹) ^ 2=2:=by
  have zn:zC≠0:=DH _;have z2:zC ^ 2≠0:=pow_ne_zero 2 zn;have zS:(zC⁻¹) ^ 2=-(zC ^ 2):=by
   apply Ck z2
   calc zC ^ 2*(zC⁻¹) ^ 2=(zC*zC⁻¹) ^ 2:=by rw[CC]
    _ = 1:=by rw[mul_inv_cancel₀ zn,B8]
    _ = -(zC ^ 4):=by rw[zQ,Dp]
    _ = zC ^ 2*-(zC ^ 2):=by ring
  calc (zC+zC⁻¹) ^ 2=zC ^ 2+2*(zC*zC⁻¹)+(zC⁻¹) ^ 2:=by ring
   _ = zC ^ 2+2+-(zC ^ 2):=by rw[mul_inv_cancel₀ zn,AK,zS]
   _ = 2:=by ring
 obtain ⟨q,hq⟩:=S.ratTr zf zg;change Qr zb zd ι (Fin S.n->Qa 7) (Matrix.toLin' HK)=(q:ℂ) at hq;rw[zx,zI,zJ] at hq;have z0:((q ^ 2:ℚ):ℂ)=((2:ℚ):ℂ):=(by push_cast;rw[<-hq,zZ]);have zE:q ^ 2=2:=Rat.cast_injective z0;have zB:q.num ^ 2=2*(q.den:ℤ) ^ 2:=by have h1:(q.num:ℚ) ^ 2=2*(q.den:ℚ) ^ 2:=(by have z3:(q.den:ℚ)≠0:=Nat.cast_ne_zero.mpr q.den_nz;have zT:q=(q.num:ℚ) / (q.den:ℚ):=(Rat.num_div_den q).symm;rw[zT,div_pow,div_eq_iff (pow_ne_zero 2 z3)] at zE;exact zE);exact_mod_cast h1
 have zU:(2:ℤ)∣q.num:=(by have zv:Even (q.num ^ 2):=⟨(q.den:ℤ) ^ 2,by linarith⟩;obtain ⟨m,hm⟩:=((Int.even_pow (n:=2)).mp zv).1;exact ⟨m,by omega⟩);obtain ⟨k,hk⟩:=zU;have zV:(2:ℤ)∣(q.den:ℤ):=by
  rw[hk] at zB;have z7:(q.den:ℤ) ^ 2=2*k ^ 2:=by linarith
  have zv:Even ((q.den:ℤ) ^ 2):=⟨k ^ 2,by linarith⟩;obtain ⟨m,hm⟩:=((Int.even_pow (n:=2)).mp zv).1;exact ⟨m,by omega⟩
 have zK:2∣q.num.natAbs:=(by rw[hk];exact ⟨k.natAbs,by simp[Int.natAbs_mul]⟩);have zL:2∣q.den:=Int.ofNat_dvd.mp zV;have z6:2∣1:=(by have h:=DR zK zL;rwa[q.reduced] at h);omega
noncomputable def Wl [Fact (Nat.Prime 7)]
  { N:ℕ} {hN_pos:0 < N} {hNp:¬ 7∣N}
  { ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N hN_pos hNp ι) : Subgroup (Aa (Fin S.n) (ZMod 7)) where
 carrier:={g | g.valᵀ*S.B*g.val=S.B/\∀ r∈(O2 S.L).map S.L.subtype,g*r*g⁻¹∈(O2 S.L).map S.L.subtype}
 one_mem':=⟨by simp,fun r hr=>by simpa using hr⟩
 mul_mem':=fun {a b} ⟨haB,haR⟩ ⟨hbB,hbR⟩=>
  ⟨by
    change (a.val*b.val)ᵀ*S.B*(a.val*b.val)=S.B
    rw[AT]
    calc b.valᵀ*a.valᵀ*S.B*(a.val*b.val)
        = b.valᵀ*(a.valᵀ*S.B*a.val)*b.val:=by simp only[Af]
      _ = S.B:=by rw[haB,hbB],
   fun r hr=>by have:=haR _ (hbR r hr);simpa[Ad] using this⟩
 inv_mem':=fun {a} ⟨haB,haR⟩=>
  ⟨by
    change a.invᵀ*S.B*a.inv=S.B
    calc a.invᵀ*S.B*a.inv=a.invᵀ*(a.valᵀ*S.B*a.val)*a.inv:=by rw[haB]
      _ = (a.val*a.inv)ᵀ*S.B*(a.val*a.inv):=by rw[AT];simp only[Af]
      _ = S.B:=by rw[a.val_inv,BM,AC,As],
   fun r hr=>by
     let za:=(O2 S.L).map S.L.subtype;have zc:Function.Injective (fun x:za=>(⟨a*x.1*a⁻¹,haR x.1 x.2⟩:za)):=by
       intro x y h;apply Ae;have h1:a*x.1*a⁻¹=a*y.1*a⁻¹:=Ah Subtype.val h
       calc x.1=a⁻¹*(a*x.1*a⁻¹)*a:=by group
         _ = a⁻¹*(a*y.1*a⁻¹)*a:=by rw[h1]
         _ = y.1:=by group
     have zb:=Finite.injective_iff_surjective.mp zc;obtain ⟨⟨y,hy⟩,hyeq⟩:=zb ⟨r,hr⟩;have zd:a*y*a⁻¹=r:=Ah Subtype.val hyeq;have:a⁻¹*r*a⁻¹⁻¹=y:=by rw[<-zd];group
     rw[this];exact hy⟩
lemma Yv [Fact (Nat.Prime 7)]
  {N:ℕ} {za:0 < N} {zb:¬ 7∣N}
  {ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N za zb ι) : S.L<=Wl S:=by
 intro g hg;have zc:(O2 S.L).Normal:=QI S.L;refine ⟨S.B_inv g hg,fun r hr=>?_⟩;rcases Subgroup.mem_map.mp hr with ⟨rL,hrR,rfl⟩
 let gL:S.L:=⟨g,hg⟩;refine Subgroup.mem_map.mpr ⟨gL*rL*gL⁻¹,zc.conj_mem rL hrR gL,?_⟩;rw[AF,AF,C5];rfl
set_option maxHeartbeats 800000 in
lemma YF [Fact (Nat.Prime 7)]
  { N:ℕ} {zg:0 < N} {zh:¬ 7∣N}
  { ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N zg zh ι) (zf:(⟨Qd S.n 7,S.negOne_mem⟩:S.L)∈O2 S.L) (za:Qn (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zf⟩) (B:Qm (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,zf⟩ 1 false) (zc:Qa 7) (ze:zc*zc=-1) (zb:(Fin S.n->Qa 7)≃ₗ[Qa 7] ((Fin 1->Bool)->Qa 7)) (zd:∀ (r:O2 S.L) (v:Fin S.n->Qa 7), zb ((r.1.1.val.map (algebraMap (ZMod 7) (Qa 7)))*ᵥv)=
      let rels:=QJ (p:=7) (m:=1) false ze
      QA za B (-1) (Qk false zc) (Ql false)
       (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥzb v) :
  ∃ ψN:Wl S→*Equiv.Perm (Fin 3),(∀ g:Wl S,g∈ψN.ker↔g.1∈(O2 S.L).map S.L.subtype)/\Nat.card (Wl S)<=48:=by
 classical
 let ιK:=algebraMap (ZMod 7) (Qa 7);let R:=O2 S.L;have vj:R.Normal:=QI S.L;let zL:S.L:=⟨Qd S.n 7,S.negOne_mem⟩;let zR:R:=⟨zL,zf⟩;have zz:zR*zR=1:=za.z_sq;have zT:Nat.card R=8:=by simpa using B.hcard
 have z9:∀ r:R,zR*r=r*zR:=fun r=>
  (Subgroup.mem_center_iff.mp ((za.center_iff zR).mpr (Or.inr rfl)) r).symm
 let R_GL:Subgroup (Aa (Fin S.n) (ZMod 7)):=R.map S.L.subtype;let zk:R≃*R_GL:=
  { toFun:=fun r=>⟨r.1.1,⟨r.1,r.2,rfl⟩⟩
    invFun:=fun x=>⟨Classical.choose x.2,(Classical.choose_spec x.2).1⟩
    left_inv:=fun r=>Ae (Ae (Classical.choose_spec (⟨r.1,r.2,rfl⟩:r.1.1∈R_GL)).2)
    right_inv:=fun x=>Ae (Classical.choose_spec x.2).2
    map_mul':=fun _ _=>rfl }
 have zB:Nat.card R_GL=8:=(by rw[<-zT];exact (Bc zk.toEquiv).symm);let xR:R:=B.x 0;let yR:R:=B.y 0;have vu:xR*xR=zR:=by simpa[xR] using B.hsq_x 0
 have vv:yR*yR=zR:=by simpa[yR] using B.hsq_y 0
 have zU:xR*yR=zR*(yR*xR):=B.hxy_same 0;have z7:yR*xR=zR*(xR*yR):=by
  calc yR*xR=(zR*zR)*(yR*xR):=by rw[zz,AA]
    _ = zR*(xR*yR):=by rw[Ad,<-zU]
 have zm:∀ (c:Bool) (a b:Fin 1->Bool),(Qe za B) (c,a,b)=(if c then zR else 1)*((if a 0 then xR else 1)*(if b 0 then yR else 1)):=fun c a b=>by
  rw[Qs];dsimp only[Qc,Qb];rw[AK]
 let u3:Fin 3->R:=![xR,yR,xR*yR];have zC:∀ r:R,r≠1/\r≠zR->∃! k:Fin 3,r=u3 k\/r=zR*u3 k:=by
  intro r ⟨hr1,hrz⟩;obtain ⟨⟨c,a,b⟩,hr⟩:=(Qe za B).surjective r;have zV:r=(if c then zR else 1)*((if a 0 then xR else 1)*(if b 0 then yR else 1)):=(by rw[<-hr,zm]);have zD:∀ a0 b0:Bool,(r=(if a0 then xR else 1)*(if b0 then yR else 1)\/r=zR*((if a0 then xR else 1)*(if b0 then yR else 1)))↔(a 0=a0/\b 0=b0):=by
    intro a0 b0;have hw:∀ c0:Bool,(if c0 then zR else 1)*((if a0 then xR else 1)*(if b0 then yR else 1))=(Qe za B) (c0,fun _=>a0,fun _=>b0):=fun c0=>(zm c0 (fun _=>a0) (fun _=>b0)).symm;rw[<-hr];constructor
    .
      rintro (h | h)
      . have h':(Qe za B) (c,a,b)=(Qe za B) (false,fun _=>a0,fun _=>b0):=(by rw[<-hw false,Aw Bz,AA];exact h);have zp:=(Qe za B).injective h';exact ⟨An (Ah (fun t=>t.2.1) zp) 0,An (Ah (fun t=>t.2.2) zp) 0⟩
      . have h':(Qe za B) (c,a,b)=(Qe za B) (true,fun _=>a0,fun _=>b0):=(by rw[<-hw true,Az rfl];exact h);have zp:=(Qe za B).injective h';exact ⟨An (Ah (fun t=>t.2.1) zp) 0,An (Ah (fun t=>t.2.2) zp) 0⟩
    .
      rintro ⟨zs,zt⟩;have vk:a=fun _=>a0:=funext fun i=>by rw[CR i,zs]
      have vl:b=fun _=>b0:=funext fun i=>by rw[CR i,zt]
      rw[vk,vl];cases c
      . left;rw[<-hw false,Aw Bz,AA]
      . right;rw[<-hw true,Az rfl]
  have zn:∀ k:Fin 3,(r=u3 k\/r=zR*u3 k)↔(a 0=(if k=1 then false else true)/\b 0=(if k=0 then false else true)):=fun k=>by
    fin_cases k
    . simpa[u3] using zD true false
    . simpa[u3] using zD false true
    . simpa[u3] using zD true true
  cases zs:a 0 <;> cases zt:b 0
  .
    exfalso;cases c
    . exact hr1 (by simpa[zs,zt] using zV)
    . exact hrz (by simpa[zs,zt] using zV)
  .
    refine ⟨1,(zn 1).mpr (by simp[zs,zt]),fun k hk=>?_⟩
    have:=(zn k).mp hk;fin_cases k <;> simp[zs,zt] at this ⊢
  .
    refine ⟨0,(zn 0).mpr (by simp[zs,zt]),fun k hk=>?_⟩
    have:=(zn k).mp hk;fin_cases k <;> simp[zs,zt] at this ⊢
  .
    refine ⟨2,(zn 2).mpr (by simp[zs,zt]),fun k hk=>?_⟩
    have:=(zn k).mp hk;fin_cases k <;> simp[zs,zt] at this ⊢
 have zJ:∀ k:Fin 3,u3 k≠1/\u3 k≠zR:=fun k=>by
  have va:(1:R)=(Qe za B) (false,fun _=>false,fun _=>false):=by rw[zm];simp
  have vb:zR=(Qe za B) (true,fun _=>false,fun _=>false):=by rw[zm];simp
  have zW:∀ k:Fin 3,u3 k=(Qe za B) (false,fun _=>if k=1 then false else true,fun _=>if k=0 then false else true):=(by intro k;rw[zm];fin_cases k <;> simp[u3]);constructor <;> intro h
  . rw[zW k,va] at h;have zp:=(Qe za B).injective h;have h0:=An (Ah (fun t=>t.2.1) zp) 0;have h1:=An (Ah (fun t=>t.2.2) zp) 0;fin_cases k <;> simp at h0 h1
  . rw[zW k,vb] at h;exact Bz (Ah Prod.fst ((Qe za B).injective h))
 let NSp:=Wl S;have zy:S.L<=NSp:=Yv S;obtain ⟨conjN,hconjN_val⟩:∃ conjN:NSp->(R≃*R),∀ (g:NSp) (r:R),(conjN g r).1.1=g.1*r.1.1*g.1⁻¹:=by
  have zi:∀ x:R_GL,(zk.symm x).1.1=x.1:=fun x=>
    (Classical.choose_spec x.2).2
  refine ⟨fun g=>
    { toFun:=fun r=>zk.symm ⟨g.1*r.1.1*g.1⁻¹,g.2.2 r.1.1 ⟨r.1,r.2,rfl⟩⟩
      invFun:=fun r=>zk.symm ⟨g.1⁻¹*r.1.1*g.1,by
       have h:=(NSp.inv_mem g.2).2 r.1.1 ⟨r.1,r.2,rfl⟩;rwa[inv_inv] at h⟩
      left_inv:=fun r=>Ae (Ae (by
       rw[zi];dsimp only;rw[zi];group))
      right_inv:=fun r=>Ae (Ae (by
       rw[zi];dsimp only;rw[zi];group))
      map_mul':=fun a b=>Ae (Ae (by
       change (zk.symm _).1.1=(zk.symm _).1.1*(zk.symm _).1.1;rw[zi,zi,zi];dsimp only
       simp only[BB];group)) },
    fun g r=>zi ⟨g.1*r.1.1*g.1⁻¹,g.2.2 r.1.1 ⟨r.1,r.2,rfl⟩⟩⟩
 have zo:∀ g:NSp,conjN g zR=zR:=fun g=>by
  apply Ae;apply Ae;rw[hconjN_val];apply A7;change g.1.val*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*g.1.inv=-1;rw[CN,As,Cp,g.1.val_inv]
 have zu:∀ (g:NSp) (k:Fin 3),∃! j:Fin 3,conjN g (u3 k)=u3 j\/conjN g (u3 k)=zR*u3 j:=fun g k=>by
  apply zC;exact ⟨fun h=>(zJ k).1 ((conjN g).injective (h.trans (BI _).symm)),fun h=>(zJ k).2 ((conjN g).injective (h.trans (zo g).symm))⟩
 obtain ⟨act3,hact3_spec⟩:∃ act3:NSp->Fin 3->Fin 3,∀ g k,conjN g (u3 k)=u3 (act3 g k)\/conjN g (u3 k)=zR*u3 (act3 g k):=
  ⟨fun g k=>Classical.choose (zu g k).exists,fun g k=>Classical.choose_spec (zu g k).exists⟩
 have zl:∀ g k j,(conjN g (u3 k)=u3 j\/conjN g (u3 k)=zR*u3 j)->j=act3 g k:=
  fun g k j hj=>(zu g k).unique hj (hact3_spec g k)
 have zE:∀ (g:NSp) (k:Fin 3),act3 g⁻¹ (act3 g k)=k:=fun g k=>by
  symm;apply zl;have h1:conjN g⁻¹ (conjN g (u3 k))=u3 k:=by apply Ae;apply Ae;rw[hconjN_val,hconjN_val,EW];group
  rcases hact3_spec g k with h | h
  . rw[<-h,h1];left;rfl
  .
    have h2:=Ah (conjN g⁻¹) h;rw[h1,AF,zo] at h2;right;calc conjN g⁻¹ (u3 (act3 g k))=zR*(zR*conjN g⁻¹ (u3 (act3 g k))):=by rw[<-Ad,zz,AA]
      _ = zR*u3 k:=by rw[<-h2]
 have zA:∀ (g:NSp) (k:Fin 3),act3 g (act3 g⁻¹ k)=k:=fun g k=>by
  symm;apply zl;have h1:conjN g (conjN g⁻¹ (u3 k))=u3 k:=by apply Ae;apply Ae;rw[hconjN_val,hconjN_val,EW];group
  rcases hact3_spec g⁻¹ k with h | h
  . rw[<-h,h1];left;rfl
  .
    have h2:=Ah (conjN g) h;rw[h1,AF,zo] at h2;right;calc conjN g (u3 (act3 g⁻¹ k))=zR*(zR*conjN g (u3 (act3 g⁻¹ k))):=by rw[<-Ad,zz,AA]
      _ = zR*u3 k:=by rw[<-h2]
 have zK:∀ k:Fin 3,act3 1 k=k:=fun k=>by
  symm;apply zl;left;apply Ae;apply Ae;rw[hconjN_val,CH,AA,inv_one,AK]
 have zM:∀ (g₁ g₂:NSp) (k:Fin 3),act3 (g₁*g₂) k=act3 g₁ (act3 g₂ k):=fun g₁ g₂ k=>by
  symm;apply zl;have vm:conjN (g₁*g₂) (u3 k)=conjN g₁ (conjN g₂ (u3 k)):=by apply Ae;apply Ae;rw[hconjN_val,hconjN_val,hconjN_val,BB];group
  rw[vm];rcases hact3_spec g₂ k with h2 | h2 <;> rw[h2]
  . exact hact3_spec g₁ (act3 g₂ k)
  .
    rw[AF,zo g₁];rcases hact3_spec g₁ (act3 g₂ k) with h1 | h1 <;> rw[h1]
    . right;rfl
    . left;rw[<-Ad,zz,AA]
 obtain ⟨ψN,hψN_apply⟩:∃ ψN:NSp→*Equiv.Perm (Fin 3),∀ g k,ψN g k=act3 g k:=
  ⟨
   { toFun:=fun g=>⟨act3 g,act3 g⁻¹,zE g,zA g⟩
     map_one':=Ec fun k=>by rw[Equiv.Perm.one_apply];exact zK k
     map_mul':=fun g₁ g₂=>Ec fun k=>by rw[Equiv.Perm.mul_apply];exact zM g₁ g₂ k },
   fun _ _=>rfl⟩
 let zq:=QJ (p:=7) (m:=1) false ze;let zN:R→*Matrix (Fin 1->Bool) (Fin 1->Bool) (Qa 7):=
  QA za B (-1) (Qk false zc) (Ql false)
    (fun A=>by simp) (by simp) zq.1 zq.2.1 zq.2.2.1 zq.2.2.2.1 zq.2.2.2.2.1 zq.2.2.2.2.2
 have vc:zN xR=Qk false zc 0:=
  Q7 za B (-1) (Qk false zc) (Ql false) _ _ _ _ _ _ _ _ 0
 have vd:zN yR=Ql false 0:=
  Wd za B (-1) (Qk false zc) (Ql false) _ _ _ _ _ _ _ _ 0
 have zv:∀ g:NSp,g∈ψN.ker↔g.1∈R_GL:=by
  intro g;constructor
  .
    intro hg;rw[Bw] at hg;have zX:conjN g xR=xR\/conjN g xR=zR*xR:=by
      have h1:act3 g 0=0:=by rw[<-hψN_apply];exact DV hg 0
      simpa[u3,h1] using hact3_spec g 0
    have zY:conjN g yR=yR\/conjN g yR=zR*yR:=by
      have h1:act3 g 1=1:=by rw[<-hψN_apply];exact DV hg 1
      simpa[u3,h1] using hact3_spec g 1
    let α:Bool:=decide (conjN g xR≠xR);let β:Bool:=decide (conjN g yR≠yR);let h:R:=(if β then xR else 1)*(if α then yR else 1);let g':NSp:=⟨h.1.1⁻¹,NSp.inv_mem (zy h.1.2)⟩*g;have zx:g'.1=h.1.1⁻¹*g.1:=by dsimp only[g'];rw[BB]
    have zF:conjN g' xR=xR:=by
      apply zk.injective;apply Ae;change (conjN g' xR).1.1=xR.1.1;rw[hconjN_val,zx];have vn:g.1*xR.1.1*g.1⁻¹=(if α then zR else 1).1.1*xR.1.1:=by
       have:=Ah (fun r:R=>r.1.1) (show conjN g xR=(if α then zR else 1)*xR by
        rcases zX with he | he
        . simp[α,he]
        .
         by_cases zO:conjN g xR=xR
         . simp[α,zO]
         . simp[α,zO,he])
       simpa only[BB,hconjN_val] using this
      have zZ:h*xR=(if α then zR else 1)*(xR*h):=by
       dsimp only[h];cases β <;> cases α <;> simp
       . exact z7
       .
        calc xR*yR*xR=xR*(yR*xR):=by rw[Ad]
         _ = xR*(zR*(xR*yR)):=by rw[z7]
         _ = zR*(xR*(xR*yR)):=by rw[<-Ad,<-z9 xR,Ad]
      have ve:h.1.1*xR.1.1=(if α then zR else 1).1.1*(xR.1.1*h.1.1):=by
       have:=Ah (fun r:R=>r.1.1) zZ
       simpa only[BB] using this
      calc (h.1.1⁻¹*g.1)*xR.1.1*(h.1.1⁻¹*g.1)⁻¹
        = h.1.1⁻¹*(g.1*xR.1.1*g.1⁻¹)*h.1.1:=by group
       _ = h.1.1⁻¹*((if α then zR else 1).1.1*xR.1.1)*h.1.1:=by rw[vn]
       _ = h.1.1⁻¹*((if α then zR else 1).1.1*(xR.1.1*h.1.1)):=by group
       _ = h.1.1⁻¹*(h.1.1*xR.1.1):=by rw[<-ve]
       _ = xR.1.1:=by group
    have zG:conjN g' yR=yR:=by
      apply zk.injective;apply Ae;change (conjN g' yR).1.1=yR.1.1;rw[hconjN_val,zx];have vo:g.1*yR.1.1*g.1⁻¹=(if β then zR else 1).1.1*yR.1.1:=by
       have:=Ah (fun r:R=>r.1.1) (show conjN g yR=(if β then zR else 1)*yR by
        rcases zY with he | he
        . simp[β,he]
        .
         by_cases zO:conjN g yR=yR
         . simp[β,zO]
         . simp[β,zO,he])
       simpa only[BB,hconjN_val] using this
      have z0:h*yR=(if β then zR else 1)*(yR*h):=(by dsimp only[h];cases β <;> cases α <;> simp[zU,Ad]);have vf:h.1.1*yR.1.1=(if β then zR else 1).1.1*(yR.1.1*h.1.1):=by
       have:=Ah (fun r:R=>r.1.1) z0
       simpa only[BB] using this
      calc (h.1.1⁻¹*g.1)*yR.1.1*(h.1.1⁻¹*g.1)⁻¹
        = h.1.1⁻¹*(g.1*yR.1.1*g.1⁻¹)*h.1.1:=by group
       _ = h.1.1⁻¹*((if β then zR else 1).1.1*yR.1.1)*h.1.1:=by rw[vo]
       _ = h.1.1⁻¹*((if β then zR else 1).1.1*(yR.1.1*h.1.1)):=by group
       _ = h.1.1⁻¹*(h.1.1*yR.1.1):=by rw[<-vf]
       _ = yR.1.1:=by group
    let Gmat:Matrix (Fin 1->Bool) (Fin 1->Bool) (Qa 7):=
      LinearMap.toMatrix' (zb.toLinearMap∘ₗMatrix.toLin' (g'.1.val.map ιK)∘ₗzb.symm.toLinearMap)
    have zS:∀ v,Gmat*ᵥv=zb ((g'.1.val.map ιK)*ᵥzb.symm v):=fun v=>CO _ v;have zr:∀ r:R,g'.1*r.1.1=r.1.1*g'.1->Gmat*zN r=zN r*Gmat:=fun r hr=>by
      apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,<-Ac,zS];have h1:zb.symm (zN r*ᵥv)=(r.1.1.val.map ιK)*ᵥzb.symm v:=(by apply zb.injective;rw[zb.apply_symm_apply,zd,zb.apply_symm_apply]);have vp:g'.1.val.map ιK*r.1.1.val.map ιK=r.1.1.val.map ιK*g'.1.val.map ιK:=(by rw[<-Aq,<-Aq];exact Ah (Matrix.map · ιK) (Ah Units.val hr));rw[h1,Ac,vp,<-Ac,zd]
    have vg:g'.1*xR.1.1=xR.1.1*g'.1:=by
      have h1:g'.1*xR.1.1*g'.1⁻¹=xR.1.1:=by rw[<-hconjN_val g' xR,zF]
      calc g'.1*xR.1.1=(g'.1*xR.1.1*g'.1⁻¹)*g'.1:=by group
       _ = xR.1.1*g'.1:=by rw[h1]
    have vh:g'.1*yR.1.1=yR.1.1*g'.1:=by
      have h1:g'.1*yR.1.1*g'.1⁻¹=yR.1.1:=by rw[<-hconjN_val g' yR,zG]
      calc g'.1*yR.1.1=(g'.1*yR.1.1*g'.1⁻¹)*g'.1:=by group
       _ = yR.1.1*g'.1:=by rw[h1]
    obtain ⟨zw,zQ⟩:=Q5 (by decide) false ze Gmat
      (fun i=>by rw[CR i,<-vc];exact zr xR vg)
      (fun i=>by rw[CR i,<-vd];exact zr yR vh)
    have zP:g'.1.val.map ιK=zw•1:=(by apply Matrix.toLin'.injective;apply Ap;intro v;simp only[Aj,Bv,AN];apply zb.injective;have h1:=zS (zb v);rw[zb.symm_apply_apply,zQ,Bv,AN] at h1;rw[<-h1,Bd]);have z4:zw*zw=1:=by
      have h1:=Ah (Matrix.map · ιK) g'.2.1;have vq:(g'.1.valᵀ).map ιK=(g'.1.val.map ιK)ᵀ:=by ext a b;rfl
      rw[Aq,Aq,vq,zP,Ch,BM,Ar,AC,Ao,As,AR] at h1;have vi:(zw*zw - 1)•(S.B.map ιK)=0:=by rw[DJ,Bx,h1,Cx]
      have z1:S.B.map ιK≠0:=fun h0=>S.B_det (by
       haveI:Nonempty (Fin S.n):=⟨⟨0,S.hn_pos⟩⟩;have:S.B=0:=by ext a b;apply ιK.injective;simpa using An (An h0 a) b
       rw[this];exact Di)
      exact sub_eq_zero.mp ((smul_eq_zero.mp vi).resolve_right z1)
    have z2:g'.1∈R_GL:=by
      rcases mul_self_eq_one_iff.mp z4 with rfl | rfl
      .
       have:g'.1=1:=by apply A7;ext a b;apply ιK.injective;simpa[BG] using An (An zP a) b
       rw[this];exact R_GL.one_mem
      .
       have:g'.1=Qd S.n 7:=by
        apply A7;ext a b;apply ιK.injective;have h:=An (An zP a) b;by_cases z8:a=b
        . subst z8;simpa[Qd] using h
        . simpa[Qd,AH z8] using h
       rw[this];exact ⟨zL,zf,rfl⟩
    have z5:g.1=h.1.1*g'.1:=by rw[zx];group
    rw[z5];exact R_GL.mul_mem ⟨h.1,h.2,rfl⟩ z2
  .
    intro vt;rw[Bw];apply Ec;intro k;rw[hψN_apply];change act3 g k=k;symm;apply zl;obtain ⟨rL,vr,vs⟩:=vt;let rR:R:=⟨rL,vr⟩;have z6:=za.comm_mem rR (u3 k);have zj:conjN g (u3 k)=(rR*u3 k*rR⁻¹*(u3 k)⁻¹)*u3 k:=by apply zk.injective;apply Ae;change (conjN g (u3 k)).1.1=((rR*u3 k*rR⁻¹*(u3 k)⁻¹)*u3 k).1.1;rw[hconjN_val,<-vs];simp only[BB,EW,Subgroup.coe_subtype,rR];group
    rcases z6 with h1 | hz
    . left;rw[zj,h1,AA]
    . right;rw[zj,hz]
 have zH:Nat.card ψN.ker=8:=by
  let eK:ψN.ker ≃ R_GL:=
    { toFun:=fun g=>⟨g.1.1,(zv g.1).mp g.2⟩
      invFun:=fun r=>⟨⟨r.1,by obtain ⟨rL,_,hr⟩:=r.2;rw[<-hr];exact zy rL.2⟩,(zv _).mpr r.2⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  rw[Bc eK,zB]
 have zI:Nat.card NSp<=48:=by
  have h1:=BX ψN.ker;have h2:Nat.card (NSp ⧸ ψN.ker)=Nat.card ψN.range:=
    Bc (QuotientGroup.quotientKerEquivRange ψN).toEquiv
  have h3:Nat.card ψN.range<=6:=(by have h6:Nat.card (Equiv.Perm (Fin 3))=6:=(by rw[Au,D5,AW];decide);have z3:=Cf ψN.range;rw[h6] at z3;exact AP (by decide) z3);change Nat.card ψN.ker*Nat.card (NSp ⧸ ψN.ker)=Nat.card NSp at h1;rw[h2,zH] at h1;omega
 exact ⟨ψN,zv,zI⟩
set_option maxHeartbeats 800000 in
lemma Wm [Fact (Nat.Prime 7)]
  {N:ℕ} {zg:0 < N} {zh:¬ 7∣N}
  {ι:Ab N (Qa 7)≃*Ab N ℂ} (S:Qg 7 N zg zh ι) (ze:(⟨Qd S.n 7,S.negOne_mem⟩:S.L)∈O2 S.L) (zc:Qn (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,ze⟩) (B:Qm (O2 S.L) ⟨⟨Qd S.n 7,S.negOne_mem⟩,ze⟩ 1 false) (zi:S.n=2 ^ 1) (zj:∀ g:S.L,(∀ r∈O2 S.L,g*r=r*g)->g.1=1\/g.1=Qd S.n 7) (za:Qa 7) (zf:za*za=-1) (zd:(Fin S.n->Qa 7)≃ₗ[Qa 7] ((Fin 1->Bool)->Qa 7)) (zb:∀ (r:O2 S.L) (v:Fin S.n->Qa 7), zd ((r.1.1.val.map (algebraMap (ZMod 7) (Qa 7)))*ᵥv)=
    let rels:=QJ (p:=7) (m:=1) false zf
    QA zc B (-1) (Qk false za) (Ql false)
     (fun A=>by simp) (by simp) rels.1 rels.2.1 rels.2.2.1 rels.2.2.2.1 rels.2.2.2.2.1 rels.2.2.2.2.2 r*ᵥzd v) :
  False:=by
 classical
 let R:=O2 S.L;have vh:R.Normal:=QI S.L;let zL:S.L:=⟨Qd S.n 7,S.negOne_mem⟩;let zR:R:=⟨zL,ze⟩;have zT:Nat.card R=8:=by simpa using B.hcard
 let R_GL:Subgroup (Aa (Fin S.n) (ZMod 7)):=R.map S.L.subtype;let NSp:=Wl S;have zm:S.L<=NSp:=Yv S;let xR:R:=B.x 0;let yR:R:=B.y 0;have vb:xR*xR=zR:=by simpa[xR] using B.hsq_x 0
 have vc:yR*yR=zR:=by simpa[yR] using B.hsq_y 0
 have zK:xR*yR=zR*(yR*xR):=B.hxy_same 0;have zC:∀ (c:Bool) (a b:Fin 1->Bool),(Qe zc B) (c,a,b)=(if c then zR else 1)*((if a 0 then xR else 1)*(if b 0 then yR else 1)):=fun c a b=>by
  rw[Qs];dsimp only[Qc,Qb];rw[AK]
 obtain ⟨vn,zJ,zB⟩:=YF S ze zc B za zf zd zb;let zk:S.L→*Equiv.Perm (Fin 3):=vn.comp
  {toFun:=fun g=>⟨g.1,zm g.2⟩,map_one':=rfl,map_mul':=fun _ _=>rfl }
 have zu:zk.ker=R:=by
  ext g;simp only[Bw,zk,Et,MonoidHom.coe_mk,OneHom.coe_mk];have h:=zJ ⟨g.1,zm g.2⟩;simp only[Bw] at h;rw[h];constructor
  . rintro ⟨rL,z3,hrg⟩;have:g=rL:=Ae hrg.symm;rwa[this]
  . intro vq;exact ⟨g,vq,rfl⟩
 have zq:Nat.card S.L=8*Nat.card zk.range:=by
  have h1:=BX zk.ker;have h2:Nat.card (S.L ⧸ zk.ker)=Nat.card zk.range:=
   Bc (QuotientGroup.quotientKerEquivRange zk).toEquiv
  change Nat.card zk.ker*Nat.card (S.L ⧸ zk.ker)=Nat.card S.L at h1;rw[h2,zu,zT] at h1;exact h1.symm
 have zw:Nat.card zk.range∣6:=(by have h1:=Cf zk.range;have h6:Nat.card (Equiv.Perm (Fin 3))=6:=(by rw[Au,D5,AW];decide);rwa[h6] at h1);have zV:3∣Nat.card zk.range:=by
  let v0:Fin S.n->ZMod 7:=Pi.single ⟨0,S.hn_pos⟩ 1;have va:v0≠0:=fun h=>by simpa[v0] using An h ⟨0,S.hn_pos⟩
  obtain ⟨g,vo,vp⟩:=S.SF v0 va (Units.mk0 (2:ZMod 7) (fun e=>by
   have h:=Ah ZMod.val e;simp only[QZ] at h;omega))
  let gL:S.L:=⟨g,vo⟩;have zW:∀ k:ℕ,(gL ^ k).1.val*ᵥv0=((2:ZMod 7) ^ k)•v0:=fun k=>by
   induction k with
   | zero=>simp
   | succ k ih=>
    rw[BA];change (g.val*(gL ^ k).1.val)*ᵥv0=_;rw[<-Ac,ih,Al,vp,DG,AR,BA,Bb]
  have zy:3∣orderOf gL:=by
   have h1:=zW (orderOf gL);rw[BE] at h1;simp only[OneMemClass.coe_one,Cn,AN] at h1;have zM:(2:ZMod 7) ^ orderOf gL=1:=by
    have:((2:ZMod 7) ^ orderOf gL - 1)•v0=0:=by rw[DJ,Bx,CE];exact h1.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right va)
   have zX:(2:ZMod 7) ^ (orderOf gL % 3)=1:=(by rw[<-Cd (orderOf gL) 3,CT,Cz,YA,B8,AA] at zM;exact zM);have vu:=DF (orderOf gL) (by decide:0 < 3);have h0:orderOf gL % 3=0:=by
    interval_cases hm:orderOf gL % 3
    . rfl
    . exact absurd zX YH
    . exact absurd zX Yu
   exact Eg h0
  have zN:3∣Nat.card S.L:=zy.trans (Dd gL);rw[zq] at zN;exact (Nat.Coprime.dvd_of_dvd_mul_left (by decide:Nat.Coprime 3 8) zN)
 have zr:Nat.card zk.range=3\/Nat.card zk.range=6:=(by have vi:=AP (by decide) zw;have vr:0 < Nat.card zk.range:=CD;interval_cases hc:Nat.card zk.range <;> omega);rcases zr with hcard3 | hcard6
 ·
  have zN:3∣Nat.card S.L:=by rw[zq,hcard3];decide
  haveI:Fact (Nat.Prime 3):=⟨by decide⟩;obtain ⟨g,zv⟩:=DD (G:=S.L) 3 zN;have zG:zk g≠1:=fun h1=>by
   have hr:g∈R:=zu ▸ MonoidHom.mem_ker.mpr h1;obtain ⟨k,hk⟩:=Wv S.L ⟨g,hr⟩;have vd:3∣2 ^ k:=zv ▸ Bl (Ah Subtype.val hk);have ve:Nat.Coprime 3 (2 ^ k):=Eo k (by decide);have:3∣1:=by have:=DR (EO 3) vd;rwa[ve.gcd_eq_one] at this
   omega
  rcases S.realMinus g with hconj_inv | hconj_zg
  .
   obtain ⟨c,hc⟩:=isConj_iff.mp hconj_inv;have zz:IsCyclic zk.range:=isCyclic_of_prime_card hcard3;have zx:∀ a b:zk.range,a*b=b*a:=fun a b=>by
    obtain ⟨zS,z2⟩:=zz.exists_generator;obtain ⟨vs,rfl⟩:=z2 a;obtain ⟨vt,rfl⟩:=z2 b;rw[<-Do,DQ,Do]
   have zY:(⟨zk c,⟨c,rfl⟩⟩:zk.range)*⟨zk g,⟨g,rfl⟩⟩*(⟨zk c,⟨c,rfl⟩⟩:zk.range)⁻¹=(⟨zk g,⟨g,rfl⟩⟩:zk.range)⁻¹:=Ae (by
    have h1:=Ah zk hc;simpa[AF,C5] using h1)
   rw[zx ⟨zk c,⟨c,rfl⟩⟩ ⟨zk g,⟨g,rfl⟩⟩,DN] at zY;have zZ:zk g*zk g=1:=by
    have h1:zk g=(zk g)⁻¹:=Ah Subtype.val zY
    conv_lhs=>rhs;rw[h1]
    exact By _
   have zO:g ^ 3=1:=by rw[<-zv];exact BE g
   have zt:zk g ^ 3=1:=by rw[<-Dc,zO,BI]
   have h1:zk g=1:=by
    calc zk g=(zk g*zk g)*zk g:=by rw[zZ,AA]
     _ = zk g ^ 3:=by rw[DK,E6]
     _ = 1:=zt
   exact zG h1
  .
   obtain ⟨c,hc⟩:=isConj_iff.mp hconj_zg;have z4:∀ k:ℕ,(c*g*c⁻¹) ^ k=c*g ^ k*c⁻¹:=fun k=>by
    induction k with
    | zero=>simp
    | succ k ih=>rw[DK,ih];group
   have zO:g ^ 3=1:=by rw[<-zv];exact BE g
   have zt:(zL*g) ^ 3=1:=(by rw[<-hc,z4,zO];group);have zU:Commute zL g:=(by apply Ae;apply A7;change (-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*g.1.val=g.1.val*(-1);simp);have z5:zL*zL=1:=(by apply Ae;apply A7;change (-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*(-1)=1;simp);rw[zU.mul_pow,zO,AK,DK,E6,z5,AA] at zt;exact zc.z_ne_one (Ae zt)
 ·
  have z6:Nat.card S.L=48:=by rw[zq,hcard6]
  have zD:NSp=S.L:=(by let f:S.L->NSp:=fun g=>⟨g.1,zm g.2⟩;have zP:Function.Injective f:=fun a b h=>Ae (Ah (fun x:NSp=>x.1) h);haveI:Fintype S.L:=Fintype.ofFinite S.L;haveI:Fintype NSp:=Fintype.ofFinite NSp;have vi:Fintype.card S.L<=Fintype.card NSp:=Cw f zP;have zH:Fintype.card S.L=Fintype.card NSp:=(by rw[<-Au,<-Au];exact DP (by rwa[Au,Au]) (z6.symm ▸ zB));have z7:Function.Surjective f:=(Ci f).mpr ⟨zP,zH⟩ |>.2;exact DP (fun g hg=>by obtain ⟨x,hx⟩:=z7 ⟨g,hg⟩;have h1:x.1=g:=Ah (fun y:NSp=>y.1) hx;rw[<-h1];exact x.2) zm);let x0:Matrix (Fin S.n) (Fin S.n) (ZMod 7):=xR.1.1.val;let y0:Matrix (Fin S.n) (Fin S.n) (ZMod 7):=yR.1.1.val;have zp:x0*x0=-1:=Ah (fun r:R=>r.1.1.val) vb;have vj:y0*y0=-1:=Ah (fun r:R=>r.1.1.val) vc;have z8:x0*y0=-(y0*x0):=(by have h:=Ah (fun r:R=>r.1.1.val) zK;simpa[x0,y0,zR,zL,Qd] using h);have zQ:x0ᵀ*S.B*x0=S.B:=S.B_inv xR.1.1 xR.1.2;let Hmat:Matrix (Fin S.n) (Fin S.n) (ZMod 7):=(2:ZMod 7)•(1+x0);let zn:Matrix (Fin S.n) (Fin S.n) (ZMod 7):=(2:ZMod 7)•(1 - x0);have zo:Hmat*zn=1:=by
   dsimp only[Hmat,zn];rw[Ar,Ao,AR,Yk];have h1:(1+x0)*(1 - x0)=(2:ZMod 7)•(1:Matrix (Fin S.n) (Fin S.n) (ZMod 7)):=by rw[BQ,Fe,Fe,AC,As,zp];ext a b;simp[EL];ring
   rw[h1,AR,Yz,Bx]
  have zA:zn*Hmat=1:=by
   dsimp only[Hmat,zn];rw[Ar,Ao,AR,Yk];have h1:(1 - x0)*(1+x0)=(2:ZMod 7)•(1:Matrix (Fin S.n) (Fin S.n) (ZMod 7)):=by rw[Matrix.sub_mul,BH,BH,AC,As,zp];ext a b;simp[EL];ring
   rw[h1,AR,Yz,Bx]
  let zl:Aa (Fin S.n) (ZMod 7):=⟨Hmat,zn,zo,zA⟩;have z0:Hmatᵀ*S.B*Hmat=S.B:=by
   have zI:x0ᵀ*S.B=-(S.B*x0):=by
    calc x0ᵀ*S.B=(x0ᵀ*S.B*x0)*(-x0):=by rw[CN,Af,zp,CN,As,Dp]
     _ = -(S.B*x0):=by rw[zQ,CN]
   dsimp only[Hmat];rw[Ch,Matrix.transpose_add,BM,Ar,Ao,Ar,AR,Yk];have h1:(1+x0ᵀ)*S.B*(1+x0)=(2:ZMod 7)•S.B:=by
    calc (1+x0ᵀ)*S.B*(1+x0)
      = S.B+S.B*x0+x0ᵀ*S.B+x0ᵀ*S.B*x0:=by simp only[BQ,BH,AC,As,Af,add_assoc];abel
     _ = S.B+S.B*x0+(-(S.B*x0))+S.B:=by rw[zQ,zI]
     _ = (2:ZMod 7)•S.B:=by ext a b;simp[EL]
   rw[h1,AR,Yz,Bx]
  have zE:∀ r∈R_GL,zl*r*zl⁻¹∈R_GL:=by
   have vk:zl*xR.1.1*zl⁻¹=xR.1.1:=(by apply A7;change Hmat*x0*zn=x0;have z9:Hmat*x0=x0*Hmat:=(by dsimp only[Hmat];rw[Ar,Ao,BQ,BH,AC,As]);rw[z9,Af,zo,As]);have vl:zl*yR.1.1*zl⁻¹=xR.1.1*yR.1.1:=by
    apply A7;change Hmat*y0*zn=x0*y0;dsimp only[Hmat,zn];rw[Ar,Ao,Ar,AR,Yk];have z1:y0*x0=-(x0*y0):=by rw[z8,Dp]
    have vf:x0*y0*x0=y0:=by rw[Af,z1,CN,<-Af,zp,Cp,AC,Dp]
    have h1:(1+x0)*y0*(1 - x0)=(2:ZMod 7)•(x0*y0):=by
     calc (1+x0)*y0*(1 - x0)
       = y0 - y0*x0+x0*y0 - x0*y0*x0:=by simp only[BQ,Fe,AC,As,add_sub_assoc];abel
      _ = y0 - (-(x0*y0))+x0*y0 - y0:=by rw[z1,vf]
      _ = (2:ZMod 7)•(x0*y0):=by ext a b;simp[EL];ring
    rw[h1,AR,Yz,Bx]
   have vm:zl*zR.1.1*zl⁻¹=zR.1.1:=(by apply A7;change Hmat*(-1:Matrix (Fin S.n) (Fin S.n) (ZMod 7))*zn=-1;rw[CN,As,Cp,zo]);intro r hr;obtain ⟨rL,z3,rfl⟩:=hr;obtain ⟨⟨c,a,b⟩,hcab⟩:=(Qe zc B).surjective ⟨rL,z3⟩;have vg:rL.1=(if c then zR else 1).1.1*((if a 0 then xR else 1).1.1*(if b 0 then yR else 1).1.1):=by have h1:(⟨rL,z3⟩:R)=(if c then zR else 1)*((if a 0 then xR else 1)*(if b 0 then yR else 1)):=(by rw[<-hcab,zC]);exact Ah (fun t:R=>t.1.1) h1
   change zl*rL.1*zl⁻¹∈R_GL;rw[vg];have zs:∀ u v:Aa (Fin S.n) (ZMod 7),zl*(u*v)*zl⁻¹=(zl*u*zl⁻¹)*(zl*v*zl⁻¹):=fun u v=>by group
   rw[zs,zs];refine R_GL.mul_mem ?_ (R_GL.mul_mem ?_ ?_)
   .
    cases c
    . simp[R_GL.one_mem]
    . rw[Az rfl,vm];exact ⟨zR.1,zR.2,rfl⟩
   .
    cases a 0
    . simp[R_GL.one_mem]
    . rw[Az rfl,vk];exact ⟨xR.1,xR.2,rfl⟩
   .
    cases b 0
    . simp[R_GL.one_mem]
    . rw[Az rfl,vl];exact R_GL.mul_mem ⟨xR.1,xR.2,rfl⟩ ⟨yR.1,yR.2,rfl⟩
  have zF:zl∈S.L:=by rw[<-zD];exact ⟨z0,zE⟩
  exact W5 S ze zc B za zf zd zb zl zF rfl
end Section6bKillCases
end GSR
theorem OMA.solution : OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H1 := by
 intro G _ _ _ hRat p hp_prime hpG;suffices h:∀ n:ℕ,∀ (G:Type) [Group G] [Fintype G] [Group.IsSolvable G],Nat.card G=n->GSR.Qw G->∀ p:ℕ,p.Prime->p∣Nat.card G->p=2\/p=3\/p=5 from
  h (Nat.card G) G rfl hRat p hp_prime hpG
 intro n;induction n using Nat.strongRecOn with
 | ind n ih=>
  intro G _ _ _ hGn hRat p hp_prime hpG;by_contra hnot;have hp7:7<=p:=by
   have h2:=hp_prime.two_le;have:p≠2/\p≠3/\p≠5:=by tauto
   have h4:p≠4:=fun h=>by subst h;exact absurd hp_prime (by decide)
   have h6:p≠6:=fun h=>by subst h;exact absurd hp_prime (by decide)
   omega
  haveI:Fact p.Prime:=⟨hp_prime⟩;have hmin:∀ (G':Type) [Group G'] [Fintype G'] [Group.IsSolvable G'],Nat.card G' < Nat.card G->GSR.Qw G'->∀ q:ℕ,q.Prime->q∣Nat.card G'->q=2\/q=3\/q=5:=
   fun G' _ _ _ hlt hRat' q hq hqG'=>ih (Nat.card G') (hGn ▸ hlt) G' rfl hRat' q hq hqG'
  obtain ⟨d,hd_pos,L,hL_solv,hL_not_p,hL_rat,hzL,hL_irred,hL_SF⟩:=
   GSR.WY hp7 hRat hpG hmin
  obtain ⟨N,hN_pos,hNp,ι,⟨S₀⟩⟩:=
   GSR.W1 hp7 hd_pos L hL_solv hL_not_p hL_rat hzL hL_irred hL_SF
  obtain ⟨S,hterm⟩:=GSR.Yd hp7 S₀;obtain ⟨hzR,hES⟩:=GSR.Yj hp7 S hterm;obtain ⟨m,eps,⟨B⟩⟩:=GSR.WJ
   (Nat.card (GSR.O2 S.L)) (GSR.O2 S.L)
   ⟨⟨GSR.Qd S.n p,S.negOne_mem⟩,hzR⟩ rfl hES
  obtain ⟨rfl,hSn,hCR,ι4,hι4,eVec,c₀,hc₀,he_inter,he_B⟩:=
   GSR.Wk hp7 S hzR hES B
  by_cases hp11:11<=p
  . exact GSR.YN hp11 S hzR hES B ι4 hι4 eVec c₀ hc₀ he_inter he_B
  .
   have hp7_eq:p=7:=by
    have h8:p≠8:=fun h=>by subst h;exact absurd hp_prime (by decide)
    have h9:p≠9:=fun h=>by subst h;exact absurd hp_prime (by decide)
    have h10:p≠10:=fun h=>by subst h;exact absurd hp_prime (by decide)
    omega
   subst hp7_eq;by_cases hm3:3<=m
   . exact GSR.YE hm3 S hzR hES B hSn ι4 hι4 eVec c₀ hc₀ he_inter he_B
   .
    have hm12:m=1\/m=2:=by have:=B.hm;omega
    rcases hm12 with rfl | rfl
    . exact GSR.Wm S hzR hES B hSn hCR ι4 hι4 eVec he_inter
    . exact GSR.YU S hzR hES B hSn hCR
