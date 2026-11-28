import OMAReductions.R_Erdos683_erdos_683_variant_erdos_log_R1
import Mathlib

-- Step Erdos683.erdos_683.variant.erdos_log.R1.H1: hypothesis H1 of reduction Erdos683.erdos_683.variant.erdos_log.R1
-- Credit: @ptc-prover-bot
-- Ingham 1937 (primes in (x, x + C x^theta], theta < 2/3). Own work of our agents (explicit formula,
-- zero density, Vinogradov zero-free region, combination). Machine-compressed (dependency closure
-- only, short names, no comments) to fit the size limit.

open AnalyticOnNhd renaming sum_divisor_le → p8
open AntitoneOn renaming sum_le_integral → lx
open ArithmeticFunction renaming moebius → c8, abs_moebius_le_one → gg, LSeries_vonMangoldt_eq_deriv_riemannZeta_div → ka, LSeriesSummable_moebius_iff → mf, vonMangoldt → ph, map_zero → ql
open Chebyshev renaming theta → j9
open Complex renaming abs_im_le_norm → a6, norm_real → ba, norm_le_abs_re_add_abs_im → b6, abs_re_le_norm → cm, norm_conj → d4, exp → d6, norm_cpow_eq_rpow_re_of_pos → e9, continuous_re → f0, norm_natCast → gf, cpow_def_of_ne_zero → gq, norm_deriv_le_of_forall_mem_sphere_norm_le → gu, exp_add → jc
open Complex renaming normSq_apply → jl, normSq_eq_norm_sq → jo, cpow_add → js, summable_one_div_nat_cpow → j7, ofReal_log → j8, exp_eq_one_iff → ke, re → kl, mul_conj' → km, ext → kn, norm_I → kr, norm_exp_ofReal_mul_I → k9, norm_intCast → lf
open Complex renaming ofReal_cpow → lq, conj_ofReal → lr, I → lu, norm_le_of_forall_mem_frontier_norm_le → me, cpow_ne_zero_iff_of_exponent_ne_zero → mm, exp_zero → m1, exp_conj → m2, ofReal_natCast → m7, conj_I → n1, exp_nat_mul → n9, re_le_norm → ot, ofReal_exp → ou
open Complex renaming zero_cpow → o7, ofReal_re → o8, borelCaratheodory_zero → pg, norm_exp → p5, cpow_one → p6, re_tsum → qk, reCLM → rl, mem_reProdIm → r9
open Continuous renaming aestronglyMeasurable → kk
open ContinuousAt renaming continuousWithinAt → ie, mul → p4
open ContinuousOn renaming intervalIntegrable → el, log → p3
open DifferentiableAt renaming differentiableWithinAt → c3, div → ld, fun_sum → mj
open DifferentiableOn renaming diffContOnCl → i2, analyticOnNhd → pe
open DifferentiableWithinAt renaming sub → qr
open ENat renaming recTopCoe → n0
open Equiv renaming Perm → jh
open Filter renaming Eventually → cz, univ_mem → nj
open Filter.Eventually renaming of_forall → bj
open Fin renaming castAdd → i0, natAdd → jg, sum_univ_eq_sum_range → md, addCases → ni
open Finset renaming mem_filter → ah, sum_congr → ai, sum_le_sum → ao, sum_le_sum_of_subset_of_nonneg → aq, mem_Icc → ar, sum_const → a9, mul_sum → bc, range → bk, mem_product → bm, mem_range → bw, mem_coe → b9, card_le_card → cf
open Finset renaming sum_nonneg → cj, card_le_card_of_injOn → ck, mem_image → cr, sum_add_distrib → cu, sum_fiberwise_of_maps_to → cx, Ico_add_one_right_eq_Icc → cy, sum_range_succ → dk, sum_sub_distrib → dn, sum_Ico_eq_sum_range → dq, mem_image_of_mem → dv, sum_comm → d0, sum_product → ep
open Finset renaming sum_div → ew, card_le_mul_card_image → e7, card_range → fa, prod_pow_eq_pow_sum → fp, sum_range_succ' → fq, mem_insert → fv, sum_mul_sum → f8, sum_filter_add_sum_filter_not → gm, sum_mul → g3, mem_Ico → g4, sum_insert → ic, prod_ne_zero_iff → ix
open Finset renaming prod_le_prod → iy, card_product → iz, card_univ → i1, sum_filter → jf, prod_univ_sum → jk, range_subset_range → jn, card_filter → j6, sum_neg_distrib → kc, card_biUnion_le → kd, coe_filter → kj, mem_Ioo → kp, mem_Ioc → kq
open Finset renaming sum_empty → k8, single_le_sum → lb, prod_nonneg → l1, mem_biUnion → l5, prod_const → mi, prod_mul_distrib → my, mem_univ → ng, card_filter_le → nh, sum_singleton → nw, mem_singleton → nx, filter_filter → ny, induction_on → n7
open Finset renaming card_eq_zero → n8, prod_insert → os, prod_congr → o6, sum_eq_sum_Ico_succ_bot → pd, sum_image → py, sum_apply → pz, mem_union → p0, filter_eq_empty_iff → qn, card_image_of_injOn → qo, sum_range_reflect → q4, subset_union_left → q5, Icc → q6
open Finset renaming mem_powersetCard → rk, sum_range_sub' → r0, sum_range_sub → r6, filter_subset → r7, card_union_le → r8, range_eq_Ico → sw, Ioc_eq_empty → s0
open Fintype renaming piFinset → dz, mem_piFinset → gd, card_fin → jr, card_piFinset → kz, prod_ite_eq' → r5
open Function renaming Injective → l0, comp → mx, support → m0, mem_support → nv, uncurry → px
open Int renaming card_Icc → ky, toNat_of_nonneg → ll, fract → ln, toNat_natCast → mh, emod_nonneg → nd, emod_add_mul_ediv → nf, mul_ediv_cancel' → nr, lt_floor_add_one → nt, emod_lt_of_pos → oq, floor_le → pc, eq_zero_of_abs_lt_dvd → qx
open LSeries renaming term → dt, term_of_ne_zero → rj, norm_term_eq → r4
open List renaming ofFn → qi
open MeasureTheory renaming integral_const_mul → ov, setIntegral_const → o5
open MeromorphicOn renaming divisor → bn, divisor_apply → qh
open Metric renaming mem_closedBall → dj
open Multiset renaming prod_X_sub_X_eq_sum_esymm → oe
open Nat renaming cast_nonneg → av, eq_zero_or_pos → c7, pow_le_pow_left → ec, log → ed, ceil_lt_add_one → ef, gcd → et, mul_le_mul_left → fu, le_ceil → f9, pow_le_pow_right → ga, mul_le_mul_right → gb, mul_le_mul → gl, mul_div_cancel' → gp
open Nat renaming le_of_dvd → g1, lt_floor_add_one → g8, cast_sub → il, find → iw, one_le_iff_ne_zero → i8, log_mono_right → ja, floor_le → ju, card_Icc → jv, pos_of_dvd_of_pos → kx, div_le_self → lj, cast_analyticOrderNatAt → lk, one_le_div_iff → lz
open Nat renaming lcm → mc, cast_zero → mw, mem_divisors → mz, lt_succ_iff → nc, factorial_le_pow → nq, zero_le → n5, pow_log_le_self → n6, exists_prime_lt_and_le_two_mul → od, add_sub_cancel → oo, lt_succ_of_le → o3, gcd_dvd_right → o4, cast_mul → pb
open Nat renaming gcd_dvd_left → pv, one_le_pow → qv, add_le_add → qw, le_floor → rv, cast_pow → rx, cast_one → ry, card_Ioc → rz, ceil → s9
open Ne renaming symm → qg
open Pi renaming zero_apply → om, add_apply → pa, sub_apply → rt, neg_apply → ru
open Polynomial renaming roots_multiset_prod_X_sub_C → nk, X → rr
open Prod renaming mk → qf, ext → s7
open Prod.mk renaming injEq → j5
open Real renaming log → aa, exp → af, sqrt → ak, rpow_le_rpow_of_exponent_le → al, norm_eq_abs → au, log_le_log → a5, log_nonneg → bd, exp_add → bs, exp_pos → bx, log_le_sub_one_of_pos → bz, exp_le_exp → b4, one_sub_inv_le_log_of_pos → b5
open Real renaming log_mul → ca, log_pow → cq, add_one_le_exp → cw, rpow_le_rpow_of_nonpos → c1, pi → c2, rpow_add → c6, rpow_def_of_pos → c9, rpow_natCast → da, exp_nat_mul → db, rpow_pos_of_pos → dc, sqrt_nonneg → df, sqrt_le_sqrt → dg
open Real renaming rpow_le_rpow → dh, pi_pos → du, le_log_iff_exp_le → d5, rpow_mul → d7, rpow_nonneg → ei, sin → en, log_pos → eo, rpow_le_one_of_one_le_of_nonpos → er, one_le_rpow → e5, mul_rpow → e6, rpow_one → fi, sqrt_sq → fk
open Real renaming exp_log → fl, cos → fo, sqrt_eq_rpow → ft, mul_self_sqrt → f5, log_two_gt_d9 → f6, exp_one_lt_d9 → f7, sin_pos_of_pos_of_lt_pi → gh, summable_nat_rpow → gr, rpow_inv_natCast_pow → g2, log_div → ik, sqrt_pos → iu, rpow_neg → iv
open Real renaming exp_one_gt_d9 → i9, pi_gt_three → jq, exp_le_one_iff → jt, pi_lt_four → j3, circleAverage → j4, log_exp → kt, le_sqrt_of_sq_le → ku, exp_neg → kv, tsum_le_of_sum_range_le → lh, sq_sqrt → ly, sqrt_mul → mv, log_lt_iff_lt_exp → m6
open Real renaming log_le_rpow_div → np, one_rpow → oi, log_rpow → oj, rpow_neg_one → o2, pi_ne_zero → qd, one_le_exp → qe, zero_rpow → qu, rpow_sub → rg, log_natCast_nonneg → rh, div_rpow → ri, tendsto_log_atTop → rm, neg_one_le_sin → sv
open Set renaming Finite → bt, mem_setOf_eq → eh, uIcc_of_le → gj, Icc → i7, indicator_of_notMem → j2, uIcc → ko, Ioc → mb, indicator → mq, Ioc_subset_Icc_self → mr, indicator_of_mem → nn, InjOn → oh, mem_ofPred_eq → o1
open Set renaming MapsTo → q1, mem_singleton_iff → rq
open Set.Finite renaming mem_toFinset → an, coe_toFinset → rf
open Summable renaming of_nonneg_of_le → d9, tsum_le_tsum → ks, of_norm_bounded → q0
open ZMod renaming intCast_zmod_eq_zero_iff_dvd → fh, natCast_eq_zero_iff → qz
open intervalIntegral renaming integral_const_mul → cv, integral_of_le → ek, norm_integral_le_of_norm_le → fc, integral_mono_on → ff, norm_integral_le_of_norm_le_const → gs, integral_add_adjacent_intervals → gz, integral_congr → ia, integral_comp_neg → oc, integral_div → pk, integral_add → pl
alias ab := mul_le_mul_of_nonneg_left
alias ag := mul_le_mul_of_nonneg_right
alias aj := pow_le_pow_left₀
alias aw := norm_nonneg
alias ax := div_le_div_iff₀
alias ay := div_le_iff₀
alias a4 := div_le_div_of_nonneg_right
alias a7 := abs_of_pos
alias a8 := mul_le_mul
alias bb := div_le_div_of_nonneg_left
alias bf := finsum_mem_eq_finite_toFinset_sum
alias bg := differentiable_riemannZeta₁
alias bh := abs_of_nonneg
alias bl := le_div_iff₀
alias bo := norm_mul
alias bq := le_max_left
alias br := le_trans
alias bu := differentiableAt_id
alias b7 := mul_nonneg
alias b8 := dist_eq_norm
alias cb := sub_ne_zero
alias cd := le_max_right
alias cp := nsmul_eq_mul
alias ct := riemannZeta_ne_zero_of_one_le_re
alias c4 := sq_nonneg
alias c5 := norm_sum_le
alias de := abs_sub_abs_le_abs_sub
alias di := mul_one
alias dm := continuous_const
alias dr := one_div_le_one_div_of_le
alias ds := norm_add_le
alias dw := div_le_one
alias dx := one_le_pow₀
alias dy := congrArg
alias d8 := pow_le_pow_iff_left₀
alias eg := abs_nonneg
alias ej := norm_sub_le
alias ez := continuousOn_const
alias e8 := add_le_add
alias fb := pow_pos
alias fe := div_nonneg
alias fj := lt_of_lt_of_le
alias fm := analyticOrderAt_eq_zero
alias fw := isOpen_compl_singleton
alias fx := smul_eq_mul
alias fy := pow_le_pow_right₀
alias gn := summable_nat_add_iff
alias gv := mul_assoc
alias gw := norm_tsum_le_tsum_norm
alias gx := mul_comm
alias gy := congrFun
alias g5 := abs_of_neg
alias g6 := tendsto_const_nhds
alias g7 := norm_pos_iff
alias g9 := logDeriv_apply
alias ib := integrable_exp_neg_mul_sq
alias ig := le_or_gt
alias ij := add_zero
alias iq := one_mul
alias i3 := sub_self
alias i4 := norm_div
alias i5 := mul_pow
alias i6 := le_of_eq
alias jb := mul_div_cancel_left₀
alias jd := div_eq_mul_one_div
alias je := differentiableAt_riemannZeta
alias ji := mul_pos
alias jj := abs_sub_comm
alias jm := mul_div_assoc
alias jw := norm_zero
alias jx := div_eq_mul_inv
alias jy := zero_add
alias jz := one_div
alias j0 := add_sub_cancel_left
alias j1 := abs_neg
alias kb := intervalIntegrable_const
alias kg := sub_zero
alias kh := mul_one_div_cancel
alias ki := div_mul_eq_mul_div
alias k0 := pow_nonneg
alias k1 := mul_ne_zero
alias k5 := measurableSet_Ioi
alias k6 := le_abs_self
alias k7 := finsum_eq_sum_of_support_subset
alias la := norm_pow
alias lg := le_of_mul_le_mul_left
alias lv := finsum_nonneg
alias l6 := tendsto_natCast_atTop_atTop
alias l7 := pow_ne_zero
alias l8 := div_pow
alias l9 := dist_zero_right
alias ma := continuous_iff_continuousAt
alias mg := riemannZeta_eq_inv_sub_mul
alias ml := div_div_eq_mul_div
alias mn := eq_or_lt_of_le
alias mo := div_pos
alias m3 := mem_ball_zero_iff
alias m4 := isLittleO_log_rpow_atTop
alias m5 := intervalIntegrable_iff_integrableOn_Ioc_of_le
alias m8 := mul_one_div
alias m9 := map_sum
alias na := lt_div_iff₀
alias nb := harmonic_le_one_add_log
alias nm := differentiableAt_const
alias n2 := isOpen_lt
alias n3 := closure_ball
alias n4 := abs_mul
alias oa := sub_nonneg
alias ob := pow_succ
alias og := zeta_eq_tsum_one_div_nat_add_one_cpow
alias ow := sub_eq_zero
alias ox := pow_mul
alias oy := pow_add
alias oz := logDeriv_congr_nhds
alias o0 := analyticOrderAt_mul
alias o9 := tendsto_zero_iff_norm_tendsto_zero
alias pj := tsum_mul_left
alias pn := integral_rpow
alias po := hasDerivAt_id
alias pq := dist_triangle
alias ps := continuous_id
alias p7 := riemannZeta_ne_zero_of_one_lt_re
alias p9 := neg_div
alias qa := mul_div_cancel₀
alias qb := map_mul
alias qc := div_mul_cancel₀
alias qj := LSeries_one_mul_Lseries_moebius
alias qm := one_le_mul_of_one_le_of_one_le
alias qs := norm_sub_norm_le
alias qt := measurable_const
alias qy := hasDerivAt_ofReal_cpow_const
alias q7 := zero_lt_one
alias q8 := slope_def_field
alias q9 := pow_sum_div_card_le_sum_pow
alias ra := norm_prod
alias rb := mul_eq_zero
alias rd := integrableOn_Ioi_rpow_of_lt
alias rn := LSeries_one_eq_riemannZeta
alias ro := sub_eq_add_neg
alias rp := mul_div_assoc'
alias r2 := neg_abs_le
alias r3 := div_eq_iff
alias se := riemannZeta_one_ne_zero
alias sf := one_pow
alias sg := neg_zero
alias sh := mul_lt_mul_of_pos_right
alias si := lt_or_ge
alias sj := logDeriv_prod
alias sm := le_of_forall_pos_le_add
alias sn := integral_complex_ofReal
alias ss := div_neg
alias su := div_le_div₀
alias s3 := tendsto_rpow_neg_atTop
alias s4 := convex_halfSpace_re_gt
alias s5 := analyticOn_riemannZeta
alias tf := logDeriv_mul
alias tg := logDeriv_div
alias th := finsum_mem_coe_finset
alias ti := dslope_of_ne
alias ub := tendsto_nhds_unique
alias uc := one_div_pos
alias ud := mul_add
alias ue := abs_pos

section
namespace bt.au4
open Finset
def sig (k s:ℕ) (x:Fin s->ℤ):Fin k->ℤ:=fun j=>∑ i,x i^(j.val+1)
abbrev tc (s:ℕ) (A:Finset ℤ):Finset (Fin s->ℤ):=dz fun _:Fin s=>A
def J (k s:ℕ) (A:Finset ℤ):ℕ:=
 ((tc s A ×ˢ tc s A).filter fun xy=>sig k s xy.1=sig k s xy.2).card
def Nf (k s:ℕ) (A:Finset ℤ) (h:Fin k->ℤ):ℕ:=((tc s A).filter fun x=>sig k s x=h).card
lemma aia (k s:ℕ) (A:Finset ℤ) (g:(Fin k->ℤ)->ℕ):
  ∑ h∈(tc s A).image (sig k s),Nf k s A h*g h=∑ x∈tc s A,g (sig k s x):=by
 classical
 rw[<- cx (s:=tc s A) (t:=(tc s A).image (sig k s))
  (g:=sig k s) (fun x hx=>dv _ hx)]
 apply ai rfl
 intro h _
 rw[ai rfl (g:=fun _=>g h) (fun x hx=>by rw[(ah.mp hx).2]),
  a9,fx,Nf]
lemma ac1 (k s:ℕ) (A:Finset ℤ) (m:Fin k->ℤ):
  ((tc s A ×ˢ tc s A).filter fun xy=>sig k s xy.1-sig k s xy.2=m).card=
   ∑ x∈tc s A,Nf k s A (sig k s x-m):=by
 classical
 rw[j6,ep]
 apply ai rfl
 intro x _
 rw[Nf,j6]
 apply ai rfl
 intro y _
 congr 1
 apply propext
 constructor
 ·intro h; rw[<- h]; abel
 ·intro h; rw[h]; abel
lemma aq7 (k s:ℕ) (A:Finset ℤ):
  J k s A=∑ h∈(tc s A).image (sig k s),Nf k s A h^2:=by
 have h1:=ac1 k s A 0
 simp only[kg,ow] at h1
 rw[J,h1,<- aia k s A (fun h=>Nf k s A h)]
 apply ai rfl; intro h _; ring
lemma am3 {k s:ℕ} {A:Finset ℤ} {h:Fin k->ℤ} (hh:h∉(tc s A).image (sig k s)):
  Nf k s A h=0:=by
 rw[Nf,n8,qn]
 intro x hx hxh
 exact hh (hxh ▸ dv _ hx)
theorem x5 (k s:ℕ) (A:Finset ℤ) (m:Fin k->ℤ):
  ((tc s A ×ˢ tc s A).filter fun xy=>sig k s xy.1-sig k s xy.2=m).card<=J k s A:=by
 classical
 set H:=(tc s A).image (sig k s) with hH
 rw[ac1,<- aia k s A (fun h=>Nf k s A (h-m)),aq7]
 have adh:∑ h∈H,Nf k s A (h-m)^2<=∑ h∈H,Nf k s A h^2:=by
  have hinj:oh (fun h:Fin k->ℤ=>h-m) H:=fun a _ b _ hab=>by
   simpa using hab
  rw[<- py (f:=fun h=>Nf k s A h^2) (g:=fun h=>h-m) hinj]
  calc ∑ h∈H.image (fun h=>h-m),Nf k s A h^2
    <= ∑ h∈H.image (fun h=>h-m) ∪ H,Nf k s A h^2:=
        Finset.sum_le_sum_of_subset q5
   _ = ∑ h∈H,Nf k s A h^2:=by
       symm
       apply Finset.sum_subset Finset.subset_union_right
       intro h _ hh
       rw[am3 hh]; simp
 have azl:∀ h∈H,2*(Nf k s A h*Nf k s A (h-m))<=
   Nf k s A h^2+Nf k s A (h-m)^2:=by
  intro h _
  nlinarith[c4 ((Nf k s A h:ℤ)-Nf k s A (h-m))]
 have h2:=ao azl
 rw[<- bc,cu] at h2
 rw[<- hH]
 omega
section Newton
variable {F:Type*} [Field F]
theorem ac9 {k:ℕ} (hk:∀ j:ℕ,0<j->j<=k->(j:F)≠0)
  {u v:Fin k->F} (h:∀ j:ℕ,0<j->j<=k->∑ i,u i^j=∑ i,v i^j):
  ∀ j ≤ k,(univ.val.map u).esymm j=(univ.val.map v).esymm j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | _ j ih=>
  intro hj
  rcases c7 j with rfl | hj0
  ·simp[Multiset.esymm]
  have key:∀ w:Fin k->F,(j:F)*(univ.val.map w).esymm j=(-1)^(j+1)*
    ∑ a∈antidiagonal j with a.1<j,
     (-1)^a.1*(univ.val.map w).esymm a.1*∑ i,w i^a.2:=by
   intro w
   have:=dy (MvPolynomial.aeval w) (MvPolynomial.mul_esymm_eq_sum (Fin k) F j)
   simp only[qb,m9,map_pow,map_neg,map_one,map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,MvPolynomial.psum,MvPolynomial.aeval_X] at this
   exact this
  have e:(j:F)*(univ.val.map u).esymm j=(j:F)*(univ.val.map v).esymm j:=by
   rw[key u,key v]
   congr 1
   apply ai rfl
   intro a ha
   rw[ah,Finset.HasAntidiagonal.mem_antidiagonal] at ha
   rw[ih a.1 ha.2 (by omega),h a.2 (by omega) (by omega)]
  exact mul_left_cancel₀ (hk j hj0 hj) e
theorem abb {k:ℕ} (hk:∀ j:ℕ,0<j->j<=k->(j:F)≠0)
  {u v:Fin k->F} (h:∀ j:ℕ,0<j->j<=k->∑ i,u i^j=∑ i,v i^j):
  univ.val.map u=univ.val.map v:=by
 have azm:((univ.val.map u).map fun t=>rr-Polynomial.C t).prod=
   ((univ.val.map v).map fun t=>rr-Polynomial.C t).prod:=by
  rw[oe,oe]
  simp only[Multiset.card_map,Finset.card_val,i1,jr]
  apply ai rfl
  intro j hj
  rw[ac9 hk h j (by simpa [nc] using hj)]
 have:=dy Polynomial.roots azm
 rwa[nk,nk] at this
theorem v3 {k:ℕ} (hk:∀ j:ℕ,0<j->j<=k->(j:F)≠0)
  (U:Finset (Fin k->F)) (c:ℕ->F)
  (hU:∀ u∈U,∀ j:ℕ,0<j->j<=k->∑ i,u i^j=c j):U.card<=k.factorial:=by
 classical
 rcases U.eq_empty_or_nonempty with rfl | ⟨am4,azn⟩
 ·simp
 have uj:U.image qi ⊆ (qi am4).permutations.toFinset:=by
  intro l hl
  rw[cr] at hl
  obtain ⟨u,hu,rfl⟩:=hl
  rw[List.mem_toFinset,List.mem_permutations,<- Multiset.coe_eq_coe,<- Fin.univ_val_map,
   <- Fin.univ_val_map]
  exact abb hk
   (fun j hj0 hj=>(hU u hu j hj0 hj).trans (hU am4 azn j hj0 hj).symm)
 calc U.card=(U.image qi).card:=
       (Finset.card_image_of_injective _ List.ofFn_injective).symm
  _<=(qi am4).permutations.toFinset.card:=cf uj
  _<=(qi am4).permutations.length:=List.toFinset_card_le _
  _=k.factorial:=by rw[List.length_permutations,List.length_ofFn]
end Newton
lemma afx (a b:ℤ) (j:ℕ):b^2∣(a+b)^j-a^j-j*a^(j-1)*b:=by
 obtain ⟨q,hq⟩:=Polynomial.binomExpansion (rr^j:Polynomial ℤ) a b
 simp only[Polynomial.eval_pow,Polynomial.eval_X,Polynomial.derivative_X_pow,
  Polynomial.eval_mul,Polynomial.eval_C] at hq
 exact ⟨q,by rw[hq]; ring⟩
theorem ali {p:ℕ} (hp:p.Prime) {k:ℕ} (hpk:k<p) {m:ℕ} (hm:1<=m)
  {u w:Fin k->ℤ} (aat:∀ i j,i≠j->¬ (p:ℤ)∣u i-u j)
  (hσ:∀ j:ℕ,0<j->j<=k->
   (p:ℤ)^(m+1)∣∑ i,(u i+(p:ℤ)^m*w i)^j-∑ i,u i^j):
  ∀ i,(p:ℤ)∣w i:=by
 have:=Fact.mk hp
 have h1:∀ j:ℕ,0<j->j<=k->(p:ℤ)∣∑ i,(j:ℤ)*u i^(j-1)*w i:=by
  intro j hj0 hjk
  have hd:=hσ j hj0 hjk
  have zr:(p:ℤ)^(m+1)∣∑ i,((u i+(p:ℤ)^m*w i)^j-u i^j-
    j*u i^(j-1)*((p:ℤ)^m*w i)):=by
   apply Finset.dvd_sum
   intro i _
   refine dvd_trans ?_ (afx (u i) ((p:ℤ)^m*w i) j)
   rw[i5,<- ox]
   exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
  have hsum:∑ i,(u i+(p:ℤ)^m*w i)^j-∑ i,u i^j=
    ∑ i,((u i+(p:ℤ)^m*w i)^j-u i^j-j*u i^(j-1)*((p:ℤ)^m*w i))+
    (p:ℤ)^m*∑ i,(j:ℤ)*u i^(j-1)*w i:=by
   rw[bc,<- dn,<- cu]
   apply ai rfl
   intro i _
   ring
  rw[hsum] at hd
  have h3:=(dvd_add_right zr).mp hd
  rw[ob] at h3
  exact (mul_dvd_mul_iff_left (l7 m (by exact_mod_cast hp.ne_zero))).mp h3
 have hinj:l0 fun i=>(u i:ZMod p):=by
  intro i j hij
  by_contra te
  apply aat i j te
  rw[<- fh]
  push_cast
  exact ow.mpr hij
 have h2:∀ e:Fin k,∑ i,(u i:ZMod p)^(e:ℕ)*(w i:ZMod p)=0:=by
  intro e
  have:=h1 (e+1) (by omega) (by omega)
  rw[<- fh] at this
  push_cast at this
  try simp only[oo] at this
  have te:((e:ℕ)+1:ZMod p)≠0:=by
   have h5:(((e:ℕ)+1:ℕ):ZMod p)≠0:=by
    rw[Ne,qz]
    intro aq8
    have:=g1 (by omega) aq8
    omega
   exact_mod_cast h5
  simp_rw[gv] at this
  rw[<- bc] at this
  exact (rb.mp this).resolve_left te
 have a3f:(Matrix.vandermonde fun i=>(u i:ZMod p)).transpose.det≠0:=by
  rw[Matrix.det_transpose,Matrix.det_vandermonde]
  apply ix.mpr
  intro i _
  apply ix.mpr
  intro j hj
  exact cb.mpr (fun h=>(ne_of_gt (Finset.mem_Ioi.mp hj)) (hinj h))
 have hmv:Matrix.mulVec (Matrix.vandermonde fun i=>(u i:ZMod p)).transpose
   (fun i=>(w i:ZMod p))=0:=by
  ext e
  simp only[Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.vandermonde_apply,
   om]
  exact h2 e
 have hz:=Matrix.eq_zero_of_mulVec_eq_zero a3f hmv
 intro i
 have hi:=gy hz i
 simp only[om] at hi
 rwa[fh] at hi
lemma afy (k:ℕ):∑ j:Fin k,(k-1-j.val)=k*(k-1)/2:=by
 rw[md (fun j=>k-1-j) k,q4 (fun j=>j) k,
  Finset.sum_range_id]
theorem ajj {p:ℕ} (hp:p.Prime) {k:ℕ} (hpk:k<p) (I:Finset ℤ)
  (hI:∀ a∈I,∀ b∈I,(p:ℤ)^k∣a-b->a=b) (c:Fin k->ℤ):
  ((tc k I).filter fun u=>(∀ i j,i≠j->¬ (p:ℤ)∣u i-u j)∧
    ∀ j:Fin k,(p:ℤ)^(j.val+1)∣sig k k u j-c j).card<=
   k.factorial*p^(k*(k-1)/2):=by
 classical
 have:=Fact.mk hp
 have zc:(0:ℤ)<p:=by exact_mod_cast hp.pos
 set U := (tc k I).filter fun u=>(∀ i j,i≠j->¬ (p:ℤ)∣u i-u j)∧
       ∀ j:Fin k,(p:ℤ)^(j.val+1)∣sig k k u j-c j with hU
 set e:(Fin k->ℤ)->(Fin k->ℤ):=fun u j=>
  ((sig k k u j-c j)/(p:ℤ)^(j.val+1)) % (p:ℤ)^(k-1-j.val) with he
 set box:=dz fun j:Fin k=>Finset.Ico (0:ℤ) ((p:ℤ)^(k-1-j.val))
  with ae7
 have ae8:U.image e ⊆ box:=by
  intro b hb
  rw[cr] at hb
  obtain ⟨u,_,rfl⟩:=hb
  rw[ae7,gd]
  intro j
  rw[g4]
  have hq:(0:ℤ)<(p:ℤ)^(k-1-j.val):=fb zc _
  exact ⟨nd _ hq.ne',oq _ hq⟩
 have azo:box.card=p^(k*(k-1)/2):=by
  rw[ae7,kz]
  simp only[Int.card_Ico,kg]
  rw[<- afy,<- fp]
  apply o6 rfl
  intro j _
  rw[<- rx,mh]
 have yu:∀ b∈U.image e,(U.filter fun u=>e u=b).card<=k.factorial:=by
  intro b _
  set Fb:=U.filter fun u=>e u=b with hFb
  set r:(Fin k->ℤ)->(Fin k->ZMod p):=fun u i=>(u i:ZMod p) with hr
  have azp:∀ u∈Fb,∀ v∈Fb,∀ j:Fin k,
    (p:ℤ)^k∣sig k k v j-sig k k u j:=by
   intro u hu v hv j
   rw[hFb,ah] at hu hv
   have hdu:=(ah.mp hu.1).2.2 j
   have hdv:=(ah.mp hv.1).2.2 j
   have am5:((sig k k u j-c j)/(p:ℤ)^(j.val+1)) % (p:ℤ)^(k-1-j.val)=
     ((sig k k v j-c j)/(p:ℤ)^(j.val+1)) % (p:ℤ)^(k-1-j.val):=by
    have h1:=gy hu.2 j
    have h2:=gy hv.2 j
    simp only[he] at h1 h2
    rw[h1,h2]
   have hd:=Int.ModEq.dvd am5
   have hk:(p:ℤ)^k=(p:ℤ)^(j.val+1)*(p:ℤ)^(k-1-j.val):=by
    rw[<- oy]; congr 1; omega
   rw[hk]
   have e1:=nr hdu
   have e2:=nr hdv
   have:sig k k v j-sig k k u j=(p:ℤ)^(j.val+1)*
     ((sig k k v j-c j)/(p:ℤ)^(j.val+1)-
      (sig k k u j-c j)/(p:ℤ)^(j.val+1)):=by
    rw[mul_sub,e1,e2]; ring
   rw[this]
   exact mul_dvd_mul_left _ hd
  have au6:oh r Fb:=by
   intro u hu v hv a3g
   have huU:u∈U:=(ah.mp hu).1
   have aat:∀ i j,i≠j->¬ (p:ℤ)∣u i-u j:=
    (ah.mp huU).2.1
   have azq:∀ i,(p:ℤ)∣v i-u i:=by
    intro i
    have:=gy a3g i
    simp only[hr] at this
    rw[<- fh]
    push_cast
    rw[this,i3]
   have a3h:∀ m:ℕ,1<=m->m<=k->∀ i,(p:ℤ)^m∣v i-u i:=by
    intro m hm1
    induction m,hm1 using Nat.le_induction with
    | base=>intro _; simpa using azq
    | succ m hm ih=>
     intro hmk
     have ih':=ih (by omega)
     set w:Fin k->ℤ:=fun i=>(v i-u i)/(p:ℤ)^m with hw
     have hvw:∀ i,v i=u i+(p:ℤ)^m*w i:=by
      intro i
      simp only[hw]
      rw[nr (ih' i)]; ring
     have hσ:∀ j:ℕ,0<j->j<=k->
       (p:ℤ)^(m+1)∣∑ i,(u i+(p:ℤ)^m*w i)^j-∑ i,u i^j:=by
      intro j hj0 hjk
      have h:=azp u hu v hv ⟨j-1,by omega⟩
      simp only[sig] at h
      rw[show j-1+1=j by omega] at h
      simp_rw[<- hvw]
      exact dvd_trans (pow_dvd_pow _ hmk) h
     have hpw:=ali hp hpk (by omega) aat hσ
     intro i
     rw[hvw i,j0,ob]
     exact mul_dvd_mul_left _ (hpw i)
   funext i
   rcases c7 k with hk0 | hk0
   ·subst hk0; exact Fin.elim0 i
   have hk:=a3h k hk0 le_rfl i
   have hui:u i∈I:=gd.mp (ah.mp huU).1 i
   have hvU:v∈U:=(ah.mp hv).1
   have hvi:v i∈I:=gd.mp (ah.mp hvU).1 i
   exact (hI _ hvi _ hui hk).symm
  rw[<- qo au6]
  set c':ℕ->ZMod p:=fun j=>if h:j-1<k then (c ⟨j-1,h⟩:ZMod p) else 0 with hc'
  apply v3 (F:=ZMod p) _ _ c'
  ·intro v hv j hj0 hjk
   rw[cr] at hv
   obtain ⟨u,hu,rfl⟩:=hv
   have huU:u∈U:=(ah.mp hu).1
   have hd:=(ah.mp huU).2.2 ⟨j-1,by omega⟩
   have hd1:(p:ℤ)∣sig k k u ⟨j-1,by omega⟩-c ⟨j-1,by omega⟩:=
    dvd_trans (dvd_pow_self _ (by omega)) hd
   rw[<- fh,Int.cast_sub,ow] at hd1
   simp only[sig] at hd1
   rw[show j-1+1=j by omega] at hd1
   push_cast at hd1
   simp only[hr,hc',dif_pos (show j-1<k by omega)]
   exact hd1
  ·intro j hj0 hjk
   rw[Ne,qz]
   intro aq8
   have:=g1 hj0 aq8
   omega
 calc U.card<=k.factorial*(U.image e).card:=e7 U _ yu
  _<=k.factorial*box.card:=fu _ (cf ae8)
  _=k.factorial*p^(k*(k-1)/2):=by rw[azo]
lemma afz {s:ℕ} (x:Fin s->ℤ) (c:ℤ) (j:ℕ):
  ∑ i,(x i+c)^j=∑ l∈range (j+1),(∑ i,x i^l)*c^(j-l)*(j.choose l):=by
 simp_rw[add_pow,g3]
 rw[d0]
lemma aiv {s k:ℕ} {x y:Fin s->ℤ}
  (h:∀ l:ℕ,0<l->l<=k->∑ i,x i^l=∑ i,y i^l) (c:ℤ):
  ∀ j:ℕ,j<=k->∑ i,(x i+c)^j=∑ i,(y i+c)^j:=by
 intro j hj
 rw[afz,afz]
 apply ai rfl
 intro l hl
 rw[bw] at hl
 rcases c7 l with rfl | hl0
 ·simp
 ·rw[h l hl0 (by omega)]
theorem zi {k s:ℕ} (x y:Fin s->ℤ) (c:ℤ):
  sig k s (fun i=>x i+c)=sig k s (fun i=>y i+c)↔sig k s x=sig k s y:=by
 have key:∀ (x y:Fin s->ℤ) (c:ℤ),sig k s x=sig k s y->
   sig k s (fun i=>x i+c)=sig k s (fun i=>y i+c):=by
  intro x y c tv
  funext j
  have h:∀ l:ℕ,0<l->l<=k->∑ i,x i^l=∑ i,y i^l:=by
   intro l hl0 hlk
   have:=gy tv ⟨l-1,by omega⟩
   simp only[sig] at this
   rwa[show l-1+1=l by omega] at this
  exact aiv h c (j.val+1) j.isLt
 constructor
 ·intro hc
  have:=key _ _ (-c) hc
  simpa using this
 ·exact key x y c
section Fourier
open Complex
def phi (k:ℕ) (x:ℤ):Fin k->ℤ:=fun j=>x^(j.val+1)
lemma abn (k s:ℕ) (x:Fin s->ℤ):sig k s x=∑ i,phi k (x i):=by
 funext j
 simp[sig,phi,pz]
noncomputable def ch (M:ℕ) {k:ℕ} (a:Fin k->ℕ) (n:Fin k->ℤ):ℂ:=
 d6 (2*c2*I*(((∑ j,(a j:ℤ)*n j:ℤ):ℂ)/M))
lemma af0 (M:ℕ) {k:ℕ} (a:Fin k->ℕ) (n n':Fin k->ℤ):
  ch M a (n+n')=ch M a n*ch M a n':=by
 unfold ch
 rw[<- jc]
 congr 1
 simp only[pa,ud,cu]
 push_cast
 ring
lemma auc (M:ℕ) {k:ℕ} (a:Fin k->ℕ):ch M a 0=1:=by
 simp[ch]
lemma au8 (M:ℕ) {k:ℕ} (a:Fin k->ℕ) (n:Fin k->ℤ):
  ch M a (-n)=(starRingEnd ℂ) (ch M a n):=by
 unfold ch
 rw[<- m2]
 congr 1
 simp only[ru,mul_neg,kc,qb,map_div₀,map_natCast,
  map_intCast,lr,n1,map_ofNat]
 push_cast
 ring
lemma au9 (M:ℕ) {k:ℕ} (a:Fin k->ℕ) {ι:Type*} (t:Finset ι) (v:ι->Fin k->ℤ):
  ch M a (∑ i∈t,v i)=∏ i∈t,ch M a (v i):=by
 classical
 refine n7 t ?_ ?_
 ·simp[auc]
 ·intro i t hi ih
  rw[ic hi,os hi,af0,ih]
lemma alj (M:ℕ) (hM:0<M) (m:ℤ):
  ∑ b∈range M,d6 (2*c2*I*((((b:ℤ)*m:ℤ):ℂ)/M))=
   if (M:ℤ)∣m then (M:ℂ) else 0:=by
 have hM':(M:ℂ)≠0:=by exact_mod_cast hM.ne'
 obtain ⟨z,hz⟩:∃ z,z=d6 (2*c2*I*((m:ℂ)/M)):=⟨_,rfl⟩
 have hpow:∀ b:ℕ,d6 (2*c2*I*((((b:ℤ)*m:ℤ):ℂ)/M))=z^b:=by
  intro b
  rw[hz,<- n9]
  congr 1
  push_cast
  ring
 simp_rw[hpow]
 have hpi:(2*c2*I:ℂ)≠0:=by simp[qd,Complex.I_ne_zero]
 split_ifs with hd
 ·obtain ⟨t,rfl⟩:=hd
  have:z=1:=by
   rw[hz,ke]
   refine ⟨t, ?_⟩
   push_cast
   rw[jb _ hM']
   ring
  simp[this]
 ·have yp:z≠1:=by
   intro h1
   rw[hz,ke] at h1
   obtain ⟨t,ht⟩:=h1
   apply hd
   refine ⟨t, ?_⟩
   have h3:(2*c2*I)*((m:ℂ)/M)=(2*c2*I)*t:=by rw[ht]; ring
   have h4:=mul_left_cancel₀ hpi h3
   rw[r3 hM'] at h4
   have h5:((m:ℤ):ℂ)=(((M:ℤ)*t:ℤ):ℂ):=by rw[h4]; push_cast; ring
   exact_mod_cast h5
  have hzM:z^M=1:=by
   rw[hz,<- n9,ke]
   refine ⟨m, ?_⟩
   rw[gx,gv,qc _ hM']
   ring
  rw[geom_sum_eq yp,hzM,i3,zero_div]
lemma aud (M:ℕ) (hM:0<M) {k:ℕ} (n:Fin k->ℤ):
  ∑ a∈dz (fun _:Fin k=>range M),ch M a n=
   if ∀ j,(M:ℤ)∣n j then (M:ℂ)^k else 0:=by
 have ai7:∀ a:Fin k->ℕ,ch M a n=
   ∏ j,d6 (2*c2*I*(((((a j:ℕ):ℤ)*n j:ℤ):ℂ)/M)):=by
  intro a
  unfold ch
  rw[<- Complex.exp_sum]
  congr 1
  push_cast
  rw[ew,bc]
 simp_rw[ai7]
 rw[<- jk (fun _:Fin k=>range M)
  (fun j b=>d6 (2*c2*I*(((((b:ℕ):ℤ)*n j:ℤ):ℂ)/M)))]
 simp_rw[alj M hM]
 rw[Fintype.prod_ite_zero]
 split_ifs <;> simp
def Tc {β:Type*} (k s:ℕ) (U:Finset β) (g:β->Fin k->ℤ) (B:Finset ℤ):ℕ:=
 (((U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B)).filter fun q=>
  g q.1.1+sig k s q.2.1=g q.1.2+sig k s q.2.2).card
noncomputable def Fs (M:ℕ) {k:ℕ} {β:Type*} (U:Finset β) (g:β->Fin k->ℤ)
  (a:Fin k->ℕ):ℂ:=
 ∑ u∈U,ch M a (g u)
noncomputable def fs (M k:ℕ) (B:Finset ℤ) (a:Fin k->ℕ):ℂ:=∑ x∈B,ch M a (phi k x)
lemma am6 (M k s:ℕ) (B:Finset ℤ) (a:Fin k->ℕ):
  ∑ x∈tc s B,ch M a (sig k s x)=fs M k B a^s:=by
 simp_rw[abn,au9]
 rw[fs,<- Fin.prod_const,jk]
lemma zs {α:Type*} (t:Finset α) (f:α->ℂ):
  ∑ q∈t ×ˢ t,f q.1*(starRingEnd ℂ) (f q.2)=
   (∑ x∈t,f x)*(starRingEnd ℂ) (∑ x∈t,f x):=by
 rw[ep,m9,f8]
lemma ahe (M:ℕ) (hM:0<M) {β:Type*} (k s:ℕ) (U:Finset β)
  (g:β->Fin k->ℤ) (B:Finset ℤ)
  (hb:∀ q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B),∀ j,
   |(g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j|<M):
  (Tc k s U g B:ℂ)*(M:ℂ)^k=
   ∑ a∈dz (fun _:Fin k=>range M),
    Fs M U g a*(starRingEnd ℂ) (Fs M U g a)*
     (fs M k B a^s*(starRingEnd ℂ) (fs M k B a^s)):=by
 classical
 have h1:(Tc k s U g B:ℂ)*(M:ℂ)^k=
   ∑ q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B),∑ a∈dz (fun _:Fin k=>range M),
    ch M a (g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)):=by
  rw[Tc,j6]
  push_cast
  rw[g3]
  apply ai rfl
  intro q hq
  rw[aud M hM]
  have avb:(∀ j,(M:ℤ)∣(g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j)↔
    g q.1.1+sig k s q.2.1=g q.1.2+sig k s q.2.2:=by
   constructor
   ·intro h
    rw[<- ow]
    funext j
    exact qx (h j) (hb q hq j)
   ·intro h j
    rw[h,i3]
    exact dvd_zero _
  by_cases h:g q.1.1+sig k s q.2.1=g q.1.2+sig k s q.2.2
  ·rw[if_pos h,if_pos (avb.mpr h),iq]
  ·rw[if_neg h,if_neg (mt avb.mp h),zero_mul]
 rw[h1,d0]
 apply ai rfl
 intro a _
 have hD:∀ q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B),
   ch M a (g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2))=
    (ch M a (g q.1.1)*(starRingEnd ℂ) (ch M a (g q.1.2)))*
     (ch M a (sig k s q.2.1)*(starRingEnd ℂ) (ch M a (sig k s q.2.2))):=by
  intro q _
  rw[ro,af0,af0,au8,af0,qb]
  ring
 rw[ai rfl hD,ep]
 simp only[]
 rw[<- f8,
  zs U (fun u=>ch M a (g u)),
  zs (tc s B) (fun x=>ch M a (sig k s x)),am6,Fs]
lemma yq (M:ℕ) (hM:0<M) {β:Type*} (k s:ℕ) (U:Finset β)
  (g:β->Fin k->ℤ) (B:Finset ℤ)
  (hb:∀ q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B),∀ j,
   |(g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j|<M):
  (Tc k s U g B:ℝ)*(M:ℝ)^k=
   ∑ a∈dz (fun _:Fin k=>range M),
    ‖Fs M U g a‖^2*‖fs M k B a‖^(2*s):=by
 have h:=ahe M hM k s U g B hb
 simp_rw[km,la] at h
 apply Complex.ofReal_injective
 push_cast
 rw[h]
 apply ai rfl
 intro a _
 push_cast
 ring
theorem ajk {β:Type*} (k s:ℕ) (hs:1<=s) (U:Finset β) (g:β->Fin k->ℤ)
  (B:Finset ℤ) (p:ℕ) (hp:0<p) (cls:ℤ->ℕ) (aq9:∀ x∈B,cls x<p):
  Tc k s U g B<=p^(2*s-1)*∑ r∈range p,Tc k s U g (B.filter fun x=>cls x=r):=by
 classical
 obtain ⟨M,af1⟩:∃ M:ℕ,M=(∑ q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B),
   ∑ j,((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs)+1:=⟨_,rfl⟩
 have hM:0<M:=by rw[af1]; exact Nat.succ_pos _
 have hbB:∀ B' ⊆ B,∀ q∈(U ×ˢ U) ×ˢ (tc s B' ×ˢ tc s B'),∀ j,
   |(g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j|<M:=by
  intro B' hB' q hq j
  have hqQ:q∈(U ×ˢ U) ×ˢ (tc s B ×ˢ tc s B):=by
   simp only[bm,gd] at hq ⊢
   exact ⟨hq.1,fun i=>hB' (hq.2.1 i),fun i=>hB' (hq.2.2 i)⟩
  have h1:((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs<=
    ∑ j,((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs:=
   lb
    (f:=fun j=>((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs)
    (fun _ _=>n5 _) (ng j)
  have h2:=lb
   (f:=fun q:(β × β) × ((Fin s->ℤ) × (Fin s->ℤ))=>
    ∑ j,((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs)
   (fun _ _=>n5 _) hqQ
  try simp only at h2
  rw[Int.abs_eq_natAbs]
  have:((g q.1.1+sig k s q.2.1-(g q.1.2+sig k s q.2.2)) j).natAbs<M:=by omega
  exact_mod_cast this
 have hid:=yq M hM k s U g B (hbB B (subset_refl _))
 have a3i:∀ r∈range p,(Tc k s U g (B.filter fun x=>cls x=r):ℝ)*(M:ℝ)^k=
   ∑ a∈dz (fun _:Fin k=>range M),
    ‖Fs M U g a‖^2*‖fs M k (B.filter fun x=>cls x=r) a‖^(2*s):=
  fun r _=>yq M hM k s U g _ (hbB _ (r7 _ _))
 have x6:(0:ℝ)<(p:ℝ)^(2*s-1):=fb (by exact_mod_cast hp) _
 have wu:∀ a:Fin k->ℕ,‖fs M k B a‖^(2*s)<=
   (p:ℝ)^(2*s-1)*∑ r∈range p,‖fs M k (B.filter fun x=>cls x=r) a‖^(2*s):=by
  intro a
  have u8:fs M k B a=∑ r∈range p,fs M k (B.filter fun x=>cls x=r) a:=by
   unfold fs
   exact (cx (g:=cls)
    (fun x hx=>bw.mpr (aq9 x hx)) _).symm
  have am7:‖fs M k B a‖<=∑ r∈range p,‖fs M k (B.filter fun x=>cls x=r) a‖:=by
   rw[u8]; exact c5 _ _
  have hj:=q9 (s:=range p)
   (f:=fun r=>‖fs M k (B.filter fun x=>cls x=r) a‖) (fun _ _=>aw _) (2*s-1)
  rw[fa,show 2*s-1+1=2*s by omega,
   ay x6] at hj
  calc ‖fs M k B a‖^(2*s)
    <= (∑ r∈range p,‖fs M k (B.filter fun x=>cls x=r) a‖)^(2*s):=
        aj (aw _) am7 _
   _<=_:=by linarith[hj]
 have hMk:(0:ℝ)<(M:ℝ)^k:=fb (by exact_mod_cast hM) _
 have key:(Tc k s U g B:ℝ)*(M:ℝ)^k<=
   ((p^(2*s-1)*∑ r∈range p,Tc k s U g (B.filter fun x=>cls x=r):ℕ):ℝ)*
    (M:ℝ)^k:=by
  rw[hid]
  calc ∑ a∈dz (fun _:Fin k=>range M),‖Fs M U g a‖^2*‖fs M k B a‖^(2*s)
    ≤ ∑ a∈dz (fun _:Fin k=>range M),‖Fs M U g a‖^2*
        ((p:ℝ)^(2*s-1)*
         ∑ r∈range p,‖fs M k (B.filter fun x=>cls x=r) a‖^(2*s)):=
        ao (fun a _=>ab (wu a) (by positivity))
   _ = ∑ a∈dz (fun _:Fin k=>range M),∑ r∈range p,(p:ℝ)^(2*s-1)*
         (‖Fs M U g a‖^2*‖fs M k (B.filter fun x=>cls x=r) a‖^(2*s)):=by
       apply ai rfl
       intro a _
       rw[bc,bc]
       apply ai rfl
       intro r _
       ring
   _ = ∑ r∈range p,(p:ℝ)^(2*s-1)*∑ a∈dz (fun _:Fin k=>range M),
         ‖Fs M U g a‖^2*‖fs M k (B.filter fun x=>cls x=r) a‖^(2*s):=by
       rw[d0]
       apply ai rfl
       intro r _
       rw[bc]
   _ = ∑ r∈range p,(p:ℝ)^(2*s-1)*
         ((Tc k s U g (B.filter fun x=>cls x=r):ℝ)*(M:ℝ)^k):=by
       apply ai rfl
       intro r hr
       rw[a3i r hr]
   _ = ((p^(2*s-1)*∑ r∈range p,Tc k s U g (B.filter fun x=>cls x=r):ℕ):ℝ)*
         (M:ℝ)^k:=by
       push_cast
       rw[bc,g3]
       apply ai rfl
       intro r _
       ring
 have:=le_of_mul_le_mul_right key hMk
 exact_mod_cast this
end Fourier
lemma td {s:ℕ} {A:Finset ℤ} {x:Fin s->ℤ}:x∈tc s A↔∀ i,x i∈A:=
 gd
lemma ajl {s:ℕ} {A B:Finset ℤ} (h:A ⊆ B):tc s A ⊆ tc s B:=
 fun _ hx=>td.mpr fun i=>h (td.mp hx i)
theorem avc (k s:ℕ) {A B:Finset ℤ} (h:A ⊆ B):J k s A<=J k s B:=by
 unfold J
 apply cf
 apply Finset.filter_subset_filter
 exact Finset.product_subset_product (ajl h) (ajl h)
theorem aue (k s:ℕ) (A:Finset ℤ) (c:ℤ):J k s (A.image (·+c))=J k s A:=by
 classical
 unfold J
 symm
 apply Finset.card_bij (fun xy _=>((fun i=>xy.1 i+c),(fun i=>xy.2 i+c)))
 ·intro xy tv
  rw[ah,bm] at tv ⊢
  refine ⟨⟨td.mpr fun i=>dv _ (td.mp tv.1.1 i),
   td.mpr fun i=>dv _ (td.mp tv.1.2 i)⟩, ?_⟩
  exact (zi _ _ c).mpr tv.2
 ·intro a _ b _ hab
  simp only[j5] at hab
  ext i
  ·have:=gy hab.1 i; simpa using this
  ·have:=gy hab.2 i; simpa using this
 ·intro xy tv
  rw[ah,bm] at tv
  have uj:∀ z∈tc s (A.image (·+c)),∀ i,z i-c∈A:=by
   intro z hz i
   obtain ⟨a,ha,h⟩:=cr.mp (td.mp hz i)
   rw[<- h]; simpa using ha
  refine ⟨((fun i=>xy.1 i-c),(fun i=>xy.2 i-c)), ?_, ?_⟩
  ·rw[ah,bm]
   refine ⟨⟨td.mpr (uj _ tv.1.1),td.mpr (uj _ tv.1.2)⟩, ?_⟩
   rw[<- zi _ _ c]
   simpa using tv.2
  ·ext i <;> simp
theorem alk (k s:ℕ) (a Q:ℤ):J k s (Icc a (a+Q-1))=J k s (Icc 1 Q):=by
 rw[show Icc a (a+Q-1)=(Icc (1:ℤ) Q).image (·+(a-1)) by
  rw[Finset.image_add_right_Icc]; congr 1 <;> ring,aue]
theorem adk (k s:ℕ) {B:Finset ℤ} {a Q:ℤ} (h:B ⊆ Icc a (a+Q-1)):
  J k s B<=J k s (Icc 1 Q):=
 (avc k s h).trans (alk k s a Q).le
lemma aiw (k:ℕ) {n:ℕ} (x:Fin n->ℤ) (π:jh (Fin n)):
  sig k n (x∘π)=sig k n x:=by
 funext j
 simp only[sig,mx]
 exact Equiv.sum_comp π (fun i=>x i^(j.val+1))
lemma adl {k s:ℕ} (ι:Fin k->Fin (k+s)) (hι:l0 ι):
  ∃ π:jh (Fin (k+s)),∀ j:Fin k,π (i0 s j)=ι j:=by
 classical
 let e1:{x:Fin (k+s) // x.val<k} ≃ Fin k:=
  {toFun:=fun x=>⟨x.1.val,x.2⟩
   invFun:=fun j=>⟨i0 s j,by simp⟩
   left_inv:=by intro x; ext; simp
   right_inv:=by intro j; ext; simp }
 let e2:Fin k ≃ {x:Fin (k+s) // x∈Set.range ι}:=Equiv.ofInjective ι hι
 let e:=e1.trans e2
 refine ⟨e.extendSubtype,fun j=>?_⟩
 rw[Equiv.extendSubtype_apply_of_mem e _ (by simp)]
 simp[e,e1,e2]
def vo (p k s:ℕ) (x:Fin (k+s)->ℤ):Prop:=
 ∀ i j:Fin k,i≠j->¬ (p:ℤ)∣x (i0 s i)-x (i0 s j)
lemma xx {p k s:ℕ} (x:Fin (k+s)->ℤ)
  (h:k<=(univ.image fun i=>x i % p).card):
  ∃ π:jh (Fin (k+s)),vo p k s (x∘π):=by
 classical
 obtain ⟨R,hR,hRc⟩:=Finset.exists_subset_card_eq h
 let eR:Fin k ≃ R:=(R.equivFin.trans (finCongr hRc)).symm
 have azr:∀ j:Fin k,∃ i,x i % p=(eR j:ℤ):=by
  intro j
  have:=hR (eR j).2
  rw[cr] at this
  obtain ⟨i,_,hi⟩:=this
  exact ⟨i,hi⟩
 choose ι hι using azr
 have hinj:l0 ι:=by
  intro a b hab
  have:(eR a:ℤ)=eR b:=by rw[<- hι a,<- hι b,hab]
  exact eR.injective (Subtype.ext this)
 obtain ⟨π,hπ⟩:=adl ι hinj
 refine ⟨π,fun a b hab hd=>hab ?_⟩
 simp only[mx,hπ] at hd
 have am5:x (ι a) % p=x (ι b) % p:=by
  have:=(Int.modEq_iff_dvd.mpr hd)
  exact this.symm
 rw[hι a,hι b] at am5
 exact eR.injective (Subtype.ext am5)
lemma aix (P p:ℕ) (hp:0<p) (r:ℤ):
  ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)=r).card<=P/p+1:=by
 have x6:(0:ℤ)<p:=by exact_mod_cast hp
 have ahf:∀ a∈(Icc (1:ℤ) P).filter (fun a:ℤ=>a % (p:ℤ)=r),a/p∈Icc (0:ℤ) ((P/p:ℕ)):=by
  intro a ha
  rw[ah,ar] at ha
  rw[ar]
  refine ⟨Int.ediv_nonneg (by linarith) x6.le, ?_⟩
  push_cast
  exact Int.ediv_le_ediv x6 ha.1.2
 have hinj:oh (fun a:ℤ=>a/p) ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)=r):=by
  intro a ha b hb hab
  rw[b9,ah] at ha hb
  have e1:=nf a p
  have e2:=nf b p
  simp only at hab
  rw[hab,ha.2] at e1
  rw[hb.2] at e2
  linarith
 calc ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)=r).card
   <= (Icc (0:ℤ) ((P/p:ℕ))).card:=ck _ ahf hinj
  _ = P/p+1:=by
      rw[ky,kg,<- ry,<- Nat.cast_add,mh]
noncomputable def wj (p k s P:ℕ):Finset (Fin (k+s)->ℤ):=
 (tc (k+s) (Icc 1 P)).filter fun x=>(univ.image fun i=>x i % p).card<k
theorem ahg (p k s P:ℕ) (hp:0<p) (hk:1<=k) (hkp:k-1<=p):
  (wj p k s P).card<=p.choose (k-1)*((k-1)*(P/p+1))^(k+s):=by
 classical
 have uj:wj p k s P ⊆ ((Ico (0:ℤ) p).powersetCard (k-1)).biUnion
   (fun R=>tc (k+s) ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)∈R)):=by
  intro x hx
  rw[wj,ah] at hx
  have ae8:(univ.image fun i=>x i % p) ⊆ Ico (0:ℤ) p:=by
   intro r hr
   rw[cr] at hr
   obtain ⟨i,_,rfl⟩:=hr
   rw[g4]
   have x6:(0:ℤ)<p:=by exact_mod_cast hp
   exact ⟨nd _ x6.ne',oq _ x6⟩
  obtain ⟨R,hR1,hR2,hR3⟩:=Finset.exists_subsuperset_card_eq (n:=k-1) ae8 (by have:=hx.2; omega)
   (by simpa using hkp)
  rw[l5]
  refine ⟨R,rk.mpr ⟨hR2,hR3⟩,td.mpr fun i=>?_⟩
  rw[ah]
  exact ⟨td.mp hx.1 i,hR1 (dv _ (ng i))⟩
 refine (cf uj).trans ((kd).trans ?_)
 have hR:∀ R∈(Ico (0:ℤ) p).powersetCard (k-1),
   (tc (k+s) ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)∈R)).card<=
    ((k-1)*(P/p+1))^(k+s):=by
  intro R hR
  rw[rk] at hR
  rw[kz,mi,i1,jr]
  apply ec
  calc ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)∈R).card
    = (R.biUnion fun r=>(Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)=r).card:=by
        congr 1
        ext a
        simp only[ah,l5]
        constructor
        ·rintro ⟨h1,h2⟩; exact ⟨_,h2,h1,rfl⟩
        ·rintro ⟨r,hr,h1,rfl⟩; exact ⟨h1,hr⟩
   _<=∑ r∈R,((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)=r).card:=kd
   _<=∑ _r∈R,(P/p+1):=ao fun r _=>aix P p hp r
   _=(k-1)*(P/p+1):=by rw[a9,hR.2,fx]
 calc ∑ R∈(Ico (0:ℤ) p).powersetCard (k-1),
       (tc (k+s) ((Icc (1:ℤ) P).filter fun a:ℤ=>a % (p:ℤ)∈R)).card
   <= ∑ _R∈(Ico (0:ℤ) p).powersetCard (k-1),((k-1)*(P/p+1))^(k+s):=
       ao hR
  _ = p.choose (k-1)*((k-1)*(P/p+1))^(k+s):=by
      rw[a9,Finset.card_powersetCard,fx]
      simp
lemma x7 (k a b:ℕ) (u:Fin a->ℤ) (x:Fin b->ℤ):
  sig k (a+b) (Fin.append u x)=sig k a u+sig k b x:=by
 funext j
 simp[sig,Fin.sum_univ_add]
theorem yv (k s P:ℕ) (c:Fin k->ℤ):
  ((tc (k+s) (Icc 1 P)).filter fun y=>sig k (k+s) y=c).card<=k.factorial*P^s:=by
 classical
 set Y:=(tc (k+s) (Icc 1 P)).filter fun y=>sig k (k+s) y=c with hY
 have ae8:Y.image (fun y=>fun i:Fin s=>y (jg k i)) ⊆ tc s (Icc 1 P):=by
  intro z hz
  rw[cr] at hz
  obtain ⟨y,hy,rfl⟩:=hz
  exact td.mpr fun i=>td.mp (ah.mp hy).1 _
 have yu:∀ z∈Y.image (fun y=>fun i:Fin s=>y (jg k i)),
   (Y.filter fun y=>(fun i:Fin s=>y (jg k i))=z).card<=k.factorial:=by
  intro z _
  set Fz:=Y.filter fun y=>(fun i:Fin s=>y (jg k i))=z with hFz
  have hinj:oh (fun y:Fin (k+s)->ℤ=>fun i:Fin k=>((y (i0 s i):ℤ):ℚ))
    Fz:=by
   intro y hy y' hy' hyy
   rw[b9,hFz,ah] at hy hy'
   have h1:∀ i:Fin k,y (i0 s i)=y' (i0 s i):=by
    intro i
    have:=gy hyy i
    simp only at this
    exact_mod_cast this
   have h2:∀ i:Fin s,y (jg k i)=y' (jg k i):=by
    intro i
    have:=gy (hy.2.trans hy'.2.symm) i
    exact this
   funext i
   refine ni (fun i=>?_) (fun i=>?_) i
   ·exact h1 i
   ·exact h2 i
  rw[<- qo hinj]
  apply v3 (F:=ℚ) (fun j hj _=>by exact_mod_cast hj.ne')
   _ (fun j=>((if h:j-1<k then c ⟨j-1,h⟩ else 0:ℤ):ℚ)-
    ∑ i:Fin s,((z i:ℤ):ℚ)^j)
  intro v hv j hj0 hjk
  rw[cr] at hv
  obtain ⟨y,hy,rfl⟩:=hv
  rw[hFz,ah] at hy
  have avh:=(ah.mp hy.1).2
  have u8:sig k (k+s) y=sig k k (fun i=>y (i0 s i))+
    sig k s (fun i=>y (jg k i)):=by
   rw[<- x7]
   congr 1
   funext i
   refine ni (fun i=>?_) (fun i=>?_) i <;> simp
  rw[u8,hy.2] at avh
  have hj:=gy avh ⟨j-1,by omega⟩
  simp only[sig,pa] at hj
  rw[show j-1+1=j by omega] at hj
  rw[dif_pos (show j-1<k by omega),<- hj]
  push_cast
  ring
 calc Y.card<=k.factorial*(Y.image (fun y=>fun i:Fin s=>y (jg k i))).card:=
       e7 Y _ yu
  _<=k.factorial*(tc s (Icc 1 P)).card:=fu _ (cf ae8)
  _ = k.factorial*P^s:=by
      rw[kz,mi,i1,jr]
      simp
lemma aic (k s:ℕ) (y:Fin (k+s)->ℤ):
  sig k (k+s) y=sig k k (fun i=>y (i0 s i))+
   sig k s (fun i=>y (jg k i)):=by
 funext j
 simp[sig,Fin.sum_univ_add]
lemma am8 (k a b:ℕ) (u v:Fin a->ℤ) (x y:Fin b->ℤ) (c:ℤ):
  sig k a u+sig k b x=sig k a v+sig k b y↔
   sig k a (fun i=>u i+c)+sig k b (fun i=>x i+c)=
    sig k a (fun i=>v i+c)+sig k b (fun i=>y i+c):=by
 rw[<- x7,<- x7,<- x7,<- x7]
 have e:∀ (w:Fin a->ℤ) (z:Fin b->ℤ),
   Fin.append (fun i=>w i+c) (fun i=>z i+c)=fun i=>Fin.append w z i+c:=by
  intro w z
  funext i
  refine ni (fun i=>?_) (fun i=>?_) i <;> simp
 rw[e,e]
 exact (zi _ _ c).symm
lemma al0 (k s:ℕ) (q:ℤ) (z:Fin s->ℤ) (j:Fin k):
  sig k s (fun i=>q*z i) j=q^(j.val+1)*sig k s z j:=by
 simp[sig,i5,bc]
lemma alm {k s P p:ℕ} (hp:0<p) (r:ℤ) (B:Finset ℤ)
  (hB:∀ x∈B,x∈Icc (1:ℤ) P∧x % p=r) (u v:Fin k->ℤ):
  ((tc s B ×ˢ tc s B).filter fun xy=>sig k k u+sig k s xy.1=sig k k v+sig k s xy.2).card<=
   if (∀ j:Fin k,(p:ℤ)^(j.val+1)∣
       sig k k (fun i=>u i-r) j-sig k k (fun i=>v i-r) j)
   then J k s (Icc 1 ((P/p:ℕ)+1:ℤ)) else 0:=by
 classical
 have x6:(0:ℤ)<p:=by exact_mod_cast hp
 have hxr:∀ x∈B,x=(p:ℤ)*(x/p)+r:=by
  intro x hx
  have:=nf x p
  rw[(hB x hx).2] at this
  linarith
 have abd:∀ x∈tc s B,∀ y∈tc s B,
   (sig k k u+sig k s x=sig k k v+sig k s y↔
    ∀ j : Fin k,(p:ℤ)^(j.val+1)*
        (sig k s (fun i=>x i/p) j-sig k s (fun i=>y i/p) j)=
     sig k k (fun i=>v i-r) j-sig k k (fun i=>u i-r) j):=by
  intro x hx y hy
  rw[am8 k k s u v x y (-r)]
  have ex:(fun i=>x i+-r)=fun i=>(p:ℤ)*(x i/p):=by
   funext i; have:=hxr (x i) (td.mp hx i); linarith
  have ey:(fun i=>y i+-r)=fun i=>(p:ℤ)*(y i/p):=by
   funext i; have:=hxr (y i) (td.mp hy i); linarith
  have eu:(fun i=>u i+-r)=fun i=>u i-r:=by funext i; ring
  have ev:(fun i=>v i+-r)=fun i=>v i-r:=by funext i; ring
  rw[ex,ey,eu,ev]
  constructor
  ·intro h j
   have hj:=gy h j
   simp only[pa,al0] at hj
   linarith
  ·intro h
   funext j
   have hj:=h j
   simp only[pa,al0]
   linarith
 split_ifs with aso
 ·obtain ⟨m,hm⟩:∃ m:Fin k->ℤ,m=fun j=>
    (sig k k (fun i=>v i-r) j-sig k k (fun i=>u i-r) j)/(p:ℤ)^(j.val+1):=
   ⟨_,rfl⟩
  set Z:=B.image (fun x=>x/(p:ℤ)) with hZ
  have ahf:∀ xy∈(tc s B ×ˢ tc s B).filter
    (fun xy=>sig k k u+sig k s xy.1=sig k k v+sig k s xy.2),
    (fun xy:(Fin s->ℤ) × (Fin s->ℤ)=>((fun i=>xy.1 i/(p:ℤ)),
     (fun i=>xy.2 i/(p:ℤ)))) xy∈
     (tc s Z ×ˢ tc s Z).filter (fun zz=>sig k s zz.1-sig k s zz.2=m):=by
   intro xy tv
   rw[ah,bm] at tv
   rw[ah,bm]
   refine ⟨⟨td.mpr fun i=>dv _ (td.mp tv.1.1 i),
    td.mpr fun i=>dv _ (td.mp tv.1.2 i)⟩, ?_⟩
   have h:=(abd _ tv.1.1 _ tv.1.2).mp tv.2
   funext j
   simp only[hm,rt]
   rw[<- h j,Int.mul_ediv_cancel_left _ (l7 _ x6.ne')]
  have hinj:oh (fun xy:(Fin s->ℤ) × (Fin s->ℤ)=>((fun i=>xy.1 i/(p:ℤ)),
    (fun i=>xy.2 i/(p:ℤ))))
    ((tc s B ×ˢ tc s B).filter
     (fun xy=>sig k k u+sig k s xy.1=sig k k v+sig k s xy.2)):=by
   intro a ha b hb hab
   rw[b9,ah,bm] at ha hb
   simp only[j5] at hab
   ext i
   ·rw[hxr _ (td.mp ha.1.1 i),hxr _ (td.mp hb.1.1 i),gy hab.1 i]
   ·rw[hxr _ (td.mp ha.1.2 i),hxr _ (td.mp hb.1.2 i),gy hab.2 i]
  calc _<=((tc s Z ×ˢ tc s Z).filter fun zz=>sig k s zz.1-sig k s zz.2=m).card:=
        ck _ ahf hinj
   _<=J k s Z:=x5 k s Z m
   _ ≤ J k s (Icc 1 ((P/p:ℕ)+1:ℤ)):=by
       apply adk k s (a:=0)
       intro z hz
       rw[hZ,cr] at hz
       obtain ⟨x,hx,rfl⟩:=hz
       have h1:=(hB x hx).1
       rw[ar] at h1 ⊢
       have h2:x/(p:ℤ)<=(P:ℤ)/p:=Int.ediv_le_ediv x6 h1.2
       have h3:((P/p:ℕ):ℤ)=(P:ℤ)/p:=Int.natCast_div P p
       constructor
       ·exact Int.ediv_nonneg (by linarith) x6.le
       ·linarith
 ·rw[Nat.le_zero,n8,qn]
  intro xy tv h
  rw[bm] at tv
  apply aso
  intro j
  have:=(abd _ tv.1 _ tv.2).mp h j
  exact ⟨-(sig k s (fun i=>xy.1 i/p) j-sig k s (fun i=>xy.2 i/p) j),by linarith⟩
noncomputable def v5 (p k P:ℕ):Finset (Fin k->ℤ):=
 (tc k (Icc 1 P)).filter fun u=>∀ i j,i≠j->¬ (p:ℤ)∣u i-u j
lemma aca (s P:ℕ):(tc s (Icc (1:ℤ) P)).card=P^s:=by
 rw[kz,mi,i1,jr]
 simp
theorem aln {k s P p:ℕ} (hp:p.Prime) (hpk:k<p) (hPp:P<=p^k) (r:ℤ)
  (B:Finset ℤ) (hB:∀ x∈B,x∈Icc (1:ℤ) P∧x % p=r):
  Tc k s (v5 p k P) (sig k k) B<=
   P^k*(k.factorial*p^(k*(k-1)/2))*J k s (Icc 1 ((P/p:ℕ)+1:ℤ)):=by
 classical
 set U:=v5 p k P with hU
 set Jq:=J k s (Icc 1 ((P/p:ℕ)+1:ℤ)) with hJq
 set cond:(Fin k->ℤ)->(Fin k->ℤ)->Prop:=fun u v=>∀ j:Fin k,(p:ℤ)^(j.val+1)∣
     sig k k (fun i=>u i-r) j-sig k k (fun i=>v i-r) j with aso
 have hTc:Tc k s U (sig k k) B=∑ uv∈U ×ˢ U,
   ((tc s B ×ˢ tc s B).filter fun xy=>
    sig k k uv.1+sig k s xy.1=sig k k uv.2+sig k s xy.2).card:=by
  rw[Tc,j6,ep]
  apply ai rfl
  intro uv _
  rw[j6]
 have ara:∀ v:Fin k->ℤ,(U.filter fun u=>cond u v).card<=
   k.factorial*p^(k*(k-1)/2):=by
  intro v
  set I:=(Icc (1:ℤ) P).image (·-r) with hI
  have hIc:∀ a∈I,∀ b∈I,(p:ℤ)^k∣a-b->a=b:=by
   intro a ha b hb hd
   rw[hI,cr] at ha hb
   obtain ⟨a',ha',rfl⟩:=ha
   obtain ⟨b',hb',rfl⟩:=hb
   rw[ar] at ha' hb'
   have bdi:(P:ℤ)<=(p:ℤ)^k:=by exact_mod_cast hPp
   have xj:|a'-r-(b'-r)|<(p:ℤ)^k:=by
    rw[abs_lt]; constructor <;> linarith
   have:=qx hd xj
   linarith
  refine br ?_ (ajj hp hpk I hIc (sig k k (fun i=>v i-r)))
  apply ck (fun u=>fun i=>u i-r)
  ·intro u hu
   rw[b9,ah] at hu
   rw[b9]
   have x8:=hu.1
   rw[hU,v5,ah] at x8
   rw[ah]
   refine ⟨td.mpr fun i=>?_,fun i j hij=>?_,fun j=>hu.2 j⟩
   ·rw[hI]; exact dv _ (td.mp x8.1 i)
   ·simp only[sub_sub_sub_cancel_right]
    exact x8.2 i j hij
  ·intro a _ b _ hab
   funext i
   have:=gy hab i
   simp only at this
   linarith
 have apb:∀ uv∈U ×ˢ U,((tc s B ×ˢ tc s B).filter fun xy=>
   sig k k uv.1+sig k s xy.1=sig k k uv.2+sig k s xy.2).card<=
    if cond uv.1 uv.2 then Jq else 0:=fun uv _=>
  alm (Nat.Prime.pos hp) r B hB uv.1 uv.2
 have hUc:U.card<=P^k:=by
  rw[hU,v5,<- aca k P]
  exact nh _ _
 rw[hTc]
 calc ∑ uv∈U ×ˢ U,((tc s B ×ˢ tc s B).filter fun xy=>
       sig k k uv.1+sig k s xy.1=sig k k uv.2+sig k s xy.2).card
   <= ∑ uv∈U ×ˢ U,(if cond uv.1 uv.2 then Jq else 0):=ao apb
  _ = ∑ v∈U,∑ u∈U,(if cond u v then Jq else 0):=by
      rw[ep,d0]
  _ = ∑ v∈U,(U.filter fun u=>cond u v).card*Jq:=by
      apply ai rfl
      intro v _
      rw[<- jf,a9,fx]
  _ ≤ ∑ _v∈U,(k.factorial*p^(k*(k-1)/2))*Jq:=
      ao fun v _=>gb _ (ara v)
  _ = U.card*((k.factorial*p^(k*(k-1)/2))*Jq):=by
      rw[a9,fx]
  _<=P^k*((k.factorial*p^(k*(k-1)/2))*Jq):=gb _ hUc
  _=P^k*(k.factorial*p^(k*(k-1)/2))*Jq:=by ring
theorem auf (p k s P:ℕ):
    J k (k+s) (Icc 1 P)<=((k+s).factorial)^2*Tc k s (v5 p k P) (sig k k) (Icc 1 P)+
      2*((wj p k s P).card*(k.factorial*P^s)):=by
  classical
  set A:Finset ℤ:=Icc 1 P with hA
  set S:=(tc (k+s) A ×ˢ tc (k+s) A).filter
    (fun xy=>sig k (k+s) xy.1=sig k (k+s) xy.2) with hS
  set x0:=wj p k s P with ahh
  have hJ:J k (k+s) A=S.card:=rfl
  rw[hJ,<- Finset.card_filter_add_card_filter_not
    (fun xy:(Fin (k+s)->ℤ) × (Fin (k+s)->ℤ)=>xy.1∉x0∧xy.2∉x0)]
  set G:=S.filter (fun xy=>vo p k s xy.1∧vo p k s xy.2) with hG
  have hGT:G.card<=Tc k s (v5 p k P) (sig k k) A:=by
    unfold Tc
    apply ck
      (fun xy=>(((fun i=>xy.1 (i0 s i)),(fun i=>xy.2 (i0 s i))),
        ((fun i=>xy.1 (jg k i)),(fun i=>xy.2 (jg k i)))))
    · intro xy tv
      rw[b9,hG,ah,hS,ah,bm] at tv
      rw[b9,ah,bm,bm,
        bm]
      refine ⟨⟨⟨?_, ?_⟩,td.mpr fun i=>td.mp tv.1.1.1 _,
        td.mpr fun i=>td.mp tv.1.1.2 _⟩, ?_⟩
      · rw[v5,ah]
        exact ⟨td.mpr fun i=>td.mp tv.1.1.1 _,tv.2.1⟩
      · rw[v5,ah]
        exact ⟨td.mpr fun i=>td.mp tv.1.1.2 _,tv.2.2⟩
      · have h:=tv.1.2
        rw[aic,aic] at h
        exact h
    · intro a _ b _ hab
      simp only[j5] at hab
      ext i
      · refine ni (fun i=>?_) (fun i=>?_) i
        · exact gy hab.1.1 i
        · exact gy hab.2.1 i
      · refine ni (fun i=>?_) (fun i=>?_) i
        · exact gy hab.1.2 i
        · exact gy hab.2.2 i
  have avi:∀ xk:jh (Fin (k+s)) × jh (Fin (k+s)),
      (S.filter fun xy=>vo p k s (xy.1∘xk.1)∧vo p k s (xy.2∘xk.2)).card<=
        G.card:=by
    intro xk
    apply ck (fun xy=>(xy.1∘xk.1,xy.2∘xk.2))
    · intro xy tv
      rw[b9,ah,hS,ah,bm] at tv
      rw[b9,hG,ah,hS,ah,bm]
      refine ⟨⟨⟨td.mpr fun i=>td.mp tv.1.1.1 _,
        td.mpr fun i=>td.mp tv.1.1.2 _⟩, ?_⟩,tv.2⟩
      simp only[aiw]
      exact tv.1.2
    · intro a _ b _ hab
      simp only[j5] at hab
      ext i
      · have:=gy hab.1 (xk.1.symm i)
        simpa using this
      · have:=gy hab.2 (xk.2.symm i)
        simpa using this
  have hgg:(S.filter fun xy=>xy.1∉x0∧xy.2∉x0).card<=((k+s).factorial)^2*G.card:=by
    have uj:(S.filter fun xy=>xy.1∉x0∧xy.2∉x0) ⊆
        (Finset.univ:Finset (jh (Fin (k+s)) × jh (Fin (k+s)))).biUnion
          (fun xk=>S.filter fun xy=>
            vo p k s (xy.1∘xk.1)∧vo p k s (xy.2∘xk.2)):=by
      intro xy tv
      rw[ah] at tv
      have hxS:=tv.1
      rw[hS,ah,bm] at hxS
      have hx:k<=(univ.image fun i=>xy.1 i % p).card:=by
        by_contra v7
        apply tv.2.1
        rw[ahh,wj,ah]
        exact ⟨hxS.1.1,by omega⟩
      have hy:k<=(univ.image fun i=>xy.2 i % p).card:=by
        by_contra v7
        apply tv.2.2
        rw[ahh,wj,ah]
        exact ⟨hxS.1.2,by omega⟩
      obtain ⟨π,hπ⟩:=xx xy.1 hx
      obtain ⟨π',hπ'⟩:=xx xy.2 hy
      rw[l5]
      exact ⟨(π,π'),ng _,ah.mpr ⟨tv.1,hπ,hπ'⟩⟩
    calc _<=_:=cf uj
      _ ≤ ∑ xk:jh (Fin (k+s)) × jh (Fin (k+s)),
          (S.filter fun xy=>vo p k s (xy.1∘xk.1)∧
            vo p k s (xy.2∘xk.2)).card:=kd
      _ ≤ ∑ bca:jh (Fin (k+s)) × jh (Fin (k+s)),G.card:=
          ao fun xk _=>avi xk
      _ = ((k+s).factorial)^2*G.card:=by
          rw[a9,i1,Fintype.card_prod,Fintype.card_perm,
            jr,fx]
          ring
  have hbx:(S.filter fun xy=>xy.1∈x0).card<=x0.card*(k.factorial*P^s):=by
    refine (e7 (f:=Prod.fst) _ (k.factorial*P^s) ?_).trans ?_
    · intro x _
      calc ((S.filter fun xy=>xy.1∈x0).filter fun xy=>xy.1=x).card
          <= ((tc (k+s) A).filter fun y=>sig k (k+s) y=sig k (k+s) x).card:=by
            apply ck Prod.snd
            · intro xy tv
              rw[b9,ah,ah,hS,ah,
                bm] at tv
              rw[b9,ah]
              exact ⟨tv.1.1.1.2,by rw[<- tv.2]; exact tv.1.1.2.symm⟩
            · intro a ha b hb hab
              rw[b9,ah] at ha hb
              exact s7 (ha.2.trans hb.2.symm) hab
        _<=k.factorial*P^s:=yv k s P _
    · rw[Nat.mul_comm (k.factorial*P^s)]
      apply gb
      apply cf
      intro x hx
      rw[cr] at hx
      obtain ⟨xy,tv,rfl⟩:=hx
      exact (ah.mp tv).2
  have hby:(S.filter fun xy=>xy.2∈x0).card<=x0.card*(k.factorial*P^s):=by
    refine (e7 (f:=Prod.snd) _ (k.factorial*P^s) ?_).trans ?_
    · intro y _
      calc ((S.filter fun xy=>xy.2∈x0).filter fun xy=>xy.2=y).card
          <= ((tc (k+s) A).filter fun x=>sig k (k+s) x=sig k (k+s) y).card:=by
            apply ck Prod.fst
            · intro xy tv
              rw[b9,ah,ah,hS,ah,
                bm] at tv
              rw[b9,ah]
              exact ⟨tv.1.1.1.1,
 by rw [← tv.2]; exact tv.1.1.2⟩
            · intro a ha b hb hab
              rw[b9,ah] at ha hb
              exact s7 hab (ha.2.trans hb.2.symm)
        _<=k.factorial*P^s:=yv k s P _
    · rw[Nat.mul_comm (k.factorial*P^s)]
      apply gb
      apply cf
      intro x hx
      rw[cr] at hx
      obtain ⟨xy,tv,rfl⟩:=hx
      exact (ah.mp tv).2
  have ae9:(S.filter fun xy=>¬(xy.1∉x0∧xy.2∉x0)).card<=
      (S.filter fun xy=>xy.1∈x0).card+(S.filter fun xy=>xy.2∈x0).card:=by
    refine br (cf ?_) (r8 _ _)
    intro xy tv
    simp only[ah,p0] at tv ⊢
    tauto
  calc _<=((k+s).factorial)^2*G.card+
        ((S.filter fun xy=>xy.1∈x0).card+(S.filter fun xy=>xy.2∈x0).card):=
        qw hgg ae9
    _ ≤ ((k+s).factorial)^2*Tc k s (v5 p k P) (sig k k) A+
        (x0.card*(k.factorial*P^s)+x0.card*(k.factorial*P^s)):=
        qw (fu _ hGT) (qw hbx hby)
    _=_:=by ring
theorem ahi {p k s P:ℕ} (hp:p.Prime) (hpk:k<p) (hPp:P<=p^k) (hs:1<=s):
  J k (k+s) (Icc 1 P)<=
   ((k+s).factorial)^2*(p^(2*s-1)*(p*(P^k*(k.factorial*
    p^(k*(k-1)/2))*J k s (Icc 1 ((P/p:ℕ)+1:ℤ)))))+
   2*((wj p k s P).card*(k.factorial*P^s)):=by
 classical
 have zc:0<p:=hp.pos
 have x6:(0:ℤ)<p:=by exact_mod_cast zc
 refine (auf p k s P).trans (Nat.add_le_add_right (fu _ ?_) _)
 have aq9:∀ x∈Icc (1:ℤ) P,(x % p).toNat<p:=by
  intro x _
  have h1:=nd x x6.ne'
  have h2:= oq x x6
  omega
 refine (ajk k s hs (v5 p k P) (sig k k) (Icc 1 P) p zc
  (fun x=>(x % p).toNat) aq9).trans (fu _ ?_)
 calc ∑ r∈range p,Tc k s (v5 p k P) (sig k k) ((Icc (1:ℤ) P).filter
       fun x=>(x % p).toNat=r)
   ≤ ∑ _r∈range p,P^k*(k.factorial*p^(k*(k-1)/2))*
       J k s (Icc 1 ((P/p:ℕ)+1:ℤ)):=by
       apply ao
       intro r _
       apply aln hp hpk hPp (r:ℤ)
       intro x hx
       rw[ah] at hx
       refine ⟨hx.1, ?_⟩
       have h1:=nd x x6.ne'
       omega
  _ = p*(P^k*(k.factorial*p^(k*(k-1)/2))*J k s (Icc 1 ((P/p:ℕ)+1:ℤ))):=by
      rw[a9,fa,fx]
lemma ahj {X Q e:ℝ} (hX:0<X) (h1:X/4<=Q) (h2:Q<=2*X):
  Q^e<=(4:ℝ)^|e| *X^e:=by
 have hQ:0<Q:=by linarith[mo hX (by norm_num:(0:ℝ)<4)]
 rcases ig 0 e with he | he
 ·rw[bh he]
  calc Q^e<=(2*X)^e:=dh hQ.le h2 he
   _=2^e *X^e:=e6 (by norm_num) hX.le
   _ ≤ 4^e *X^e:=by
       apply ag _ (ei hX.le _)
       exact dh (by norm_num) (by norm_num) he
 ·rw[g5 he]
  calc Q^e<=(X/4)^e:=
        c1 (mo hX (by norm_num)) h1 he.le
   _ = X^e *(4:ℝ)^(-e):=by
       rw[ri hX.le (by norm_num),iv (by norm_num),jx]
   _=(4:ℝ)^(-e)*X^e:=by ring
lemma abo (k P:ℕ) (hk:1<=k) (hP:k^k<=P):
  ∃ p:ℕ,p.Prime∧k<p∧P<=p^k∧(P:ℝ)^((k:ℝ)⁻¹)<p∧
   (p:ℝ)<=4*(P:ℝ)^((k:ℝ)⁻¹):=by
 classical
 have hP1:1<=P:=br (qv _ _ (by omega)) hP
 have hex:∃ n,P<=n^k:=⟨P,Nat.le_self_pow (by omega) P⟩
 have xb:P<=(iw hex)^k:=Nat.find_spec hex
 have t6:iw hex≠0:=by
  intro h; rw[h,zero_pow (by omega)] at xb; omega
 have hnk:k<=iw hex:=by
  by_contra h
  push_neg at h
  have:(iw hex)^k<k^k:=Nat.pow_lt_pow_left h (by omega)
  omega
 have avl:(iw hex-1)^k<P:=by
  have:=Nat.find_min hex (show iw hex-1< iw hex by omega)
  push_neg at this
  exact this
 obtain ⟨p,hp,hnp,hp2⟩:= od (iw hex) t6
 have hk0:k≠0:=by omega
 have avm:((P:ℝ)^((k:ℝ)⁻¹))^k=P:=g2 (av _) hk0
 have am9:0<=(P:ℝ)^((k:ℝ)⁻¹):=ei (av _) _
 have zj:1<=(P:ℝ)^((k:ℝ)⁻¹):=
  e5 (by exact_mod_cast hP1) (by positivity)
 have bdj:(P:ℝ)^((k:ℝ)⁻¹)<=(iw hex:ℝ):=by
  have h:(P:ℝ)<=(iw hex:ℝ)^k:=by exact_mod_cast xb
  rw[<- avm] at h
  exact le_of_pow_le_pow_left₀ hk0 (av _) h
 have bdk:(iw hex:ℝ)-1<(P:ℝ)^((k:ℝ)⁻¹):=by
  by_contra h
  push_neg at h
  have h1:((iw hex-1:ℕ):ℝ)=(iw hex:ℝ)-1:=by
   rw[il (by omega),ry]
  have h2:((P:ℝ)^((k:ℝ)⁻¹))^k<=((iw hex-1:ℕ):ℝ)^k:=by
   rw[h1]; exact aj am9 h k
  rw[avm] at h2
  have:P<=(iw hex-1)^k:=by exact_mod_cast h2
  omega
 refine ⟨p,hp,by omega,br xb (ec hnp.le k), ?_, ?_⟩
 ·have:(iw hex:ℝ)<p:=by exact_mod_cast hnp
  linarith
 ·have:(p:ℝ)<=2*(iw hex:ℝ):=by exact_mod_cast hp2
  linarith
lemma aug (k n P:ℕ):(J k n (Icc 1 (P:ℤ)):ℝ)<=((P:ℝ)^n)^2:=by
 have h:J k n (Icc 1 (P:ℤ))<=(P^n)^2:=by
  unfold J
  refine (nh _ _).trans ?_
  rw[iz,aca,sq]
 exact_mod_cast h
noncomputable def aau (k s:ℕ) (Δ C:ℝ):ℝ:=
 (((k^k:ℕ):ℝ)^(k+s))^2*((k^k:ℕ):ℝ)^
     |2*((k+s:ℕ):ℝ)-k*(k+1)/2+
      max ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k)|+
  ((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)*
   (C*(4:ℝ)^|2*(s:ℝ)-k*(k+1)/2+Δ|)+
  2*((4:ℝ)^(k-1)*(((k-1:ℕ):ℝ)*2)^(k+s)*k.factorial)
theorem apc {k s:ℕ} {Δ C:ℝ} (hk:2<=k) (hs:1<=s) (x9:0<=C)
  (hC:∀ P:ℕ,1<=P->
   (J k s (Icc 1 (P:ℤ)):ℝ)<=C*(P:ℝ)^(2*(s:ℝ)-k*(k+1)/2+Δ)):
  ∀ P:ℕ,1<=P->(J k (k+s) (Icc 1 (P:ℤ)):ℝ)<=aau k s Δ C*(P:ℝ)^
   (2*((k+s:ℕ):ℝ)-k*(k+1)/2+
    max ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k)):=by
 have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
 have hk0:(k:ℝ)≠0:=by linarith
 set Δ':=max ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k) with ana
 set e:=2*((k+s:ℕ):ℝ)-k*(k+1)/2+Δ' with he
 set es:=2*(s:ℝ)-k*(k+1)/2+Δ with hes
 set xl:ℕ:=k^k with bcb
 have avo:(1:ℝ)<=xl:=by exact_mod_cast qv _ _ (by omega)
 set N1:ℕ:=2*s+k*(k-1)/2 with hN1
 set K0:ℝ:=((xl:ℝ)^(k+s))^2*(xl:ℝ)^|e| with ya
 set K1:ℝ:=((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^N1*(C*(4:ℝ)^|es|)
  with hK1
 set K2:ℝ:=2*((4:ℝ)^(k-1)*(((k-1:ℕ):ℝ)*2)^(k+s)*k.factorial) with hK2
 have a3j:0<=K0:=by positivity
 have avp:0<=K1:=by positivity
 have avq:0<=K2:=by positivity
 have hsc:aau k s Δ C=K0+K1+K2:=rfl
 rw[hsc]
 intro P hP
 have hPr:(1:ℝ)<=P:=by exact_mod_cast hP
 have wa:(0:ℝ)<P:=by linarith
 have hPe:0<=(P:ℝ)^e:=ei wa.le _
 rcases si P xl with wz | avs
 ·
  have h1:=aug k (k+s) P
  have h2:((P:ℝ)^(k+s))^2<=((xl:ℝ)^(k+s))^2:=by
   have:(P:ℝ)<=xl:=by exact_mod_cast wz.le
   gcongr
  have h3:1<=(xl:ℝ)^|e| *(P:ℝ)^e:=by
   rcases ig 0 e with he0 | he0
   ·exact qm (e5 avo (eg _))
     (e5 hPr he0)
   ·rw[g5 he0]
    have:(xl:ℝ)^e<=(P:ℝ)^e:=
     c1 wa (by exact_mod_cast wz.le) he0.le
    calc (1:ℝ)=(xl:ℝ)^(-e)*(xl:ℝ)^e:=by
          rw[<- c6 (by linarith)]; simp
     _ ≤ (xl:ℝ)^(-e)*(P:ℝ)^e:=
         ab this (ei (by linarith) _)
  have h4:(J k (k+s) (Icc 1 (P:ℤ)):ℝ)<=K0*(P:ℝ)^e:=by
   calc (J k (k+s) (Icc 1 (P:ℤ)):ℝ)<=((xl:ℝ)^(k+s))^2:=h1.trans h2
    _=((xl:ℝ)^(k+s))^2*1:=by ring
    _ ≤ ((xl:ℝ)^(k+s))^2*((xl:ℝ)^|e| *(P:ℝ)^e):=
        ab h3 (by positivity)
    _=K0*(P:ℝ)^e:=by rw[ya]; ring
  linarith[b7 avp hPe,b7 avq hPe]
 ·
  obtain ⟨p,hp,hkp,hPp,a3k,hp4⟩:=abo k P (by omega) avs
  set θ:=(P:ℝ)^((k:ℝ)⁻¹) with hθ
  have zj:1<=θ:=e5 hPr (by positivity)
  have anb:(0:ℝ)<p:=by linarith
  have aeg:=ahi hp hkp hPp hs
  set Q:ℕ:=P/p+1 with hQ
  have hJQ:J k s (Icc 1 ((P/p:ℕ)+1:ℤ))=J k s (Icc 1 (Q:ℤ)):=by
   rw[hQ]; push_cast; rfl
  rw[hJQ] at aeg
  set X:=(P:ℝ)^(1-(k:ℝ)⁻¹) with hX
  have arb:X=(P:ℝ)/θ:=by
   rw[hX,rg wa,fi]
  have bdl:θ<=P:=by
   calc θ=(P:ℝ)^((k:ℝ)⁻¹):=rfl
    _ ≤ (P:ℝ)^(1:ℝ):=al hPr (by
        rw[inv_le_one₀ (by linarith)]; linarith)
    _=P:=fi _
  have hX1:1<=X:=by rw[arb,bl (by linarith)]; linarith
  have anc:0<X:=by linarith
  have azs:X/4<=(Q:ℝ):=by
   have h1:(P:ℝ)/p<=Q:=by
    rw[hQ,ay anb]
    have:P<p*(P/p+1):=Nat.lt_mul_div_succ P hp.pos
    push_cast
    have h':((P:ℕ):ℝ)<(p:ℝ)*((P/p:ℕ)+1):=by exact_mod_cast this
    linarith
   have h2:X/4<=(P:ℝ)/p:=by
    rw[arb,div_div,ax (by positivity) anb]
    nlinarith
   linarith
  have avt:(Q:ℝ)<=2*X:=by
   have h1:((P/p:ℕ):ℝ)<=(P:ℝ)/p:=Nat.cast_div_le
   have h2:(P:ℝ)/p<=X:=by
    rw[arb]; exact bb (by linarith) (by linarith) a3k.le
   rw[hQ]; push_cast; linarith
  have hQ1:1<=Q:=by rw[hQ]; exact Nat.le_add_left 1 _
  have hpow:∀ N:ℕ,(p:ℝ)^N<=(4:ℝ)^N*(P:ℝ)^((N:ℝ)/k):=by
   intro N
   calc (p:ℝ)^N<=(4*θ)^N:=aj anb.le hp4 N
    _=(4:ℝ)^N*θ^N:=i5 _ _ _
    _ = (4:ℝ)^N*(P:ℝ)^((N:ℝ)/k):=by
        rw[hθ,<- da ((P:ℝ)^((k:ℝ)⁻¹)) N,
         <- d7 (av _)]
        congr 2
        ring
  have hJs:(J k s (Icc 1 (Q:ℤ)):ℝ)<=C*((4:ℝ)^|es| *(P:ℝ)^((1-(k:ℝ)⁻¹)*es)):=by
   refine (hC Q hQ1).trans (ab ?_ x9)
   rw[d7 wa.le,<- hX]
   exact ahj anc azs avt
  have hkk:((k*(k-1)/2:ℕ):ℝ)=(k:ℝ)*(k-1)/2:=by
   rw[Nat.cast_div (Nat.even_mul_pred_self k).two_dvd (by norm_num),pb,
    il (by omega)]
   push_cast; ring
  have a3l:(N1:ℝ)=2*s+(k:ℝ)*(k-1)/2:=by
   rw[hN1]; push_cast[hkk]; ring
  have azt:(((k+s).factorial^2*(p^(2*s-1)*(p*(P^k*(k.factorial*
    p^(k*(k-1)/2))*J k s (Icc 1 (Q:ℤ))))):ℕ):ℝ)<=
    K1*(P:ℝ)^(2*((k+s:ℕ):ℝ)-k*(k+1)/2+(1-1/(k:ℝ))*Δ):=by
   have hpN:p^(2*s-1)*(p*(P^k*(k.factorial*p^(k*(k-1)/2))*
     J k s (Icc 1 (Q:ℤ))))=p^N1*P^k*k.factorial*J k s (Icc 1 (Q:ℤ)):=by
    have h2s:p^(2*s-1)*p=p^(2*s):=by
     rw[<- ob]; congr 1; omega
    rw[hN1,oy,<- h2s]
    ring
   rw[hpN]
   simp only[pb,rx]
   have hPk:(P:ℝ)^k=(P:ℝ)^(k:ℝ):=(da _ _).symm
   have xm:(N1:ℝ)/k+k+(1-(k:ℝ)⁻¹)*es=
     2*((k+s:ℕ):ℝ)-k*(k+1)/2+(1-1/(k:ℝ))*Δ:=by
    rw[a3l,hes]; push_cast; field_simp; ring
   calc ((k+s).factorial:ℝ)^2*((p:ℝ)^N1*(P:ℝ)^k*k.factorial*
         (J k s (Icc 1 (Q:ℤ)):ℝ))
     ≤ ((k+s).factorial:ℝ)^2*(((4:ℝ)^N1*(P:ℝ)^((N1:ℝ)/k))*
         (P:ℝ)^(k:ℝ)*k.factorial*
         (C*((4:ℝ)^|es| *(P:ℝ)^((1-(k:ℝ)⁻¹)*es)))):=by
         rw[hPk]
         gcongr
         ·exact hpow N1
    _ = K1*((P:ℝ)^((N1:ℝ)/k)*(P:ℝ)^(k:ℝ)*
         (P:ℝ)^((1-(k:ℝ)⁻¹)*es)):=by rw[hK1]; ring
    _ = K1*(P:ℝ)^(2*((k+s:ℕ):ℝ)-k*(k+1)/2+(1-1/(k:ℝ))*Δ):=by
        rw[<- c6 wa,<- c6 wa,xm]
  have ahh:((2*((wj p k s P).card*(k.factorial*P^s)):ℕ):ℝ)<=
    K2*(P:ℝ)^(2*((k+s:ℕ):ℝ)-k*(k+1)/2+
     ((k:ℝ)*(k-1)/2-(s+1)/k)):=by
   have hb:=ahg p k s P hp.pos (by omega) (by omega)
   have hb':((wj p k s P).card:ℝ)<=(p.choose (k-1):ℝ)*
     (((k-1:ℕ):ℝ)*(Q:ℝ))^(k+s):=by
    rw[hQ] at *
    exact_mod_cast hb
   have hch:(p.choose (k-1):ℝ)<=(p:ℝ)^(k-1):=by
    have:=Nat.choose_le_pow_div (α:=ℝ) (k-1) p
    refine this.trans (div_le_self (by positivity) ?_)
    exact_mod_cast i8.mpr (Nat.factorial_ne_zero _)
   have hQX:(((k-1:ℕ):ℝ)*(Q:ℝ))^(k+s)<=
     (((k-1:ℕ):ℝ)*2)^(k+s)*(P:ℝ)^((1-(k:ℝ)⁻¹)*((k+s:ℕ):ℝ)):=by
    rw[d7 wa.le,<- hX,da,<- i5,gv]
    apply aj (by positivity)
    exact ab avt (av _)
   have x1:(((k-1:ℕ):ℝ))=(k:ℝ)-1:=by rw[il (by omega),ry]
   have xm:(((k-1:ℕ):ℝ))/k+(1-(k:ℝ)⁻¹)*((k+s:ℕ):ℝ)+s=
     2*((k+s:ℕ):ℝ)-k*(k+1)/2+((k:ℝ)*(k-1)/2-(s+1)/k):=by
    rw[x1]; push_cast; field_simp; ring
   have hPs:(P:ℝ)^s=(P:ℝ)^(s:ℝ):=(da _ _).symm
   simp only[pb,rx,Nat.cast_ofNat]
   calc 2*((wj p k s P).card*(k.factorial*(P:ℝ)^s))
     ≤ 2 * (((p:ℝ)^(k-1)*((((k-1:ℕ):ℝ)*2)^(k+s)*
         (P:ℝ)^((1-(k:ℝ)⁻¹)*((k+s:ℕ):ℝ))))*(k.factorial*(P:ℝ)^s)):=by
         gcongr
         exact hb'.trans (a8 hch hQX (by positivity) (by positivity))
    _ ≤ 2 * ((((4:ℝ)^(k-1)*(P:ℝ)^((((k-1:ℕ):ℝ))/k))*
          ((((k-1:ℕ):ℝ)*2)^(k+s)*
          (P:ℝ)^((1-(k:ℝ)⁻¹)*((k+s:ℕ):ℝ))))*(k.factorial*(P:ℝ)^s)):=by
        gcongr
        exact hpow (k-1)
    _ = K2*((P:ℝ)^((((k-1:ℕ):ℝ))/k)*
         (P:ℝ)^((1-(k:ℝ)⁻¹)*((k+s:ℕ):ℝ))*(P:ℝ)^(s:ℝ)):=by
        rw[hK2,hPs]; ring
    _=_:=by rw[<- c6 wa,<- c6 wa,xm]
  have avv:(P:ℝ)^(2*((k+s:ℕ):ℝ)-k*(k+1)/2+(1-1/(k:ℝ))*Δ)<=
    (P:ℝ)^e:=
   al hPr (by
    have hm:=bq ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k)
    rw[he,ana]
    linarith)
  have avw:(P:ℝ)^(2*((k+s:ℕ):ℝ)-k*(k+1)/2+
    ((k:ℝ)*(k-1)/2-(s+1)/k))<=(P:ℝ)^e:=
   al hPr (by
    have hm:=cd ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k)
    rw[he,ana]
    linarith)
  have hcast:(J k (k+s) (Icc 1 (P:ℤ)):ℝ)<=
    (((k+s).factorial^2*(p^(2*s-1)*(p*(P^k*(k.factorial*
     p^(k*(k-1)/2))*J k s (Icc 1 (Q:ℤ))))):ℕ):ℝ)+
    ((2*((wj p k s P).card*(k.factorial*P^s)):ℕ):ℝ):=by
   exact_mod_cast aeg
  have uq:(J k (k+s) (Icc 1 (P:ℤ)):ℝ)<=K1*(P:ℝ)^e+K2*(P:ℝ)^e:=by
   refine hcast.trans (e8 (azt.trans ?_) (ahh.trans ?_))
   ·exact ab avv avp
   ·exact ab avw avq
  linarith[b7 a3j hPe]
lemma avx (k P:ℕ):J k k (Icc 1 (P:ℤ))<=k.factorial*P^k:=by
 classical
 unfold J
 set S:=(tc k (Icc (1:ℤ) P) ×ˢ tc k (Icc (1:ℤ) P)).filter
  (fun xy=>sig k k xy.1=sig k k xy.2) with hS
 refine (e7 (f:=Prod.fst) S k.factorial ?_).trans ?_
 ·intro x _
  calc (S.filter fun xy=>xy.1=x).card
    <= ((tc k (Icc (1:ℤ) P)).filter fun y=>sig k k y=sig k k x).card:=by
        apply ck Prod.snd
        ·intro xy tv
         rw[b9,ah,hS,ah,
          bm] at tv
         rw[b9,ah]
         exact ⟨tv.1.1.2,by rw[<- tv.2]; exact tv.1.2.symm⟩
        ·intro a ha b hb hab
         rw[b9,ah] at ha hb
         exact s7 (ha.2.trans hb.2.symm) hab
   _ ≤ k.factorial:=by
       have:=yv k 0 P (sig k k x)
       simpa using this
 ·apply fu
  rw[<- aca k P]
  apply cf
  intro x hx
  rw[cr] at hx
  obtain ⟨xy,tv,rfl⟩:=hx
  rw[hS,ah,bm] at tv
  exact tv.1.1
noncomputable def wb (k:ℕ):ℕ->ℝ
 | 0=>(k:ℝ)*(k-1)/2
 | τ + 1=>max ((1-1/(k:ℝ))*wb k τ)
     ((k:ℝ)*(k-1)/2-(((k*(τ+1):ℕ):ℝ)+1)/k)
lemma aae (k:ℕ) (hk:2<=k):
  ∀ τ,0<=wb k τ∧wb k τ<=(k:ℝ)*(k-1)/2:=by
 have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
 have t9:0<=1-1/(k:ℝ):=by
  rw[oa,dw (by linarith)]; linarith
 have hc1:1-1/(k:ℝ)<=1:=by
  have:0<=1/(k:ℝ):=by positivity
  linarith
 intro τ
 induction τ with
 | zero=>
  simp only[wb]
  constructor
  ·have:(0:ℝ)<=(k:ℝ)-1:=by linarith
   positivity
  ·exact le_rfl
 | succ τ ih=>
  simp only[wb]
  constructor
  ·exact br (b7 t9 ih.1) (bq _ _)
  ·apply max_le
   ·nlinarith[ih.1,ih.2]
   ·have:0<=(((k*(τ+1):ℕ):ℝ)+1)/k:=by positivity
    linarith
lemma ane (k:ℕ) (hk:2<=k) (m:ℕ):
  wb k (s9 ((k:ℝ)*(k-1)/2)+m)<=
   (1-1/(k:ℝ))^m*((k:ℝ)*(k-1)/2):=by
 have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
 have t9:0<=1-1/(k:ℝ):=by
  rw[oa,dw (by linarith)]; linarith
 set τ₀:=s9 ((k:ℝ)*(k-1)/2) with a7r
 induction m with
 | zero=>simpa using (aae k hk τ₀).2
 | succ m ih=>
  rw[show τ₀+(m+1)=(τ₀+m)+1 by ring]
  simp only[wb]
  have ae9:(k:ℝ)*(k-1)/2-(((k*(τ₀+m+1):ℕ):ℝ)+1)/k<=
    (1-1/(k:ℝ))*wb k (τ₀+m):=by
   have h1:(k:ℝ)*(k-1)/2<=τ₀:=f9 _
   have h2:(((k*(τ₀+m+1):ℕ):ℝ)+1)/k>=(τ₀:ℝ)+1:=by
    rw[ge_iff_le,bl (by linarith)]
    push_cast
    nlinarith
   have h3:=b7 t9 (aae k hk (τ₀+m)).1
   linarith
  rw[max_eq_left ae9,ob]
  calc (1-1/(k:ℝ))*wb k (τ₀+m)
    <= (1-1/(k:ℝ))*((1-1/(k:ℝ))^m*((k:ℝ)*(k-1)/2)):=
        ab ih t9
   _=(1-1/(k:ℝ))^m*(1-1/(k:ℝ))*((k:ℝ)*(k-1)/2):=by ring
end bt.au4
end
section
namespace bt.ZFR
open Complex Set Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
lemma ada (x:ℝ):0<=3+4*fo x+fo (2*x):=by
 rw[Real.cos_two_mul]; nlinarith[c4 (1+fo x)]
lemma wk {n:ℕ} (hn:n≠0) (σ γ:ℝ):
  (dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+γ*I) n).re=
   Λ n*af (-σ*aa n)*fo (γ*aa n):=by
 rw[rj hn]
 have v8:(n:ℂ)≠0:=by exact_mod_cast hn
 rw[jx,<- cpow_neg,cpow_def_of_ne_zero v8]
 have ur:Complex.log (n:ℂ)=(aa n:ℂ):=by
  rw[<- m7,j8 (av n)]
 rw[ur]
 have e:(aa n:ℂ)*-((σ:ℂ)+γ*I)=
   ((-σ*aa n:ℝ):ℂ)+((-(γ*aa n):ℝ):ℂ)*I:=by push_cast; ring
 rw[e,Complex.exp_add_mul_I,<- ou,<- Complex.ofReal_cos,<- Complex.ofReal_sin]
 simp only[mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_im,add_im]
 rw[Real.cos_neg]
 ring
lemma zk {s:ℂ} (hs:1<s.re):Summable (dt (fun n:ℕ=>(Λ n:ℂ)) s):=
 ArithmeticFunction.LSeriesSummable_vonMangoldt hs
theorem ahk {σ γ:ℝ} (hσ:1<σ):
  0<=3*(-logDeriv riemannZeta (σ:ℂ)).re+
   4*(-logDeriv riemannZeta ((σ:ℂ)+γ*I)).re+
   (-logDeriv riemannZeta ((σ:ℂ)+((2*γ:ℝ):ℂ)*I)).re:=by
 have hL:∀ γ':ℝ,-logDeriv riemannZeta ((σ:ℂ)+γ'*I)=
   LSeries (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+γ'*I):=by
  intro γ'
  have hs:1<((σ:ℂ)+γ'*I).re:=by simp; exact hσ
  rw[ka hs,g9,
   p9]
 have h0:=hL 0
 simp only[ofReal_zero,zero_mul,ij] at h0
 rw[h0,hL γ,hL (2*γ)]
 have hs:∀ γ':ℝ,1<((σ:ℂ)+γ'*I).re:=fun γ'=>by simp; exact hσ
 have xc:1<(σ:ℂ).re:=by simp; exact hσ
 have af3:=zk xc
 have aeh:=zk (hs γ)
 have ai8:=zk (hs (2*γ))
 unfold LSeries
 rw[qk af3,qk aeh,qk ai8,
  <- pj,<- pj]
 have sa:Summable fun n=>3*(dt (fun n:ℕ=>(Λ n:ℂ)) (σ:ℂ) n).re:=by
  simpa using (rl.summable af3).mul_left 3
 have sb:Summable fun n=>4*(dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+γ*I) n).re:=by
  simpa using (rl.summable aeh).mul_left 4
 have sc:Summable fun n=>(dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+((2*γ:ℝ):ℂ)*I) n).re:=by
  simpa using (rl.summable ai8)
 have e:∑' n,(3*(dt (fun n:ℕ=>(Λ n:ℂ)) (σ:ℂ) n).re+
   4*(dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+γ*I) n).re+
   (dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+((2*γ:ℝ):ℂ)*I) n).re)=
   ∑' n,3*(dt (fun n:ℕ=>(Λ n:ℂ)) (σ:ℂ) n).re+
   ∑' n,4*(dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+γ*I) n).re+
   ∑' n,(dt (fun n:ℕ=>(Λ n:ℂ)) ((σ:ℂ)+((2*γ:ℝ):ℂ)*I) n).re:=by
  rw[(sa.add sb).tsum_add sc,sa.tsum_add sb]
 rw[<- e]
 apply tsum_nonneg
 intro n
 rcases eq_or_ne n 0 with rfl | hn
 ·simp
 have h0':(dt (fun n:ℕ=>(Λ n:ℂ)) (σ:ℂ) n).re=Λ n*af (-σ*aa n):=by
  have:=wk hn σ 0
  simp only[ofReal_zero,zero_mul,ij,Real.cos_zero,di] at this
  exact this
 rw[h0',wk hn,wk hn]
 have hΛ:0<=Λ n:=ArithmeticFunction.vonMangoldt_nonneg
 have he:0<af (-σ*aa n):=bx _
 have bcc:=ada (γ*aa n)
 rw[show 2*γ*aa n=2*(γ*aa n) by ring]
 have:0<=Λ n*af (-σ*aa n):=b7 hΛ he.le
 nlinarith
theorem z4:∃ xg > 0,∃ abe:ℝ,∀ η:ℝ,0<η->η<xg->
  (-logDeriv riemannZeta ((1+η:ℝ):ℂ)).re<=1/η+abe:=by
 obtain ⟨C,hC⟩:=log_deriv_riemannZeta_add_inv_sub_bounded.bound
 rw[eventually_nhdsWithin_iff,Metric.eventually_nhds_iff] at hC
 obtain ⟨ε,hε,af4⟩:=hC
 refine ⟨ε,hε,C,fun η hη azu=>?_⟩
 set s:ℂ:=((1+η:ℝ):ℂ) with hs
 have uu:s≠1:=by
  intro h; have:=dy re h; simp[hs] at this; linarith
 have hd:dist s 1<ε:=by
  rw[b8,hs]
  have:((1+η:ℝ):ℂ)-1=(η:ℂ):=by push_cast; ring
  rw[this,ba,au,a7 hη]; exact azu
 have hb:=af4 hd uu
 simp only[norm_one,di] at hb
 set X:ℂ:=deriv riemannZeta s/riemannZeta s+(s-1)⁻¹ with hX
 have hinv:(s-1)⁻¹=((1/η:ℝ):ℂ):=by
  rw[hs]; push_cast; ring
 have e:-logDeriv riemannZeta s=((1/η:ℝ):ℂ)-X:=by
  rw[g9,hX,<- hinv]; ring
 rw[e,sub_re,ofReal_re]
 have h1:=cm X
 have h2:=neg_le_abs X.re
 linarith
lemma ux {a:ℝ} (ha:0<a) (N:ℕ):
  ∑ n∈bk N,(n:ℝ)^(-(1+a))<=1+1/a:=by
 have u5:∀ M:ℕ,∑ n∈bk (M+2),(n:ℝ)^(-(1+a))<=1+1/a:=by
  intro M
  rw[fq,fq]
  have hint:∑ i∈bk M,((i+1+1:ℕ):ℝ)^(-(1+a))<=
    ∫ u in (1:ℝ)..1+M,u^(-(1+a)):=by
   have:=lx (x₀:=1) (a:=M) (f:=fun u:ℝ=>u^(-(1+a)))
    (by
     intro u hu v _ huv
     exact c1 (by linarith[hu.1]) huv (by linarith))
   refine br (i6 ?_) this
   apply ai rfl
   intro i _
   push_cast; ring_nf
  have hM:(0:ℝ)<=M:=av M
  have hI:∫ u in (1:ℝ)..1+M,u^(-(1+a))=((1+M)^(-a)-1)/(-a):=by
   rw[pn (Or.inr ⟨by linarith,by
    rw[gj (by linarith)]; norm_num⟩)]
   rw[show -(1+a)+1=-a by ring,oi]
  have tj:0<=(1+(M:ℝ))^(-a):=by positivity
  have hI':((1+M)^(-a)-1)/(-a)<=1/a:=by
   rw[ss,<- p9]
   apply a4 (by linarith) ha.le
  have h0:((0:ℕ):ℝ)^(-(1+a))=0:=by
   rw[mw]; exact qu (by linarith)
  have h1:((0+1:ℕ):ℝ)^(-(1+a))=1:=by simp
  rw[h0,h1]
  linarith
 calc ∑ n∈bk N,(n:ℝ)^(-(1+a))
   <= ∑ n∈bk (N+2),(n:ℝ)^(-(1+a)):=
       aq (jn.mpr (by omega))
        (fun _ _ _=>by positivity)
  _<=1+1/a:=u5 N
theorem abf {s:ℂ} (hs:1<s.re):(s.re-1)/s.re<=‖riemannZeta s‖:=by
 have hmul:=qj hs
 rw[rn hs] at hmul
 have af5:Summable fun n:ℕ=>‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖:=
  summable_norm_iff.mpr (mf.mpr hs)
 set a:=s.re-1 with ha
 have ha0:0<a:=by linarith
 have vw:∀ n:ℕ,‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖<=(n:ℝ)^(-(1+a)):=by
  intro n
  rw[r4]
  split_ifs with hn
  ·positivity
  ·have v8:(1:ℝ)<=n:=by exact_mod_cast i8.mpr hn
   have hμ:‖((μ n:ℤ):ℂ)‖<=1:=by
    rw[lf]; exact_mod_cast gg
   calc ‖((μ n:ℤ):ℂ)‖/(n:ℝ)^s.re<=1/(n:ℝ)^s.re:=
         a4 hμ (by positivity)
    _ = (n:ℝ)^(-(1+a)):=by
        rw[ha,show -(1+(s.re-1))=-s.re by ring,iv (by linarith),jz]
 have hL:‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖<=1+1/a:=by
  calc ‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖<=∑' n,‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖:=gw af5
   _ ≤ ∑' n:ℕ,(n:ℝ)^(-(1+a)):=
       ks vw af5 (gr.mpr (by linarith))
   _ ≤ 1+1/a:=
       lh (fun n=>by positivity) (ux ha0)
 have hn:=dy norm hmul
 rw[bo,norm_one] at hn
 have ug:0<‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖:=by
  by_contra h; push_neg at h
  have:‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖=0:=le_antisymm h (aw _)
  rw[this,mul_zero] at hn; exact zero_ne_one hn
 have e1:1+1/a=s.re/a:=by field_simp; ring
 rw[e1] at hL
 have zt:‖riemannZeta s‖=1/‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖:=by
  field_simp; linarith
 rw[zt,ax (by linarith) ug]
 rw[bl ha0] at hL
 nlinarith
end bt.ZFR
namespace bt.zd
open Complex Set Filter Topology Metric
lemma aew {f:ℂ->ℂ} (hf:Differentiable ℂ f) {ρ:ℂ} (uq:analyticOrderAt f ρ≠⊤):
  ∃ g:ℂ->ℂ,Differentiable ℂ g∧g ρ≠0∧
   ∀ z,f z=(z-ρ)^(analyticOrderNatAt f ρ)*g z:=by
 set n:=analyticOrderNatAt f ρ with a7s
 have hn:analyticOrderAt f ρ=n:=(lk uq).symm
 obtain ⟨g0,a3m,azv,hev⟩:=((hf.analyticAt ρ).analyticOrderAt_eq_natCast).mp hn
 set g:ℂ->ℂ:=fun z=>if z=ρ then g0 ρ else f z/(z-ρ)^n with hg
 refine ⟨g, ?_,by simp[hg,azv], ?_⟩
 ·intro z
  by_cases hz:z=ρ
  ·subst hz
   have:g =ᶠ[𝓝 z] g0:=by
    filter_upwards[hev] with w hw
    by_cases zu:w=z
    ·simp[hg,zu]
    ·simp only[hg,if_neg zu,hw,fx]
     rw[jb _ (l7 _ (cb.mpr zu))]
   exact a3m.differentiableAt.congr_of_eventuallyEq this
  ·have:g =ᶠ[𝓝 z] fun w=>f w/(w-ρ)^n:=by
    filter_upwards[fw.mem_nhds hz] with w hw
    simp[hg,show w≠ρ from hw]
   refine DifferentiableAt.congr_of_eventuallyEq ?_ this
   exact (hf z).div (by fun_prop) (l7 _ (cb.mpr hz))
 ·intro z
  by_cases hz:z=ρ
  ·subst hz
   have:=hev.self_of_nhds
   simp only[fx] at this
   rw[this]; simp[hg]
  ·simp only[hg,if_neg hz]
   rw[qa _ (l7 _ (cb.mpr hz))]
lemma yb {f:ℂ->ℂ} (hf:Differentiable ℂ f) (uq:∀ ρ,analyticOrderAt f ρ≠⊤)
  (S:Finset ℂ):
  ∃ g:ℂ->ℂ,Differentiable ℂ g∧(∀ ρ∈S,g ρ≠0)∧
   (∀ z,f z=(∏ ρ∈S,(z-ρ)^(analyticOrderNatAt f ρ))*g z)∧
   ∀ w∉S,analyticOrderAt g w=analyticOrderAt f w:=by
 classical
 refine n7 S ?_ ?_
 ·exact ⟨f,hf,by simp,by simp,fun _ _=>rfl⟩
 ·intro a S ha ih
  obtain ⟨g,hg,hgS,hfg,anf⟩:=ih
  have hga:analyticOrderAt g a=analyticOrderAt f a:=anf a ha
  obtain ⟨g',hg',a3n,ang⟩:=aew hg (by rw[hga]; exact uq a)
  have hn:analyticOrderNatAt g a=analyticOrderNatAt f a:=by
   unfold analyticOrderNatAt; rw[hga]
  rw[hn] at ang
  refine ⟨g',hg', ?_, ?_, ?_⟩
  ·intro ρ s8
   rw[fv] at s8
   rcases s8 with rfl | s8
   ·exact a3n
   ·intro h0; apply hgS ρ s8; rw[ang ρ,h0,mul_zero]
  ·intro z; rw[os ha,hfg z,ang z]; ring
  ·intro w hw
   rw[fv,not_or] at hw
   have e:g=(fun z=>(z-a)^(analyticOrderNatAt f a))*g':=funext ang
   have h1:analyticOrderAt g w=
     analyticOrderAt (fun z=>(z-a)^(analyticOrderNatAt f a)) w+analyticOrderAt g' w:=by
    rw[e]; exact o0 (by fun_prop) (hg'.analyticAt w)
   have h0:analyticOrderAt (fun z=>(z-a)^(analyticOrderNatAt f a)) w=0:=
    fm.mpr (Or.inr (l7 _ (cb.mpr hw.1)))
   rw[h0,jy] at h1
   rw[<- h1,anf w hw.2]
lemma wc (ρ z:ℂ) (m:ℕ):
  logDeriv (fun w=>(w-ρ)^m) z=m/(z-ρ):=by
 rw[logDeriv_fun_pow (by fun_prop) m]
 simp[g9,jx]
theorem aiy {f:ℂ->ℂ} (hf:Differentiable ℂ f) (uq:∀ ρ,analyticOrderAt f ρ≠⊤)
  {s6:ℂ} {u:ℝ} (hu:0<u) (ai9:f s6≠0) (S:Finset ℂ)
  (zl:∀ ρ∈S,ρ∈closedBall s6 (11/5*u))
  (aaw:∀ ρ∈closedBall s6 (11/5*u),f ρ=0->ρ∈S)
  {M:ℝ} (hM:1<=M) (hbound:∀ z∈sphere s6 (12/5*u),‖f z‖<=M*‖f s6‖)
  {z:ℂ} (hz:z∈closedBall s6 (2*u)) (zv:f z≠0):
  ‖logDeriv f z-∑ ρ∈S,(analyticOrderNatAt f ρ:ℂ)/(z-ρ)‖<=
   420*(aa M+(∑ ρ∈S,analyticOrderNatAt f ρ)*aa 11+1)/u:=by
 classical
 obtain ⟨g,hg,hgS,hfg,-⟩:=yb hf uq S
 set m:ℂ->ℕ:=fun ρ=>analyticOrderNatAt f ρ with hm
 set N:ℕ:=∑ ρ∈S,m ρ with hN
 set P:ℂ->ℂ:=fun w=>∏ ρ∈S,(w-ρ)^m ρ with hP
 have aaf:∀ w,f w=P w*g w:=hfg
 have acb:∀ w∈closedBall s6 (11/5*u),g w≠0:=by
  intro w hw h0
  by_cases hwS:w∈S
  ·exact hgS w hwS h0
  ·exact hwS (aaw w hw (by rw[aaf w,h0,mul_zero]))
 have arc:g s6≠0:=acb s6 (mem_closedBall_self (by positivity))
 have afa:∀ w∈sphere s6 (12/5*u),(u/5:ℝ)^N<=‖P w‖:=by
  intro w hw
  simp only[hP,ra,la]
  rw[hN,<- fp]
  apply iy (fun _ _=>by positivity)
  intro ρ s8
  apply aj (by positivity)
  have h1:=zl ρ s8
  rw[mem_closedBall,b8] at h1
  rw[mem_sphere,b8] at hw
  have:=qs (w-s6) (ρ-s6)
  have e:(w-s6)-(ρ-s6)=w-ρ:=by ring
  rw[e] at this; linarith
 have ard:‖P s6‖<=(11/5*u:ℝ)^N:=by
  simp only[hP,ra,la]
  rw[hN,<- fp]
  apply iy (fun _ _=>by positivity)
  intro ρ s8
  apply aj (aw _)
  have h1:=zl ρ s8
  rw[mem_closedBall,b8] at h1
  rw[norm_sub_rev]; exact h1
 have anh:∀ w∈closedBall s6 (11/5*u),‖g w‖<=M*‖f s6‖/(u/5)^N:=by
  intro w hw
  apply me (U:=ball s6 (12/5*u)) isBounded_ball
   hg.diffContOnCl
  ·intro v hv
   rw[frontier_ball _ (by positivity)] at hv
   have hPv:=afa v hv
   have avy:0<‖P v‖:=fj (by positivity) hPv
   have hfv:‖f v‖=‖P v‖*‖g v‖:=by rw[aaf,bo]
   calc ‖g v‖=‖f v‖/‖P v‖:=by rw[hfv]; field_simp
    _ ≤ M*‖f s6‖/(u/5)^N:=
        su (by positivity) (hbound v hv) (by positivity) hPv
  ·rw[n3 _ (by positivity)]
   exact closedBall_subset_closedBall (by nlinarith) hw
 have ajr:∀ w∈closedBall s6 (11/5*u),‖g w‖<=M*11^N*‖g s6‖:=by
  intro w hw
  have a3o:‖f s6‖<=‖g s6‖*(11/5*u)^N:=by
   rw[aaf,bo,gx]
   exact ab ard (aw _)
  have hu5:0<(u/5)^N:=by positivity
  have e:(11/5*u:ℝ)^N/(u/5)^N=11^N:=by
   rw[<- l8]; congr 1; field_simp
  calc ‖g w‖<=M*‖f s6‖/(u/5)^N:=anh w hw
   _<=M*(‖g s6‖*(11/5*u)^N)/(u/5)^N:=by gcongr
   _=M*‖g s6‖*((11/5*u)^N/(u/5)^N):=by ring
   _=M*11^N*‖g s6‖:=by rw[e]; ring
 set φ:ℂ->ℂ:=fun w=>deriv g w/g w with abr
 have hφ:DifferentiableOn ℂ φ (ball s6 (11/5*u)):=fun w hw=>
  (((hg.analyticAt w).deriv.differentiableAt).div (hg w)
   (acb w (ball_subset_closedBall hw))).differentiableWithinAt
 obtain ⟨h,hh0,hhd⟩:=(hφ.isExactOn_ball).with_val_at s6 0
 have xm:∀ w∈ball s6 (11/5*u),g w*d6 (-h w)=g s6:=by
  intro w hw
  have yc:DifferentiableOn ℂ (fun w=>g w*d6 (-h w)) (ball s6 (11/5*u)):=
   fun v hv=>((hg v).mul ((hhd v hv).differentiableAt.neg.cexp)).differentiableWithinAt
  have are:EqOn (deriv fun w=>g w*d6 (-h w)) 0 (ball s6 (11/5*u)):=by
   intro v hv
   have hd:HasDerivAt (fun w=>g w*d6 (-h w)) _ v:=
    (hg v).hasDerivAt.mul ((hhd v hv).neg.cexp)
   rw[hd.deriv]
   have hgv:=acb v (ball_subset_closedBall hv)
   simp only[abr,om,ru]
   field_simp
   ring
  have:=(isOpen_ball).is_const_of_deriv_eq_zero (convex_ball s6 _).isPreconnected yc are
   hw (mem_ball_self (by positivity))
  rw[this,hh0,sg,m1,di]
 have tu:∀ w∈ball s6 (11/5*u),(h w).re<=aa M+N*aa 11:=by
  intro w hw
  have hgw:g w=g s6*d6 (h w):=by
   rw[<- xm w hw,gv,<- jc,neg_add_cancel,m1,di]
  have hn:‖g w‖=‖g s6‖*af (h w).re:=by rw[hgw,bo,p5]
  have hr:=ajr w (ball_subset_closedBall hw)
  rw[hn] at hr
  have ani:0<‖g s6‖:=g7.mpr arc
  have hle:af (h w).re<=M*11^N:=by
   have:=hr; rw[gx (M*11^N)] at this
   exact lg this ani
  have tj:0<M*11^N:=by positivity
  have:=(d5 tj).mpr hle
  rw[ca (by positivity) (by positivity),cq] at this
  exact this
 set A:ℝ:=aa M+N*aa 11+1 with ajs
 have hA:0<A:=by
  have h1:=bd hM
  have h2:0<=(N:ℝ)*aa 11:=
   b7 (av _) (bd (by norm_num))
  linarith
 have hBC:∀ v∈closedBall s6 (21/10*u),‖h v‖<=42*A:=by
  intro v hv
  set H:ℂ->ℂ:=fun w=>h (s6+w) with hH
  have u3:∀ w∈ball (0:ℂ) (11/5*u),s6+w∈ball s6 (11/5*u):=by
   intro w hw
   rw[m3] at hw
   rw[mem_ball,b8,j0]; exact hw
  have hHd:DifferentiableOn ℂ H (ball 0 (11/5*u)):=fun w hw=>
   (((hhd (s6+w) (u3 w hw)).differentiableAt).comp w
    (bu.const_add s6)).differentiableWithinAt
  have wd:MapsTo H (ball 0 (11/5*u)) {z | z.re<=A}:=by
   intro w hw
   simp only[o1,hH]
   have:=tu (s6+w) (u3 w hw)
   linarith
  have hH0:H 0=0:=by simp[hH,hh0]
  rw[mem_closedBall,b8] at hv
  have hw:v-s6∈ball (0:ℂ) (11/5*u):=by
   rw[m3]; nlinarith
  have hb:=pg hA hHd wd (by positivity) hw hH0
  simp only[hH,add_sub_cancel] at hb
  refine hb.trans ?_
  have xo:0<11/5*u-‖v-s6‖:=by nlinarith
  rw[ay xo]
  nlinarith[aw (v-s6)]
 have ado:z∈ball s6 (11/5*u):=by
  rw[mem_closedBall] at hz; rw[mem_ball]; nlinarith
 have ahl:‖deriv h z‖<=42*A/(u/10):=by
  apply gu (by positivity)
  ·apply i2
   rw[n3 _ (by positivity)]
   intro v hv
   apply (hhd v ?_).differentiableAt.differentiableWithinAt
   rw[mem_closedBall] at hv hz; rw[mem_ball]
   nlinarith[pq v z s6]
  ·intro v hv
   apply hBC
   rw[mem_sphere] at hv; rw[mem_closedBall] at hz ⊢
   nlinarith[pq v z s6]
 have hdz:deriv h z=φ z:=(hhd z ado).deriv
 have hPz:P z≠0:=fun h0=>zv (by rw[aaf,h0,zero_mul])
 have hgz:g z≠0:=acb z (ball_subset_closedBall ado)
 have hPd:DifferentiableAt ℂ P z:=by simp only[hP]; fun_prop
 have ur:logDeriv f z=logDeriv P z+logDeriv g z:=by
  rw[show f=fun w=>P w*g w from funext aaf]
  exact tf z hPz hgz hPd (hg z)
 have anj:logDeriv P z=∑ ρ∈S,(m ρ:ℂ)/(z-ρ):=by
  have te:∀ ρ∈S,(z-ρ)^m ρ≠0:=fun ρ s8=>(ix.mp hPz) ρ s8
  rw[hP,sj (f:=fun ρ w=>(w-ρ)^m ρ) te (fun ρ _=>by fun_prop)]
  exact ai rfl (fun ρ _=>wc ρ z (m ρ))
 have ajt:logDeriv f z-∑ ρ∈S,(analyticOrderNatAt f ρ:ℂ)/(z-ρ)=deriv h z:=by
  rw[hdz,ur,anj]
  simp only[hm,abr,g9]
  ring
 rw[ajt]
 calc ‖deriv h z‖<=42*A/(u/10):=ahl
  _ = 420*(aa M+(∑ ρ∈S,analyticOrderNatAt f ρ)*aa 11+1)/u:=by
      rw[ajs,hN]; push_cast; field_simp; ring
end bt.zd
namespace bt.abg
open Complex Set Filter Topology Metric bt.ZFR bt.zd
def GB (α A vd:ℝ):Prop:=
 ∀ s:ℂ,vd<=|s.im|->1-aa |s.im|^(-α)<=s.re->s.re<=3->
  ‖riemannZeta s‖<=aa |s.im|^A
def ZFR:Prop:=∀ K:ℝ,∃ afb:ℝ,∀ ρ:ℂ,riemannZeta ρ=0->0<ρ.re->afb<=|ρ.im|->
    ρ.re<=1-K*aa (aa |ρ.im|)/aa |ρ.im|
lemma tb {s:ℂ} (hs:s≠1):riemannZeta₁ s=(s-1)*riemannZeta s:=by
 rw[mg hs,<- gv,mul_inv_cancel₀ (cb.mpr hs),iq]
lemma tl (ρ:ℂ):analyticOrderAt riemannZeta₁ ρ≠⊤:=by
 have hA:AnalyticOnNhd ℂ riemannZeta₁ univ:=fun z _=>bg.analyticAt z
 have h2:riemannZeta₁ 2≠0:=by
  rw[tb (by norm_num)]
  exact k1 (by norm_num) (p7 (by norm_num))
 have h0:analyticOrderAt riemannZeta₁ 2=0:=fm.mpr (Or.inr h2)
 exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 2) (mem_univ ρ)
  (by rw[h0]; exact ENat.zero_ne_top)
lemma aag {f:ℂ->ℂ} (hf:Differentiable ℂ f) {U:Set ℂ} {ρ:ℂ} (hU:ρ∈U):
  bn f U ρ=(analyticOrderNatAt f ρ:ℤ):=by
 have hA:AnalyticAt ℂ f ρ:=hf.analyticAt ρ
 have hM:MeromorphicOn f U:=fun z _=>(hf.analyticAt z).meromorphicAt
 rw[qh hM hU,hA.meromorphicOrderAt_eq]
 unfold analyticOrderNatAt
 generalize analyticOrderAt f ρ=k
 induction k using n0 <;> simp
lemma aju {f:ℂ->ℂ} (hf:Differentiable ℂ f) {ρ:ℂ} (uq:analyticOrderAt f ρ≠⊤)
  (h0:f ρ=0):1<=analyticOrderNatAt f ρ:=by
 have tj:analyticOrderAt f ρ≠0:=by
  intro h
  rw[fm] at h
  rcases h with h | h
  ·exact h (hf.analyticAt ρ)
  ·exact h h0
 by_contra v7
 push_neg at v7
 have:analyticOrderNatAt f ρ=0:=by omega
 apply tj
 rw[<- lk uq,this]; rfl
lemma zm:aa 11<5/2:=by
 rw[m6 (by norm_num)]
 have he:=i9
 have h5:(3/2:ℝ)<=af (1/2):=by linarith[cw (1/2:ℝ)]
 have:af (5/2)=af 1*af 1*af (1/2):=by
  rw[<- bs,<- bs]; norm_num
 rw[this]
 have:(2.7182818283:ℝ)*2.7182818283*(3/2)<=af 1*af 1*af (1/2):=by
  apply a8 _ h5 (by norm_num) (by positivity)
  exact a8 he.le he.le (by norm_num) (by positivity)
 linarith
theorem aex {t η u B:ℝ} (ht:4<=|t|) (hη:0<η) (ank:η<=1) (hu:0<u)
  (x8:u<=1/3) (hB:1<=B)
  (hbd:∀ z∈sphere (((1+η:ℝ):ℂ)+t *I) (12/5*u),‖riemannZeta z‖<=B):
  (-logDeriv riemannZeta (((1+η:ℝ):ℂ)+t *I)).re<=
    1+13100*(aa (4*B/η)+1)/u∧
   ∀ ρ,riemannZeta ρ=0->ρ∈closedBall (((1+η:ℝ):ℂ)+t *I) (11/5*u)->
    (-logDeriv riemannZeta (((1+η:ℝ):ℂ)+t *I)).re<=
     1+13100*(aa (4*B/η)+1)/u-(1/((((1+η:ℝ):ℂ)+t *I)-ρ)).re:=by
 classical
 set s6:ℂ:=((1+η:ℝ):ℂ)+t *I with ai9
 have abt:s6.re=1+η:=by simp[ai9]
 have aei:s6.im=t:=by simp[ai9]
 have t8:0< |t|:=by linarith
 have xp:∀ w:ℂ,‖w-s6‖<=12/5*u->w≠1:=by
  intro w hw h
  rw[h] at hw
  have h1:|(1-s6).im|<=‖1-s6‖:=a6 _
  have h2:(1-s6).im=-t:=by rw[sub_im,one_im,aei,zero_sub]
  rw[h2,j1] at h1
  linarith
 have abu:s6≠1:=xp s6 (by rw[i3,jw]; linarith)
 have auh:riemannZeta s6≠0:=p7 (by rw[abt]; linarith)
 have zv:riemannZeta₁ s6≠0:=by
  rw[tb abu]; exact k1 (cb.mpr abu) auh
 have aah:|t| *η/2<=‖riemannZeta₁ s6‖:=by
  rw[tb abu,bo]
  have h1:|t|<=‖s6-1‖:=by
   have:=a6 (s6-1)
   rwa[sub_im,aei,one_im,kg] at this
  have h2:=abf (s:=s6) (by rw[abt]; linarith)
  rw[abt] at h2
  have h3:η/2<=(1+η-1)/(1+η):=by
   rw[show 1+η-1=η by ring,ax (by norm_num) (by linarith)]; nlinarith
  calc |t| *η/2=|t| *(η/2):=by ring
   _ ≤ ‖s6-1‖*‖riemannZeta s6‖:=
       a8 h1 (h3.trans h2) (by linarith) (aw _)
 have hup:∀ w∈sphere s6 (12/5*u),‖riemannZeta₁ w‖<=2*|t| *B:=by
  intro w hw
  have zu:‖w-s6‖=12/5*u:=by rw[mem_sphere,b8] at hw; exact hw
  have hw1:w≠1:=xp w zu.le
  rw[tb hw1,bo]
  have tu:|w.re-(1+η)|<=12/5*u:=by
   have:=cm (w-s6); rwa[sub_re,abt,zu] at this
  have um:|w.im-t|<=12/5*u:=by
   have:=a6 (w-s6); rwa[sub_im,aei,zu] at this
  have hn:‖w-1‖<=2*|t|:=by
   have:=b6 (w-1)
   have h1:|(w-1).re|<=9/5:=by
    rw[sub_re,one_re]; rw[abs_le] at tu ⊢; constructor <;> linarith
   have h2:|(w-1).im|<=|t|+4/5:=by
    rw[sub_im,one_im,kg]
    have:=de w.im t; linarith
   linarith
  calc ‖w-1‖*‖riemannZeta w‖<=(2*|t|)*B:=
        a8 hn (hbd w hw) (aw _) (by linarith)
   _=2*|t| *B:=by ring
 set M:ℝ:=4*B/η with af1
 have w6:1<=M:=by rw[af1,bl hη]; linarith
 have hMf:2*|t| *B<=M*‖riemannZeta₁ s6‖:=by
  calc 2*|t| *B=M*(|t| *η/2):=by
        rw[af1,ki,eq_div_iff hη.ne']; ring
   _<=M*‖riemannZeta₁ s6‖:=ab aah (by linarith)
 have hbound:∀ w∈sphere s6 (12/5*u),‖riemannZeta₁ w‖<=M*‖riemannZeta₁ s6‖:=
  fun w hw=>(hup w hw).trans hMf
 set Z:Set ℂ:={ρ | riemannZeta ρ=0∧ρ∈closedBall s6 (11/5*u)} with hZ
 have azw:Z.Finite:=by
  apply ((isCompact_closedBall s6 (11/5*u)).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0,s8⟩
  exact ⟨s8,h0⟩
 set S:=azw.toFinset with hS
 have aie:∀ ρ∈closedBall s6 (11/5*u),ρ≠1:=by
  intro ρ s8; apply xp; rw[mem_closedBall,b8] at s8; linarith
 have zl:∀ ρ∈S,ρ∈closedBall s6 (11/5*u):=by
  intro ρ s8; rw[hS,an] at s8; exact s8.2
 have av6:∀ ρ∈S,riemannZeta ρ=0:=by
  intro ρ s8; rw[hS,an] at s8; exact s8.1
 have aaw:∀ ρ∈closedBall s6 (11/5*u),riemannZeta₁ ρ=0->ρ∈S:=by
  intro ρ s8 h0
  have yd:=aie ρ s8
  rw[tb yd] at h0
  rw[hS,an]
  exact ⟨(rb.mp h0).resolve_left (cb.mpr yd),s8⟩
 have hS1:∀ ρ∈S,riemannZeta₁ ρ=0:=by
  intro ρ s8; rw[tb (aie ρ (zl ρ s8)),av6 ρ s8,mul_zero]
 have h11:(0:ℝ)<11/5*u:=by linarith
 have h12:(0:ℝ)<12/5*u:=by linarith
 have a3p:1<=M*‖riemannZeta₁ s6‖:=by
  refine br ?_ hMf
  nlinarith[a8 ht hB (by norm_num) (eg t)]
 have hJ:=p8 (c:=s6) (r:=11/5*u) (R:=12/5*u)
  (f:=riemannZeta₁) (by rw[a7 h11]; exact h11)
  (by rw[a7 h11,a7 h12]; linarith) a3p
  (fun z _=>bg.analyticAt z) zv
  (by rw[a7 h12]; exact hbound)
 rw[a7 h11] at hJ
 have anl:0<‖riemannZeta₁ s6‖:=g7.mpr zv
 have hRr:12/5*u/(11/5*u)=12/11:=by
  rw[mul_div_mul_right _ _ hu.ne']; norm_num
 rw[mul_div_cancel_right₀ M anl.ne',hRr] at hJ
 have xh:m0 (bn riemannZeta₁ (closedBall s6 (11/5*u)))
   ⊆ ↑S:=by
  intro w hw
  have hwB:w∈closedBall s6 (11/5*u):=
   (bn riemannZeta₁ _).supportWithinDomain hw
  rw[b9]
  apply aaw w hwB
  by_contra hz
  apply hw
  rw[aag bg hwB]
  have:analyticOrderAt riemannZeta₁ w=0:=fm.mpr (Or.inr hz)
  simp[analyticOrderNatAt,this]
 rw[k7 _ xh] at hJ
 push_cast at hJ
 have hlM:0<=aa M:=bd w6
 have hN:((∑ ρ∈S,analyticOrderNatAt riemannZeta₁ ρ:ℕ):ℝ)<=12*aa M:=by
  have e:((∑ ρ∈S,analyticOrderNatAt riemannZeta₁ ρ:ℕ):ℝ)=
    ∑ ρ∈S,((bn riemannZeta₁ (closedBall s6 (11/5*u)) ρ:ℤ):ℝ):=by
   push_cast
   apply ai rfl
   intro ρ s8
   rw[aag bg (zl ρ s8)]
   norm_cast
  rw[e]
  refine hJ.trans ?_
  have ur:1/12<=aa (12/11):=by
   have:=b5 (show (0:ℝ)<12/11 by norm_num)
   norm_num at this ⊢; linarith
  calc aa M/aa (12/11)<=aa M/(1/12):=
        bb hlM (by norm_num) ur
   _=12*aa M:=by ring
 obtain ⟨sc,hsc⟩:∃ sc:ℂ,
   sc=∑ ρ∈S,(analyticOrderNatAt riemannZeta₁ ρ:ℂ)/(s6-ρ):=⟨_,rfl⟩
 have hL:=aiy bg tl hu zv S
  zl aaw w6 hbound (mem_closedBall_self (by linarith)) zv
 rw[<- hsc] at hL
 have av7:‖logDeriv riemannZeta₁ s6-sc‖<=13100*(aa M+1)/u:=by
  refine hL.trans (a4 ?_ hu.le)
  have av8:=zm
  have ast:0<=aa 11:=bd (by norm_num)
  have:=a8 hN av8.le ast (by linarith)
  nlinarith
 have hev:riemannZeta =ᶠ[𝓝 s6] fun w=>riemannZeta₁ w/(w-1):=by
  filter_upwards[fw.mem_nhds abu] with w hw
  have zu:w≠1:=hw
  rw[tb zu,jb _ (cb.mpr zu)]
 have hld:logDeriv riemannZeta s6=logDeriv riemannZeta₁ s6-1/(s6-1):=by
  rw[(oz hev).self_of_nhds,
   tg (f:=riemannZeta₁) (g:=fun w=>w-1) s6 zv
    (show s6-1≠0 from cb.mpr abu) (bg s6) (by fun_prop)]
  congr 1
  simp[g9]
 have hinv:‖1/(s6-1)‖<=1:=by
  rw[i4,norm_one,dw (g7.mpr (cb.mpr abu))]
  have:=a6 (s6-1)
  rw[sub_im,aei,one_im,kg] at this
  linarith
 have aui:sc.re=∑ ρ∈S,(analyticOrderNatAt riemannZeta₁ ρ:ℝ)*(1/(s6-ρ)).re:=by
  rw[hsc,Complex.re_sum]
  apply ai rfl
  intro ρ _
  rw[jd,<- m7,Complex.re_ofReal_mul]
 have vw:∀ ρ∈S,0<=(1/(s6-ρ)).re:=by
  intro ρ s8
  have yd:ρ.re<1:=by
   by_contra h; push_neg at h; exact ct h (av6 ρ s8)
  rw[jz,Complex.inv_re]
  apply fe _ (Complex.normSq_nonneg _)
  rw[sub_re,abt]; linarith
 have u5:(-logDeriv riemannZeta s6).re<=1+13100*(aa M+1)/u-
   ∑ ρ∈S,(analyticOrderNatAt riemannZeta₁ ρ:ℝ)*(1/(s6-ρ)).re:=by
  rw[hld,neg_sub,sub_re,<- aui]
  have h1:= ot (1/(s6-1))
  have h2:=cm (logDeriv riemannZeta₁ s6-sc)
  rw[abs_le,sub_re] at h2
  linarith[h2.1]
 have af3:0<=∑ ρ∈S,(analyticOrderNatAt riemannZeta₁ ρ:ℝ)*(1/(s6-ρ)).re:=
  cj (fun ρ s8=>b7 (av _) (vw ρ s8))
 refine ⟨by linarith, ?_⟩
 intro ρ yw ahm
 have arf:ρ∈S:=by rw[hS,an]; exact ⟨yw,ahm⟩
 have hm1:(1:ℝ)<=analyticOrderNatAt riemannZeta₁ ρ:=by
  exact_mod_cast aju bg (tl ρ)
   (hS1 ρ arf)
 have a6s:=lb
  (f:=fun ρ=>(analyticOrderNatAt riemannZeta₁ ρ:ℝ)*(1/(s6-ρ)).re)
  (fun ρ s8=>b7 (av _) (vw ρ s8)) arf
 have h1:(1/(s6-ρ)).re<=(analyticOrderNatAt riemannZeta₁ ρ:ℝ)*(1/(s6-ρ)).re:=by
  nlinarith[vw ρ arf]
 linarith[u5]
lemma auj {α α' A A' vd anm:ℝ} (h:GB α A vd) (hα:α<=α') (hA:A<=A') (ht:vd<=anm)
  (ht3:3<=anm):GB α' A' anm:=by
 intro s hs tu arh
 have hs3:3<=|s.im|:=ht3.trans hs
 have hl:1<=aa |s.im|:=by
  have h1:af 1<=|s.im|:=by have:=f7; linarith
  have:=a5 (bx 1) h1; rwa[kt] at this
 have h1:aa |s.im|^(-α')<=aa |s.im|^(-α):=
  al hl (by linarith)
 calc ‖riemannZeta s‖<=aa |s.im|^A:=h s (ht.trans hs) (by linarith) arh
  _<=aa |s.im|^A':=al hl hA
lemma adq {α A vd:ℝ} (hGB:GB α A vd) (hA:0<=A) (hα:0<=α) {T t η θ:ℝ}
  (hT:vd+4<=T) (af6:3<=vd) (htT:T<=|t|) (bdm:|t|<=2*T) (hη:0<η)
  (bcd:η<=θ/5) (zj:θ<=1) (hθ:θ<=(2*aa T)^(-α)):
  ∀ z∈sphere (((1+η:ℝ):ℂ)+t *I) (12/5*(θ/3)),
   ‖riemannZeta z‖<=(2*aa T)^A:=by
 intro z hz
 rw[mem_sphere,b8] at hz
 have tu:|z.re-(1+η)|<=12/5*(θ/3):=by
  have:=cm (z-(((1+η:ℝ):ℂ)+t *I))
  rw[hz] at this
  have e:(z-(((1+η:ℝ):ℂ)+t *I)).re=z.re-(1+η):=by simp
  rwa[e] at this
 have um:|z.im-t|<=12/5*(θ/3):=by
  have:=a6 (z-(((1+η:ℝ):ℂ)+t *I))
  rw[hz] at this
  have e:(z-(((1+η:ℝ):ℂ)+t *I)).im=z.im-t:=by simp
  rwa[e] at this
 have am9:0<=θ:=by linarith
 rw[abs_le] at tu
 have adr:T-1<=|z.im|:=by
  have:=de t z.im; rw[jj] at this; linarith
 have ahn:|z.im|<=2*T+1:=by
  have:=de z.im t; linarith
 have ua:0<T:=by linarith
 have al7:0<aa |z.im|:=eo (by linarith)
 have apn:aa |z.im|<=2*aa T:=by
  calc aa |z.im|<=aa (T^2):=a5 (by linarith) (by nlinarith)
   _=2*aa T:=by rw[cq]; norm_num
 have hrp:θ<=aa |z.im|^(-α):=
  hθ.trans (c1 al7 apn (by linarith))
 calc ‖riemannZeta z‖<=aa |z.im|^A:=hGB z (by linarith) (by linarith) (by linarith)
  _<=(2*aa T)^A:=dh al7.le apn hA
theorem ari {α A vd:ℝ} (hGB:GB α A vd) (bdn:1/2<=α) (bdo:α<1) (hA:0<=A)
  (af6:3<=vd):ZFR:=by
 obtain ⟨xg,ajv,abe,azx⟩:=z4
 intro K
 obtain ⟨c,ajw⟩:∃ c:ℝ,c=2000000*(A+4):=⟨_,rfl⟩
 have t9:0<c:=by rw[ajw]; linarith
 have hc5:5<=c:=by rw[ajw]; linarith
 obtain ⟨K',al8⟩:∃ K':ℝ,K'=max K 0:=⟨_,rfl⟩
 have a3q:K<=K':=by rw[al8]; exact bq _ _
 have bdp:0<=K':=by rw[al8]; exact cd _ _
 obtain ⟨ε,al9⟩:∃ ε:ℝ,ε=1-α:=⟨_,rfl⟩
 have hε:0<ε:=by rw[al9]; linarith
 obtain ⟨X₀,ann⟩:∃ X₀:ℝ,X₀=max (max 1 (4*(3*|abe|+5))) (2/xg):=⟨_,rfl⟩
 have hX1:1<=X₀:=by rw[ann]; exact br (bq _ _) (bq _ _)
 have hX2:4*(3*|abe|+5)<=X₀:=by rw[ann]; exact br (cd _ _) (bq _ _)
 have hX3:2/xg<=X₀:=by rw[ann]; exact cd _ _
 have e1:∀ᶠ L:ℝ in atTop,X₀<=aa L:=rm.eventually_ge_atTop X₀
 have e2:∀ᶠ L:ℝ in atTop,c*aa L<=L^(1/2:ℝ):=by
  have h:=(m4 (r:=1/2) (by norm_num)).bound (uc.mpr t9)
  filter_upwards[h,eventually_ge_atTop (1:ℝ)] with L hL hL1
  rw[au,au,bh (bd hL1),
   bh (ei (by linarith) _)] at hL
  calc c*aa L<=c*(1/c*L^(1/2:ℝ)):=ab hL t9.le
   _=L^(1/2:ℝ):=by rw[<- gv,kh t9.ne',iq]
 have e3:∀ᶠ L:ℝ in atTop,14*c*K'*aa L^2<=L^ε:=by
  obtain ⟨d,hd⟩:∃ d:ℝ,d=14*c*K':=⟨_,rfl⟩
  have hd0:0<=d:=by rw[hd]; positivity
  have h:=(m4 (r:=ε/2) (by linarith)).bound
   (uc.mpr (show (0:ℝ)<d+1 by linarith))
  filter_upwards[h,eventually_ge_atTop (1:ℝ)] with L hL hL1
  rw[au,au,bh (bd hL1),
   bh (ei (by linarith) _)] at hL
  have vc:0<L:=by linarith
  have hpow:(L^(ε/2))^2=L^ε:=by
   rw[<- da,<- d7 vc.le]; congr 1; push_cast; ring
  have aax:=bd hL1
  have h2:aa L^2<=(1/(d+1))^2*L^ε:=by
   rw[<- hpow,<- i5]; exact aj aax hL 2
  rw[<- hd]
  have a3r:0<=L^ε:=ei vc.le _
  have hdd:d*(1/(d+1))^2<=1:=by
   rw[l8,sf,m8,dw (by positivity)]; nlinarith
  calc d*aa L^2<=d*((1/(d+1))^2*L^ε):=ab h2 hd0
   _=(d*(1/(d+1))^2)*L^ε:=by ring
   _<=1*L^ε:=ag hdd a3r
   _=L^ε:=iq _
 obtain ⟨L₁,azy⟩:=eventually_atTop.mp (e1.and (e2.and e3))
 refine ⟨max (vd+4) (af L₁),fun ρ yw bcf hT=>?_⟩
 have bdq:ρ.re<1:=by
  by_contra h; push_neg at h; exact ct h yw
 obtain ⟨T,aai⟩:∃ T,T=|ρ.im|:=⟨_,rfl⟩
 rw[<- aai] at hT ⊢
 have hT4:vd+4<=T:=(bq _ _).trans hT
 have hTe:af L₁<=T:=(cd _ _).trans hT
 have ua:0<T:=by linarith
 obtain ⟨L,ads⟩:∃ L,L=aa T:=⟨_,rfl⟩
 rw[<- ads]
 have awb:L₁<=L:=by
  rw[ads]; have:=a5 (bx _) hTe; rwa[kt] at this
 obtain ⟨hX,hc2,hc3⟩:=azy L awb
 obtain ⟨tz,afc⟩:∃ tz,tz=aa L:=⟨_,rfl⟩
 rw[<- afc] at hX hc2 hc3 ⊢
 have ano:1<=tz:=hX1.trans hX
 have ug:0<L:=by rw[ads]; exact eo (by linarith)
 have hLe:af 1<=L:=by
  rw[<- fl ug,<- afc]; exact b4.mpr ano
 have hL2:2<=L:=by have:=i9; linarith
 have h2L:1<=2*L:=by linarith
 have af8:0<2*L:=by linarith
 obtain ⟨θ,abv⟩:∃ θ:ℝ,θ=(2*L)^(-α):=⟨_,rfl⟩
 have adt:0<θ:=by rw[abv]; exact dc af8 _
 have zj:θ<=1:=by rw[abv]; exact er h2L (by linarith)
 have awd:1/(2*L)<=θ:=by
  rw[abv,jz,<- o2]
  exact al h2L (by linarith)
 have ajx:θ=(2:ℝ)^(-α)*L^(-α):=by
  rw[abv,e6 (by norm_num) ug.le]
 have h2a:(2:ℝ)^(-α)<=1:=er (by norm_num) (by linarith)
 have h2b:(1/2:ℝ)<=(2:ℝ)^(-α):=by
  rw[show (1/2:ℝ)=(2:ℝ)^(-1:ℝ) by rw[o2]; norm_num]
  exact al (by norm_num) (by linarith)
 have hLa:L^(-α)<=L^(-(1/2:ℝ)):=
  al (by linarith) (by linarith)
 have awe:0<L^(-α):=dc ug _
 have auk:c*tz*θ<=1:=by
  have h1:θ<=L^(-(1/2:ℝ)):=by
   rw[ajx]
   calc (2:ℝ)^(-α)*L^(-α)<=1*L^(-α):=ag h2a awe.le
    _=L^(-α):=iq _
    _<=L^(-(1/2:ℝ)):=hLa
  have h2:L^(1/2:ℝ)*L^(-(1/2:ℝ))=1:=by
   rw[<- c6 ug]; norm_num
  calc c*tz*θ<=L^(1/2:ℝ)*L^(-(1/2:ℝ)):=
        a8 hc2 h1 adt.le (ei ug.le _)
   _=1:=h2
 have aja:0<c*tz:=ji t9 (by linarith)
 obtain ⟨η,aab⟩:∃ η:ℝ,η=θ/(c*tz):=⟨_,rfl⟩
 have ye:0<η:=by rw[aab]; exact mo adt aja
 have awf:θ^2<=η:=by
  rw[aab,bl aja]
  linarith[ab auk adt.le]
 have apr:η<=θ/5:=by
  rw[aab]
  exact bb adt.le (by norm_num)
   (by linarith[a8 hc5 ano (by norm_num) t9.le])
 have aps:η<=1/tz:=by
  rw[aab,ax aja (by linarith)]
  linarith[ag zj (by linarith:(0:ℝ)<=tz),
   ag (by linarith:(1:ℝ)<=c) (by linarith:(0:ℝ)<=tz)]
 have ank:η<=1:=aps.trans (by rw[dw (by linarith)]; exact ano)
 have arj:η<xg:=by
  have h1:2<=tz*xg:=by have:=hX3.trans hX; rwa[ay ajv] at this
  have h2:1/tz<=xg/2:=by rw[ax (by linarith) (by norm_num)]; linarith
  linarith
 have bdr:η*(3*|abe|+5)<=1/4:=by
  have h4:4*(3*|abe|+5)<=tz:=hX2.trans hX
  calc η*(3*|abe|+5)<=(1/tz)*(3*|abe|+5):=
        ag aps (by positivity)
   _<=1/4:=by rw[ki,iq,ay (by linarith)]; linarith
 obtain ⟨B,ajy⟩:∃ B:ℝ,B=(2*L)^A:=⟨_,rfl⟩
 have hB1:1<=B:=by rw[ajy]; exact e5 h2L hA
 have asy:θ<=(2*aa T)^(-α):=by rw[<- ads,abv]
 have asz:=adq hGB hA (by linarith) (T:=T) (t:=ρ.im) (η:=η) (θ:=θ) hT4 af6
  (by rw[aai]) (by rw[aai]; linarith[eg ρ.im]) ye apr zj asy
 have as0:=adq hGB hA (by linarith) (T:=T) (t:=2*ρ.im) (η:=η) (θ:=θ) hT4 af6
  (by rw[n4,abs_two,<- aai]; linarith) (by rw[n4,abs_two,<- aai])
  ye apr zj asy
 rw[<- ads,<- ajy] at asz as0
 have yf:0<θ/3:=mo adt (by norm_num)
 have x8:θ/3<=1/3:=by linarith
 have hT7:4<=|ρ.im|:=by rw[<- aai]; linarith
 have h2T:4<=|2*ρ.im|:=by rw[n4,abs_two,<- aai]; linarith
 obtain ⟨hA1,awg⟩:=aex hT7 ye ank yf x8 hB1 asz
 obtain ⟨hA2,-⟩:=aex h2T ye ank yf x8 hB1 as0
 obtain ⟨E,hE⟩:∃ E:ℝ,E=13100*(aa (4*B/η)+1)/(θ/3):=⟨_,rfl⟩
 rw[<- hE] at hA1 awg hA2
 have anp:4*B/η<=4*B*(2*L)^2:=by
  rw[ay ye]
  have h1:(1/(2*L))^2<=θ^2:=aj (by positivity) awd 2
  have h2:(2*L)^2*(1/(2*L))^2=1:=by
   rw[<- i5,kh af8.ne',sf]
  have h3:1<=(2*L)^2*η:=by
   calc (1:ℝ)=(2*L)^2*(1/(2*L))^2:=h2.symm
    _<=(2*L)^2*θ^2:=ab h1 (by positivity)
    _<=(2*L)^2*η:=ab awf (by positivity)
  linarith[ab h3 (show (0:ℝ)<=4*B by linarith)]
 have anq:aa (4*B/η)+1<=(2*A+8)*tz:=by
  have h1:aa (4*B/η)<=aa (4*B*(2*L)^2):=
   a5 (mo (by linarith) ye) anp
  have h2:aa (4*B*(2*L)^2)=
    aa 4+A*aa (2*L)+2*aa (2*L):=by
   rw[ca (ne_of_gt (by linarith:(0:ℝ)<4*B)) (l7 2 af8.ne'),
    ca (by norm_num) (ne_of_gt (by linarith:(0:ℝ)<B)),ajy,
    oj af8,cq]
   push_cast; ring
  have h3:aa (2*L)=aa 2+tz:=by
   rw[ca (by norm_num) ug.ne',afc]
  have h4:aa 4<=3:=by
   have:=bz (show (0:ℝ)<4 by norm_num); linarith
  have h5:aa 2<1:=by have:=Real.log_two_lt_d9; linarith
  have h6:0<=aa 2:=bd (by norm_num)
  rw[h2,h3] at h1
  linarith[ab h5.le hA,b7 (by linarith:(0:ℝ)<=A+6)
   (by linarith:(0:ℝ)<=tz-1)]
 have bds:E*η<=1/20:=by
  have e:E*η=39300*(aa (4*B/η)+1)/(c*tz):=by
   rw[hE,aab]; field_simp; ring
  rw[e,ay aja,ajw]
  linarith[b7 (by linarith:(0:ℝ)<=A+4) (by linarith:(0:ℝ)<=tz)]
 have bdt:=ahk (σ:=1+η) (γ:=ρ.im) (by linarith)
 have hX0:=azx η ye arj
 have amb:(((1+η:ℝ):ℂ)+(ρ.im:ℂ)*I)-ρ=((1+η-ρ.re:ℝ):ℂ):=by
  apply kn <;> simp
 have anr:0<1+η-ρ.re:=by linarith
 have af9:η/7<=1-ρ.re:=by
  by_cases hin:ρ∈closedBall (((1+η:ℝ):ℂ)+(ρ.im:ℂ)*I) (11/5*(θ/3))
  ·have hb:=awg ρ yw hin
   rw[amb] at hb
   have tu:(1/((1+η-ρ.re:ℝ):ℂ)).re=1/(1+η-ρ.re):=by
    rw[<- Complex.ofReal_one,<- Complex.ofReal_div,o8]
   rw[tu] at hb
   have bcg:=k6 abe
   have key:4*(1/(1+η-ρ.re))<=3*(1/η)+3*|abe|+5+5*E:=by
    linarith
   have hy:(1/(1+η-ρ.re))*(1+η-ρ.re)=1:= one_div_mul_cancel anr.ne'
   have a75:η*(1/η)=1:=kh ye.ne'
   have k2:=ab key ye.le
   have k3:4*η*(1/(1+η-ρ.re))<=7/2:=by linarith
   have k4:=ag k3 anr.le
   have hy':η*((1/(1+η-ρ.re))*(1+η-ρ.re))=η:=by rw[hy,di]
   linarith
  ·rw[mem_closedBall,b8,not_le] at hin
   have:‖ρ-(((1+η:ℝ):ℂ)+(ρ.im:ℂ)*I)‖=1+η-ρ.re:=by
    rw[<- norm_neg,neg_sub,amb,ba,au,a7 anr]
   rw[this] at hin
   linarith
 have bdu:L^ε/2<=θ*L:=by
  rw[ajx]
  have h1:L^(-α)*L=L^ε:=by
   rw[al9,show (1-α)=-α+1 by ring,c6 ug,fi]
  calc L^ε/2=(1/2)*L^ε:=by ring
   _<=(2:ℝ)^(-α)*L^ε:=ag h2b (ei ug.le _)
   _=(2:ℝ)^(-α)*L^(-α)*L:=by rw[gv,h1]
 have uq:K'*tz/L<=η/7:=by
  rw[ay ug,aab]
  have:θ/(c*tz)/7*L=θ*L/(7*c*tz):=by ring
  rw[this,bl (ji (ji (by norm_num) t9) (by linarith))]
  linarith
 have hKK:K*tz/L<=K'*tz/L:=
  a4 (ag a3q (by linarith)) ug.le
 linarith
theorem apt:(∃ α<1,∃ A vd,GB α A vd)->ZFR:=by
 rintro ⟨α,hα,A,vd,h⟩
 exact ari (auj h (bq α (1/2)) (bq A 0) (bq vd 3)
  (cd _ _)) (cd _ _) (max_lt hα (by norm_num)) (cd _ _)
  (cd _ _)
end bt.abg
end
section
namespace bt.abw
open Complex Real Filter Finset
def abx (T:ℝ):Set ℂ:={ρ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T}
lemma ts {ρ:ℂ} (h:riemannZeta ρ=0):ρ.re<1:=by
 by_contra h'
 exact ct (not_lt.mp h') h
lemma aby (T:ℝ):(abx T).Finite:=by
 apply ((isCompact_closedBall (0:ℂ) (T+1)).inter_riemannZetaZeros_finite).subset
 rintro ρ ⟨h0,tu,um⟩
 refine ⟨?_,h0⟩
 rw[dj,l9]
 have h1:=ts h0
 have:=b6 ρ
 rw[a7 tu] at this
 linarith
lemma afd (afb:ℝ):∃ xg:ℝ,0<xg∧∀ ρ:ℂ,riemannZeta ρ=0->0<ρ.re->
  |ρ.im|<=afb->ρ.re<=1-xg:=by
 classical
 set F:=(aby afb).toFinset
 by_cases te:F.Nonempty
 ·obtain ⟨as2,awi,avl⟩:=F.exists_min_image (fun ρ=>1-ρ.re) te
  have aul:as2∈abx afb:=(an _).mp awi
  refine ⟨1-as2.re,by linarith[ts aul.1],fun ρ h0 tu um=>?_⟩
  have:=avl ρ ((an _).mpr ⟨h0,tu,um⟩)
  linarith
 ·refine ⟨1,one_pos,fun ρ h0 tu um=>?_⟩
  exact absurd ⟨ρ,(an _).mpr ⟨h0,tu,um⟩⟩ te
lemma acd {a b:ℝ} (ha:0<a) (hab:a<=b) {ρ:ℂ} (s8:ρ≠0)
  (tu:ρ.re<=1):
  ‖((b:ℂ)^ρ-(a:ℂ)^ρ)/ρ‖<=(b-a)*a^(ρ.re-1):=by
 have adu:∀ u∈i7 a b,HasDerivWithinAt (fun y:ℝ=>(y:ℂ)^ρ/ρ)
   ((u:ℂ)^(ρ-1)) (i7 a b) u:=by
  intro u hu
  have yf:u≠0:=(fj ha hu.1).ne'
  have:=hasDerivAt_ofReal_cpow_const' yf (r:=ρ-1) (by
   intro h; apply s8; linear_combination h)
  simp only[sub_add_cancel] at this
  exact this.hasDerivWithinAt
 have hbound:∀ u∈i7 a b,‖(u:ℂ)^(ρ-1)‖<=a^(ρ.re-1):=by
  intro u hu
  have yf:0<u:=fj ha hu.1
  rw[e9 yf]
  simp only[sub_re,one_re]
  exact c1 ha hu.1 (by linarith)
 have:=(convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le adu hbound
  (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
 rw[<- sub_div] at this
 rw[au,bh (by linarith)] at this
 linarith
lemma alo (F:Finset ℂ) (m:ℂ->ℝ) (hm:∀ ρ,0<=m ρ) {x η:ℝ} (hx:1<=x)
  {J:ℕ} (hJ:0<J) (hJx:aa x<=J)
  (hF:∀ ρ∈F,0<=ρ.re∧ρ.re<=1-η∧ρ.re<1):
  ∑ ρ∈F,m ρ*x^(ρ.re-1)<=
   af 1*∑ j∈(range J).filter (fun j:ℕ=>(j:ℝ)/J<=1-η),
    x^((j:ℝ)/J-1)*∑ ρ∈F.filter (fun ρ=>(j:ℝ)/J<=ρ.re),m ρ:=by
 classical
 have aga:(0:ℝ)<J:=by exact_mod_cast hJ
 have tp:0<x:=by linarith
 set JF:=(range J).filter (fun j:ℕ=>(j:ℝ)/J<=1-η) with hJF
 set g:ℕ->ℂ->ℝ:=fun j ρ=>
  if (j:ℝ)/J<=ρ.re then af 1*(x^((j:ℝ)/J-1)*m ρ) else 0 with hg
 have hg0:∀ j ρ,0<=g j ρ:=by
  intro j ρ; simp only[hg]; split_ifs
  ·exact b7 (bx 1).le (b7 (by positivity) (hm ρ))
  ·exact le_refl 0
 have a3s:∀ ρ∈F,m ρ*x^(ρ.re-1)<=∑ j∈JF,g j ρ:=by
  intro ρ s8
  obtain ⟨h0,hη,h1⟩:=hF ρ s8
  set xq:=⌊ρ.re *J⌋₊ with bch
  have a6t:(xq:ℝ)<=ρ.re *J:=ju (by positivity)
  have a6u:ρ.re *J<xq+1:=g8 _
  have awk:xq<J:=by
   have:(xq:ℝ)<J:=by nlinarith
   exact_mod_cast this
  have hσ:(xq:ℝ)/J<=ρ.re:=by rw[ay aga]; linarith
  have hσ':ρ.re-(xq:ℝ)/J<=1/J:=by
   rw[sub_le_iff_le_add,<- add_div,bl aga]; linarith
  have vw:m ρ*x^(ρ.re-1)<=af 1*(x^((xq:ℝ)/J-1)*m ρ):=by
   have u8:x^(ρ.re-1)=x^(ρ.re-(xq:ℝ)/J)*x^((xq:ℝ)/J-1):=by
    rw[<- c6 tp]; ring_nf
   have wz:x^(ρ.re-(xq:ℝ)/J)<=af 1:=by
    calc x^(ρ.re-(xq:ℝ)/J)<=x^(1/(J:ℝ)):=
          al hx hσ'
     _ = af (aa x/J):=by
         rw[c9 tp]; ring_nf
     _ ≤ af 1:=by
         apply b4.mpr
         rw[dw aga]; exact hJx
   rw[u8]
   have h2:0<=x^((xq:ℝ)/J-1)*m ρ:=b7 (by positivity) (hm ρ)
   have:=ag wz h2
   linarith
  have u3:xq∈JF:=by
   rw[hJF,ah]; exact ⟨bw.mpr awk,br hσ hη⟩
  have:=lb (fun j _=>hg0 j ρ) u3
  have hgj:g xq ρ=af 1*(x^((xq:ℝ)/J-1)*m ρ):=by
   simp only[hg,if_pos hσ]
  linarith
 calc ∑ ρ∈F,m ρ*x^(ρ.re-1)<=∑ ρ∈F,∑ j∈JF,g j ρ:=ao a3s
  _=∑ j∈JF,∑ ρ∈F,g j ρ:=d0
  _=_:=by
   rw[bc]
   apply ai rfl
   intro j _
   rw[jf,bc,bc]
   apply ai rfl
   intro ρ _
   simp only[hg]
   split_ifs <;> ring
lemma aaj {x:ℕ} {y:ℝ} (h:j9 x<j9 y):
  ∃ p:ℕ,p.Prime∧x<p∧(p:ℝ)<=y:=by
 classical
 by_contra hno
 push_neg at hno
 apply (lt_irrefl _ (fj h _))
 unfold j9
 rw[Nat.floor_natCast]
 apply aq
 ·intro p hp
  simp only[ah,kq] at hp ⊢
  refine ⟨⟨hp.1.1, ?_⟩,hp.2⟩
  by_contra v7
  push_neg at v7
  have hpy:(p:ℝ)<=y:=by
   have h0:(0:ℝ)<=y:=by
    by_contra hy; push_neg at hy
    have:⌊y⌋₊=0:=Nat.floor_eq_zero.mpr (by linarith)
    omega
   exact (Nat.le_floor_iff h0).mp hp.1.2
  exact absurd hpy (not_le.mpr (hno p hp.2 v7))
 ·intro p hp _
  simp only[ah] at hp
  exact bd (by exact_mod_cast hp.2.one_lt.le)
export bt.abg (ZFR)
def ZD:Prop:=∃ A:ℝ,A<3∧∃ B C:ℝ,∀ σ T:ℝ,2<=T->
    (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T},
     (analyticOrderNatAt riemannZeta ρ:ℝ))<=C*T^(A*(1-σ))*aa T^B
def EF:Prop:=∃ C:ℝ,∀ x T:ℝ,2<=x->2<=T->T<=x->
    ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+
     ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T},
      (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=C*x*aa x^2/T
lemma aho (hZ:ZFR) {K:ℝ} (hK:0<=K):∃ ahp:ℝ,∀ T:ℝ,ahp<=T->
  ∀ ρ∈abx T,ρ.re<=1-K*aa (aa T)/aa T:=by
 obtain ⟨afb,azz⟩:=hZ K
 set ans:=max afb (af (af 1))
 obtain ⟨xg,ajv,aah⟩:=afd ans
 have h0:Tendsto (fun u=>aa u/u) atTop (nhds 0):=by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
 have h1:Tendsto (fun T=>K*(aa (aa T)/aa T)) atTop (nhds 0):=by
  simpa using (h0.comp rm).const_mul K
 obtain ⟨ahp,ant⟩:=((h1.eventually (gt_mem_nhds ajv)).and
  (eventually_ge_atTop ans)).exists_forall_of_atTop
 refine ⟨ahp,fun T hT ρ s8=>?_⟩
 obtain ⟨v7,hTT⟩:=ant T hT
 obtain ⟨awl,tu,um⟩:=s8
 rw[jm]
 by_cases wz:|ρ.im|<=ans
 ·have:=aah ρ awl tu wz
  have bdv:K*(aa (aa T)/aa T)<xg:=v7
  linarith
 ·push_neg at wz
  have abh:=azz ρ awl tu (br (bq _ _) wz.le)
  rw[jm] at abh
  have he:af (af 1)<=|ρ.im|:=br (cd _ _) wz.le
  have aej:af 1<=aa |ρ.im|:=by
   rw[d5 (fj (bx _) he)]; exact he
  have aay:aa |ρ.im|<=aa T:=
   a5 (fj (bx _) he) um
  have az0:=Real.log_div_self_antitoneOn (Set.mem_Ici.mpr aej)
   (Set.mem_Ici.mpr (br aej aay)) aay
  have:=ab az0 hK
  simp only at this
  linarith
lemma abz {a b:ℝ} (hab:a<b) (c:ℝ):
  ∀ᶠ x:ℝ in atTop,c*(x^a*aa x^2)<=x^b:=by
 have hr:0<(b-a)/2:=by linarith
 have ho:=(m4 hr).pow (n:=2) two_pos
 have hε:0<1/(|c|+1):=by positivity
 filter_upwards[ho.bound hε,eventually_gt_atTop 0] with x hx tp
 have hxa:0<x^a:=dc tp a
 have hpow:(x^((b-a)/2))^2=x^(b-a):=by
  rw[<- da,<- d7 tp.le]; ring_nf
 rw[la,la,au,au,sq_abs,sq_abs,hpow] at hx
 have u8:x^b=x^a*x^(b-a):=by rw[<- c6 tp]; ring_nf
 have hl:0<=aa x^2:=c4 _
 have hc:c<=|c|:=k6 c
 have hxb:0<x^(b-a):=dc tp _
 have key:|c| *aa x^2<=x^(b-a):=by
  have h1:|c| *aa x^2<=|c| *(1/(|c|+1)*x^(b-a)):=
   ab hx (eg c)
  have h2:|c| *(1/(|c|+1)*x^(b-a))<=x^(b-a):=by
   rw[<- gv,m8]
   have:|c|/(|c|+1)<=1:=by
    rw[dw (by positivity)]; linarith
   nlinarith
  linarith
 rw[u8]
 nlinarith[ag hc (b7 hxa.le hl)]
lemma anu {x T A θ₁ δ K B σ:ℝ} (hx:1<x) (hT:T=x^(1-θ₁)) (amc:0<=θ₁)
  (adv:θ₁<1) (uf:δ=1-A*(1-θ₁)) (ab0:0<δ) (hK:δ*K=B+3) (ya:0<=K)
  (as4:1<=aa T) (hσ:K*aa (aa T)/aa T<=1-σ):
  x^(σ-1)*T^(A*(1-σ))*aa T^B<=1/aa T^3:=by
 have tp:0<x:=by linarith
 have hlx:0<aa x:=eo hx
 have ua:0<T:=by rw[hT]; exact dc tp _
 have hLT:aa T=(1-θ₁)*aa x:=by rw[hT,oj tp]
 have anv:0<aa T:=by linarith
 set L:=aa (aa T) with hL
 have vc:0<=L:=bd as4
 have az1:af L=aa T:=fl anv
 rw[c9 tp,c9 ua,c9 anv,<- hL,
  <- bs,<- bs]
 have a3t:1/aa T^3=af (-(3*L)):=by
  rw[kv,<- az1,<- db]; push_cast; rw[jz]
 rw[a3t,b4]
 have h1:K*L<=(1-σ)*aa T:=by
  rw[ay anv] at hσ; linarith
 have h2:0<=1-σ:=by
  have:0<=K*L/aa T:=fe (b7 ya vc) anv.le
  linarith
 have h3:aa T<=aa x:=by rw[hLT]; nlinarith
 have h4:(1-σ)*aa T<=(1-σ)*aa x:=ab h3 h2
 have h5:δ*(K*L)<=δ*((1-σ)*aa x):=
  ab (br h1 h4) ab0.le
 have h6:δ*(K*L)=(B+3)*L:=by rw[<- gv,hK]
 rw[hLT,uf] at *
 nlinarith
set_option maxHeartbeats 4000000 in
theorem aen (hZ:ZFR) (hD:ZD) (hE:EF):
  ∃ θ:ℝ,θ<2/3∧∃ C:ℝ,∀ x:ℕ,2<=x->
   ∃ p:ℕ,p.Prime∧x<p∧(p:ℝ)<=x+C*(x:ℝ)^θ:=by
 classical
 obtain ⟨aj0,az2,aj1,CD,hCD⟩:=hD
 obtain ⟨CE,hCE⟩:=hE
 set A:=max aj0 2 with as5
 have hA2:2<=A:=cd _ _
 have hA3:A<3:=max_lt az2 (by norm_num)
 set B:=max aj1 0 with bci
 have hB0:0<=B:=cd _ _
 set yg:=max CD 0 with a8a
 set CE':=max CE 0 with a8b
 set a:=1-1/A with ha
 have agb:0<A:=by linarith
 have ha1:1/2<=a:=by
  have:1/A<=1/2:=by rw[ax agb two_pos]; linarith
  linarith
 have ha2:a<2/3:=by
  have:1/3<1/A:=by rw[div_lt_div_iff₀ (by norm_num) agb]; linarith
  linarith
 set θ₁:=a+(2/3-a)/3 with adv
 set θ:=a+2*(2/3-a)/3 with hθ
 set δ:=1-A*(1-θ₁) with uf
 have ab0:0<δ:=by
  have hA1:A*(1-a)=1:=by rw[ha]; field_simp; ring
  have:A*(1-θ₁)<A*(1-a):=by
   apply mul_lt_mul_of_pos_left _ agb; rw[adv]; linarith
  linarith
 set K:=(B+3)/δ with as7
 have ya:0<=K:=fe (by linarith) ab0.le
 have a3u:δ*K=B+3:=by rw[as7]; field_simp
 obtain ⟨ahp,ant⟩:=aho hZ ya
 have amc:0<=θ₁:=by rw[adv]; linarith
 have aum:θ₁<1:=by rw[adv]; linarith
 have ark:θ₁<θ:=by rw[adv,hθ]; linarith
 have aun:1/2<θ:=by rw[hθ]; linarith
 have az3:θ<2/3:=by rw[hθ]; linarith
 have anw:(1:ℝ)-θ₁ > 0:=by linarith
 have ev:=(((eventually_ge_atTop (max 2 (af 1))).and
  ((tendsto_rpow_atTop anw).eventually_ge_atTop
   (max (max 2 ahp) (af (24*af 1*yg+1))))).and
  ((abz ark (64*CE')).and (abz aun 48)))
 obtain ⟨X,hX⟩:=ev.exists_forall_of_atTop
 refine ⟨θ,az3,max 1 (⌈X⌉₊:ℝ),fun x hx2=>?_⟩
 have bdw:(2:ℝ)<=x:=by exact_mod_cast hx2
 have tp:(0:ℝ)<x:=by linarith
 have bcj:1<=(x:ℝ)^θ:=e5 (by linarith) (by linarith)
 by_cases hxX:X<=(x:ℝ)
 swap
 ·
  push_neg at hxX
  obtain ⟨p,hp,v7,hle⟩:= od x (by omega)
  refine ⟨p,hp,v7, ?_⟩
  have hpR:(p:ℝ)<=2*x:=by exact_mod_cast hle
  have hC:(x:ℝ)<=max 1 (⌈X⌉₊:ℝ):=
   br (br hxX.le (f9 X)) (cd _ _)
  have:(x:ℝ)<=max 1 (⌈X⌉₊:ℝ)*(x:ℝ)^θ:=by
   have h0:0<=max 1 (⌈X⌉₊:ℝ):=br zero_le_one (bq _ _)
   nlinarith
  linarith
 obtain ⟨⟨hxe,anx⟩,hE3,hE4⟩:=hX (x:ℝ) hxX
 set xr:ℝ:=(x:ℝ) with hxr
 have a3v:2<=xr:=br (bq _ _) hxe
 have a3w:af 1<=xr:=br (cd _ _) hxe
 set T:=xr^(1-θ₁) with ace
 set h:=xr^θ with az4
 have hT2:2<=T:=br (br (bq _ _) (bq _ _)) anx
 have awo:ahp<=T:=br (br (cd _ _) (bq _ _)) anx
 have as8:af (24*af 1*yg+1)<=T:=br (cd _ _) anx
 have anz:1<xr:=by linarith
 have hTx:T<=xr:=by
  calc T<=xr^(1:ℝ):=al anz.le (by linarith)
   _=xr:=fi xr
 have hh0:0<h:=dc tp θ
 have hhx:h<=xr:=by
  calc h<=xr^(1:ℝ):=al anz.le (by linarith)
   _=xr:=fi xr
 have ua:0<T:=by linarith
 have a8e:1<=aa xr:=by rw[d5 (by linarith)]; exact a3w
 have as4:24*af 1*yg+1<=aa T:=by
  rw[d5 ua]; exact as8
 have as9:0<=yg:=cd _ _
 have apv:1<=aa T:=by
  have:0<=24*af 1*yg:=by positivity
  linarith
 have hLT:aa T=(1-θ₁)*aa xr:=by rw[ace,oj tp]
 set F:=(aby T).toFinset with hF
 set m:ℂ->ℝ:=fun ρ=>(analyticOrderNatAt riemannZeta ρ:ℝ) with hm
 have hm0:∀ ρ,0<=m ρ:=fun ρ=>av _
 have an0:∀ ρ,ρ∈F↔ρ∈abx T:=fun ρ=>an _
 set η:=K*aa (aa T)/aa T with hη
 have a3x:∀ ρ∈F,0<=ρ.re∧ρ.re<=1-η∧ρ.re<1:=by
  intro ρ s8
  have afe:=(an0 ρ).mp s8
  exact ⟨afe.2.1.le,ant T awo ρ afe,ts afe.1⟩
 set S:=∑ ρ∈F,m ρ*xr^(ρ.re-1) with hS
 set J:=⌈aa xr⌉₊ with hJ
 have aga:0<J:=Nat.ceil_pos.mpr (by linarith)
 have hJx:aa xr<=J:=f9 _
 have a3y:(J:ℝ)<=6*aa T:=by
  have:(J:ℝ)<aa xr+1:=ef (by linarith)
  have a3z:1/3<=1-θ₁:=by linarith
  have h3:=ag a3z (by linarith:(0:ℝ)<=aa xr)
  rw[hLT]; linarith
 have aj2:=alo F m hm0 anz.le aga hJx a3x
 have hNj:∀ j∈(range J).filter (fun j:ℕ=>(j:ℝ)/J<=1-η),
   xr^((j:ℝ)/J-1)*∑ ρ∈F.filter (fun ρ=>(j:ℝ)/J<=ρ.re),m ρ<=
    yg*(1/aa T^3):=by
  intro j hj
  rw[ah] at hj
  set σ:ℝ:=(j:ℝ)/J
  have abi:σ<=1:=by
   have:(j:ℝ)<=J:=by exact_mod_cast (bw.mp hj.1).le
   exact div_le_one_of_le₀ this (by positivity)
  have arl:{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T}=
    ↑(F.filter (fun ρ=>σ<=ρ.re)):=by
   ext ρ
   simp only[o1,kj,an0,abx]
   tauto
  have hN:=hCD σ T hT2
  rw[arl,th] at hN
  have hTA:T^(aj0*(1-σ))<=T^(A*(1-σ)):=
   al (by linarith)
    (ag (bq _ _) (by linarith))
  have hTB:aa T^aj1<=aa T^B:=
   al apv (bq _ _)
  have az5:0<=T^(aj0*(1-σ)):=by positivity
  have ata:0<=aa T^aj1:=by positivity
  have hN':∑ ρ∈F.filter (fun ρ=>σ<=ρ.re),m ρ<=
    yg*(T^(A*(1-σ))*aa T^B):=by
   refine br hN ?_
   calc CD*T^(aj0*(1-σ))*aa T^aj1
     <= yg*T^(aj0*(1-σ))*aa T^aj1:=by
         apply ag _ ata
         exact ag (bq _ _) az5
    _ ≤ yg*(T^(A*(1-σ))*aa T^B):=by
        rw[gv]
        apply ab _ as9
        exact a8 hTA hTB ata (by positivity)
  have v7:=anu (x:=xr) (T:=T) (A:=A) (θ₁:=θ₁) (δ:=δ) (K:=K) (B:=B)
   (σ:=σ) anz rfl amc aum rfl ab0 a3u ya apv (by linarith[hj.2])
  have a30:0<=xr^(σ-1):=by positivity
  calc xr^(σ-1)*∑ ρ∈F.filter (fun ρ=>σ<=ρ.re),m ρ
    <= xr^(σ-1)*(yg*(T^(A*(1-σ))*aa T^B)):=
        ab hN' a30
   _=yg*(xr^(σ-1)*T^(A*(1-σ))*aa T^B):=by ring
   _<=yg*(1/aa T^3):=ab v7 as9
 have bdx:S<=1/4:=by
  have hsum:=ao hNj
  rw[a9] at hsum
  have aa0:((range J).filter (fun j:ℕ=>(j:ℝ)/J<=1-η)).card<=J:=
   br (nh _ _) (by simp)
  have awp:(((range J).filter (fun j:ℕ=>(j:ℝ)/J<=1-η)).card:ℝ)<=J:=by
   exact_mod_cast aa0
  have hl3:0<aa T^3:=by positivity
  have hq:0<=yg*(1/aa T^3):=by positivity
  have hS1:S<=af 1*((J:ℝ)*(yg*(1/aa T^3))):=by
   refine br aj2 (ab (br hsum ?_) (bx 1).le)
   rw[cp]; exact ag awp hq
  have hS2:af 1*((J:ℝ)*(yg*(1/aa T^3)))<=
    6*af 1*yg/aa T^2:=by
   have e1:af 1*((J:ℝ)*(yg*(1/aa T^3)))<=
     af 1*((6*aa T)*(yg*(1/aa T^3))):=by
    apply ab _ (bx 1).le
    exact ag a3y hq
   refine br e1 (i6 ?_)
   field_simp
  have hS3:6*af 1*yg/aa T^2<=1/4:=by
   rw[ay (by positivity)]
   have:aa T<=aa T^2:=by nlinarith
   nlinarith[bx 1]
  linarith
 set Z:ℝ->ℂ:=fun y=>∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℂ)*(y:ℂ)^ρ/ρ
  with az6
 have hEF:∀ y:ℝ,2<=y->T<=y->
   ‖((Chebyshev.psi y:ℝ):ℂ)-(y:ℂ)+Z y‖<=CE'*y *aa y^2/T:=by
  intro y hy hTy
  have:=hCE y T hy hT2 hTy
  have arl:{ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T}=↑F:=by
   rw[hF,rf]; rfl
  rw[arl,th] at this
  refine br this ?_
  apply a4 _ ua.le
  apply ag _ (c4 _)
  exact ag (bq _ _) (by linarith)
 have awr:‖Z (xr+h)-Z xr‖<=h*S:=by
  rw[az6]; simp only
  rw[<- dn,hS,bc]
  refine br (c5 _ _) (ao fun ρ s8=>?_)
  have afe:=(an0 ρ).mp s8
  have yw:ρ≠0:=fun h0=>by simp[h0] at afe; exact lt_irrefl _ afe.2.1
  have hb:=acd tp (by linarith:xr<=xr+h) yw
   (ts afe.1).le
  have heq:(analyticOrderNatAt riemannZeta ρ:ℂ)*((xr+h:ℝ):ℂ)^ρ/ρ-
    (analyticOrderNatAt riemannZeta ρ:ℂ)*(xr:ℂ)^ρ/ρ=
    (analyticOrderNatAt riemannZeta ρ:ℂ)*((((xr+h:ℝ):ℂ)^ρ-(xr:ℂ)^ρ)/ρ):=by
   ring
  rw[heq,bo,gf]
  simp only[j0] at hb
  calc (analyticOrderNatAt riemannZeta ρ:ℝ)*‖(((xr+h:ℝ):ℂ)^ρ-(xr:ℂ)^ρ)/ρ‖
    <= (analyticOrderNatAt riemannZeta ρ:ℝ)*(h*xr^(ρ.re-1)):=
        ab hb (av _)
   _=h*(m ρ*xr^(ρ.re-1)):=by rw[hm]; ring
 have apw:aa (xr+h)<=2*aa xr:=by
  have:aa (xr+h)<=aa (xr*xr):=
   a5 (by linarith) (by nlinarith)
  rw[ca (by linarith) (by linarith)] at this; linarith
 have aax:0<=aa (xr+h):=bd (by linarith)
 have hxT:xr/T=xr^θ₁:=by
  rw[ace,r3 (by positivity),<- c6 tp]; norm_num
 have atb:0<=CE':=cd _ _
 have av7:CE'*(xr+h)*aa (xr+h)^2/T+CE'*xr*aa xr^2/T<=
   h/4:=by
  have h1:CE'*(xr+h)*aa (xr+h)^2<=CE'*(2*xr)*(2*aa xr)^2:=by
   apply a8 (ab (by linarith) atb)
    (aj aax apw 2) (c4 _) (by positivity)
  have h2:CE'*xr*aa xr^2<=CE'*(2*xr)*(2*aa xr)^2:=by
   apply a8 (ab (by linarith) atb) (by nlinarith)
    (c4 _) (by positivity)
  have h3:CE'*(2*xr)*(2*aa xr)^2/T=
    8*CE'*(xr^θ₁*aa xr^2):=by
   rw[<- hxT]; field_simp; ring
  have h4:=a4 h1 ua.le
  have h5:=a4 h2 ua.le
  rw[h3] at h4 h5
  have:64*CE'*(xr^θ₁*aa xr^2)<=h:=hE3
  nlinarith
 have bdy:h/2<=Chebyshev.psi (xr+h)-Chebyshev.psi xr:=by
  have e1:=hEF (xr+h) (by linarith) (by linarith)
  have e0:=hEF xr a3v hTx
  set D:=Chebyshev.psi (xr+h)-Chebyshev.psi xr-h
  have key:((D:ℝ):ℂ)=(((Chebyshev.psi (xr+h):ℝ):ℂ)-((xr+h:ℝ):ℂ)+Z (xr+h))
    - (((Chebyshev.psi xr:ℝ):ℂ)-(xr:ℂ)+Z xr)-(Z (xr+h)-Z xr):=by
   simp only[D]; push_cast; ring
  have hD:|D|<=CE'*(xr+h)*aa (xr+h)^2/T+
    CE'*xr*aa xr^2/T+h*S:=by
   rw[<- au,<- ba,key]
   refine br (ej _ _) ?_
   refine e8 (br (ej _ _) (e8 e1 e0)) awr
  have:=r2 D
  have:h*S<=h/4:=by nlinarith
  simp only[D] at *
  linarith
 have wu:Chebyshev.psi (xr+h)-j9 (xr+h)<=h/8:=by
  refine br (Chebyshev.psi_sub_theta_le (by linarith)) ?_
  have zr:√(xr+h)<=2*xr^(1/2:ℝ):=by
   rw[ft]
   calc (xr+h)^(1/2:ℝ)<=(4*xr)^(1/2:ℝ):=
         dh (by linarith) (by linarith) (by norm_num)
    _ = 2*xr^(1/2:ℝ):=by
        rw[e6 (by norm_num) tp.le]
        congr 1
        rw[show (4:ℝ)=2^(2:ℝ) by norm_num,<- d7 (by norm_num)]
        norm_num
  have hxh:0<=xr^(1/2:ℝ):=by positivity
  have:48*(xr^(1/2:ℝ)*aa xr^2)<=h:=hE4
  have hl:aa xr<=aa xr^2:=by nlinarith
  calc 2*√(xr+h)*aa (xr+h)<=2*(2*xr^(1/2:ℝ))*(2*aa xr):=by
        apply a8 (by linarith) apw aax (by positivity)
   _<=h/8:=by nlinarith
 have awt:j9 (x:ℝ)<j9 (xr+h):=by
  have:=Chebyshev.theta_le_psi xr
  linarith
 obtain ⟨p,hp,v7,hle⟩:=aaj awt
 refine ⟨p,hp,v7,br hle ?_⟩
 have:h<=max 1 (⌈X⌉₊:ℝ)*(x:ℝ)^θ:=by
  have:=bq 1 (⌈X⌉₊:ℝ)
  rw[az4]; nlinarith
 linarith
end bt.abw
end
section
namespace bt.ZD
open Complex Finset
open scoped Real
noncomputable def ee (x:ℝ):ℂ:=d6 (((2*π*x:ℝ):ℂ)*I)
lemma w5 (x:ℝ):‖ee x‖=1:=k9 _
lemma aj3 (x y:ℝ):ee (x+y)=ee x*ee y:=by
 unfold ee; rw[<- jc]; congr 1; push_cast; ring
lemma an1 (k:ℤ):ee k=1:=by
 unfold ee
 have:(((2*π*(k:ℝ):ℝ):ℂ)*I)=(k:ℂ)*(2*π*I):=by push_cast; ring
 rw[this,Complex.exp_int_mul_two_pi_mul_I]
lemma ahq (x:ℝ) (k:ℤ):ee (x+k)=ee x:=by
 rw[aj3,an1,di]
lemma adw (x:ℝ):ee (-x)=(starRingEnd ℂ) (ee x):=by
 unfold ee
 rw[<- m2,qb,lr,n1]
 congr 1; push_cast; ring
lemma az7 (d:ℝ):ee d=(fo (2*π*d):ℂ)+(en (2*π*d):ℂ)*I:=by
 unfold ee; rw[Complex.exp_mul_I,<- Complex.ofReal_cos,<- Complex.ofReal_sin]
lemma aff {x y:ℝ} (hx:0<x) (tv:x<=y) (hy:y<π):
  fo y/en y<=fo x/en x:=by
 have sx:0<en x:=gh hx (by linarith)
 have sy:0<en y:=gh (by linarith) hy
 rw[ax sy sx]
 have h:=Real.sin_nonneg_of_nonneg_of_le_pi (oa.mpr tv) (by linarith)
 rw[Real.sin_sub] at h
 linarith
lemma an2 {x:ℝ} (hx:0<x) (hx2:x<=π/2):0<=fo x/en x:=
 fe (Real.cos_nonneg_of_mem_Icc ⟨by linarith,hx2⟩)
  (gh hx (by linarith[du])).le
lemma an3 {x:ℝ} (hx:0<x) (hx2:x<=π/2):fo x/en x<=1/x:=by
 have sx:0<en x:=gh hx (by linarith[du])
 rw[ax sx hx]
 rcases mn hx2 with h | h
 ·rw[h,Real.cos_pi_div_two]; simp[Real.sin_pi_div_two]
 ·have hc:0<fo x:=Real.cos_pos_of_mem_Ioo ⟨by linarith,h⟩
  have:=Real.lt_tan hx h
  rw[Real.tan_eq_sin_div_cos,na hc] at this
  linarith
lemma ahr {d:ℝ} (hs:en (π*d)≠0):
  ((-1/2:ℂ)+((-(fo (π*d)/en (π*d))/2:ℝ):ℂ)*I)*(ee d-1)=1:=by
 rw[az7]
 have h2:2*π*d=2*(π*d):=by ring
 rw[h2,Real.cos_two_mul,Real.sin_two_mul]
 set s:=en (π*d)
 set c:=fo (π*d)
 have hsc:s^2+c^2=1:=Real.sin_sq_add_cos_sq _
 apply kn
 ·simp only[mul_re,add_re,sub_re,ofReal_re,I_re,mul_im,ofReal_im,I_im,add_im,sub_im,
   one_re,one_im,div_ofNat_re,neg_re,div_ofNat_im,neg_im]
  field_simp
  ring
 ·simp only[mul_re,add_re,sub_re,ofReal_re,I_re,mul_im,ofReal_im,I_im,add_im,sub_im,
   one_re,one_im,div_ofNat_re,neg_re,div_ofNat_im,neg_im]
  field_simp
  linear_combination (-2*c:ℝ)*hsc
lemma apx (κ:ℕ->ℝ) (z:ℕ->ℂ) (hz:∀ j,‖z j‖=1) (K:ℕ)
  (u6:∀ j,j+1<K+1->κ j<=κ (j+1)):
  ‖∑ j∈range (K+1),(κ j:ℂ)*(z (j+1)-z j)-(κ K:ℂ)*z (K+1)+(κ 0:ℂ)*z 0‖
   <= κ K-κ 0:=by
 induction K with
 | zero=>
  rw[i3,norm_le_zero_iff,Finset.sum_range_one]; ring
 | succ K ih=>
  have ih':=ih (fun j hj=>u6 j (by omega))
  have hK:=u6 K (by omega)
  rw[dk]
  have e:∑ j∈range (K+1),(κ j:ℂ)*(z (j+1)-z j)+
    (κ (K+1):ℂ)*(z (K+1+1)-z (K+1))-(κ (K+1):ℂ)*z (K+1+1)+
    (κ 0:ℂ)*z 0=
    (∑ j∈range (K+1),(κ j:ℂ)*(z (j+1)-z j)-(κ K:ℂ)*z (K+1)+
     (κ 0:ℂ)*z 0)+((κ K-κ (K+1):ℝ):ℂ)*z (K+1):=by
   push_cast; ring
  rw[e]
  refine (ds _ _).trans ?_
  rw[bo,hz,di,ba,au,abs_of_nonpos (by linarith)]
  linarith
theorem adx (φ:ℕ->ℝ) (K:ℕ) {δ:ℝ} (uf:0<δ) (zn:δ<=1/2)
  (hd:∀ j<K,δ<=φ (j+1)-φ j∧φ (j+1)-φ j<=1-δ)
  (u6:∀ j,j+1<K->φ (j+1)-φ j<=φ (j+2)-φ (j+1)):
  ‖∑ j∈range (K+1),ee (φ j)‖<=1+2*(fo (π*δ)/en (π*δ)):=by
 have hpd:0<π*δ:=ji du uf
 have arn:π*δ<=π/2:=by nlinarith[du]
 have bdz:=an2 hpd arn
 rcases c7 K with rfl | hK
 ·simp[w5]; linarith
 set d:ℕ->ℝ:=fun j=>φ (j+1)-φ j with apy
 set B:ℝ:=fo (π*δ)/en (π*δ)
 set κ:ℕ->ℝ:=fun j=>-(fo (π*d j)/en (π*d j))/2 with hκ
 set z:ℕ->ℂ:=fun j=>ee (φ j) with apz
 have hzn:∀ j,‖z j‖=1:=fun j=>w5 _
 have agc:∀ j<K,π*δ<=π*d j∧π*d j<=π-π*δ:=by
  intro j hj
  obtain ⟨h1,h2⟩:=hd j hj
  constructor
  ·exact ab h1 du.le
  ·have:=ab h2 du.le; linarith
 have aro:∀ j<K,en (π*d j)≠0:=by
  intro j hj
  obtain ⟨h1,h2⟩:=agc j hj
  exact (gh (by linarith) (by linarith)).ne'
 have awv:∀ j<K,-B/2<=κ j∧κ j<=B/2:=by
  intro j hj
  obtain ⟨h1,h2⟩:=agc j hj
  have u1:fo (π*d j)/en (π*d j)<=B:=
   aff hpd h1 (by linarith)
  have u2:fo (π-π*δ)/en (π-π*δ)<=
    fo (π*d j)/en (π*d j):=
   aff (by linarith) h2 (by linarith)
  rw[Real.cos_pi_sub,Real.sin_pi_sub,p9] at u2
  simp only[hκ]
  constructor <;> linarith
 have a31:∀ j,j+1<K->κ j<=κ (j+1):=by
  intro j hj
  obtain ⟨h1,_⟩:=agc j (by omega)
  obtain ⟨_,h2'⟩:=agc (j+1) hj
  have hm:=u6 j hj
  have:fo (π*d (j+1))/en (π*d (j+1))<=
    fo (π*d j)/en (π*d j):=
   aff (by linarith) (ab (by simpa [apy] using hm)
    du.le) (by linarith)
  simp only[hκ]; linarith
 have hzj:∀ j<K,z j=((-1/2:ℂ)+(κ j:ℂ)*I)*(z (j+1)-z j):=by
  intro j hj
  have hzz:z (j+1)=z j*ee (d j):=by
   simp only[apz,apy]; rw[<- aj3]; congr 1; ring
  rw[hzz,show z j*ee (d j)-z j=z j*(ee (d j)-1) by ring,mul_left_comm,
   ahr (aro j hj),di]
 obtain ⟨K',rfl⟩:∃ K',K=K'+1:=⟨K-1,by omega⟩
 have hA:∑ j∈range (K'+1),(-1/2:ℂ)*(z (j+1)-z j)=
   (-1/2:ℂ)*(z (K'+1)-z 0):=by
  rw[<- bc,r6 (fun j=>z j)]
 have af3:∑ j∈range (K'+1),z j=(-1/2:ℂ)*(z (K'+1)-z 0)+
   I*∑ j∈range (K'+1),(κ j:ℂ)*(z (j+1)-z j):=by
  rw[ai rfl (fun j hj=>hzj j (bw.mp hj)),<- hA,bc,
   <- cu]
  exact ai rfl (fun j _=>by ring)
 have hsum:∑ j∈range (K'+1+1),z j=
   z (K'+1)+(-1/2:ℂ)*(z (K'+1)-z 0)+
    I*∑ j∈range (K'+1),(κ j:ℂ)*(z (j+1)-z j):=by
  rw[dk,af3]; ring
 have hab:=apx κ z hzn K' (fun j hj=>a31 j hj)
 set T:=∑ j∈range (K'+1),(κ j:ℂ)*(z (j+1)-z j)
 have hT:‖T‖<=(κ K'-κ 0)+|κ K'|+|κ 0|:=by
  have e:T=(T-(κ K':ℂ)*z (K'+1)+(κ 0:ℂ)*z 0)+(κ K':ℂ)*z (K'+1)-
    (κ 0:ℂ)*z 0:=by ring
  rw[e]
  refine (ej _ _).trans ?_
  refine (e8 (ds _ _) le_rfl).trans ?_
  rw[bo,bo,hzn,hzn,di,di,ba,ba,
   au,au]
  linarith
 rw[apz] at hsum
 simp only at hsum
 rw[hsum]
 have e2:ee (φ (K'+1))+(-1/2:ℂ)*(ee (φ (K'+1))-ee (φ 0))=
   (1/2:ℂ)*ee (φ (K'+1))+(1/2:ℂ)*ee (φ 0):=by ring
 rw[e2]
 refine (ds _ _).trans ?_
 refine (e8 (ds _ _) le_rfl).trans ?_
 rw[bo,bo,bo,w5,w5,kr]
 have h1:‖(1/2:ℂ)‖=1/2:=by norm_num
 rw[h1]
 obtain ⟨a1,a2⟩:=awv K' (by omega)
 obtain ⟨b1,b2⟩:=awv 0 (by omega)
 have:(κ K'-κ 0)+|κ K'|+|κ 0|<=2*B:=by
  rcases abs_cases (κ K') with ⟨h,_⟩ | ⟨h,_⟩ <;>
  rcases abs_cases (κ 0) with ⟨h',_⟩ | ⟨h',_⟩ <;> linarith
 linarith
lemma arp {δ:ℝ} (uf:0<δ) (zn:δ<=1/2):
  1+2*(fo (π*δ)/en (π*δ))<=2/δ:=by
 have hpd:0<π*δ:=ji du uf
 have arn:π*δ<=π/2:=by nlinarith[du]
 have h:=an3 hpd arn
 have hpi:3<π:=jq
 have h4:1/(π*δ)<=1/(3*δ):=dr (by positivity) (by nlinarith)
 have h5:2/δ-(1+2*(1/(3*δ)))=(4/3-δ)/δ:=by field_simp; ring
 have h6:0<=(4/3-δ)/δ:=fe (by linarith) uf.le
 linarith
theorem ac5 (φ:ℕ->ℝ) {A B:ℕ} (hAB:A<=B) {δ:ℝ} (uf:0<δ) (zn:δ<=1/2)
  (k:ℤ) (hd:∀ n,A<=n->n<B->k+δ<=φ (n+1)-φ n∧φ (n+1)-φ n<=k+1-δ)
  (u6:∀ n,A<=n->n+1<B->φ (n+1)-φ n<=φ (n+2)-φ (n+1)):
  ‖∑ n∈Icc A B,ee (φ n)‖<=2/δ:=by
 set ψ:ℕ->ℝ:=fun j=>φ (A+j)-k*(A+j:ℕ)
 have key:=adx ψ (B-A) uf zn
  (by
   intro j hj
   obtain ⟨h1,h2⟩:=hd (A+j) (by omega) (by omega)
   simp only[ψ]; push_cast
   have e:A+(j+1)=A+j+1:=by ring
   rw[e]; constructor <;> linarith)
  (by
   intro j hj
   have h:=u6 (A+j) (by omega) (by omega)
   simp only[ψ]; push_cast
   have e1:A+(j+1)=A+j+1:=by ring
   have e2:A+(j+2)=A+j+2:=by ring
   rw[e1,e2]; linarith)
 have hsum:∑ n∈Icc A B,ee (φ n)=∑ j∈range (B-A+1),ee (ψ j):=by
  rw[<- cy,dq]
  rw[show B+1-A=B-A+1 by omega]
  refine ai rfl (fun j _=>?_)
  simp only[ψ]
  rw[ro,show (-( (k:ℝ)*((A+j:ℕ):ℝ)))=(((-(k*(A+j:ℕ)):ℤ)):ℝ) by
   push_cast; ring,ahq]
 rw[hsum]
 exact key.trans (arp uf zn)
theorem ady (φ:ℕ->ℝ) {A B:ℕ} (hAB:A<=B) {δ:ℝ} (uf:0<δ)
  (zn:δ<=1/2) (k:ℤ)
  (hd:∀ n,A<=n->n<B->k+δ<=φ (n+1)-φ n∧φ (n+1)-φ n<=k+1-δ)
  (u6:∀ n,A<=n->n+1<B->φ (n+2)-φ (n+1)<=φ (n+1)-φ n):
  ‖∑ n∈Icc A B,ee (φ n)‖<=2/δ:=by
 have key:=ac5 (fun n=>-φ n) hAB uf zn (-k-1)
  (by
   intro n h1 h2
   obtain ⟨a,b⟩:=hd n h1 h2
   push_cast; constructor <;> linarith)
  (by intro n h1 h2; have:=u6 n h1 h2; linarith)
 have e:∑ n∈Icc A B,ee (-φ n)=(starRingEnd ℂ) (∑ n∈Icc A B,ee (φ n)):=by
  rw[m9]; exact ai rfl (fun n _=>adw _)
 rw[e,d4] at key
 exact key
def dd (φ:ℕ->ℝ) (n:ℕ):ℝ:=φ (n+1)-φ n
lemma aj4 (φ:ℕ->ℝ) {A B:ℕ} {lam:ℝ}
  (h2:∀ n,A<=n->n+2<=B->lam<=dd φ (n+1)-dd φ n):
  ∀ j n,A<=n->n+j+1<=B->(j:ℝ)*lam<=dd φ (n+j)-dd φ n:=by
 intro j
 induction j with
 | zero=>intro n _ _; simp
 | succ j ih=>
  intro n hn hj
  have h1:=ih n hn (by omega)
  have h3:=h2 (n+j) (by omega) (by omega)
  rw[show n+(j+1)=n+j+1 by ring]
  push_cast; linarith
lemma zo (G:Finset ℕ) (te:G.Nonempty)
  (y7:∀ a∈G,∀ b∈G,∀ m,a<=m->m<=b->m∈G):
  G=Icc (G.min' te) (G.max' te):=by
 ext n
 constructor
 ·intro hn
  exact ar.mpr ⟨G.min'_le n hn,G.le_max' n hn⟩
 ·intro hn
  rw[ar] at hn
  exact y7 _ (G.min'_mem te) _ (G.max'_mem te) n hn.1 hn.2
lemma uz (s:Finset ℕ) (φ:ℕ->ℝ):‖∑ n∈s,ee (φ n)‖<=s.card:=by
 refine (c5 _ _).trans ?_
 simp[w5]
lemma aeo (G:Finset ℕ) (c:ℝ) (hc:0<=c)
  (h:∀ a∈G,∀ b∈G,a<=b->(b:ℝ)-a<=c):(G.card:ℝ)<=c+1:=by
 rcases G.eq_empty_or_nonempty with he | te
 ·rw[he]; simp; linarith
 have hpq:G.min' te<=G.max' te:=G.min'_le _ (G.max'_mem te)
 have uj:G ⊆ Icc (G.min' te) (G.max' te):=fun n hn=>
  ar.mpr ⟨G.min'_le n hn,G.le_max' n hn⟩
 have h1:=cf uj
 rw[jv] at h1
 have h2:=h _ (G.min'_mem te) _ (G.max'_mem te) hpq
 have h3:((G.max' te+1-G.min' te:ℕ):ℝ)=(G.max' te:ℝ)-G.min' te+1:=by
  rw[il (by omega)]; push_cast; ring
 have h4:(G.card:ℝ)<=((G.max' te+1-G.min' te:ℕ):ℝ):=by exact_mod_cast h1
 linarith
theorem aa1             (φ : ℕ → ℝ) {A B : ℕ} (hAB : A + 1 ≤ B) {lam δ : ℝ} (vu   : 0 < lam)
    (uf : 0 < δ) (zn  : δ ≤ 1 / 2)
    (h2 : ∀ n, A ≤ n → n + 2 ≤ B → lam ≤ dd φ (n + 1) - dd φ n) :
    ‖∑ n ∈ Icc A B, ee (φ n)‖ ≤
      1 + (dd φ (B - 1) - dd φ A + 2) * (2 * δ / lam + 1 + 2 / δ) := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have gap := aj4    φ h2
  have mono : ∀ n m, A ≤ n → n ≤ m → m ≤ B' → dd φ n ≤ dd φ m := by
    intro n m hn hnm hm
    have := gap (m - n) n hn (by omega)
    rw [show n + (m - n) = m by omega] at this
    have : (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) * lam := by positivity
    linarith
  set κ : ℕ → ℤ := fun n => ⌊dd φ n + δ⌋ with hκ
  have adz   : ∀ n m, A ≤ n → n ≤ m → m ≤ B' → κ n ≤ κ m := by
    intro n m hn hnm hm
    exact Int.floor_le_floor (by linarith [mono n m hn hnm hm])
  have hfl : ∀ n, (κ n : ℝ) ≤ dd φ n + δ ∧ dd φ n + δ < κ n + 1 := fun n =>
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  rw [Finset.sum_Icc_succ_top (by omega), ← Finset.sum_fiberwise_of_maps_to
    (g := κ) (t := Icc (κ A) (κ B')) (by
      intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨adz   A n le_rfl hn.1 hn.2, adz   n B' hn.1 hn.2 le_rfl⟩)]
  set W : ℝ := 2 * δ / lam + 1 + 2 / δ
  have yu   : ∀ k : ℤ, ‖∑ n ∈ Icc A B' with κ n = k, ee (φ n)‖ ≤ W := by
    intro k
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun n => dd φ n < k + δ)]
    refine (norm_add_le _ _).trans ?_
    rw [Finset.filter_filter, Finset.filter_filter]
    set Gb := (Icc A B').filter (fun n => κ n = k ∧ dd φ n < k + δ)
    set Gg := (Icc A B').filter (fun n => κ n = k ∧ ¬ dd φ n < k + δ)
    have hb : ‖∑ n ∈ Gb, ee (φ n)‖ ≤ 2 * δ / lam + 1 := by
      refine (uz                  _ _).trans ?_
      refine aeo               Gb (2 * δ / lam) (by positivity) ?_
      intro a ha b hb' hab
      simp only [Gb, Finset.mem_filter, Finset.mem_Icc] at ha hb'
      have hg := gap (b - a) a ha.1.1 (by omega)
      rw [show a + (b - a) = b by omega, Nat.cast_sub hab] at hg
      have x1  := (hfl a).1
      rw [ha.2.1] at x1 
      have hk2 := hb'.2.2
      rw [le_div_iff₀ vu  ]; linarith
    have hg : ‖∑ n ∈ Gg, ee (φ n)‖ ≤ 2 / δ := by
      rcases Gg.eq_empty_or_nonempty with he | te 
      · rw [he]; simp; positivity
      have y7    : ∀ a ∈ Gg, ∀ b ∈ Gg, ∀ m, a ≤ m → m ≤ b → m ∈ Gg := by
        intro a ha b hb m ham hmb
        simp only [Gg, Finset.mem_filter, Finset.mem_Icc] at ha hb ⊢
        refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
        · have := adz   a m ha.1.1 ham (by omega)
          have := adz   m b (by omega) hmb hb.1.2
          omega
        · have := mono a m ha.1.1 ham (by omega)
          intro v7 ; exact ha.2.2 (by linarith)
      rw [zo            Gg te  y7   ]
      have hpq : Gg.min' te  ≤ Gg.max' te  := Gg.min'_le _ (Gg.max'_mem te )
      have u3   : ∀ n, Gg.min' te  ≤ n → n ≤ Gg.max' te  → n ∈ Gg := fun n h1 h2 =>
        y7    _ (Gg.min'_mem te ) _ (Gg.max'_mem te ) n h1 h2
      refine ac5           φ hpq uf zn  k ?_ ?_
      · intro n h1 h2'
        have hn := u3   n h1 h2'.le
        simp only [Gg, Finset.mem_filter, Finset.mem_Icc] at hn
        have := hfl n
        rw [hn.2.1] at this
        change k + δ ≤ dd φ n ∧ dd φ n ≤ k + 1 - δ
        constructor
        · push Not at hn; exact hn.2.2
        · linarith [this.2]
      · intro n h1 h2'
        have hn := u3   (n + 1) (by omega) h2'.le
        simp only [Gg, Finset.mem_filter, Finset.mem_Icc] at hn
        have := mono n (n + 1) (by have := (u3   n h1 (by omega)); simp only [Gg,
          Finset.mem_filter, Finset.mem_Icc] at this; exact this.1.1) (by omega) hn.1.2
        simpa [dd] using this
    linarith
  have a8l    : (((Icc (κ A) (κ B')).card : ℕ) : ℝ) ≤ dd φ B' - dd φ A + 2 := by
    rw [Int.card_Icc]
    have hle : κ A ≤ κ B' := adz   A B' le_rfl (by omega) le_rfl
    have h0 : (0 : ℤ) ≤ κ B' + 1 - κ A := by omega
    have : (((κ B' + 1 - κ A).toNat : ℕ) : ℝ) = ((κ B' + 1 - κ A : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
      exact_mod_cast this
    rw [this]; push_cast
    have a1 := (hfl A).2
    have a2 := (hfl B').1
    linarith
  have hW : 0 ≤ W := by positivity
  calc ‖∑ k ∈ Icc (κ A) (κ B'), ∑ n ∈ Icc A B' with κ n = k, ee (φ n) + ee (φ (B' + 1))‖
      ≤ ‖∑ k ∈ Icc (κ A) (κ B'), ∑ n ∈ Icc A B' with κ n = k, ee (φ n)‖ + 1 := by
        refine (norm_add_le _ _).trans ?_; rw [w5     ]
    _ ≤ (∑ k ∈ Icc (κ A) (κ B'), W) + 1 := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => yu   k))
    _ = ((Icc (κ A) (κ B')).card : ℝ) * W + 1 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (dd φ B' - dd φ A + 2) * W + 1 := by gcongr
    _ = _ := by ring
theorem afg (φ:ℕ->ℝ) {A B:ℕ} (hAB:A+1<=B) {lam:ℝ} (vu:0<lam)
  (h2:∀ n,A<=n->n+2<=B->lam<=dd φ (n+1)-dd φ n):
  ‖∑ n∈Icc A B,ee (φ n)‖<=(dd φ (B-1)-dd φ A+2)*(6+4/ak lam):=by
 have hD:0<=dd φ (B-1)-dd φ A:=by
  have:=aj4 φ h2 (B-1-A) A le_rfl (by omega)
  rw[show A+(B-1-A)=B-1 by omega] at this
  have:(0:ℝ)<=((B-1-A:ℕ):ℝ)*lam:=by positivity
  linarith
 have hs:0<ak lam:=iu.mpr vu
 have zr:ak lam^2=lam:=ly vu.le
 have key:∃ δ:ℝ,0<δ∧δ<=1/2∧2*δ/lam+1+2/δ<=5+4/ak lam:=by
  by_cases hl:lam<=1/4
  ·refine ⟨ak lam,hs, ?_, ?_⟩
   ·rw[show (1/2:ℝ)=ak (1/4) by
     rw[show (1/4:ℝ)=(1/2)^2 by norm_num,fk (by norm_num)]]
    exact dg hl
   ·have hm:=f5 vu.le
    have:2*ak lam/lam=2/ak lam:=by
     rw[div_eq_div_iff vu.ne' hs.ne']; linear_combination 2*hm
    rw[this]
    have:4/ak lam=2/ak lam+2/ak lam:=by ring
    linarith
  ·push Not at hl
   refine ⟨1/2,by norm_num,le_rfl, ?_⟩
   have h1:1/ak lam<=4:=by
    rw[ay hs]
    have:(1/4:ℝ)<=ak lam:=by
     rw[show (1/4:ℝ)=ak (1/16) by
      rw[show (1/16:ℝ)=(1/4)^2 by norm_num,fk (by norm_num)]]
     exact dg (by linarith)
    linarith
   have h2':2*(1/2)/lam=(1/ak lam)*(1/ak lam):=by
    rw[div_mul_div_comm,iq,f5 vu.le]; ring
   rw[h2']
   have:(1/ak lam)*(1/ak lam)<=4*(1/ak lam):=
    ag h1 (by positivity)
   have e:4/ak lam=4*(1/ak lam):=by ring
   have e1:2/(1/2:ℝ)=4:=by norm_num
   rw[e,e1]; linarith
 obtain ⟨δ,uf,zn,hW⟩:=key
 have:=aa1 φ hAB vu uf zn h2
 have tj:0<=4/ak lam:=by positivity
 calc ‖∑ n∈Icc A B,ee (φ n)‖<=1+(dd φ (B-1)-dd φ A+2)*(2*δ/lam+1+2/δ):=
       this
  _<=1+(dd φ (B-1)-dd φ A+2)*(5+4/ak lam):=by gcongr
  _<=_:=by nlinarith
lemma yx (f:ℕ->ℂ) {A B H r:ℕ} (hHA:H<=A) (hr:r<H)
  (xh:∀ n,(n<A∨B<n)->f n=0):
  ∑ m∈Icc (A+1-H) B,f (m+r)=∑ n∈Icc A B,f n:=by
 rw[<- cy,<- cy,Finset.sum_Ico_add']
 symm
 apply Finset.sum_subset
 ·intro n hn
  simp only[g4] at hn ⊢
  omega
 ·intro n _ hn
  apply xh
  simp only[g4] at hn
  omega
theorem arq (z:ℕ->ℂ) {A B H:ℕ} (hHA:H<=A)
  (xh:∀ n,(n<A∨B<n)->z n=0):
  (H:ℝ)^2*‖∑ n∈Icc A B,z n‖^2<=((B+H-A:ℕ):ℝ)*
   ∑ r∈range H,∑ r'∈range H,
    ‖∑ m∈Icc (A+1-H) B,z (m+r)*(starRingEnd ℂ) (z (m+r'))‖:=by
 set M:=Icc (A+1-H) B
 set v:ℕ->ℂ:=fun m=>∑ r∈range H,z (m+r)
 have hM:M.card=B+1-(A+1-H):=by simp only[M,jv]
 have h1:(H:ℂ)*∑ n∈Icc A B,z n=∑ m∈M,v m:=by
  simp only[v]
  rw[d0]
  rw[ai rfl (fun r hr=>yx z hHA (bw.mp hr) xh)]
  rw[a9,fa,cp]
 have h2:‖∑ m∈M,v m‖^2<=(M.card:ℝ)*∑ m∈M,‖v m‖^2:=by
  calc ‖∑ m∈M,v m‖^2<=(∑ m∈M,‖v m‖)^2:=by
        gcongr; exact c5 _ _
   _<=_:=sq_sum_le_card_mul_sum_sq
 have h3:∀ m,(‖v m‖^2:ℝ)=(∑ r∈range H,∑ r'∈range H,
   z (m+r)*(starRingEnd ℂ) (z (m+r'))).re:=by
  intro m
  have:v m*(starRingEnd ℂ) (v m)=∑ r∈range H,∑ r'∈range H,
    z (m+r)*(starRingEnd ℂ) (z (m+r')):=by
   simp only[v]; rw[m9,f8]
  rw[<- this,km]
  norm_cast
 have h4:∑ m∈M,‖v m‖^2<=∑ r∈range H,∑ r'∈range H,
   ‖∑ m∈M,z (m+r)*(starRingEnd ℂ) (z (m+r'))‖:=by
  simp_rw[h3]
  rw[<- Complex.re_sum]
  rw[d0]
  simp_rw[d0 (s:=M)]
  refine (ot _).trans ?_
  exact (c5 _ _).trans (ao (fun r _=>c5 _ _))
 have e:(H:ℝ)^2*‖∑ n∈Icc A B,z n‖^2=‖∑ m∈M,v m‖^2:=by
  rw[<- h1,bo,i5,gf]
 have hMc:M.card<=B+H-A:=by rw[hM]; omega
 rw[e]
 refine h2.trans ?_
 have h0:0<=∑ m∈M,‖v m‖^2:=cj (fun _ _=>by positivity)
 calc (M.card:ℝ)*∑ m∈M,‖v m‖^2<=((B+H-A:ℕ):ℝ)*∑ m∈M,‖v m‖^2:=by
       gcongr
  _<=_:=by gcongr
def d2 (φ:ℕ->ℝ) (n:ℕ):ℝ:=dd φ (n+1)-dd φ n
def d3 (φ:ℕ->ℝ) (n:ℕ):ℝ:=d2 φ (n+1)-d2 φ n
lemma auo (u:ℕ->ℝ) {A:ℕ} {c:ℝ}:
  ∀ j,(∀ n,A<=n->n<A+j->u (n+1)-u n<=c)->u (A+j)-u A<=j*c:=by
 intro j
 induction j with
 | zero=>intro _; simp
 | succ j ih=>
  intro h
  have h1:=ih (fun n h1 h2=>h n h1 (by omega))
  have h2:=h (A+j) (by omega) (by omega)
  rw[show A+(j+1)=A+j+1 by ring]
  push_cast; linarith
lemma ae1 (φ:ℕ->ℝ) (h m:ℕ):
  dd (fun m=>φ (m+h)-φ m) m=∑ j∈range h,d2 φ (m+j):=by
 have:=r6 (fun j=>dd φ (m+j)) h
 have e:∑ j∈range h,d2 φ (m+j)=∑ j∈range h,(dd φ (m+(j+1))-dd φ (m+j)):=by
  refine ai rfl (fun j _=>?_)
  simp only[d2]; rw[show m+(j+1)=m+j+1 by ring]
 rw[e,this]
 simp only[dd]
 rw[show m+1+h=m+h+1 by ring]
 simp only[ij]
 ring
lemma amj (φ:ℕ->ℝ) (h n:ℕ):
  dd (fun m=>φ (m+h)-φ m) (n+1)-dd (fun m=>φ (m+h)-φ m) n=
   ∑ j∈range h,d3 φ (n+j):=by
 rw[ae1,ae1,<- dn]
 refine ai rfl (fun j _=>?_)
 simp only[d3]
 rw[show n+1+j=n+j+1 by ring]
theorem agg (φ:ℕ->ℝ) {A B:ℕ} (hAB:A<=B) {ν κ:ℝ} (hν:0<ν)
  (ars:ν^2<=1/2) (hκ:1<=κ) (hA:2/ν<=A)
  (h3:∀ n,A<=n->n+3<=B->ν^4<=d3 φ n∧d3 φ n<=κ*ν^4):
  ‖∑ n∈Icc A B,ee (φ n)‖^2<=
   22*κ*((B-A+1:ℕ):ℝ)^2*ν+22*((B-A+1:ℕ):ℝ)/ν^2:=by
 set N:ℕ:=B-A+1 with hN
 have bd0:ν<=1:=by nlinarith
 have az8:1<=1/ν:=by rw[bl hν]; linarith
 have bck:1<=1/ν^2:=by rw[bl (by positivity)]; nlinarith
 have hN1:(1:ℝ)<=N:=by exact_mod_cast (show 1<=N by omega)
 have agh:((Icc A B).card:ℝ)=N:=by
  rw[jv,hN,show B+1-A=B-A+1 by omega]
 have hS:‖∑ n∈Icc A B,ee (φ n)‖<=N:=by
  rw[<- agh]; exact uz _ _
 set H:ℕ:=⌈1/ν⌉₊ with hH
 have hH1:1/ν<=H:=f9 _
 have hH2:(H:ℝ)<=2/ν:=by
  have:=ef (show 0<=1/ν by positivity)
  have:(2:ℝ)/ν=1/ν+1/ν:=by ring
  linarith
 have bcl:(1:ℝ)<=H:=az8.trans hH1
 have hHA:H<=A:=by exact_mod_cast hH2.trans hA
 by_cases hHN:N<H
 ·
  have h1:(N:ℝ)<1/ν:=Nat.lt_ceil.mp hHN
  have h2:1/ν<=1/ν^2:=by
   rw[ax hν (by positivity)]; nlinarith
  have hp:0<=22*κ*(N:ℝ)^2*ν:=by positivity
  have h3':(N:ℝ)*(1/ν^2)<=22*N/ν^2:=by
   rw[m8]; gcongr; linarith
  have hS2:‖∑ n∈Icc A B,ee (φ n)‖^2<=(N:ℝ)*(N:ℝ):=by
   rw[sq]; exact a8 hS hS (aw _) (by positivity)
  have h4:(N:ℝ)*(N:ℝ)<=(N:ℝ)*(1/ν^2):=
   ab (by linarith) (by positivity)
  linarith
 push Not at hHN
 set Bd:ℝ:=10*N*κ*ν+11/ν^2 with hBd
 have bd1:0<=Bd:=by positivity
 set z:ℕ->ℂ:=fun n=>if A<=n∧n<=B then ee (φ n) else 0 with hz
 have xh:∀ n,(n<A∨B<n)->z n=0:=by
  intro n hn; simp only[hz]; rw[if_neg (by omega)]
 have hS':∑ n∈Icc A B,ee (φ n)=∑ n∈Icc A B,z n:=by
  refine ai rfl (fun n hn=>?_)
  rw[ar] at hn; simp only[hz]; rw[if_pos hn]
 set C:ℕ->ℕ->ℂ:=fun r r'=>
  ∑ m∈Icc (A+1-H) B,z (m+r)*(starRingEnd ℂ) (z (m+r')) with hC
 have ate:∀ r r',r'<r->r<H->
   C r r'=∑ n∈Icc A (B-(r-r')),ee (φ (n+(r-r'))-φ n):=by
  intro r r' hrr hr
  set h:=r-r'
  have e1:C r r'=∑ m∈Icc (A+1-H) B,
    (fun n=>z (n+h)*(starRingEnd ℂ) (z n)) (m+r'):=by
   refine ai rfl (fun m _=>?_)
   simp only
   rw[show m+r'+h=m+r by omega]
  rw[e1,yx (fun n=>z (n+h)*(starRingEnd ℂ) (z n)) hHA (by omega)
   (fun n hn=>by simp only[xh n hn,map_zero,mul_zero])]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  ·intro n hn; simp only[ar] at hn ⊢; omega
  ·intro n hn
   simp only[Finset.mem_sdiff,ar] at hn
   rw[xh (n+h) (by omega),zero_mul]
  ·intro n hn
   simp only[ar] at hn
   simp only[hz]
   rw[if_pos (by omega),if_pos (by omega),<- adw,<- aj3]
   ring_nf
 have az9:∀ r r',C r r'=(starRingEnd ℂ) (C r' r):=by
  intro r r'
  simp only[hC,m9,qb,Complex.conj_conj]
  exact ai rfl (fun m _=>gx _ _)
 have a0a:∀ r,r<H->‖C r r‖<=N:=by
  intro r hr
  have:C r r=∑ n∈Icc A B,(fun n=>z n*(starRingEnd ℂ) (z n)) n:=by
   rw[<- yx (fun n=>z n*(starRingEnd ℂ) (z n)) hHA hr
    (fun n hn=>by simp only[xh n hn,zero_mul])]
  rw[this]
  refine (c5 _ _).trans ?_
  have:∀ n∈Icc A B,‖z n*(starRingEnd ℂ) (z n)‖<=1:=by
   intro n hn
   rw[ar] at hn
   simp only[hz]; rw[if_pos hn,bo,d4,w5]; norm_num
  refine (ao this).trans ?_
  rw[a9,cp,di,agh]
 have awx:∀ h,1<=h->h<H->
   ‖∑ n∈Icc A (B-h),ee (φ (n+h)-φ n)‖<=Bd:=by
  intro h hh1 hhH
  set g:ℕ->ℝ:=fun m=>φ (m+h)-φ m with hg
  have bd2:1<=Bd:=by
   have:0<=10*N*κ*ν:=by positivity
   have e:(11:ℝ)/ν^2=11*(1/ν^2):=by ring
   rw[hBd,e]; linarith
  by_cases hlen:A+1<=B-h
  ·have h2:∀ n,A<=n->n+2<=B-h->ν^4<=dd g (n+1)-dd g n:=by
    intro n hn hn2
    rw[hg,amj]
    have:∀ j∈range h,ν^4<=d3 φ (n+j):=fun j hj=>
     (h3 (n+j) (by omega) (by have:=bw.mp hj; omega)).1
    have hs:=ao this
    rw[a9,fa,cp] at hs
    have:(1:ℝ)<=h:=by exact_mod_cast hh1
    nlinarith[fb hν 4]
   have uf:0<ν^2:=by positivity
   have key:=aa1 g hlen (fb hν 4) uf ars h2
   have hD:dd g (B-h-1)-dd g A<=N*(2*κ*ν^3):=by
    have ht:=auo (dd g) (A:=A) (c:=h*(κ*ν^4)) (B-h-1-A) (by
     intro n hn hn2
     rw[hg,amj]
     have:∀ j∈range h,d3 φ (n+j)<=κ*ν^4:=fun j hj=>
      (h3 (n+j) (by omega) (by have:=bw.mp hj; omega)).2
     have hs:=ao this
     rw[a9,fa,cp] at hs
     exact hs)
    rw[show A+(B-h-1-A)=B-h-1 by omega] at ht
    have hj:((B-h-1-A:ℕ):ℝ)<=N:=by
     rw[hN]; exact_mod_cast (by omega)
    have bd3:(h:ℝ)*ν<=2:=by
     have:(h:ℝ)<=H:=by exact_mod_cast hhH.le
     have:=(bl hν).mp (this.trans hH2); linarith
    have hc:0<=(h:ℝ)*(κ*ν^4):=by positivity
    calc dd g (B-h-1)-dd g A<=((B-h-1-A:ℕ):ℝ)*(h*(κ*ν^4)):=ht
     _<=N*(h*(κ*ν^4)):=by gcongr
     _=N*(κ*ν^3)*(h*ν):=by ring
     _<=N*(κ*ν^3)*2:=by gcongr
     _=_:=by ring
   have hw:2*ν^2/ν^4+1+2/ν^2<=5/ν^2:=by
    have e:2*ν^2/ν^4=2/ν^2:=by field_simp
    rw[e]
    have e2:(5:ℝ)/ν^2=2/ν^2+2/ν^2+1/ν^2:=by ring
    rw[e2]; linarith
   have hD0:0<=dd g (B-h-1)-dd g A:=by
    have:=aj4 g h2 (B-h-1-A) A le_rfl (by omega)
    rw[show A+(B-h-1-A)=B-h-1 by omega] at this
    have:(0:ℝ)<=((B-h-1-A:ℕ):ℝ)*ν^4:=by positivity
    linarith
   have hw0:0<=2*ν^2/ν^4+1+2/ν^2:=by positivity
   calc ‖∑ n∈Icc A (B-h),ee (φ (n+h)-φ n)‖
     <= 1+(dd g (B-h-1)-dd g A+2)*(2*ν^2/ν^4+1+2/ν^2):=key
    _<=1+(N*(2*κ*ν^3)+2)*(5/ν^2):=by gcongr
    _=1+10*N*κ*ν+10/ν^2:=by field_simp; ring
    _<=Bd:=by
     rw[hBd]
     have e:(11:ℝ)/ν^2=10/ν^2+1/ν^2:=by ring
     rw[e]; linarith
  ·
   have hc:(Icc A (B-h)).card<=1:=by rw[jv]; omega
   refine (uz _ _).trans ?_
   have:((Icc A (B-h)).card:ℝ)<=1:=by exact_mod_cast hc
   linarith
 have hCb:∀ r,r<H->∀ r',r'<H->‖C r r'‖<=(if r'=r then (N:ℝ) else 0)+Bd:=by
  intro r hr r' hr'
  rcases lt_trichotomy r' r with v7 | heq | hgt
  ·rw[if_neg v7.ne,ate r r' v7 hr,jy]
   exact awx (r-r') (by omega) (by omega)
  ·rw[if_pos heq,heq]; linarith[a0a r hr]
  ·rw[if_neg hgt.ne',az9,d4,ate r' r hgt hr',jy]
   exact awx (r'-r) (by omega) (by omega)
 have a32:∀ r,r<H->∑ r'∈range H,‖C r r'‖<=N+H*Bd:=by
  intro r hr
  refine (ao (fun r' hr'=>hCb r hr r' (bw.mp hr'))).trans ?_
  rw[cu,Finset.sum_ite_eq' (range H) r,if_pos (bw.mpr hr),
   a9,fa,cp]
 have bd4:∑ r∈range H,∑ r'∈range H,‖C r r'‖<=H*(N+H*Bd):=by
  refine (ao (fun r hr=>a32 r (bw.mp hr))).trans ?_
  rw[a9,fa,cp]
 have hW:=arq z hHA xh
 rw[<- hS'] at hW
 have hBH:((B+H-A:ℕ):ℝ)<=2*N:=by
  have:B+H-A<=2*N:=by omega
  exact_mod_cast this
 have u5:(H:ℝ)^2*‖∑ n∈Icc A B,ee (φ n)‖^2<=(2*N)*(H*(N+H*Bd)):=by
  refine hW.trans ?_
  have h0:0<=∑ r∈range H,∑ r'∈range H,‖C r r'‖:=
   cj (fun _ _=>cj (fun _ _=>aw _))
  calc ((B+H-A:ℕ):ℝ)*∑ r∈range H,∑ r'∈range H,‖C r r'‖
    <= (2*N)*∑ r∈range H,∑ r'∈range H,‖C r r'‖:=by gcongr
   _<=_:=by gcongr
 have hHp:(0:ℝ)<H:=by linarith
 have e:(2*(N:ℝ))*(H*(N+H*Bd))=(H:ℝ)^2*(2*N*(N/H+Bd)):=by
  field_simp
 rw[e] at u5
 have hX:=lg u5 (by positivity)
 have hNH:(N:ℝ)/H<=N*ν:=by
  rw[ay hHp]
  have:=(ay hν).mp hH1
  nlinarith
 calc ‖∑ n∈Icc A B,ee (φ n)‖^2<=2*N*(N/H+Bd):=hX
  _<=2*N*(N*ν+Bd):=by gcongr
  _ = 2*(N:ℝ)^2*ν+20*κ*(N:ℝ)^2*ν+22*N/ν^2:=by
      rw[hBd]; field_simp; ring
  _ ≤ _:=by
      have:2*(N:ℝ)^2*ν<=2*κ*(N:ℝ)^2*ν:=by
       have:0<=(N:ℝ)^2*ν:=by positivity
       nlinarith
      linarith
end bt.ZD
namespace bt.ZD
open Complex Finset Filter Topology
open scoped Real
noncomputable def cn (s:ℂ) (n:ℕ):ℂ:=
 ∫ x in (n:ℝ)..(n+1),((x-n:ℝ):ℂ)*(x:ℂ)^(-s-1)
lemma ahs {x:ℝ} (hx:0<x) (r:ℂ):(x:ℂ)^(r+1)=x*(x:ℂ)^r:=by
 rw[js _ _ (ofReal_ne_zero.mpr hx.ne'),p6,gx]
lemma zw (s:ℂ) {n:ℕ} (hn:1<=n):
  ContinuousOn (fun x:ℝ=>((x-n:ℝ):ℂ)*(x:ℂ)^(-s-1)) (ko (n:ℝ) (n+1)):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 intro x hx
 rw[gj (by linarith)] at hx
 have tp:0<x:=by linarith[hx.1]
 apply ie
 apply p4
 ·exact (continuous_ofReal.comp (ps.sub dm)).continuousAt
 ·exact continuousAt_ofReal_cpow_const x _ (Or.inr tp.ne')
lemma aij {s:ℂ} (xc:s≠0) (uu:s≠1) {n:ℕ} (hn:1<=n):
  cn s n=((n+1:ℂ)^(1-s)-(n:ℂ)^(1-s))/(1-s)+
   n*((n+1:ℂ)^(-s)-(n:ℂ)^(-s))/s:=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have h1s:(1-s)≠0:=cb.mpr (qg uu)
 set F:ℝ->ℂ:=fun y=>(y:ℂ)^(1-s)/(1-s)+n*(y:ℂ)^(-s)/s with hF
 have adu:∀ x∈ko (n:ℝ) (n+1),HasDerivAt F
   (((x-n:ℝ):ℂ)*(x:ℂ)^(-s-1)) x:=by
  intro x hx
  rw[gj (by linarith)] at hx
  have tp:0<x:=by linarith[hx.1]
  have d1:=(qy tp.ne' h1s).div_const (1-s)
  have d2:=((qy tp.ne' (neg_ne_zero.mpr xc)).const_mul
   (n:ℂ)).div_const s
  refine (d1.add d2).congr_deriv ?_
  have e1:(1-s-1:ℂ)=(-s-1)+1:=by ring
  rw[e1,ahs tp]
  field_simp
  push_cast
  ring
 have hint:=(zw s hn).intervalIntegrable (μ:=MeasureTheory.volume)
 unfold cn
 rw[intervalIntegral.integral_eq_sub_of_hasDerivAt adu hint]
 simp only[hF]
 push_cast
 field_simp
 ring
lemma acf {s:ℂ} (hs:0<=s.re) {n:ℕ} (hn:1<=n):
  ‖cn s n‖<=(n:ℝ)^(-s.re-1):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have:=gs (a:=(n:ℝ)) (b:=n+1)
  (C:=(n:ℝ)^(-s.re-1))
  (f:=fun x:ℝ=>((x-n:ℝ):ℂ)*(x:ℂ)^(-s-1)) (by
   intro x hx
   rw[Set.uIoc_of_le (by linarith)] at hx
   have tp:0<x:=by linarith[hx.1]
   rw[bo,ba,au,norm_cpow_eq_rpow_re_of_pos tp]
   have h1:|x-n|<=1:=by rw[abs_le]; constructor <;> linarith[hx.1,hx.2]
   have h2:x^(-s-1).re<=(n:ℝ)^(-s.re-1):=by
    have:(-s-1).re=-s.re-1:=by simp
    rw[this]
    exact c1 t6 hx.1.le (by linarith)
   calc |x-n| *x^(-s-1).re<=1*(n:ℝ)^(-s.re-1):=by
         gcongr
    _=_:=iq _)
 unfold cn
 simpa using this
lemma alp {s:ℂ} (hs:0<s.re) {n:ℕ} (hn:1<=n):
  ‖cn s n‖<=((n:ℝ)^(-s.re)-((n:ℝ)+1)^(-s.re))/s.re:=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hle:(n:ℝ)<=n+1:=by linarith
 unfold cn
 refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
 have wv:ContinuousOn (fun x:ℝ=>x^(-s.re-1)) (ko (n:ℝ) (n+1)):=by
  intro x hx
  rw[gj hle] at hx
  exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith[hx.1]))).continuousWithinAt
 have u6:∫ x in (n:ℝ)..(n+1),‖((x-n:ℝ):ℂ)*(x:ℂ)^(-s-1)‖<=
   ∫ x in (n:ℝ)..(n+1),x^(-s.re-1):=by
  apply ff hle
  ·exact ((zw s hn).norm).intervalIntegrable
  ·exact wv.intervalIntegrable
  ·intro x hx
   have tp:0<x:=by linarith[hx.1]
   rw[bo,ba,au,norm_cpow_eq_rpow_re_of_pos tp]
   have h1:|x-n|<=1:=by rw[abs_le]; constructor <;> linarith[hx.1,hx.2]
   have:(-s-1).re=-s.re-1:=by simp
   rw[this]
   calc |x-n| *x^(-s.re-1)<=1*x^(-s.re-1):=by gcongr
    _=_:=iq _
 refine u6.trans (i6 ?_)
 rw[pn (Or.inr ⟨by linarith,by
  rw[gj hle]; intro h; linarith[h.1]⟩)]
 have e:-s.re-1+1=-s.re:=by ring
 rw[e]
 have hs':-s.re≠0:=by linarith
 field_simp
 ring
lemma aiz {s:ℂ} (xc:s≠0) (uu:s≠1) {M:ℕ} (hM:1<=M):
  1/((M:ℂ)+1)^s=
   ((M:ℂ)^(1-s)-((M:ℂ)+1)^(1-s))/(s-1)-s*cn s M:=by
 have hM0:(0:ℝ)<M:=by exact_mod_cast hM
 have hMc:(M:ℂ)≠0:=by exact_mod_cast hM0.ne'
 have w6:(M:ℂ)+1≠0:=by
  have:(0:ℝ)<M+1:=by linarith
  exact_mod_cast this.ne'
 have h1s:(1-s)≠0:=cb.mpr (qg uu)
 have aw1:(s-1)≠0:=cb.mpr uu
 have ha:(M:ℂ)^(1-s)=M*(M:ℂ)^(-s):=by
  rw[show (1-s:ℂ)=-s+1 by ring,js _ _ hMc,p6,gx]
 have hb:((M:ℂ)+1)^(1-s)=((M:ℂ)+1)*((M:ℂ)+1)^(-s):=by
  rw[show (1-s:ℂ)=-s+1 by ring,js _ _ w6,p6,gx]
 have hc:1/((M:ℂ)+1)^s=((M:ℂ)+1)^(-s):=by
  rw[Complex.cpow_neg,jz]
 rw[aij xc uu hM,hc,ha,hb]
 field_simp
 ring
lemma agi {s:ℂ} (xc:s≠0) (uu:s≠1) {N:ℕ} (hN:1<=N) (j:ℕ):
  ∑ k∈range (N+j),1/((k:ℂ)+1)^s=
   ∑ k∈range N,1/((k:ℂ)+1)^s+((N:ℂ)^(1-s)-((N+j:ℕ):ℂ)^(1-s))/
    (s-1)-s*∑ k∈range j,cn s (k+N):=by
 induction j with
 | zero=>simp
 | succ j ih=>
  rw[show N+(j+1)=(N+j)+1 by ring,dk,ih,dk,
   aiz xc uu (show 1<=N+j by omega)]
  push_cast
  rw[show j+N=N+j by ring]
  ring
lemma ad0 {s:ℂ} (hs:1<s.re) {N:ℕ} (hN:1<=N):
  riemannZeta s=∑ k∈range N,1/((k:ℂ)+1)^s+(N:ℂ)^(1-s)/(s-1)-
   s*∑' k,cn s (k+N):=by
 have xc:s≠0:=by intro h; rw[h] at hs; simp at hs; linarith
 have uu:s≠1:=by intro h; rw[h] at hs; simp at hs
 have aeh:HasSum (fun k:ℕ=>1/((k:ℂ)+1)^s) (riemannZeta s):=by
  rw[og hs]
  have:Summable (fun k:ℕ=>1/((k:ℂ)+1)^s):=by
   have:=(gn 1).mpr (j7.mpr hs)
   simpa using this
  exact this.hasSum
 have ai8:Summable (fun k:ℕ=>cn s (k+N)):=by
  refine q0 (g:=fun k:ℕ=>((k+N:ℕ):ℝ)^(-s.re-1)) ?_ ?_
  ·exact (gn N).mpr (gr.mpr (by linarith))
  ·intro k; exact acf (by linarith) (by omega)
 have t1:Tendsto (fun j=>∑ k∈range (N+j),1/((k:ℂ)+1)^s) atTop
   (𝓝 (riemannZeta s)):=by
  have:=aeh.tendsto_sum_nat.comp (tendsto_add_atTop_nat N)
  refine this.congr (fun j=>?_)
  simp only[mx,add_comm j N]
 have t2:Tendsto (fun j:ℕ=>((N+j:ℕ):ℂ)^(1-s)) atTop (𝓝 0):=by
  rw[o9]
  have h0:Tendsto (fun j:ℕ=>((N+j:ℕ):ℝ)^(-(s.re-1))) atTop (𝓝 0):=by
   have:=(s3 (show 0<s.re-1 by linarith)).comp
    (l6.comp (tendsto_add_atTop_nat N))
   refine this.congr (fun j=>?_)
   simp only[mx]; push_cast; ring_nf
  refine h0.congr (fun j=>?_)
  have tj:(0:ℝ)<((N+j:ℕ):ℝ):=by exact_mod_cast (show 0<N+j by omega)
  rw[show (((N+j:ℕ):ℂ))=(((N+j:ℕ):ℝ):ℂ) by push_cast; rfl,
   norm_cpow_eq_rpow_re_of_pos tj]
  congr 1; simp
 have t3:Tendsto (fun j=>∑ k∈range j,cn s (k+N)) atTop (𝓝 (∑' k,cn s (k+N))):=
  ai8.hasSum.tendsto_sum_nat
 have t4:Tendsto (fun j=>∑ k∈range N,1/((k:ℂ)+1)^s+
   ((N:ℂ)^(1-s)-((N+j:ℕ):ℂ)^(1-s))/(s-1)-
    s*∑ k∈range j,cn s (k+N)) atTop
   (𝓝 (∑ k∈range N,1/((k:ℂ)+1)^s+((N:ℂ)^(1-s)-0)/(s-1)-
    s*∑' k,cn s (k+N))):=by
  refine ((g6.add ((g6.sub t2).div_const _)).sub
   (g6.mul t3))
 have:=ub t1 (t4.congr (fun j=>(agi xc uu hN j).symm))
 rw[this,kg]
def vn:Set ℂ:={s | 1/4<s.re∧1<s.im}
lemma yy:IsOpen vn:=
 (n2 dm f0).inter
  (n2 dm Complex.continuous_im)
lemma aht:Convex ℝ vn:=
 (s4 (1/4)).inter (convex_halfSpace_im_gt 1)
lemma z5 {s:ℂ} (hs:s∈vn):s≠0∧s≠1:=by
 obtain ⟨_,h2⟩:=hs
 constructor <;> (intro h; rw[h] at h2; simp at h2; try linarith)
lemma adb (N k:ℕ) (hN:1<=N):
  DifferentiableOn ℂ (fun s=>cn s (k+N)) vn:=by
 have hn:1<=k+N:=by omega
 have t6:((k+N:ℕ):ℂ)≠0:=by exact_mod_cast (show k+N≠0 by omega)
 have xb:((k+N:ℕ):ℂ)+1≠0:=by
  have:(0:ℝ)<((k+N:ℕ):ℝ)+1:=by positivity
  exact_mod_cast this.ne'
 refine DifferentiableOn.congr (f:=fun s:ℂ=>
   ((((k+N:ℕ):ℂ)+1)^(1-s)-((k+N:ℕ):ℂ)^(1-s))/(1-s)+
   ((k+N:ℕ):ℂ)*((((k+N:ℕ):ℂ)+1)^(-s)-((k+N:ℕ):ℂ)^(-s))/s) ?_ ?_
 ·intro s hs
  obtain ⟨h0,h1⟩:=z5 hs
  have h1s:(1-s)≠0:=cb.mpr (qg h1)
  apply c3
  apply DifferentiableAt.add
  ·apply ld _ _ h1s
   ·exact ((bu.const_sub 1).const_cpow (Or.inl xb)).sub
     ((bu.const_sub 1).const_cpow (Or.inl t6))
   ·exact bu.const_sub 1
  ·apply ld _ bu h0
   exact (((bu.neg).const_cpow (Or.inl xb)).sub
    ((bu.neg).const_cpow (Or.inl t6))).const_mul _
 ·intro s hs
  obtain ⟨h0,h1⟩:=z5 hs
  show cn s (k+N)=_
  rw[aij h0 h1 hn]
theorem ab2 {s:ℂ} (hs:s∈vn) {N:ℕ} (hN:1<=N):
  riemannZeta s=∑ k∈range N,1/((k:ℂ)+1)^s+(N:ℂ)^(1-s)/(s-1)-
   s*∑' k,cn s (k+N):=by
 set g:ℂ->ℂ:=fun s=>∑ k∈range N,1/((k:ℂ)+1)^s+(N:ℂ)^(1-s)/(s-1)-
     s*∑' k,cn s (k+N) with hg
 have hNc:(N:ℂ)≠0:=by exact_mod_cast (show N≠0 by omega)
 have zt:AnalyticOnNhd ℂ riemannZeta vn:=by
  apply pe _ yy
  intro s hs
  exact (je (z5 hs).2).differentiableWithinAt
 have hgd:DifferentiableOn ℂ g vn:=by
  have a0b:DifferentiableOn ℂ (fun s=>∑' k,cn s (k+N)) vn:=by
   refine differentiableOn_tsum_of_summable_norm
    (u:=fun k:ℕ=>((k+N:ℕ):ℝ)^(-(5/4:ℝ)))
    ((gn N).mpr (gr.mpr (by norm_num)))
    (fun k=>adb N k hN) yy ?_
   intro k s hs
   refine (acf (by linarith[hs.1]) (by omega)).trans ?_
   apply al
   ·exact_mod_cast (show 1<=k+N by omega)
   ·linarith[hs.1]
  intro s hs
  obtain ⟨h0,h1⟩:=z5 hs
  have aw1:s-1≠0:=cb.mpr h1
  apply qr
  ·apply DifferentiableWithinAt.add
   ·apply c3
    apply mj
    intro k _
    have hk:((k:ℂ)+1)≠0:=by
     have:(0:ℝ)<(k:ℝ)+1:=by positivity
     exact_mod_cast this.ne'
    apply ld (nm _) _
    ·exact mm h0 |>.mpr hk |> fun h=>by
      simpa using (mm h0).mpr hk
    ·exact bu.const_cpow (Or.inl hk)
   ·apply c3
    exact ((bu.const_sub 1).const_cpow (Or.inl hNc)).div
     (bu.sub_const 1) aw1
  ·exact differentiableWithinAt_id.mul (a0b s hs)
 have hgA:AnalyticOnNhd ℂ g vn:=hgd.analyticOnNhd yy
 have hz0:(2+2*I:ℂ)∈vn:=by
  constructor <;> norm_num
 have hev:riemannZeta =ᶠ[𝓝 (2+2*I)] g:=by
  have an4:IsOpen {s:ℂ | 1<s.re}:=n2 dm f0
  filter_upwards[an4.mem_nhds (show (1:ℝ)<(2+2*I:ℂ).re by norm_num)]
   with s hs
  exact ad0 hs hN
 exact zt.eqOn_of_preconnected_of_eventuallyEq hgA aht.isPreconnected hz0 hev hs
theorem ad1 {s:ℂ} (hs:0<s.re) {N:ℕ} (hN:1<=N):
  ‖s*∑' k,cn s (k+N)‖<=‖s‖*((N:ℝ)^(-s.re)/s.re):=by
 have hsum:Summable (fun k:ℕ=>‖cn s (k+N)‖):=by
  refine d9 (fun _=>aw _) (fun k=>acf hs.le (by omega))
   ((gn N).mpr (gr.mpr (by linarith)))
 rw[bo]
 gcongr
 refine (gw hsum).trans ?_
 refine hsum.tsum_le_of_sum_range_le (fun j=>?_)
 have hb:∀ k∈range j,‖cn s (k+N)‖<=
   (((k+N:ℕ):ℝ)^(-s.re)-(((k+1+N:ℕ):ℝ))^(-s.re))/s.re:=by
  intro k _
  refine (alp hs (by omega)).trans (i6 ?_)
  push_cast; ring_nf
 refine (ao hb).trans ?_
 rw[<- ew]
 have:=r0 (fun k=>(((k+N:ℕ):ℝ))^(-s.re)) j
 rw[this]
 simp only[jy]
 have:0<=(((j+N:ℕ):ℝ))^(-s.re):=by positivity
 gcongr
 linarith
end bt.ZD
namespace bt.ZD
open Complex Finset Filter Topology
open scoped Real
lemma aw2 {x:ℝ} (hx:0<x):
  1/(x+1)<=aa (x+1)-aa x∧aa (x+1)-aa x<=1/x:=by
 have x2:0<x+1:=by linarith
 rw[<- ik x2.ne' hx.ne']
 have hr:0<(x+1)/x:=by positivity
 constructor
 ·have:=b5 hr
  have e:1-((x+1)/x)⁻¹=1/(x+1):=by field_simp; ring
  linarith
 ·have:=bz hr
  have e:(x+1)/x-1=1/x:=by field_simp; ring
  linarith
lemma aw3 {x:ℝ} (hx:0<x):
  1/(x+1)^2<=-(aa (x+2)-2*aa (x+1)+aa x):=by
 have x2:0<x+1:=by linarith
 have hx2:0<x+2:=by linarith
 have e:-(aa (x+2)-2*aa (x+1)+aa x)=
   aa ((x+1)^2/(x*(x+2))):=by
  rw[ik (by positivity) (by positivity),ca hx.ne' hx2.ne',cq]
  push_cast; ring
 rw[e]
 have hr:0<(x+1)^2/(x*(x+2)):=by positivity
 have:=b5 hr
 have e2:1-((x+1)^2/(x*(x+2)))⁻¹=1/(x+1)^2:=by field_simp; ring
 linarith
lemma aw4 {x:ℝ} (hx:0<x):
  2/(x+3)^3<=aa (x+3)-3*aa (x+2)+3*aa (x+1)-aa x∧
  aa (x+3)-3*aa (x+2)+3*aa (x+1)-aa x<=2/x^3:=by
 have x2:0<x+1:=by linarith
 have hx2:0<x+2:=by linarith
 have hx3:0<x+3:=by linarith
 set r:=(x+1)^3*(x+3)/(x*(x+2)^3) with aj8
 have hr:0<r:=by positivity
 have e:aa (x+3)-3*aa (x+2)+3*aa (x+1)-aa x=
   aa r:=by
  rw[aj8,ik (by positivity) (by positivity),ca (by positivity)
   hx3.ne',ca hx.ne' (by positivity),cq,cq]
  push_cast; ring
 rw[e]
 have hr1:r-1=(2*x+3)/(x*(x+2)^3):=by rw[aj8]; field_simp; ring
 have hr2:1-r⁻¹=(2*x+3)/((x+1)^3*(x+3)):=by rw[aj8]; field_simp; ring
 constructor
 ·have:=b5 hr
  have:2/(x+3)^3<=(2*x+3)/((x+1)^3*(x+3)):=by
   rw[ax (by positivity) (by positivity)]
   nlinarith[c4 x,ji hx hx,ji (ji hx hx) hx]
  linarith
 ·have:=bz hr
  have:(2*x+3)/(x*(x+2)^3)<=2/x^3:=by
   rw[ax (by positivity) (by positivity)]
   nlinarith[c4 x,ji hx hx,ji (ji hx hx) hx]
  linarith
noncomputable def psi (c:ℝ) (n:ℕ):ℝ:=c*aa n
lemma aw6 {c:ℝ} (hc:0<=c) {n:ℕ} (hn:1<=n):
  2*c/((n:ℝ)+3)^3<=d3 (psi c) n∧d3 (psi c) n<=2*c/(n:ℝ)^3:=by
 have hx:(0:ℝ)<n:=by exact_mod_cast hn
 obtain ⟨h1,h2⟩:=aw4 hx
 have e:d3 (psi c) n=c*(aa ((n:ℝ)+3)-3*aa ((n:ℝ)+2)+
   3*aa ((n:ℝ)+1)-aa n):=by
  simp only[d3,d2,dd,psi]; push_cast; ring_nf
 rw[e]
 constructor
 ·have:=ab h1 hc
  calc 2*c/((n:ℝ)+3)^3=c*(2/((n:ℝ)+3)^3):=by ring
   _<=_:=this
 ·have:=ab h2 hc
  calc _<=c*(2/(n:ℝ)^3):=this
   _=_:=by ring
lemma ap2 {c:ℝ} (hc:0<=c) {n:ℕ} (hn:1<=n):
  c/((n:ℝ)+1)^2<=dd (fun m=>-psi c m) (n+1)-dd (fun m=>-psi c m) n:=by
 have hx:(0:ℝ)<n:=by exact_mod_cast hn
 have h:=aw3 hx
 have e:dd (fun m=>-psi c m) (n+1)-dd (fun m=>-psi c m) n=
   c*(-(aa ((n:ℝ)+2)-2*aa ((n:ℝ)+1)+aa n)):=by
  simp only[dd,psi]; push_cast; ring_nf
 rw[e]
 have:=ab h hc
 calc c/((n:ℝ)+1)^2=c*(1/((n:ℝ)+1)^2):=by ring
  _<=_:=this
lemma aj9 {c:ℝ} (hc:0<=c) {n:ℕ} (hn:1<=n):
  c/((n:ℝ)+1)<=dd (psi c) n∧dd (psi c) n<=c/n:=by
 have hx:(0:ℝ)<n:=by exact_mod_cast hn
 obtain ⟨h1,h2⟩:=aw2 hx
 have e:dd (psi c) n=c*(aa ((n:ℝ)+1)-aa n):=by
  simp only[dd,psi]; push_cast; ring
 rw[e]
 constructor
 ·have:=ab h1 hc
  calc c/((n:ℝ)+1)=c*(1/((n:ℝ)+1)):=by ring
   _<=_:=this
 ·have:=ab h2 hc
  calc _<=c*(1/(n:ℝ)):=this
   _=_:=by ring
lemma alq {c:ℝ} (hc:0<=c) {n:ℕ} (hn:1<=n):
  dd (psi c) (n+1)<=dd (psi c) n:=by
 have hx:(0:ℝ)<n:=by exact_mod_cast hn
 have e:∀ m:ℕ,1<=m->dd (psi c) m=c*aa (((m:ℝ)+1)/m):=by
  intro m hm
  have hm0:(0:ℝ)< m:=by exact_mod_cast hm
  simp only[dd,psi]; push_cast
  rw[ik (by positivity) hm0.ne']; ring
 rw[e n hn,e (n+1) (by omega)]
 apply ab _ hc
 apply a5 (by positivity)
 push_cast
 rw[ax (by positivity) hx]
 nlinarith
lemma aak {τ:ℝ} (u0:4<=τ):
  0<τ^5/(2*π)∧τ^5/(2*π)<=τ^5∧τ^5/8<=τ^5/(2*π)∧
   (16:ℝ)<=τ^2∧(1024:ℝ)<=τ^5:=by
 have hpi:3<π:=jq
 have a33:π<4:=j3
 have vh:0<τ:=by linarith
 have h5:(1024:ℝ)<=τ^5:=by
  have:=aj (by norm_num) u0 5; norm_num at this; linarith
 refine ⟨by positivity, ?_, ?_,by nlinarith,h5⟩
 ·rw[ay (by positivity)]; nlinarith[fb vh 5]
 ·rw[ax (by norm_num) (by positivity)]; nlinarith[fb vh 5]
lemma a34 {τ c:ℝ} {P m:ℕ} (hPm:m<2*P) (u0:0<τ) (h1:(P:ℝ)<=τ^2):
  ‖∑ n∈Icc P m,ee (psi c n)‖^2<=2000*P*τ^2:=by
 have aa0:((Icc P m).card:ℝ)<=P:=by
  rw[jv]; exact_mod_cast (show m+1-P<=P by omega)
 have aa2:=(uz (Icc P m) (psi c)).trans aa0
 have hP0:(0:ℝ)<=P:=by positivity
 have a1:‖∑ n∈Icc P m,ee (psi c n)‖^2<=(P:ℝ)*(P:ℝ):=by
  rw[sq]; exact a8 aa2 aa2 (aw _) hP0
 have a2:(P:ℝ)*(P:ℝ)<=(P:ℝ)*τ^2:=ab h1 hP0
 have a3:(P:ℝ)*τ^2<=2000*P*τ^2:=by
  have:0<=(P:ℝ)*τ^2:=by positivity
  linarith
 linarith
lemma a0c {τ c:ℝ} (u0:4<=τ) (hc:c=τ^5/(2*π)) {P m:ℕ} (hP:1<=P)
  (hPm:P<=m) (hm:m<2*P) (h1:τ^2<P) (h2:(P:ℝ)<=τ^3):
  ‖∑ n∈Icc P m,ee (psi c n)‖^2<=2000*P*τ^2:=by
 obtain ⟨t9,acg,-,-,bcm⟩:=aak u0
 rw[<- hc] at t9 acg
 have vh:0<τ:=by linarith
 have hP0:(1:ℝ)<=P:=by exact_mod_cast hP
 have wa:(0:ℝ)<P:=by linarith
 set ν:ℝ:=(c/(4*(P:ℝ)^3))^((4:ℕ)⁻¹:ℝ) with a6v
 have hq:0<c/(4*(P:ℝ)^3):=by positivity
 have aw7:0<ν:=dc hq _
 have akb:ν^4=c/(4*(P:ℝ)^3):=g2 hq.le (by norm_num)
 have hP3:τ^6<=(P:ℝ)^3:=by
  have:=aj (by positivity) h1.le 3
  calc τ^6=(τ^2)^3:=by ring
   _<=_:=this
 have bcn:τ^5<=τ^6:=fy (by linarith) (by norm_num)
 have a8w:ν^4<=1/4:=by
  rw[akb,ax (by positivity) (by norm_num)]; linarith
 have ars:ν^2<=1/2:=by
  have e:ν^4=(ν^2)^2:=by ring
  nlinarith[c4 (ν^2)]
 have bd5:64<=c:=by
  have a33:π<4:=j3
  rw[hc,bl (by positivity)]; nlinarith
 have hA:2/ν<=P:=by
  have h16:(2/ν)^4<=(P:ℝ)^4:=by
   rw[l8,akb,ay (by positivity)]
   have e:(P:ℝ)^4*(c/(4*(P:ℝ)^3))=P*c/4:=by field_simp
   rw[e]
   have:(64:ℝ)<=P*c:=by nlinarith
   linarith
  exact (d8 (by positivity) wa.le (by norm_num)).mp h16
 have h3:∀ n,P<=n->n+3<=m->ν^4<=d3 (psi c) n∧d3 (psi c) n<=8*ν^4:=by
  intro n hn hn3
  obtain ⟨a,b⟩:=aw6 t9.le (show 1<=n by omega)
  have t6:(P:ℝ)<=n:=by exact_mod_cast hn
  have bco:(0:ℝ)<n:=by linarith
  have hn2:(n:ℝ)+3<=2*P:=by
   have:n+3<=2*P:=by omega
   exact_mod_cast this
  rw[akb]
  constructor
  ·refine br ?_ a
   rw[ax (by positivity) (by positivity)]
   have h:=aj (by positivity) hn2 3
   have h':=ab h t9.le
   have e:c*(2*(P:ℝ))^3=2*c*(4*(P:ℝ)^3):=by ring
   linarith
  ·refine b.trans ?_
   have:=aj (by positivity) t6 3
   rw[ay (by positivity)]
   have e:8*(c/(4*(P:ℝ)^3))*(n:ℝ)^3=2*c*((n:ℝ)^3/(P:ℝ)^3):=by
    field_simp; ring
   rw[e]
   have:1<=(n:ℝ)^3/(P:ℝ)^3:=by rw[bl (by positivity)]; linarith
   nlinarith
 have key:=agg (psi c) hPm aw7 ars (by norm_num) hA h3
 have hN:((m-P+1:ℕ):ℝ)<=P:=by exact_mod_cast (show m-P+1<=P by omega)
 have hN0:(0:ℝ)<=((m-P+1:ℕ):ℝ):=by positivity
 have a35:(P:ℝ)*ν<=τ^2:=by
  have h4:((P:ℝ)*ν)^4<=(τ^2)^4:=by
   rw[i5,akb]
   have e:(P:ℝ)^4*(c/(4*(P:ℝ)^3))=P*c/4:=by field_simp
   rw[e,ay (by norm_num)]
   have:(P:ℝ)*c<=τ^3*τ^5:=a8 h2 acg t9.le (by positivity)
   have e2:(τ^2)^4=τ^3*τ^5:=by ring
   have:0<=τ^3*τ^5:=by positivity
   linarith
  exact (d8 (by positivity) (by positivity) (by norm_num)).mp h4
 have aw9:1/ν^2<=6*τ^2:=by
  have h4:(1/ν^2)^2<=(6*τ^2)^2:=by
   have e:(1/ν^2)^2=4*(P:ℝ)^3/c:=by
    rw[l8,sf,<- ox,akb]; field_simp
   rw[e,ay t9]
   have hP9:(P:ℝ)^3<=τ^9:=by
    have:=aj (by positivity) h2 3
    calc (P:ℝ)^3<=(τ^3)^3:=this
     _=τ^9:=by ring
   have a36:τ^5/8<=c:=(aak u0).2.2.1.trans (i6 hc.symm)
   have h:=ab a36 (by positivity:(0:ℝ)<=36*τ^4)
   have e2:(6*τ^2)^2=36*τ^4:=by ring
   have e3:36*τ^4*(τ^5/8)=9/2*τ^9:=by ring
   rw[e2]
   linarith
  exact (d8 (by positivity) (by positivity) (by norm_num)).mp h4
 have hi:0<=1/ν^2:=by positivity
 have e1:22*((m-P+1:ℕ):ℝ)/ν^2=22*((m-P+1:ℕ):ℝ)*(1/ν^2):=by
  ring
 have b1:22*8*((m-P+1:ℕ):ℝ)^2*ν<=176*P*τ^2:=by
  have hNN:((m-P+1:ℕ):ℝ)^2<=(P:ℝ)*P:=by
   rw[sq]; exact a8 hN hN hN0 (by positivity)
  have h1':((m-P+1:ℕ):ℝ)^2*ν<=(P:ℝ)*P*ν:=
   ag hNN aw7.le
  have h2':(P:ℝ)*P*ν<=P*τ^2:=by
   rw[gv]; exact ab a35 (by positivity)
  have e:22*8*((m-P+1:ℕ):ℝ)^2*ν=176*(((m-P+1:ℕ):ℝ)^2*ν):=by
   ring
  rw[e]; linarith
 have b2:22*((m-P+1:ℕ):ℝ)*(1/ν^2)<=132*P*τ^2:=by
  have:((m-P+1:ℕ):ℝ)*(1/ν^2)<=P*(6*τ^2):=
   a8 hN aw9 hi (by positivity)
  have e:22*((m-P+1:ℕ):ℝ)*(1/ν^2)=22*(((m-P+1:ℕ):ℝ)*(1/ν^2)):=by
   ring
  rw[e]; linarith
 have hP2:0<=(P:ℝ)*τ^2:=by positivity
 linarith
lemma axa {τ c:ℝ} (u0:4<=τ) (hc:c=τ^5/(2*π)) {P m:ℕ} (hP:1<=P)
  (a37:P+1<=m) (hm:m<2*P) (h2:τ^3<P) (h3:(P:ℝ)<=τ^5):
  ‖∑ n∈Icc P m,ee (psi c n)‖^2<=2000*P*τ^2:=by
 obtain ⟨t9,acg,ajb,a0d,-⟩:=aak u0
 rw[<- hc] at t9 acg ajb
 have vh:0<τ:=by linarith
 have hP0:(1:ℝ)<=P:=by exact_mod_cast hP
 have wa:(0:ℝ)<P:=by linarith
 set lam:ℝ:=c/(4*(P:ℝ)^2) with vu
 have ajc:0<lam:=by positivity
 have h2':∀ n,P<=n->n+2<=m->lam<=dd (fun k=>-psi c k) (n+1)-
   dd (fun k=>-psi c k) n:=by
  intro n hn hn2
  refine br ?_ (ap2 t9.le (show 1<=n by omega))
  have xb:(n:ℝ)+1<=2*P:=by
   have:n+1<=2*P:=by omega
   exact_mod_cast this
  rw[vu,ax (by positivity) (by positivity)]
  have:=aj (by positivity) xb 2
  nlinarith
 have key:=afg (fun k=>-psi c k) a37 ajc h2'
 have hD:dd (fun k=>-psi c k) (m-1)-dd (fun k=>-psi c k) P<=c/P:=by
  have a1:=(aj9 t9.le (show 1<=m-1 by omega)).1
  have a2:=(aj9 t9.le hP).2
  have e1:dd (fun k=>-psi c k) (m-1)=-dd (psi c) (m-1):=by simp only[dd]; ring
  have e2:dd (fun k=>-psi c k) P=-dd (psi c) P:=by simp only[dd]; ring
  rw[e1,e2]
  have:0<=c/(((m-1:ℕ):ℝ)+1):=by positivity
  linarith
 have hS1:‖∑ n∈Icc P m,ee (psi c n)‖<=(c/P+2)*(6+4/ak lam):=by
  have e:∑ n∈Icc P m,ee (psi c n)=(starRingEnd ℂ) (∑ n∈Icc P m,ee (-psi c n)):=by
   rw[m9]
   exact ai rfl (fun n _=>by rw[adw,Complex.conj_conj])
  rw[e,d4]
  refine key.trans ?_
  have:0<=6+4/ak lam:=by positivity
  exact ag (by linarith) this
 have hX:(c/P+2)^2<=2*(c/P)^2+8:=by nlinarith[c4 (c/P-2)]
 have zr:(4/ak lam)^2=16/lam:=by
  rw[l8,ly ajc.le]; norm_num
 have hY:(6+4/ak lam)^2<=72+2*(16/lam):=by
  nlinarith[c4 (6-4/ak lam)]
 have aup:16/lam=64*(P:ℝ)^2/c:=by rw[vu]; field_simp; ring
 have t1:(c/P)^2<=P*τ^2:=by
  rw[l8,ay (by positivity)]
  have hP3:τ^9<=(P:ℝ)^3:=by
   have:=aj (by positivity) h2.le 3
   calc τ^9=(τ^3)^3:=by ring
    _<=_:=this
  have:c^2<=τ^10:=by
   have:=aj t9.le acg 2
   calc c^2<=(τ^5)^2:=this
    _=τ^10:=by ring
  have e:(P:ℝ)*τ^2*(P:ℝ)^2=(P:ℝ)^3*τ^2:=by ring
  rw[e]
  nlinarith[fb vh 9,fb vh 2,fb vh 10]
 have t2:c<=P*τ^2:=by
  have:τ^3*τ^2<=P*τ^2:=by gcongr
  nlinarith[fb vh 5]
 have t4:(P:ℝ)^2/c<=P*τ^2:=by
  rw[ay t9]
  have:(P:ℝ)<=τ^2*c:=by
   have:τ^5<=τ^2*(τ^5/8):=by nlinarith[fb vh 5]
   nlinarith
  nlinarith
 have hS2:‖∑ n∈Icc P m,ee (psi c n)‖^2<=
   (2*(c/P)^2+8)*(72+2*(64*(P:ℝ)^2/c)):=by
  have tj:0<=‖∑ n∈Icc P m,ee (psi c n)‖:=aw _
  calc ‖∑ n∈Icc P m,ee (psi c n)‖^2<=((c/P+2)*(6+4/ak lam))^2:=
        aj tj hS1 2
   _=(c/P+2)^2*(6+4/ak lam)^2:=by ring
   _ ≤ (2*(c/P)^2+8)*(72+2*(16/lam)):=
       a8 hX hY (by positivity) (by positivity)
   _=_:=by rw[aup]
 have e:(2*(c/P)^2+8)*(72+2*(64*(P:ℝ)^2/c))=
   144*(c/P)^2+256*c+576+1024*((P:ℝ)^2/c):=by
  field_simp; ring
 rw[e] at hS2
 have t3:(1:ℝ)<=P*τ^2:=by nlinarith
 linarith
lemma a0e {τ c:ℝ} (u0:4<=τ) (hc:c=τ^5/(2*π)) {P m:ℕ} (hP:1<=P)
  (hPm:P<=m) (hm:m<2*P) (h3:τ^5<P) (axb:(P:ℝ)<=2*τ^10):
  ‖∑ n∈Icc P m,ee (psi c n)‖^2<=2000*P*τ^2:=by
 obtain ⟨t9,acg,ajb,a0d,-⟩:=aak u0
 rw[<- hc] at t9 acg ajb
 have hpi:3<π:=jq
 have vh:0<τ:=by linarith
 have hP0:(1:ℝ)<=P:=by exact_mod_cast hP
 have wa:(0:ℝ)<P:=by linarith
 set δ:ℝ:=c/(2*P) with uf
 have ahu:0<δ:=by positivity
 have zn:δ<=1/2:=by
  rw[uf,ax (by positivity) (by norm_num)]; nlinarith
 have h15:(3/2)*c<=P:=by
  have:(3/2)*c<=τ^5:=by
   rw[hc]
   have e:(3/2:ℝ)*(τ^5/(2*π))=τ^5*(3/(4*π)):=by ring
   rw[e]
   have:3/(4*π)<=1:=by rw[dw (by positivity)]; linarith
   nlinarith[fb vh 5]
  linarith
 have hd:∀ n,P<=n->n< m->((0:ℤ):ℝ)+δ<=psi c (n+1)-psi c n∧
   psi c (n+1)-psi c n<=((0:ℤ):ℝ)+1-δ:=by
  intro n hn hnm
  obtain ⟨a,b⟩:=aj9 t9.le (show 1<=n by omega)
  simp only[dd] at a b
  have t6:(P:ℝ)<=n:=by exact_mod_cast hn
  have xb:(n:ℝ)+1<=2*P:=by
   have:n+1<=2*P:=by omega
   exact_mod_cast this
  simp only[Int.cast_zero,jy]
  constructor
  ·refine br ?_ a
   rw[uf,ax (by positivity) (by positivity)]; nlinarith
  ·refine b.trans ?_
   have h4:c/n<=c/P:=bb t9.le wa t6
   have h5:c/P+δ<=1:=by
    rw[uf]
    have e:c/P+c/(2*P)=(3/2)*c/P:=by field_simp; ring
    rw[e,dw wa]; exact h15
   linarith
 have key:=ady (psi c) hPm ahu zn 0 hd (by
  intro n hn xb
  have:=alq t9.le (show 1<=n by omega)
  simpa [dd] using this)
 have hS1:‖∑ n∈Icc P m,ee (psi c n)‖<=4*P/c:=by
  refine key.trans (i6 ?_)
  rw[uf]; field_simp; ring
 have hc2:τ^10/64<=c^2:=by
  have:=aj (by positivity) ajb 2
  calc τ^10/64=(τ^5/8)^2:=by ring
   _<=_:=this
 have tj:0<=‖∑ n∈Icc P m,ee (psi c n)‖:=aw _
 calc ‖∑ n∈Icc P m,ee (psi c n)‖^2<=(4*P/c)^2:=aj tj hS1 2
  _=16*P*P/c^2:=by ring
  _ ≤ _:=by
      rw[ay (by positivity)]
      have:16*(P:ℝ)<=2000*c^2*τ^2:=by
       nlinarith[fb vh 10,fb vh 12]
      nlinarith
theorem abj {τ:ℝ} (u0:4<=τ) {P m:ℕ} (hP:1<=P) (hPm:P<=m) (hm:m<2*P)
  (axb:(P:ℝ)<=2*τ^10):
  ‖∑ n∈Icc P m,ee (psi (τ^5/(2*π)) n)‖^2<=2000*P*τ^2:=by
 have vh:0<τ:=by linarith
 by_cases hmP:m=P
 ·have h1:‖∑ n∈Icc P m,ee (psi (τ^5/(2*π)) n)‖=1:=by
   rw[hmP,Finset.Icc_self,nw,w5]
  rw[h1]
  have hP0:(1:ℝ)<=P:=by exact_mod_cast hP
  have:(16:ℝ)<=τ^2:=(aak u0).2.2.2.1
  nlinarith
 rcases ig (P:ℝ) (τ^2) with h1 | h1
 ·exact a34 hm vh h1
 rcases ig (P:ℝ) (τ^3) with h2 | h2
 ·exact a0c u0 rfl hP hPm hm h1 h2
 rcases ig (P:ℝ) (τ^5) with h3 | h3
 ·exact axa u0 rfl hP (by omega) hm h2 h3
 ·exact a0e u0 rfl hP hPm hm h3 axb
lemma ai0 (a:ℕ->ℝ) (w:ℕ->ℂ) (P:ℕ) (J:ℕ):
  ∑ j∈range (J+1),(a (P+j):ℂ)*w (P+j)=
   (a (P+J):ℂ)*∑ i∈range (J+1),w (P+i)+
    ∑ j∈range J,((a (P+j)-a (P+j+1):ℝ):ℂ)*∑ i∈range (j+1),w (P+i):=by
 induction J with
 | zero=>simp
 | succ J ih=>
  rw[dk,ih,dk (fun j=>((a (P+j)-a (P+j+1):ℝ):ℂ)*_),
   dk (fun i=>w (P+i)) (J+1)]
  rw[show P+(J+1)=P+J+1 by ring]
  push_cast
  ring
theorem agj (a:ℕ->ℝ) (w:ℕ->ℂ) {P Q:ℕ} (hPQ:P<=Q)
  (ha0:∀ n,P<=n->n<=Q->0<=a n) (ha:∀ n,P<=n->n<Q->a (n+1)<=a n)
  {K:ℝ} (hW:∀ m,P<=m->m<=Q->‖∑ n∈Icc P m,w n‖<=K):
  ‖∑ n∈Icc P Q,(a n:ℂ)*w n‖<=a P*K:=by
 obtain ⟨J,rfl⟩:∃ J,Q=P+J:=⟨Q-P,by omega⟩
 have axc:∀ (f:ℕ->ℂ) (j:ℕ),∑ n∈Icc P (P+j),f n=∑ i∈range (j+1),f (P+i):=by
  intro f j
  rw[<- cy,dq]
  rw[show P+j+1-P=j+1 by omega]
 have hK:0<=K:=(aw _).trans (hW P le_rfl (by omega))
 rw[axc,ai0]
 refine (ds _ _).trans ?_
 have hW':∀ j,j<=J->‖∑ i∈range (j+1),w (P+i)‖<=K:=by
  intro j hj
  have:=hW (P+j) (by omega) (by omega)
  rwa[axc] at this
 have h1:‖(a (P+J):ℂ)*∑ i∈range (J+1),w (P+i)‖<=a (P+J)*K:=by
  rw[bo,ba,au,bh (ha0 _ (by omega) le_rfl)]
  exact ab (hW' J le_rfl) (ha0 _ (by omega) le_rfl)
 have h2:‖∑ j∈range J,((a (P+j)-a (P+j+1):ℝ):ℂ)*∑ i∈range (j+1),w (P+i)‖
   <= ∑ j∈range J,(a (P+j)-a (P+j+1))*K:=by
  refine (c5 _ _).trans (ao (fun j hj=>?_))
  have hj:=bw.mp hj
  have hd:0<=a (P+j)-a (P+j+1):=by
   have:=ha (P+j) (by omega) (by omega); linarith
  rw[bo,ba,au,bh hd]
  exact ab (hW' j hj.le) hd
 have h3:∑ j∈range J,(a (P+j)-a (P+j+1))*K=(a P-a (P+J))*K:=by
  rw[<- g3]
  have:=r0 (fun j=>a (P+j)) J
  simp only[ij] at this
  rw [show ∑ j∈range J,(a (P+j)-a (P+j+1))=
      ∑ j∈range J,(a (P+j)-a (P+(j+1))) by rfl,this]
 rw[h3] at h2
 have:a (P+J)*K+(a P-a (P+J))*K=a P*K:=by ring
 linarith
lemma ad3 {n:ℕ} (hn:1<=n) (t:ℝ):
  1/(n:ℂ)^((1/2:ℂ)+t *I)=
   ((1/ak n:ℝ):ℂ)*ee (-psi (t/(2*π)) n):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hnc:(n:ℂ)≠0:=by exact_mod_cast t6.ne'
 rw[js _ _ hnc]
 have h1:(n:ℂ)^(1/2:ℂ)=((ak n:ℝ):ℂ):=by
  rw[ft,lq t6.le]; push_cast; ring_nf
 have h2:(n:ℂ)^((t:ℂ)*I)=d6 (((t *aa n:ℝ):ℂ)*I):=by
  rw[gq hnc,show (n:ℂ)=((n:ℝ):ℂ) by push_cast; rfl,
   <- j8 t6.le]
  congr 1; push_cast; ring
 rw[h1,h2]
 unfold ee psi
 have hs:(ak n:ℂ)≠0:=by
  exact_mod_cast (iu.mpr t6).ne'
 have e3:(((2*π*-(t/(2*π)*aa n):ℝ):ℂ)*I)=
   -(((t *aa n:ℝ):ℂ)*I):=by
  push_cast; field_simp
 rw[e3,Complex.exp_neg]
 push_cast
 field_simp
lemma z6 (N j:ℕ):
  ∀ n∈(Icc 1 N).filter (fun n=>ed 2 n=j),2^j<=n∧n<2^(j+1):=by
 intro n hn
 simp only[ah,ar] at hn
 obtain ⟨⟨h1,_⟩,h2⟩:=hn
 constructor
 ·rw[<- h2]; exact n6 2 (by omega)
 ·rw[<- h2]; exact Nat.lt_pow_succ_log_self (by norm_num) n
theorem ach {τ:ℝ} (u0:4<=τ) {N:ℕ} (hN:(N:ℝ)<=2*τ^10):
  ‖∑ n∈Icc 1 N,1/(n:ℂ)^((1/2:ℂ)+(τ^5:ℝ)*I)‖<=
   45*τ*(ed 2 N+1):=by
 set c:=τ^5/(2*π) with hc
 have vh:0<τ:=by linarith
 rw[<- cx (g:=fun n=>ed 2 n) (t:=range (ed 2 N+1))
  (by
   intro n hn
   simp only[ar] at hn
   exact bw.mpr (o3 (ja hn.2)))]
 refine (c5 _ _).trans ?_
 have yu:∀ j,‖∑ n∈(Icc 1 N).filter (fun n=>ed 2 n=j),
   1/(n:ℂ)^((1/2:ℂ)+(τ^5:ℝ)*I)‖<=45*τ:=by
  intro j
  set G:=(Icc 1 N).filter (fun n=>ed 2 n=j) with hG
  rcases G.eq_empty_or_nonempty with he | te
  ·rw[he,k8,jw]; positivity
  have y7:∀ a∈G,∀ b∈G,∀ m,a<=m->m<=b->m∈G:=by
   intro a ha b hb m ham hmb
   simp only[hG,ah,ar] at ha hb ⊢
   refine ⟨⟨by omega,by omega⟩, ?_⟩
   have:=ja (b:=2) ham
   have:=ja (b:=2) hmb
   omega
  rw[zo G te y7]
  set p:=G.min' te
  set q:=G.max' te
  have hp:=z6 N j p (G.min'_mem te)
  have hq:=z6 N j q (G.max'_mem te)
  have hpq:p<=q:=G.min'_le _ (G.max'_mem te)
  have hpG:=G.min'_mem te
  have hqG:=G.max'_mem te
  simp only[hG,ah,ar] at hpG hqG
  have hp1:1<=p:=hpG.1.1
  have hq2:q<2*p:=by
   have:2^(j+1)=2*2^j:=by ring
   omega
  have hpN:(p:ℝ)<=2*τ^10:=by
   have:(p:ℝ)<=N:=by exact_mod_cast hpG.1.2
   linarith
  have vw:∀ n∈Icc p q,1/(n:ℂ)^((1/2:ℂ)+(τ^5:ℝ)*I)=
    ((1/ak n:ℝ):ℂ)*ee (-psi c n):=by
   intro n hn
   rw[ar] at hn
   exact ad3 (by omega) _
  rw[ai rfl vw]
  have axd:∀ m,p<=m->m<=q->‖∑ n∈Icc p m,ee (-psi c n)‖<=
    ak (2000*p*τ^2):=by
   intro m hm1 hm2
   have e:∑ n∈Icc p m,ee (-psi c n)=(starRingEnd ℂ) (∑ n∈Icc p m,ee (psi c n)):=by
    rw[m9]; exact ai rfl (fun n _=>adw _)
   rw[e,d4]
   apply ku
   exact abj u0 hp1 hm1 (by omega) hpN
  have:=agj (fun n=>1/ak n) (fun n=>ee (-psi c n)) hpq
   (fun n _ _=>by positivity)
   (fun n hn _=>by
    have h1:(0:ℝ)<ak n:=iu.mpr (by exact_mod_cast (show 0<n by omega))
    apply dr h1
    exact dg (by push_cast; linarith))
   axd
  refine this.trans ?_
  have zc:(0:ℝ)<p:=by exact_mod_cast hp1
  have hsp:0<ak p:=iu.mpr zc
  rw[mv (by positivity),mv (by norm_num),fk vh.le]
  have h45:ak 2000<=45:=by
   calc ak 2000<=ak (45^2):=dg (by norm_num)
    _=45:=fk (by norm_num)
  calc 1/ak p*(ak 2000*ak p*τ)=ak 2000*τ:=by
        field_simp
   _<=45*τ:=by gcongr
 calc ∑ j∈range (ed 2 N+1),‖∑ n∈(Icc 1 N).filter (fun n=>ed 2 n=j),
       1/(n:ℂ)^((1/2:ℂ)+(τ^5:ℝ)*I)‖
   <= ∑ j∈range (ed 2 N+1),45*τ:=ao (fun j _=>yu j)
  _=_:=by rw[a9,fa,cp]; push_cast; ring
theorem ade {t:ℝ} (ht:1024<=t):
  ‖riemannZeta ((1/2:ℂ)+t *I)‖<=
   45*t^((5:ℕ)⁻¹:ℝ)*(ed 2 ⌈t^2⌉₊+1)+6:=by
 have t8:0<t:=by linarith
 set τ:ℝ:=t^((5:ℕ)⁻¹:ℝ) with a82
 have abk:τ^5=t:=g2 t8.le (by norm_num)
 have vh:0<τ:=dc t8 _
 have afh:4<=τ:=by
  have:(4:ℝ)^5<=τ^5:=by rw[abk]; norm_num; linarith
  exact (d8 (by norm_num) vh.le (by norm_num)).mp this
 set N:ℕ:=⌈t^2⌉₊ with an5
 have hN1:t^2<=N:=f9 _
 have hN2:(N:ℝ)<t^2+1:=ef (by positivity)
 have ht2:(1:ℝ)<=t^2:=by nlinarith
 have t7:0<N:=by
  have:(0:ℝ)<N:=by linarith
  exact_mod_cast this
 have hNR:(0:ℝ)<N:=by exact_mod_cast t7
 set s:ℂ:=(1/2:ℂ)+t *I with hs
 have wm:s.re=1/2:=by simp[hs]
 have afi:s.im=t:=by simp[hs]
 have hsU:s∈vn:=⟨by rw[wm]; norm_num,by rw[afi]; linarith⟩
 rw[ab2 hsU t7]
 have hsum:∑ k∈range N,1/((k:ℂ)+1)^s=∑ n∈Icc 1 N,1/(n:ℂ)^s:=by
  rw[<- cy,dq,
   show N+1-1=N by omega]
  refine ai rfl (fun k _=>?_)
  push_cast; ring_nf
 have u5:‖∑ k∈range N,1/((k:ℂ)+1)^s‖<=45*τ*(ed 2 N+1):=by
  rw[hsum]
  have hs':s=(1/2:ℂ)+((τ^5:ℝ):ℂ)*I:=by rw[hs,abk]
  rw[hs']
  apply ach afh
  have:(2:ℝ)*τ^10=2*t^2:=by rw[<- abk]; ring
  rw[this]; linarith
 have a83:ak N<=2*t:=by
  have:ak N<=ak ((2*t)^2):=dg (by nlinarith)
  rwa[fk (by linarith)] at this
 have ahv:t<=ak N:=by
  have:ak (t^2)<=ak N:=dg hN1
  rwa[fk t8.le] at this
 have yh:‖(N:ℂ)^(1-s)/(s-1)‖<=2:=by
  rw[i4,norm_natCast_cpow_of_pos t7]
  have tu:(1-s).re=1/2:=by simp[hs]; norm_num
  rw[tu,<- ft]
  have um:t<=‖s-1‖:=by
   have:=a6 (s-1)
   have e:(s-1).im=t:=by simp[hs]
   rw[e,a7 t8] at this; exact this
  rw[ay (by linarith)]
  linarith
 have a0f:‖s*∑' k,cn s (k+N)‖<=4:=by
  refine (ad1 (by rw[wm]; norm_num) t7).trans ?_
  rw[wm]
  have hsn:‖s‖<=2*t:=by
   rw[hs]
   refine (ds _ _).trans ?_
   rw[bo,kr,di,ba,au,
    a7 t8]
   have:‖(1/2:ℂ)‖=1/2:=by norm_num
   rw[this]; linarith
  have hNi:(N:ℝ)^(-(1/2:ℝ))<=1/t:=by
   rw[iv hNR.le,<- ft,<- jz]
   exact dr t8 ahv
  calc ‖s‖*((N:ℝ)^(-(1/2:ℝ))/(1/2))<=(2*t)*((1/t)/(1/2)):=by
        gcongr
   _=4:=by field_simp; ring
 calc ‖∑ k∈range N,1/((k:ℂ)+1)^s+(N:ℂ)^(1-s)/(s-1)-
       s*∑' k,cn s (k+N)‖
   <= ‖∑ k∈range N,1/((k:ℂ)+1)^s‖+‖(N:ℂ)^(1-s)/(s-1)‖+
       ‖s*∑' k,cn s (k+N)‖:=by
       refine (ej _ _).trans ?_
       gcongr
       exact ds _ _
  _<=45*τ*(ed 2 N+1)+2+4:=by gcongr
  _=_:=by ring
theorem agn {t:ℝ} (ht:1024<=t):
  ‖riemannZeta ((1/2:ℂ)+t *I)‖<=200*t^((5:ℕ)⁻¹:ℝ)*aa t:=by
 have t8:0<t:=by linarith
 have h:=ade ht
 set N:ℕ:=⌈t^2⌉₊ with an5
 have hN2:(N:ℝ)<t^2+1:=ef (by positivity)
 have t7:0<N:=by
  have:(0:ℝ)<N:=fj (by positivity) (f9 (t^2))
  exact_mod_cast this
 have aay:(2:ℝ)/3<aa 2:=by
  have:=f6; linarith
 have a0g:6<=aa t:=by
  have h1:af 6<=1024:=by
   have:=f7
   have e:af 6=af 1^6:=by rw[<- db]; norm_num
   rw[e]
   calc af 1^6<=(2.7182818286:ℝ)^6:=by gcongr
    _<=1024:=by norm_num
  rw[d5 t8]; linarith
 have a0h:(ed 2 N:ℝ)*aa 2<=aa 2+2*aa t:=by
  have hp:2^ed 2 N<=N:=n6 2 t7.ne'
  have x6:((2:ℝ)^ed 2 N)<=N:=by exact_mod_cast hp
  have:=a5 (by positivity) x6
  rw[cq] at this
  have an6:(N:ℝ)<=2*t^2:=by nlinarith
  have:=this.trans (a5 (by exact_mod_cast t7) an6)
  rw[ca (by norm_num) (by positivity),cq] at this
  push_cast at this; linarith
 have ap3:(ed 2 N:ℝ)+1<=4*aa t:=by
  have h0:(0:ℝ)<=ed 2 N:=by positivity
  have:(ed 2 N:ℝ)<=1+3*aa t:=by
   by_contra hc
   push Not at hc
   have:(1+3*aa t)*aa 2<(ed 2 N:ℝ)*aa 2:=
    sh hc (by linarith)
   nlinarith
  linarith
 have u0:1<=t^((5:ℕ)⁻¹:ℝ):=e5 (by linarith) (by norm_num)
 calc ‖riemannZeta ((1/2:ℂ)+t *I)‖
   <= 45*t^((5:ℕ)⁻¹:ℝ)*(ed 2 N+1)+6:=h
  _<=45*t^((5:ℕ)⁻¹:ℝ)*(4*aa t)+6:=by gcongr
  _<=200*t^((5:ℕ)⁻¹:ℝ)*aa t:=by nlinarith
end bt.ZD
namespace bt.ZD
open Complex MeasureTheory Set Metric
open scoped Real
lemma aci {α:Type*} [MeasurableSpace α] {μ:Measure α} {f g:α->ℝ}
  (hf0:∀ x,0<=f x) (hg0:∀ x,0<=g x) (hf:Integrable (fun x=>f x^2) μ)
  (hg:Integrable (fun x=>g x^2) μ) (hfg:Integrable (fun x=>f x*g x) μ):
  ∫ x,f x*g x ∂μ<=ak (∫ x,f x^2 ∂μ)*ak (∫ x,g x^2 ∂μ):=by
 set A:=∫ x,f x^2 ∂μ
 set B:=∫ x,g x^2 ∂μ
 have hA:0<=A:=integral_nonneg (fun x=>c4 _)
 have hB:0<=B:=integral_nonneg (fun x=>c4 _)
 have key:∀ l:ℝ,0<l->∫ x,f x*g x ∂μ<=(l*A+B/l)/2:=by
  intro l hl
  have h1:∫ x,f x*g x ∂μ<=∫ x,(l*f x^2+g x^2/l)/2 ∂μ:=by
   apply integral_mono hfg
   ·exact ((hf.const_mul l).add (hg.div_const l)).div_const 2
   ·intro x
    have:0<=(l*f x-g x)^2/l:=by positivity
    have e:(l*f x^2+g x^2/l)/2-f x*g x=(l*f x-g x)^2/l/2:=by
     field_simp; ring
    simp only
    linarith
  have h2:∫ x,(l*f x^2+g x^2/l)/2 ∂μ=(l*A+B/l)/2:=by
   rw[integral_div,integral_add (hf.const_mul l) (hg.div_const l),integral_const_mul,
    integral_div]
  linarith
 rcases mn hA with hA0 | agb
 ·
  rw[<- hA0,Real.sqrt_zero,zero_mul]
  refine sm (fun ε hε=>?_)
  have:=key (B/ε+1) (by positivity)
  rw[<- hA0,mul_zero,jy] at this
  have h3:B/(B/ε+1)/2<=ε:=by
   rw[div_div,ay (by positivity)]
   have:B<=ε*((B/ε+1)*2):=by
    have:ε*((B/ε+1)*2)=2*B+2*ε:=by field_simp
    rw[this]; linarith
   exact this
  linarith
 rcases mn hB with hB0 | a0i
 ·rw[<- hB0,Real.sqrt_zero,mul_zero]
  refine sm (fun ε hε=>?_)
  have:=key (ε/(A+1)) (by positivity)
  rw[<- hB0,zero_div,ij] at this
  have h3:ε/(A+1)*A/2<=ε:=by
   have:ε/(A+1)*A<=ε:=by
    rw[ki,ay (by positivity)]; nlinarith
   linarith
  linarith
 ·have hA':A=ak A*ak A:=(f5 hA).symm
  have hB':B=ak B*ak B:=(f5 hB).symm
  obtain ⟨sa,hsa⟩:∃ x,x=ak A:=⟨_,rfl⟩
  obtain ⟨sb,hsb⟩:∃ x,x=ak B:=⟨_,rfl⟩
  rw[<- hsa] at hA' ⊢
  rw[<- hsb] at hB' ⊢
  have hsA:0<sa:=by rw[hsa]; exact iu.mpr agb
  have hsB:0<sb:=by rw[hsb]; exact iu.mpr a0i
  have:=key (sb/sa) (by positivity)
  have h1:sb/sa*A=sb*sa:=by
   rw[ki,r3 hsA.ne',hA']; ring
  have h2:B/(sb/sa)=sb*sa:=by
   rw[ml,r3 hsB.ne',hB']; ring
  rw[h1,h2] at this
  linarith
lemma afj {x w:ℂ} {r:ℝ} (h:‖x-w‖<=r):w.re-r<=x.re∧x.re<=w.re+r:=by
 have:=cm (x-w)
 rw[Complex.sub_re] at this
 have:=abs_le.mp (this.trans h)
 constructor <;> linarith[this.1,this.2]
noncomputable def tq (F:ℂ->ℂ) (σ:ℝ):ℝ:=∫ t:ℝ,‖F (σ+t *I)‖^2
theorem ahw (F:ℂ->ℂ) {a b δ M:ℝ} (hab:a<b) (uf:0<δ)
  (hF:DifferentiableOn ℂ F {s | a-δ<s.re∧s.re<b+δ})
  (hM:∀ s:ℂ,a-δ<s.re->s.re<b+δ->‖F s‖<=M)
  (hJa:Integrable (fun t:ℝ=>‖F (a+t *I)‖^2))
  (hJb:Integrable (fun t:ℝ=>‖F (b+t *I)‖^2))
  {u:ℝ} (x8:a<=u) (hu2:u<=b) (R:ℝ):
  ∫ t in Icc (-R) R,‖F (u+t *I)‖^2<=
   tq F a^((b-u)/(b-a))*tq F b^((u-a)/(b-a)):=by
 set D:Set ℂ:={s | a-δ<s.re∧s.re<b+δ} with hD
 have axi:IsOpen D:=
  (n2 dm f0).inter
   (n2 f0 dm)
 have hM0:0<=M:=(aw _).trans (hM a (by simp; linarith) (by simp; linarith))
 set μ:Measure ℝ:=volume.restrict (Icc (-R) R) with hμ
 haveI:IsFiniteMeasure μ:=by rw[hμ]; exact isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
 have axj:ContinuousOn F D:=hF.continuousOn
 have ajd:∀ z:ℂ,a-δ<z.re->z.re<b+δ->Continuous (fun t:ℝ=>F (z+t *I)):=by
  intro z h1 h2
  have hc:Continuous (fun t:ℝ=>z+(t:ℂ)*I):=by fun_prop
  refine axj.comp_continuous hc (fun t=>?_)
  show z+(t:ℂ)*I∈D
  simp only[hD,eh,add_re,mul_re,ofReal_re,I_re,mul_zero,ofReal_im,I_im,
   di,i3,ij]
  exact ⟨h1,h2⟩
 set g:ℝ->ℂ:=fun t=>(starRingEnd ℂ) (F (u+t *I)) with hg
 have hgc:Continuous g:=by
  have:=ajd u (by simp; linarith) (by simp; linarith)
  exact continuous_conj.comp this
 have hgM:∀ t,‖g t‖<=M:=by
  intro t; simp only[hg,d4]
  exact hM _ (by simp; linarith) (by simp; linarith)
 set K:ℝ:=∫ t,‖F (u+t *I)‖^2 ∂μ with hK
 have ya:0<=K:=integral_nonneg (fun _=>c4 _)
 set Φ:ℂ->ℂ:=fun z=>∫ t,F (z+t *I)*g t ∂μ with hΦ
 have a38:Φ u=(K:ℂ):=by
  simp only[hΦ,hK,hg]
  rw[<- sn]
  refine integral_congr_ae (bj (fun t=>?_))
  simp only
  rw[km]; push_cast; ring
 have auq:∀ w:ℂ,a-δ/2<w.re->w.re<b+δ/2->‖deriv F w‖<=M/(δ/4):=by
  intro w h1 h2
  apply gu (by positivity)
  ·apply i2
   apply hF.mono
   intro x hx
   rw[n3 w (show δ/4≠0 by positivity)] at hx
   rw[mem_closedBall,b8] at hx
   have:=afj hx
   show a-δ<x.re∧x.re<b+δ
   constructor <;> linarith[this.1,this.2]
  ·intro x hx
   rw[mem_sphere,b8] at hx
   have:=afj hx.le
   exact hM x (by linarith[this.1]) (by linarith[this.2])
 have aur:∀ z:ℂ,a-δ/4<=z.re->z.re<=b+δ/4->DifferentiableAt ℂ Φ z:=by
  intro z h1 h2
  have af4:∀ x∈ball z (δ/8),a-δ/2<x.re∧x.re<b+δ/2:=by
   intro x hx
   rw[mem_ball,b8] at hx
   have:=afj hx.le
   constructor <;> linarith[this.1,this.2]
  have tu:∀ (x:ℂ) (t:ℝ),(x+t *I).re=x.re:=by intro x t; simp
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ)
   (F:=fun x t=>F (x+t *I)*g t) (F':=fun x t=>deriv F (x+t *I)*g t)
   (x₀:=z) (bound:=fun _=>M/(δ/4)*M) (ball_mem_nhds z (by positivity:(0:ℝ)<δ/8))
   ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt
  ·filter_upwards[ball_mem_nhds z (by positivity:(0:ℝ)<δ/8)] with x hx
   have:=af4 x hx
   exact ((ajd x (by linarith[this.1]) (by linarith[this.2])).mul hgc).aestronglyMeasurable
  ·refine Integrable.of_bound (C:=M*M) ?_ ?_
   ·exact ((ajd z (by linarith) (by linarith)).mul hgc).aestronglyMeasurable
   ·refine bj (fun t=>?_)
    rw[bo]
    exact a8 (hM _ (by rw[tu]; linarith) (by rw[tu]; linarith)) (hgM t)
     (aw _) hM0
  ·exact (((measurable_deriv F).comp (by fun_prop:Measurable fun t:ℝ=>z+t *I)).mul
    hgc.measurable).aestronglyMeasurable
  ·refine bj (fun t x hx=>?_)
   rw[bo]
   have:=af4 x hx
   exact a8 (auq _ (by rw[tu]; linarith[this.1]) (by rw[tu]; linarith[this.2]))
    (hgM t) (aw _) (by positivity)
  ·exact integrable_const _
  ·refine bj (fun t x hx=>?_)
   have:=af4 x hx
   have hd:DifferentiableAt ℂ F (x+t *I):=
    hF.differentiableAt (axi.mem_nhds (by
     simp only[hD,mem_setOf_eq,tu]; constructor <;> linarith[this.1,this.2]))
   have h1:HasDerivAt (fun x=>x+(t:ℂ)*I) 1 x:=(po x).add_const _
   have h2:=hd.hasDerivAt.comp x h1
   simp only[di] at h2
   exact h2.mul_const (g t)
 have a39:∀ z:ℂ,a-δ/4<=z.re->z.re<=b+δ/4->‖Φ z‖<=M*M*μ.real univ:=by
  intro z h1 h2
  refine norm_integral_le_of_norm_le_const (bj (fun t=>?_))
  rw[bo]
  have tu:(z+t *I).re=z.re:=by simp
  exact a8 (hM _ (by rw[tu]; linarith) (by rw[tu]; linarith)) (hgM t)
   (aw _) hM0
 have hgK:∫ t,‖g t‖^2 ∂μ=K:=by
  simp only[hg,d4,hK]
 have atl:∀ (σ:ℝ),(σ=a∨σ=b)->
   Integrable (fun t:ℝ=>‖F (σ+t *I)‖^2)->∀ z:ℂ,z.re=σ->
   ‖Φ z‖<=ak (tq F σ)*ak K:=by
  intro σ hσ hint z hz
  have abi:a-δ<σ:=by rcases hσ with h | h <;> rw[h] <;> linarith
  have an7:σ<b+δ:=by rcases hσ with h | h <;> rw[h] <;> linarith
  have hzc:Continuous (fun t:ℝ=>F (z+t *I)):=ajd z (by rw[hz]; exact abi)
   (by rw[hz]; exact an7)
  have hbF:∀ t:ℝ,‖F (z+t *I)‖<=M:=fun t=>hM _ (by simp[hz]; exact abi)
   (by simp[hz]; exact an7)
  have a0j:Integrable (fun t:ℝ=>‖F (z+t *I)‖^2) μ:=
   Integrable.of_bound (C:=M^2) (hzc.norm.pow 2).aestronglyMeasurable
    (bj (fun t=>by
     rw[au,bh (c4 _)]
     exact aj (aw _) (hbF t) 2))
  have aje:Integrable (fun t:ℝ=>‖g t‖^2) μ:=
   Integrable.of_bound (C:=M^2) (hgc.norm.pow 2).aestronglyMeasurable
    (bj (fun t=>by
     rw[au,bh (c4 _)]
     exact aj (aw _) (hgM t) 2))
  have a0k:Integrable (fun t:ℝ=>‖F (z+t *I)‖*‖g t‖) μ:=
   Integrable.of_bound (C:=M*M) (hzc.norm.mul hgc.norm).aestronglyMeasurable
    (bj (fun t=>by
     rw[au,bh (by positivity)]
     exact a8 (hbF t) (hgM t) (aw _) hM0))
  have h1:‖Φ z‖<=∫ t:ℝ,‖F (z+t *I)‖*‖g t‖ ∂μ:=by
   refine (norm_integral_le_integral_norm _).trans (i6 ?_)
   exact integral_congr_ae (bj (fun t=>bo _ _))
  have h2:=aci (μ:=μ) (fun t:ℝ=>aw (F (z+t *I)))
   (fun t:ℝ=>aw (g t)) a0j aje a0k
  have h3:∫ t:ℝ,‖F (z+t *I)‖^2 ∂μ<=tq F σ:=by
   have wu:∀ t:ℝ,z+(t:ℂ)*I=σ+((t+z.im:ℝ):ℂ)*I:=by
    intro t; apply kn <;> simp[hz] <;> ring
   have adh:(fun t:ℝ=>‖F (z+t *I)‖^2)=
     (fun t:ℝ=>‖F (σ+((t+z.im:ℝ):ℂ)*I)‖^2):=by
    funext t; rw[wu t]
   have a0l:Integrable (fun t:ℝ=>‖F (z+t *I)‖^2):=by
    rw[adh]; exact hint.comp_add_right z.im
   calc ∫ t:ℝ,‖F (z+t *I)‖^2 ∂μ<=∫ t:ℝ,‖F (z+t *I)‖^2:=
         setIntegral_le_integral a0l (bj (fun _=>c4 _))
    _ = tq F σ:=by
        rw[adh,tq]
        exact integral_add_right_eq_self (fun t:ℝ=>‖F (σ+t *I)‖^2) z.im
  rw[hgK] at h2
  refine h1.trans (h2.trans ?_)
  gcongr
 have hz:(u:ℂ)∈HadamardThreeLines.verticalClosedStrip a b:=by
  simp[HadamardThreeLines.verticalClosedStrip]; exact ⟨x8,hu2⟩
 have hdc:DiffContOnCl ℂ Φ (HadamardThreeLines.verticalStrip a b):=by
  apply i2
  intro z zx
  have hcl:closure (HadamardThreeLines.verticalStrip a b) ⊆
    HadamardThreeLines.verticalClosedStrip a b:=
   closure_minimal (fun x hx=>Ioo_subset_Icc_self hx)
    (isClosed_Icc.preimage f0)
  have:=hcl zx
  simp only[HadamardThreeLines.verticalClosedStrip,mem_preimage,mem_Icc] at this
  exact (aur z (by linarith[this.1]) (by linarith[this.2])).differentiableWithinAt
 have hB:BddAbove ((norm∘Φ) '' HadamardThreeLines.verticalClosedStrip a b):=by
  refine ⟨M*M*μ.real univ, ?_⟩
  rintro _ ⟨z,zx,rfl⟩
  simp only[HadamardThreeLines.verticalClosedStrip,mem_preimage,mem_Icc] at zx
  exact a39 z (by linarith[zx.1]) (by linarith[zx.2])
 have h3l:=HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab hz hdc hB
  (fun z zx=>atl a (Or.inl rfl) hJa z zx) (fun z zx=>atl b (Or.inr rfl) hJb z zx)
 rw[a38,ba,au,bh ya] at h3l
 simp only[ofReal_re] at h3l
 set θ:=(u-a)/(b-a) with hθ
 have hba:b-a≠0:=ne_of_gt (sub_pos.mpr hab)
 have zj:1-θ=(b-u)/(b-a):=by
  rw[hθ,eq_div_iff hba,sub_mul,qc _ hba]; ring
 rw[<- zj]
 have a4a:0<=tq F a:=integral_nonneg (fun _=>c4 _)
 have a4b:0<=tq F b:=integral_nonneg (fun _=>c4 _)
 have am9:0<=θ:=fe (by linarith) (by linarith)
 have bcp:0<=1-θ:=by rw[zj]; exact fe (by linarith) (by linarith)
 change K<=_
 rcases mn ya with a4c | atm
 ·rw[<- a4c]; positivity
 have e1:(ak (tq F a)*ak K)^(1-θ)*
   (ak (tq F b)*ak K)^θ=
   ak K*(ak (tq F a)^(1-θ)*ak (tq F b)^θ):=by
  rw[e6 (df _) (df _),
   e6 (df _) (df _)]
  have:ak K^(1-θ)*ak K^θ=ak K:=by
   rw[<- c6 (iu.mpr atm)]; simp
  calc _=(ak K^(1-θ)*ak K^θ)*
        (ak (tq F a)^(1-θ)*ak (tq F b)^θ):=by ring
   _=_:=by rw[this]
 rw[e1] at h3l
 set Q:=ak (tq F a)^(1-θ)*ak (tq F b)^θ with hQ
 have hsK:=iu.mpr atm
 have a4d:K=ak K*ak K:=(f5 ya).symm
 have h4:ak K<=Q:=by
  have a4e:ak K*ak K<=ak K*Q:=by
   rw[f5 ya]; exact h3l
  exact lg a4e hsK
 have hQ0:0<=Q:=by positivity
 have h5:K<=Q*Q:=by
  calc K=ak K*ak K:=a4d
   _<=Q*Q:=a8 h4 h4 hsK.le hQ0
 have e2:Q*Q=tq F a^(1-θ)*tq F b^θ:=by
  rw[hQ]
  have ea:ak (tq F a)^(1-θ)*ak (tq F a)^(1-θ)=
    tq F a^(1-θ):=by
   rw[<- e6 (df _) (df _),f5 a4a]
  have eb:ak (tq F b)^θ*ak (tq F b)^θ=tq F b^θ:=by
   rw[<- e6 (df _) (df _),f5 a4b]
  calc _=(ak (tq F a)^(1-θ)*ak (tq F a)^(1-θ))*
        (ak (tq F b)^θ*ak (tq F b)^θ):=by ring
   _=_:=by rw[ea,eb]
 rw[<- e2]; exact h5
end bt.ZD
namespace bt.ZD
open Complex Finset MeasureTheory
open scoped Real
lemma adf (p:ℕ) (hp:1<=p):
  ∀ j,∑ i∈range j,1/((p+1+i:ℕ):ℝ)^2<=1/(p:ℝ)-1/((p+j:ℕ):ℝ):=by
 have zc:(0:ℝ)<p:=by exact_mod_cast hp
 intro j
 induction j with
 | zero=>simp
 | succ j ih=>
  rw[dk]
  have hq:(0:ℝ)<((p+j:ℕ):ℝ):=by exact_mod_cast (show 0<p+j by omega)
  have h1:1/((p+1+j:ℕ):ℝ)^2<=1/((p+j:ℕ):ℝ)-1/((p+(j+1):ℕ):ℝ):=by
   have e1:((p+1+j:ℕ):ℝ)=((p+j:ℕ):ℝ)+1:=by push_cast; ring
   have e2:((p+(j+1):ℕ):ℝ)=((p+j:ℕ):ℝ)+1:=by push_cast; ring
   rw[e1,e2]
   set q:=((p+j:ℕ):ℝ)
   rw[div_sub_div _ _ hq.ne' (by positivity),ax (by positivity) (by positivity)]
   nlinarith
  linarith
lemma zq (T:Finset ℕ) (p:ℕ) (hp:1<=p) (hT:∀ k∈T,p<k):
  ∑ k∈T,1/(k:ℝ)^2<=1/(p:ℝ):=by
 rcases T.eq_empty_or_nonempty with he | te
 ·simp[he]
 set M:=T.max' te
 have uj:T ⊆ Icc (p+1) M:=fun k hk=>
  ar.mpr ⟨hT k hk,T.le_max' k hk⟩
 have hM:p<M:=hT M (T.max'_mem te)
 calc ∑ k∈T,1/(k:ℝ)^2<=∑ k∈Icc (p+1) M,1/(k:ℝ)^2:=
       aq uj (fun _ _ _=>by positivity)
  _ = ∑ i∈range (M-p),1/((p+1+i:ℕ):ℝ)^2:=by
      rw[<- cy,dq,
       show M+1-(p+1)=M-p by omega]
  _<=1/(p:ℝ)-1/((p+(M-p):ℕ):ℝ):=adf p hp _
  _ ≤ 1/(p:ℝ):=by
      have:(0:ℝ)<=1/((p+(M-p):ℕ):ℝ):=by positivity
      linarith
lemma ab3 {x:ℝ} (hx:0<x):af (-x)<=1/x:=by
 rw[kv,<- jz]
 apply dr hx
 linarith[cw x]
noncomputable def gk (Y:ℝ) (m n:ℕ):ℝ:=
 af (-(Y^2*(aa m-aa n)^2/4))
lemma amo (Y:ℝ) (m n:ℕ):gk Y m n=gk Y n m:=by
 unfold gk; congr 2; ring
lemma ap7 (Y:ℝ) (m n:ℕ):gk Y m n<=1:=by
 unfold gk; rw[jt]
 have:0<=Y^2*(aa m-aa n)^2/4:=by positivity
 linarith
lemma axm {Y:ℝ} (hY:6<=Y) {m n:ℕ} (hn:1<=n) (hm:2*n< m):
  gk Y m n<=3/Y*((n:ℝ)^2*(1/(m:ℝ)^2)):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hm0:(0:ℝ)< m:=by exact_mod_cast (show 0< m by omega)
 have hmn:(2:ℝ)*n<=m:=by exact_mod_cast hm.le
 set u:=aa m-aa n with hu
 have ato:u=aa ((m:ℝ)/n):=by rw[ik hm0.ne' t6.ne']
 have hu2:aa 2<=u:=by
  rw[ato]; apply a5 (by norm_num)
  rw[bl t6]; linarith
 have hl2:=f6
 have bcq:0<u:=by linarith
 have hYu:4<=Y*u:=by nlinarith
 have h1:Y^2*u^2/4>=Y*u:=by nlinarith
 have a0m:af u=(m:ℝ)/n:=by rw[ato,fl (by positivity)]
 have h2:af (-(2*u))=(n:ℝ)^2*(1/(m:ℝ)^2):=by
  rw[kv,show 2*u=u+u by ring,bs,a0m]
  field_simp
 have h3:af (-((Y-2)*u))<=3/Y:=by
  refine (ab3 (by nlinarith)).trans ?_
  rw[ax (by nlinarith) (by linarith)]
  nlinarith
 unfold gk
 calc af (-(Y^2*u^2/4))<=af (-(Y*u)):=b4.mpr (by linarith)
  _ = af (-(2*u))*af (-((Y-2)*u)):=by
      rw[<- bs]; congr 1; ring
  _ ≤ (n:ℝ)^2*(1/(m:ℝ)^2)*(3/Y):=by
      rw[h2]; exact ab h3 (by positivity)
  _=_:=by ring
lemma an8 {m n:ℕ} (hn:1<=n) (hnm:n< m) (hm:m<=2*n):
  (((m-n:ℕ):ℝ)/(2*n))<=aa m-aa n:=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hm0:(0:ℝ)< m:=by exact_mod_cast (show 0< m by omega)
 rw[<- ik hm0.ne' t6.ne']
 have:=b5 (show (0:ℝ)< m/n by positivity)
 have hmr:(m:ℝ)<=2*n:=by exact_mod_cast hm
 have e:1-((m:ℝ)/n)⁻¹=((m:ℝ)-n)/m:=by field_simp
 rw[e] at this
 have hc:((m-n:ℕ):ℝ)=(m:ℝ)-n:=by rw[il hnm.le]
 rw[hc]
 refine br ?_ this
 apply bb (by linarith[show (n:ℝ)< m by exact_mod_cast hnm]) hm0 hmr
lemma akf {m n:ℕ} (hm1:1<=m) (hmn:m<n):
  (((n-m:ℕ):ℝ)/(2*n))<=aa n-aa m:=by
 have hm0:(0:ℝ)< m:=by exact_mod_cast hm1
 have t6:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
 rw[<- ik t6.ne' hm0.ne']
 have:=b5 (show (0:ℝ)<n/m by positivity)
 have e:1-((n:ℝ)/m)⁻¹=((n:ℝ)-m)/n:=by field_simp
 rw[e] at this
 have hc:((n-m:ℕ):ℝ)=(n:ℝ)-m:=by rw[il hmn.le]
 rw[hc]
 refine br ?_ this
 have:0<=(n:ℝ)-m:=by linarith[show (m:ℝ)<n by exact_mod_cast hmn]
 rw[ax (by positivity) t6]
 nlinarith
lemma ae3 {Y:ℝ} (hY:0<Y) {n k:ℕ} (hn:1<=n) (hk:1<=k) {u:ℝ}
  (hu:(k:ℝ)/(2*n)<=|u|):
  af (-(Y^2*u^2/4))<=16*(n:ℝ)^2/Y^2*(1/(k:ℝ)^2):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hk0:(0:ℝ)<k:=by exact_mod_cast hk
 have hu2:((k:ℝ)/(2*n))^2<=u^2:=by
  rw[<- sq_abs u]; exact aj (by positivity) hu 2
 set x:=Y^2*(k:ℝ)^2/(16*(n:ℝ)^2) with hx
 have tp:0<x:=by positivity
 have bd6:x<=Y^2*u^2/4:=by
  have e:x=Y^2*((k:ℝ)/(2*n))^2/4:=by rw[hx]; field_simp; ring
  rw[e]; gcongr
 calc af (-(Y^2*u^2/4))<=af (-x):=b4.mpr (by linarith)
  _<=1/x:=ab3 tp
  _=_:=by rw[hx]; field_simp
theorem ap8 (S:Finset ℕ) (hS:∀ m∈S,1<=m) {Y:ℝ} (hY:6<=Y) {n:ℕ}
  (hn:1<=n):∑ m∈S,gk Y m n<=3+18*n/Y:=by
 have xd:0<Y:=by linarith
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 set K:ℕ:=⌈4*(n:ℝ)/Y⌉₊ with hK
 have hK1:1<=K:=i8.mpr (by
  rw[hK]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
 have a4f:4*(n:ℝ)/Y<=K:=f9 _
 have bd7:(K:ℝ)<4*(n:ℝ)/Y+1:=ef (by positivity)
 have ya:(0:ℝ)<K:=by exact_mod_cast hK1
 set c:ℝ:=16*(n:ℝ)^2/Y^2 with hc
 have wu:∀ m∈S,gk Y m n<=
   (if 2*n< m then 3/Y*((n:ℝ)^2*(1/(m:ℝ)^2)) else 0)+
   (if m<=2*n∧m<=n+K∧n<=m+K then 1 else 0)+
   (if m<=2*n∧n+K< m then c*(1/((m-n:ℕ):ℝ)^2) else 0)+
   (if m+K<n then c*(1/((n-m:ℕ):ℝ)^2) else 0):=by
  intro m hm
  have hm1:=hS m hm
  by_cases h1:2*n< m
  ·rw[if_pos h1,if_neg (by omega),if_neg (by omega),if_neg (by omega)]
   have:=axm hY hn h1
   linarith
  rw[if_neg h1]
  by_cases h2:m<=2*n∧m<=n+K∧n<=m+K
  ·rw[if_pos h2,if_neg (by omega),if_neg (by omega)]
   have:=ap7 Y m n; linarith
  rw[if_neg h2]
  by_cases h3:n+K< m
  ·rw[if_pos ⟨by omega,h3⟩,if_neg (by omega)]
   have hg:=an8 (m:=m) (n:=n) hn (by omega) (by omega)
   have:=ae3 xd hn (show 1<=m-n by omega)
    (u:=aa m-aa n) (by
     refine hg.trans (k6 _))
   unfold gk; rw[hc]; linarith
  ·have h4:m+K<n:=by omega
   rw[if_neg (by omega),if_pos h4]
   have hg:=akf (m:=m) (n:=n) hm1 (by omega)
   have:=ae3 xd hn (show 1<=n-m by omega)
    (u:=aa m-aa n) (by
     rw[jj]; exact hg.trans (k6 _))
   unfold gk; rw[hc]; linarith
 refine (ao wu).trans ?_
 simp only[cu,<- jf]
 have xp:∑ m∈S.filter (fun m=>2*n< m),3/Y*((n:ℝ)^2*(1/(m:ℝ)^2))
   <= 3/Y*((n:ℝ)^2*(1/(2*n:ℕ))):=by
  rw[<- bc,<- bc]
  gcongr
  exact zq _ (2*n) (by omega) (fun k hk=>(ah.mp hk).2)
 have bcr:3/Y*((n:ℝ)^2*(1/(2*n:ℕ)))=3/2*(n/Y):=by
  push_cast; field_simp
 have yh:∑ m∈S.filter (fun m=>m<=2*n∧m<=n+K∧n<=m+K),(1:ℝ)<=2*K+1:=by
  rw[a9,cp,di]
  have uj:S.filter (fun m=>m<=2*n∧m<=n+K∧n<=m+K) ⊆ Icc (n-K) (n+K):=by
   intro m hm
   simp only[ah,ar] at hm ⊢
   omega
  have:=cf uj
  rw[jv] at this
  have:(S.filter (fun m=>m<=2*n∧m<=n+K∧n<=m+K)).card<=2*K+1:=by omega
  exact_mod_cast this
 have hup:∑ m∈S.filter (fun m=>m<=2*n∧n+K< m),c*(1/((m-n:ℕ):ℝ)^2)
   <= c*(1/K):=by
  rw[<- bc]
  gcongr
  rw[<- py (f:=fun k:ℕ=>1/(k:ℝ)^2) (g:=fun m=>m-n) (by
   intro a ha b hb hab
   simp only[kj,eh] at ha hb
   simp only at hab
   omega)]
  apply zq _ K hK1
  intro k hk
  simp only[cr,ah] at hk
  obtain ⟨m,⟨_,_,h⟩,rfl⟩:=hk
  omega
 have bcs:∑ m∈S.filter (fun m=>m+K<n),c*(1/((n-m:ℕ):ℝ)^2)
   <= c*(1/K):=by
  rw[<- bc]
  gcongr
  rw[<- py (f:=fun k:ℕ=>1/(k:ℝ)^2) (g:=fun m=>n-m) (by
   intro a ha b hb hab
   simp only[kj,eh] at ha hb
   simp only at hab
   omega)]
  apply zq _ K hK1
  intro k hk
  simp only[cr,ah] at hk
  obtain ⟨m,⟨_,h⟩,rfl⟩:=hk
  omega
 have hcK:c*(1/K)<=4*(n/Y):=by
  rw[hc,m8,ay ya]
  have:4*(n:ℝ)/Y*(4*(n/Y))<=K*(4*(n/Y)):=
   ag a4f (by positivity)
  have e:16*(n:ℝ)^2/Y^2=4*(n:ℝ)/Y*(4*(n/Y)):=by field_simp; ring
  rw[e]; linarith
 have hKn:2*(K:ℝ)+1<=8*(n/Y)+3:=by
  have:(K:ℝ)<=4*(n/Y)+1:=by
   have e:4*(n:ℝ)/Y=4*(n/Y):=by ring
   linarith
  linarith
 have e18:18*(n:ℝ)/Y=18*(n/Y):=by ring
 rw[e18]
 have:0<=(n:ℝ)/Y:=by positivity
 linarith
lemma art {Y:ℝ} (hY:0<Y) (u:ℝ):
  ∫ t:ℝ,cexp (-(1/(Y:ℂ)^2)*(t:ℂ)^2+(-(u:ℂ)*I)*t+0)=
   ((ak π*Y*af (-(Y^2*u^2/4)):ℝ):ℂ):=by
 have hb:(-(1/(Y:ℂ)^2)).re<0:=by
  have:(1/(Y:ℂ)^2)=((1/Y^2:ℝ):ℂ):=by push_cast; ring
  rw[this,<- ofReal_neg,ofReal_re]
  have:0<1/Y^2:=by positivity
  linarith
 rw[integral_cexp_quadratic hb]
 have h1:(π:ℂ)/ -(-(1/(Y:ℂ)^2))=((π*Y^2:ℝ):ℂ):=by
  push_cast; field_simp
 have h2:(1/2:ℂ)=((1/2:ℝ):ℂ):=by push_cast; ring
 rw[h1,h2,<- lq (by positivity),<- ft,
  mv du.le,fk hY.le]
 have h3:(0:ℂ)-(-(u:ℂ)*I)^2/(4*-(1/(Y:ℂ)^2))=
   ((-(Y^2*u^2/4):ℝ):ℂ):=by
  push_cast
  have:(Y:ℂ)≠0:=by exact_mod_cast hY.ne'
  field_simp
  rw[I_sq]; ring
 rw[h3,<- ou]
 push_cast; ring
noncomputable def yi (t:ℝ) (n:ℕ):ℂ:=cexp (-((t *aa n:ℝ):ℂ)*I)
theorem aal (S:Finset ℕ) (hS:∀ n∈S,1<=n) (b:ℕ->ℂ) {Y:ℝ}
  (hY:6<=Y):
  ∫ t:ℝ,‖∑ n∈S,b n*yi t n‖^2*af (-(1/Y^2)*t^2)<=
   ak π*∑ n∈S,‖b n‖^2*(3*Y+18*n):=by
 have xd:0<Y:=by linarith
 set w:ℝ->ℝ:=fun t=>af (-(1/Y^2)*t^2) with hw
 set E:ℝ->ℝ->ℂ:=fun u t=>
  cexp (-(1/(Y:ℂ)^2)*(t:ℂ)^2+(-(u:ℂ)*I)*t+0) with hE
 set G:ℕ->ℕ->ℝ:=fun m n=>ak π*Y*gk Y m n with hG
 have atp:∀ u,Integrable (E u):=by
  intro u
  have hb:0<(1/(Y:ℂ)^2).re:=by
   have:(1/(Y:ℂ)^2)=((1/Y^2:ℝ):ℂ):=by push_cast; ring
   rw[this,ofReal_re]; positivity
  exact integrable_cexp_quadratic hb _ _
 have a4g:∀ m n:ℕ,∫ t,E (aa m-aa n) t=(G m n:ℂ):=by
  intro m n
  simp only[hE,hG,gk]
  rw[art xd]
 have wu:∀ t:ℝ,((‖∑ n∈S,b n*yi t n‖^2*w t:ℝ):ℂ)=
   ∑ m∈S,∑ n∈S,b m*(starRingEnd ℂ) (b n)*E (aa m-aa n) t:=by
  intro t
  have e0:((‖∑ n∈S,b n*yi t n‖^2*w t:ℝ):ℂ)=
    (∑ n∈S,b n*yi t n)*(starRingEnd ℂ) (∑ n∈S,b n*yi t n)*(w t:ℂ):=by
   rw[km]; push_cast; ring
  rw[e0,m9,f8,g3]
  refine ai rfl (fun m _=>?_)
  rw[g3]
  refine ai rfl (fun n _=>?_)
  simp only[hE,hw,yi,qb]
  rw[<- m2]
  have e1:(starRingEnd ℂ) (-((t *aa n:ℝ):ℂ)*I)=((t *aa n:ℝ):ℂ)*I:=by
   rw[qb,map_neg,lr,n1]; ring
  rw[e1,ou]
  have e2:b m*cexp (-((t *aa m:ℝ):ℂ)*I)*
    ((starRingEnd ℂ) (b n)*cexp (((t *aa n:ℝ):ℂ)*I))*
    cexp ((-(1/Y^2)*t^2:ℝ):ℂ)=
    b m*(starRingEnd ℂ) (b n)*(cexp (-((t *aa m:ℝ):ℂ)*I)*
     cexp (((t *aa n:ℝ):ℂ)*I)*cexp ((-(1/Y^2)*t^2:ℝ):ℂ)):=by ring
  rw[e2,<- jc,<- jc]
  congr 2
  push_cast; ring
 have hint:∫ t:ℝ,‖∑ n∈S,b n*yi t n‖^2*w t=
   (∑ m∈S,∑ n∈S,b m*(starRingEnd ℂ) (b n)*(G m n:ℂ)).re:=by
  have h1:=(sn (μ:=volume)
   (f:=fun t=>‖∑ n∈S,b n*yi t n‖^2*w t))
  rw[integral_congr_ae (bj wu)] at h1
  rw[integral_finset_sum _ (fun m _=>integrable_finset_sum _
   (fun n _=>(atp _).const_mul _))] at h1
  have h2:∀ m∈S,∫ t,∑ n∈S,b m*(starRingEnd ℂ) (b n)*E (aa m-aa n) t=
    ∑ n∈S,b m*(starRingEnd ℂ) (b n)*(G m n:ℂ):=by
   intro m _
   rw[integral_finset_sum _ (fun n _=>(atp _).const_mul _)]
   refine ai rfl (fun n _=>?_)
   rw[integral_const_mul,a4g]
  rw[ai rfl h2] at h1
  rw[h1,o8]
 rw[hint]
 have hG0:∀ m n,0<=G m n:=fun m n=>by simp only[hG,gk]; positivity
 have hb1:(∑ m∈S,∑ n∈S,b m*(starRingEnd ℂ) (b n)*(G m n:ℂ)).re<=
   ∑ m∈S,∑ n∈S,(‖b m‖^2+‖b n‖^2)/2*G m n:=by
  refine (ot _).trans ?_
  refine (c5 _ _).trans (ao (fun m _=>?_))
  refine (c5 _ _).trans (ao (fun n _=>?_))
  rw[bo,bo,d4,ba,au,
   bh (hG0 m n)]
  apply ag _ (hG0 m n)
  nlinarith[c4 (‖b m‖-‖b n‖)]
 have u8:∑ m∈S,∑ n∈S,(‖b m‖^2+‖b n‖^2)/2*G m n=
   ∑ m∈S,‖b m‖^2*∑ n∈S,G n m:=by
  have e1:∑ m∈S,∑ n∈S,(‖b m‖^2+‖b n‖^2)/2*G m n=
    (∑ m∈S,∑ n∈S,‖b m‖^2*G m n)/2+(∑ m∈S,∑ n∈S,‖b n‖^2*G m n)/2:=by
   rw[ew,ew,<- cu]
   refine ai rfl (fun m _=>?_)
   rw[ew,ew,<- cu]
   refine ai rfl (fun n _=>by ring)
  have e2:∑ m∈S,∑ n∈S,‖b n‖^2*G m n=∑ m∈S,∑ n∈S,‖b m‖^2*G m n:=by
   rw[d0]
   refine ai rfl (fun m _=>ai rfl (fun n _=>?_))
   simp only[hG]; rw[amo]
  rw[e1,e2]
  have e3:∀ m∈S,∑ n∈S,‖b m‖^2*G m n=‖b m‖^2*∑ n∈S,G n m:=by
   intro m _
   rw[bc]
   refine ai rfl (fun n _=>?_)
   simp only[hG]; rw[amo]
  rw[ai rfl e3]; ring
 rw[u8] at hb1
 refine hb1.trans ?_
 rw[bc]
 refine ao (fun m hm=>?_)
 have hW:∑ n∈S,G n m<=ak π*(3*Y+18*m):=by
  simp only[hG]
  rw[<- bc]
  have:=ap8 S hS hY (hS m hm)
  calc ak π*Y*∑ n∈S,gk Y n m<=ak π*Y*(3+18*m/Y):=by
        gcongr
   _=ak π*(3*Y+18*m):=by field_simp
 calc ‖b m‖^2*∑ n∈S,G n m<=‖b m‖^2*(ak π*(3*Y+18*m)):=
       ab hW (by positivity)
  _=_:=by ring
end bt.ZD
namespace bt.ZD
open Complex Finset ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius
lemma ad4 {a:ℝ} (ha:0<a) (N:ℕ):
  ∑ n∈bk N,(n:ℝ)^(-(1+a))<=1+1/a:=by
 have u5:∀ M:ℕ,∑ n∈bk (M+2),(n:ℝ)^(-(1+a))<=1+1/a:=by
  intro M
  rw[fq,fq]
  have hint:∑ i∈bk M,((i+1+1:ℕ):ℝ)^(-(1+a))<=
    ∫ u in (1:ℝ)..1+M,u^(-(1+a)):=by
   have:=lx (x₀:=1) (a:=M) (f:=fun u:ℝ=>u^(-(1+a)))
    (by
     intro u hu v _ huv
     exact c1 (by linarith[hu.1]) huv (by linarith))
   refine br (i6 ?_) this
   apply ai rfl
   intro i _
   push_cast; ring_nf
  have hM:(0:ℝ)<=M:=av M
  have hI:∫ u in (1:ℝ)..1+M,u^(-(1+a))=((1+M)^(-a)-1)/(-a):=by
   rw[pn (Or.inr ⟨by linarith,by
    rw[gj (by linarith)]; norm_num⟩)]
   rw[show -(1+a)+1=-a by ring,oi]
  have tj:0<=(1+(M:ℝ))^(-a):=by positivity
  have hI':((1+M)^(-a)-1)/(-a)<=1/a:=by
   rw[ss,<- p9]
   apply a4 (by linarith) ha.le
  have h0:((0:ℕ):ℝ)^(-(1+a))=0:=by
   rw[mw]; exact qu (by linarith)
  have h1:((0+1:ℕ):ℝ)^(-(1+a))=1:=by simp
  rw[h0,h1]
  linarith
 calc ∑ n∈bk N,(n:ℝ)^(-(1+a))
   <= ∑ n∈bk (N+2),(n:ℝ)^(-(1+a)):=
       aq (jn.mpr (by omega))
        (fun _ _ _=>by positivity)
  _<=1+1/a:=u5 N
lemma aa4 {σ:ℝ} (hσ:1<σ) (Z:ℕ):
  ∑ x∈Icc 1 Z,(x:ℝ)^(-σ)<=1+1/(σ-1):=by
 have h:=ad4 (a:=σ-1) (by linarith) (Z+1)
 rw[show -(1+(σ-1))=-σ by ring] at h
 refine br ?_ h
 apply aq
 ·intro x hx; simp only[ar,bw] at hx ⊢; omega
 ·intro _ _ _; positivity
lemma ahx {n Z:ℕ} (hn:1<=n) (hnZ:n<=Z):
  n.divisors.card^2<=(((Icc 1 Z ×ˢ Icc 1 Z) ×ˢ (Icc 1 Z ×ˢ Icc 1 Z)).filter
   (fun q=>q.1.1*q.1.2*(q.2.1*q.2.2)=n)).card:=by
 rw[sq,<- iz]
 have t6:n≠0:=by omega
 apply ck (fun p=>((et p.1 p.2,p.1/et p.1 p.2),
  (p.2/et p.1 p.2,n/mc p.1 p.2)))
 ·intro p hp
  simp only[Finset.coe_product,Set.mem_prod,b9,mz] at hp
  obtain ⟨⟨hu,-⟩,⟨hv,-⟩⟩:=hp
  set u:=p.1; set v:=p.2
  have yf:0<u:=kx hu (by omega)
  have hv0:0<v:=kx hv (by omega)
  have hg0:0<et u v:=Nat.gcd_pos_of_pos_left _ yf
  have hgu:et u v∣u:=pv u v
  have hgv:et u v∣v:= o4 u v
  have hl:mc u v∣n:=Nat.lcm_dvd hu hv
  have hl0:0< mc u v:=Nat.lcm_pos yf hv0
  have hun:u<=n:=g1 (by omega) hu
  have hvn:v<=n:=g1 (by omega) hv
  have hln:mc u v<=n:=g1 (by omega) hl
  have h1:1<=u/et u v:=(lz hg0).mpr (g1 yf hgu)
  have h2:1<=v/et u v:=(lz hg0).mpr (g1 hv0 hgv)
  have h3:1<=n/mc u v:=(lz hl0).mpr hln
  have h4:u/et u v<=Z:=(lj _ _).trans (hun.trans hnZ)
  have h5:v/et u v<=Z:=(lj _ _).trans (hvn.trans hnZ)
  have h6:n/mc u v<=Z:=(lj _ _).trans hnZ
  have h7:et u v<=Z:=(g1 yf hgu).trans (hun.trans hnZ)
  simp only[kj,bm,ar,eh]
  refine ⟨⟨⟨⟨hg0,h7⟩,h1,h4⟩,⟨h2,h5⟩,h3,h6⟩, ?_⟩
  have a4h:u*(v/et u v)=mc u v:=by
   rw[mc,Nat.mul_div_assoc _ hgv]
  calc et u v*(u/et u v)*(v/et u v*(n/mc u v))
    = (et u v*(u/et u v))*(v/et u v)*(n/mc u v):=by ring
   _=mc u v*(n/mc u v):=by rw[gp hgu,a4h]
   _=n:=gp hl
 ·intro p hp q hq hpq
  simp only[j5] at hpq
  obtain ⟨⟨hg,h1⟩,h2,-⟩:=hpq
  have hpu:p.1=et p.1 p.2*(p.1/et p.1 p.2):=
   (gp (pv _ _)).symm
  have hpv:p.2=et p.1 p.2*(p.2/et p.1 p.2):=
   (gp (o4 _ _)).symm
  have hqu:q.1=et q.1 q.2*(q.1/et q.1 q.2):=
   (gp (pv _ _)).symm
  have hqv:q.2=et q.1 q.2*(q.2/et q.1 q.2):=
   (gp (o4 _ _)).symm
  apply s7
  ·calc p.1=et p.1 p.2*(p.1/et p.1 p.2):=hpu
    _=et q.1 q.2*(q.1/et q.1 q.2):=by rw[h1,hg]
    _=q.1:=hqu.symm
  ·calc p.2=et p.1 p.2*(p.2/et p.1 p.2):=hpv
    _=et q.1 q.2*(q.2/et q.1 q.2):=by rw[h2,hg]
    _=q.2:=hqv.symm
lemma card_div_le {n Z:ℕ} (hn:1<=n) (hnZ:n<=Z):
  n.divisors.card<=((Icc 1 Z ×ˢ Icc 1 Z).filter (fun q=>q.1*q.2=n)).card:=by
 apply ck (fun x=>(x,n/x))
 ·intro x hx
  simp only[b9,mz] at hx
  obtain ⟨hx,-⟩:=hx
  have tp:0<x:=kx hx (by omega)
  have hxn:x<=n:=g1 (by omega) hx
  simp only[kj,bm,ar,eh]
  refine ⟨⟨⟨by omega,by omega⟩,(lz tp).mpr hxn,
   (lj _ _).trans hnZ⟩,gp hx⟩
 ·intro x _ y _ h
  simp only[j5] at h
  exact h.1
lemma ad5 {α:Type*} [DecidableEq α] (B:Finset α) (pr:α->ℕ) (Z:ℕ)
  (hpr:∀ q∈B,1<=pr q) (f:ℕ->ℝ) (hf:∀ n,0<=f n):
  ∑ n∈Icc 1 Z,((B.filter (fun q=>pr q=n)).card:ℝ)*f n<=∑ q∈B,f (pr q):=by
 have h1:∑ n∈Icc 1 Z,((B.filter (fun q=>pr q=n)).card:ℝ)*f n=
   ∑ q∈B.filter (fun q=>pr q<=Z),f (pr q):=by
  rw[<- cx (g:=pr) (t:=Icc 1 Z) (by
   intro q hq
   simp only[ah] at hq
   exact ar.mpr ⟨hpr q hq.1,hq.2⟩)]
  refine ai rfl (fun n hn=>?_)
  rw[ar] at hn
  rw[ai rfl (fun q hq=>by rw[(ah.mp hq).2]),
   a9,cp,ny]
  congr 2
  congr 1
  apply Finset.filter_congr
  intro q _
  constructor
  ·intro h; exact ⟨by omega,h⟩
  ·intro h; exact h.2
 rw[h1]
 exact aq (r7 _ _)
  (fun _ _ _=>hf _)
theorem ai1 {σ:ℝ} (hσ:1<σ) (Z:ℕ):
  ∑ n∈Icc 1 Z,(n.divisors.card:ℝ)^2*(n:ℝ)^(-σ)<=(1+1/(σ-1))^4:=by
 set A:=Icc 1 Z
 set B:=(A ×ˢ A) ×ˢ (A ×ˢ A)
 set f:ℕ->ℝ:=fun x=>(x:ℝ)^(-σ) with hf
 have hf0:∀ n,0<=f n:=fun n=>by positivity
 have h1:∑ n∈A,(n.divisors.card:ℝ)^2*f n<=
   ∑ n∈A,((B.filter (fun q=>q.1.1*q.1.2*(q.2.1*q.2.2)=n)).card:ℝ)*f n:=by
  refine ao (fun n hn=>?_)
  rw[ar] at hn
  apply ag _ (hf0 n)
  exact_mod_cast ahx hn.1 hn.2
 have h2:=ad5 B (fun q=>q.1.1*q.1.2*(q.2.1*q.2.2)) Z (by
  intro q hq
  simp only[B,A,bm,ar] at hq
  have:=gl (gl hq.1.1.1 hq.1.2.1) (gl hq.2.1.1 hq.2.2.1)
  simpa using this) f hf0
 have h3:∑ q∈B,f (q.1.1*q.1.2*(q.2.1*q.2.2))=(∑ x∈A,f x)^4:=by
  have e:∀ a b c d:ℕ,f (a*b*(c*d))=f a*f b*(f c*f d):=by
   intro a b c d
   simp only[hf]; push_cast
   rw[e6 (by positivity) (by positivity),e6 (by positivity)
    (by positivity),e6 (by positivity) (by positivity)]
  simp_rw[e]
  have hP:∑ x∈A ×ˢ A,f x.1*f x.2=(∑ a∈A,f a)^2:=by
   rw[ep,sq,f8]
  rw[ep]
  have h2':∑ x∈A ×ˢ A,∑ y∈A ×ˢ A,f x.1*f x.2*(f y.1*f y.2)=
    (∑ x∈A ×ˢ A,f x.1*f x.2)*(∑ y∈A ×ˢ A,f y.1*f y.2):=
   (f8 _ _ _ _).symm
  rw[h2',hP]; ring
 have h4:∑ x∈A,f x<=1+1/(σ-1):=aa4 hσ Z
 have h5:(∑ x∈A,f x)^4<=(1+1/(σ-1))^4:=
  aj (cj (fun x _=>hf0 x)) h4 4
 calc _=∑ n∈A,(n.divisors.card:ℝ)^2*f n:=rfl
  _<=_:=h1.trans (h2.trans (i6 h3 |>.trans h5))
theorem an9 {σ:ℝ} (hσ:1<σ) (Z:ℕ):
  ∑ n∈Icc 1 Z,(n.divisors.card:ℝ)*(n:ℝ)^(-σ)<=(1+1/(σ-1))^2:=by
 set A:=Icc 1 Z
 set B:=A ×ˢ A
 set f:ℕ->ℝ:=fun x=>(x:ℝ)^(-σ) with hf
 have hf0:∀ n,0<=f n:=fun n=>by positivity
 have h1:∑ n∈A,(n.divisors.card:ℝ)*f n<=
   ∑ n∈A,((B.filter (fun q=>q.1*q.2=n)).card:ℝ)*f n:=by
  refine ao (fun n hn=>?_)
  rw[ar] at hn
  apply ag _ (hf0 n)
  exact_mod_cast card_div_le hn.1 hn.2
 have h2:=ad5 B (fun q=>q.1*q.2) Z (by
  intro q hq
  simp only[B,A,bm,ar] at hq
  have:=gl hq.1.1 hq.2.1
  simpa using this) f hf0
 have h3:∑ q∈B,f (q.1*q.2)=(∑ x∈A,f x)^2:=by
  have e:∀ a b:ℕ,f (a*b)=f a*f b:=by
   intro a b; simp only[hf]; push_cast
   rw[e6 (by positivity) (by positivity)]
  simp_rw[e]
  rw[ep,sq,f8]
 have h4:∑ x∈A,f x<=1+1/(σ-1):=aa4 hσ Z
 have h5:(∑ x∈A,f x)^2<=(1+1/(σ-1))^2:=
  aj (cj (fun x _=>hf0 x)) h4 2
 calc _=∑ n∈A,(n.divisors.card:ℝ)*f n:=rfl
  _<=_:=h1.trans (h2.trans (i6 h3 |>.trans h5))
noncomputable def cX (X n:ℕ):ℝ:=
 (∑ d∈(Icc 1 X).filter (·∣n),((μ d:ℤ):ℝ))-if n=1 then 1 else 0
noncomputable def MX (X:ℕ) (s:ℂ):ℂ:=∑ d∈Icc 1 X,((μ d:ℤ):ℂ)/(d:ℂ)^s
lemma acj (n:ℕ) (hn:1<=n):
  ∑ d∈n.divisors,((μ d:ℤ):ℝ)=if n=1 then 1 else 0:=by
 have h:=dy (fun f:ArithmeticFunction ℤ=>f n) moebius_mul_coe_zeta
 simp only[coe_mul_zeta_apply,one_apply] at h
 have:((∑ d∈n.divisors,μ d:ℤ):ℝ)=((if n=1 then 1 else 0:ℤ):ℝ):=by rw[h]
 push_cast at this
 rw[this]
lemma filter_dvd_eq_divisors {X n:ℕ} (hn:1<=n) (hnX:n<=X):
  (Icc 1 X).filter (·∣n)=n.divisors:=by
 ext d
 simp only[ah,ar,mz]
 constructor
 ·rintro ⟨-,h⟩; exact ⟨h,by omega⟩
 ·rintro ⟨h,-⟩
  have hd:0<d:=kx h (by omega)
  exact ⟨⟨hd,(g1 (by omega) h).trans hnX⟩,h⟩
theorem acn {X n:ℕ} (hn:1<=n) (hnX:n<=X):cX X n=0:=by
 unfold cX
 rw[filter_dvd_eq_divisors hn hnX,acj n hn]; ring
theorem ad6 {X n:ℕ} (hX:1<=X) (hn:1<=n):|cX X n|<=n.divisors.card:=by
 by_cases h1:n=1
 ·rw[acn hn (by omega)]; simp
 unfold cX
 rw[if_neg h1,kg]
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have uj:(Icc 1 X).filter (·∣n) ⊆ n.divisors:=by
  intro d hd
  simp only[ah,ar,mz] at hd ⊢
  exact ⟨hd.2,by omega⟩
 calc ∑ d∈(Icc 1 X).filter (·∣n),|((μ d:ℤ):ℝ)|<=∑ d∈(Icc 1 X).filter (·∣n),1:=
       ao (fun d _=>by exact_mod_cast abs_moebius_le_one)
  _=((Icc 1 X).filter (·∣n)).card:=by simp
  _<=n.divisors.card:=by exact_mod_cast cf uj
theorem ae4 {s:ℂ} (hs:1<s.re) (X:ℕ):
  riemannZeta s*MX X s-1=∑' n:ℕ,(cX X n:ℂ)/(n:ℂ)^s:=by
 have xc:s≠0:=by intro h; rw[h] at hs; simp at hs; linarith
 have hsum:Summable (fun m:ℕ=>1/(m:ℂ)^s):=j7.mpr hs
 rw[zeta_eq_tsum_one_div_nat_cpow hs,MX,bc]
 have hd:∀ d∈Icc 1 X,(∑' m:ℕ,1/(m:ℂ)^s)*(((μ d:ℤ):ℂ)/(d:ℂ)^s)=
   ∑' n:ℕ,(if d∣n then ((μ d:ℤ):ℂ)/(n:ℂ)^s else 0):=by
  intro d hd
  rw[ar] at hd
  have hd0:(d:ℂ)≠0:=by exact_mod_cast (show d≠0 by omega)
  rw[<- tsum_mul_right]
  have hinj:l0 (fun m:ℕ=>d*m):=fun a b h=>by
   simpa [show d≠0 by omega] using h
  rw[<- hinj.tsum_eq (f:=fun n:ℕ=>if d∣n then ((μ d:ℤ):ℂ)/(n:ℂ)^s else 0)]
  ·refine tsum_congr (fun m=>?_)
   simp only[dvd_mul_right,if_true]
   push_cast
   rw[Complex.natCast_mul_natCast_cpow]
   field_simp
  ·intro n hn
   simp only[nv,ne_eq,ite_eq_right_iff,Classical.not_imp] at hn
   obtain ⟨k,rfl⟩:=hn.1
   exact ⟨k,rfl⟩
 rw[ai rfl hd]
 have atq:∀ d∈Icc 1 X,Summable (fun n:ℕ=>
   if d∣n then ((μ d:ℤ):ℂ)/(n:ℂ)^s else 0):=by
  intro d _
  refine q0 (g:=fun n:ℕ=>‖1/(n:ℂ)^s‖) hsum.norm (fun n=>?_)
  split_ifs
  ·rw[jd,bo]
   have:‖((μ d:ℤ):ℂ)‖<=1:=by
    rw[lf]; exact_mod_cast abs_moebius_le_one
   calc _<=1*‖1/(n:ℂ)^s‖:=by gcongr
    _=_:=iq _
  ·simp
 rw[<- Summable.tsum_finsetSum atq]
 have a4i:(1:ℂ)=∑' n:ℕ,(if n=1 then (1:ℂ) else 0)/(n:ℂ)^s:=by
  rw[tsum_eq_single 1 (fun n hn=>by simp[hn])]; simp
 have aeh:Summable (fun n:ℕ=>(if n=1 then (1:ℂ) else 0)/(n:ℂ)^s):=
  (hasSum_single 1 (fun n hn=>by simp[hn])).summable
 rw[a4i,<- (summable_sum atq).tsum_sub aeh]
 refine tsum_congr (fun n=>?_)
 unfold cX
 push_cast
 rw[sub_div,ew]
 congr 1
 ·rw[jf]
 ·split_ifs <;> simp
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory MeromorphicOn
open scoped Real
lemma aco (p:ℕ) (hp:1<=p):
  ∀ j,∑ i∈range j,1/((p+1+i:ℕ):ℝ)^2<=1/(p:ℝ)-1/((p+j:ℕ):ℝ):=by
 have zc:(0:ℝ)<p:=by exact_mod_cast hp
 intro j
 induction j with
 | zero=>simp
 | succ j ih=>
  rw[dk]
  have hq:(0:ℝ)<((p+j:ℕ):ℝ):=by exact_mod_cast (show 0<p+j by omega)
  have h1:1/((p+1+j:ℕ):ℝ)^2<=1/((p+j:ℕ):ℝ)-1/((p+(j+1):ℕ):ℝ):=by
   have e1:((p+1+j:ℕ):ℝ)=((p+j:ℕ):ℝ)+1:=by push_cast; ring
   have e2:((p+(j+1):ℕ):ℝ)=((p+j:ℕ):ℝ)+1:=by push_cast; ring
   rw[e1,e2]
   set q:=((p+j:ℕ):ℝ)
   rw[div_sub_div _ _ hq.ne' (by positivity),ax (by positivity) (by positivity)]
   nlinarith
  linarith
lemma ahy (T:Finset ℕ) (p:ℕ) (hp:1<=p) (hT:∀ k∈T,p<k):
  ∑ k∈T,1/(k:ℝ)^2<=1/(p:ℝ):=by
 rcases T.eq_empty_or_nonempty with he | te
 ·simp[he]
 set M:=T.max' te
 have uj:T ⊆ Icc (p+1) M:=fun k hk=>
  ar.mpr ⟨hT k hk,T.le_max' k hk⟩
 have hM:p<M:=hT M (T.max'_mem te)
 calc ∑ k∈T,1/(k:ℝ)^2<=∑ k∈Icc (p+1) M,1/(k:ℝ)^2:=
       aq uj (fun _ _ _=>by positivity)
  _ = ∑ i∈range (M-p),1/((p+1+i:ℕ):ℝ)^2:=by
      rw[<- cy,dq,
       show M+1-(p+1)=M-p by omega]
  _<=1/(p:ℝ)-1/((p+(M-p):ℕ):ℝ):=aco p hp _
  _ ≤ 1/(p:ℝ):=by
      have:(0:ℝ)<=1/((p+(M-p):ℕ):ℝ):=by positivity
      linarith
noncomputable def fz (X:ℕ) (s:ℂ):ℂ:=riemannZeta s*MX X s-1
noncomputable def hz (X:ℕ) (s:ℂ):ℂ:=1-fz X s^2
lemma vx (X:ℕ):Differentiable ℂ (MX X):=by
 intro s
 unfold MX
 apply mj
 intro d hd
 rw[ar] at hd
 have hd0:(d:ℂ)≠0:=by exact_mod_cast (show d≠0 by omega)
 have te:(d:ℂ)^s≠0:=by
  rw[gq hd0]; exact Complex.exp_ne_zero _
 exact (nm _).div (bu.const_cpow (Or.inl hd0)) te
lemma xt (X:ℕ) {U:Set ℂ} (hU:(1:ℂ)∉U):AnalyticOnNhd ℂ (hz X) U:=by
 have an4:IsOpen ({1}ᶜ:Set ℂ):=fw
 have hd:DifferentiableOn ℂ (hz X) ({1}ᶜ:Set ℂ):=by
  intro s hs
  have h1:s≠1:=hs
  apply c3
  unfold hz fz
  exact (nm _).sub
   ((((je h1).mul (vx X s)).sub_const 1).pow 2)
 exact (hd.analyticOnNhd an4).mono (fun z zx=>by
  intro h; exact hU (h ▸ zx))
lemma a0n (X:ℕ) (s:ℂ):
  hz X s=riemannZeta s*(MX X s*(2-riemannZeta s*MX X s)):=by
 unfold hz fz; ring
theorem aoa {c:ℂ} {r R:ℝ} {g:ℂ->ℂ} (hr:0<r) (ze:r<R)
  (hg:AnalyticOnNhd ℂ g (closedBall c R)) (hgc:g c≠0):
  (∑ᶠ u,(bn g (closedBall c r) u:ℝ))*aa (R/r)<=
   j4 (fun z=>aa ‖g z‖) c R-aa ‖g c‖:=by
 have hR:0<R:=hr.trans ze
 have r_pos:0< |r|:=by rw[a7 hr]; exact hr
 have aqa:|r|< |R|:=by rw[a7 hr,a7 hR]; exact ze
 have agp:AnalyticOnNhd ℂ g (closedBall c |R|):=by rw[a7 hR]; exact hg
 have a9l:=agp.circleAverage_log_norm hR.ne' hgc
 have uq:(m0 (fun u=>(bn g (closedBall c r) u:ℝ))).Finite:=by
  apply ((bn g (closedBall c r)).finiteSupport (isCompact_closedBall _ _)).subset
  intro u hu
  simp only[nv,ne_eq,Int.cast_eq_zero] at hu ⊢
  exact hu
 rw[finsum_mul]
 have key:∑ᶠ u,(bn g (closedBall c r) u:ℝ)*aa (R/r)<=
   ∑ᶠ u,((bn g (closedBall c |R|)) u)*aa (R*‖c-u‖⁻¹):=by
  rw[<- a7 hr]
  refine finsum_le_finsum' ?_ ?_ fun u=>?_
  ·exact (bn g (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
    fun _ _=>(by simp_all)
  ·exact (bn g (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
    fun _ _=>(by simp_all)
  ·by_cases h1:u∈closedBall c |R|
   ·by_cases h2:u∈closedBall c |r|
    ·simp only[(agp.mono (closedBall_subset_closedBall aqa.le)),h2,
      AnalyticOnNhd.divisor_apply,agp,h1]
     by_cases! h3:u=c
     ·rw[h3,(agp c (by simp)).analyticOrderAt_eq_zero.mpr hgc]
      simp
     simp +singlePass only[<- Real.log_abs]
     gcongr 2
     ·simp
     ·have:‖c-u‖≠0:=by simpa [ow] using h3.symm
      simpa [field,abs_div,r_pos.trans aqa,dist_eq_norm'] using h2
    ·simp only[h2,not_false_eq_true,Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Int.cast_zero,zero_mul]
     refine b7 (mod_cast (AnalyticOnNhd.divisor_nonneg agp) u) ?_
     apply Real.log_abs _ ▸ bd
     simp only[mem_closedBall,dist_eq_norm',not_le] at h1 h2
     have:‖c-u‖≠0:=(r_pos.trans h2).ne'
     simpa [field]
   ·have:u∉closedBall c |r|:=by
     simp_all
     linarith
    simp[h1,this]
 linarith
theorem afk (X:ℕ) {c:ℂ} {r R:ℝ} (ze:r<=R)
  (h1:(1:ℂ)∉closedBall c R) (hhc:hz X c≠0):
  ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall c r},(analyticOrderNatAt riemannZeta ρ:ℝ)<=
   ∑ᶠ u,(bn (hz X) (closedBall c r) u:ℝ):=by
 set B:=closedBall c r with hB
 have h1B:(1:ℂ)∉B:=fun h=>h1 (closedBall_subset_closedBall ze h)
 have uq:{ρ:ℂ | riemannZeta ρ=0∧ρ∈B}.Finite:=by
  apply ((isCompact_closedBall c r).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0,s8⟩; exact ⟨s8,h0⟩
 have hA:AnalyticOnNhd ℂ (hz X) (closedBall c R):=xt X h1
 have hAB:AnalyticOnNhd ℂ (hz X) B:=hA.mono (closedBall_subset_closedBall ze)
 have aru:(m0 (fun u=>(bn (hz X) B u:ℝ))).Finite:=by
  apply ((bn (hz X) B).finiteSupport (isCompact_closedBall _ _)).subset
  intro u hu
  simp only[nv,ne_eq,Int.cast_eq_zero] at hu ⊢
  exact hu
 rw[bf _ uq]
 rw[k7 _ (s:=uq.toFinset ∪ aru.toFinset) (by
  intro u hu; simp only[Finset.coe_union,rf]; exact Or.inr hu)]
 have ahz:∀ u,0<=(bn (hz X) B u:ℝ):=fun u=>by
  exact_mod_cast (AnalyticOnNhd.divisor_nonneg hAB) u
 refine br ?_ (aq q5
  (fun u _ _=>ahz u))
 refine ao (fun ρ s8=>?_)
 rw[an] at s8
 obtain ⟨zt,ahm⟩:=s8
 have yd:ρ≠1:=fun h=>h1B (h ▸ ahm)
 rw[AnalyticOnNhd.divisor_apply hAB ahm]
 have axq:AnalyticAt ℂ riemannZeta ρ:=s5 ρ yd
 have hMA:AnalyticAt ℂ (MX X) ρ:=(vx X).analyticAt ρ
 have hqA:AnalyticAt ℂ (fun s=>MX X s*(2-riemannZeta s*MX X s)) ρ:=
  hMA.mul (analyticAt_const.sub (axq.mul hMA))
 have heq:hz X=riemannZeta*(fun s=>MX X s*(2-riemannZeta s*MX X s)):=
  funext (a0n X)
 have anf:analyticOrderAt (hz X) ρ=analyticOrderAt riemannZeta ρ+
   analyticOrderAt (fun s=>MX X s*(2-riemannZeta s*MX X s)) ρ:=by
  rw[heq]; exact o0 axq hqA
 have hr0:0<=r:=by
  have:=mem_closedBall.mp ahm; exact dist_nonneg.trans this
 have hnt:analyticOrderAt (hz X) ρ≠⊤:=by
  apply hA.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
   (mem_closedBall_self (hr0.trans ze)) (closedBall_subset_closedBall ze ahm)
  rw[(hA c (mem_closedBall_self (hr0.trans ze))).analyticOrderAt_eq_zero.mpr hhc]
  simp
 unfold analyticOrderNatAt
 rw[anf] at hnt ⊢
 generalize analyticOrderAt riemannZeta ρ=a at hnt ⊢
 generalize analyticOrderAt (fun s=>MX X s*(2-riemannZeta s*MX X s)) ρ=b at hnt ⊢
 induction a using n0 with
 | top=>simp at hnt
 | coe m=>
  induction b using n0 with
  | top=>simp at hnt
  | coe k=>
   rw[<- ENat.coe_add,ENat.toNat_coe]
   simp only[ENat.map_coe,WithTop.untop₀_coe]
   push_cast
   have:(0:ℝ)<=k:=by positivity
   linarith
theorem aob {X:ℕ} (hX:1<=X) {s:ℂ} (hs:3<=s.re):‖fz X s‖<=1/(X:ℝ):=by
 have uu:1<s.re:=by linarith
 have xc:s≠0:=by intro h; rw[h] at hs; simp at hs; linarith
 unfold fz
 rw[ae4 uu X]
 set g:ℕ->ℝ:=fun n=>if X<n then 1/(n:ℝ)^2 else 0 with hg
 have hbd:∀ n:ℕ,‖(cX X n:ℂ)/(n:ℂ)^s‖<=g n:=by
  intro n
  simp only[hg]
  split_ifs with h
  ·have xb:1<=n:=by omega
   have t6:(0:ℝ)<n:=by exact_mod_cast xb
   rw[i4,norm_natCast_cpow_of_pos (by omega),ba,au]
   have hc:=ad6 hX xb
   have hd:(n.divisors.card:ℝ)<=n:=by exact_mod_cast Nat.card_divisors_le_self n
   have hpow:(n:ℝ)^(3:ℝ)<=(n:ℝ)^s.re:=
    al (by exact_mod_cast xb) hs
   have h3:(n:ℝ)^(3:ℝ)=(n:ℝ)^3:=by norm_cast
   rw[ax (by positivity) (by positivity)]
   rw[h3] at hpow
   nlinarith[fb t6 2,fb t6 3]
  ·rcases c7 n with h0 | tj
   ·subst h0; simp[o7 xc]
   ·rw[acn tj (by omega)]; simp
 have aoc:Summable g:=by
  refine d9 (fun n=>by simp only[hg]; split_ifs <;> positivity)
   (fun n=>?_) (Real.summable_one_div_nat_pow.mpr (by norm_num:1<2))
  simp only[hg]; split_ifs
  ·exact le_rfl
  ·positivity
 have hsum:Summable (fun n:ℕ=>‖(cX X n:ℂ)/(n:ℂ)^s‖):=
  d9 (fun _=>aw _) hbd aoc
 refine (gw hsum).trans ((hsum.tsum_le_tsum hbd aoc).trans ?_)
 refine aoc.tsum_le_of_sum_le (fun F=>?_)
 rw[<- jf]
 exact ahy _ X hX (fun k hk=>(ah.mp hk).2)
lemma vq (X:ℕ) {U:Set ℂ} (hU:(1:ℂ)∉U):ContinuousOn (fz X) U:=by
 intro z zx
 have yp:z≠1:=fun h=>hU (h ▸ zx)
 unfold fz
 exact (((je yp).continuousAt.mul
  (vx X z).continuousAt).sub continuousAt_const).continuousWithinAt
theorem akh {X:ℕ} (hX:2<=X) {c:ℂ} {r R:ℝ} (hr:0<r) (ze:r<R)
  (h1:(1:ℂ)∉closedBall c R) (hc:3<=c.re):
  (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall c r},
      (analyticOrderNatAt riemannZeta ρ:ℝ))*aa (R/r)<=
   j4 (fun z=>aa (1+‖fz X z‖^2)) c R+2/(X:ℝ)^2:=by
 have hR:0<R:=hr.trans ze
 have hX0:(2:ℝ)<=X:=by exact_mod_cast hX
 have hfc:=aob (by omega:1<=X) hc
 have hx:‖fz X c‖^2<=1/(X:ℝ)^2:=by
  rw[jz,<- inv_pow,<- jz]; exact aj (aw _) hfc 2
 have hx4:1/(X:ℝ)^2<=1/4:=by
  rw[ax (by positivity) (by norm_num)]; nlinarith
 have aki:1-‖fz X c‖^2<=‖hz X c‖:=by
  unfold hz
  have:=qs (1:ℂ) (fz X c^2)
  rw[norm_one,la] at this; linarith
 have hhc:hz X c≠0:=by
  intro h; rw[h,jw] at aki; linarith
 have ur:0<=aa (R/r):=bd (by rw[bl hr]; linarith)
 have hZ:=afk X ze.le h1 hhc
 have hJ:=aoa hr ze (xt X h1) hhc
 have arv:(1:ℂ)∉sphere c |R|:=by
  rw[a7 hR]; exact fun h=>h1 (sphere_subset_closedBall h)
 have u6:j4 (fun z=>aa ‖hz X z‖) c R<=
   j4 (fun z=>aa (1+‖fz X z‖^2)) c R:=by
  apply Real.circleAverage_mono
  ·apply MeromorphicOn.circleIntegrable_log_norm
   intro z zx
   exact (xt X arv z zx).meromorphicAt
  ·apply ContinuousOn.circleIntegrable hR.le
   have hc':=vq X (U:=sphere c R)
    (by rw[a7 hR] at arv; exact arv)
   exact p3 (ez.add (hc'.norm.pow 2))
    (fun z _=>by positivity)
  ·intro z _
   by_cases h0:hz X z=0
   ·rw[h0,jw,Real.log_zero]; exact bd (by nlinarith[aw (fz X z)])
   ·apply a5 (g7.mpr h0)
    unfold hz
    refine (ej _ _).trans ?_
    rw[norm_one,la]
 have bd8:-aa ‖hz X c‖<=2/(X:ℝ)^2:=by
  set x:=‖fz X c‖^2 with aa5
  have tp:0<=x:=by positivity
  have tj:0<1-x:=by linarith
  have h2:aa (1-x)<=aa ‖hz X c‖:=a5 tj aki
  have h3:=b5 tj
  have h4:-(2*x)<=1-(1-x)⁻¹:=by
   rw[show 1-(1-x)⁻¹=-x/(1-x) by field_simp; ring]
   rw[bl tj]; nlinarith
  have:x<=1/(X:ℝ)^2:=hx
  have e:2/(X:ℝ)^2=2*(1/(X:ℝ)^2):=by ring
  linarith
 calc (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall c r},
       (analyticOrderNatAt riemannZeta ρ:ℝ))*aa (R/r)
   <= (∑ᶠ u,(bn (hz X) (closedBall c r) u:ℝ))*aa (R/r):=
       ag hZ ur
  _<=_:=hJ
  _<=_:=by linarith
lemma ad7 (c:ℂ) (R θ:ℝ):(circleMap c R θ).im=c.im+R*en θ:=by
 simp[circleMap,Complex.exp_ofReal_mul_I_im]
lemma akj (c:ℂ) (R θ:ℝ):(circleMap c R θ).re=c.re+R*fo θ:=by
 simp[circleMap,Complex.exp_ofReal_mul_I_re]
lemma agr {a1 a2 γ η:ℝ} (hη:0<=η) (h1:a1<=γ-η) (h2:γ+η<=a2):
  2*η<=∫ x in a1..a2,(if |γ-x|<=η then (1:ℝ) else 0):=by
 have e:(fun x:ℝ=>if |γ-x|<=η then (1:ℝ) else 0)=
   mq (i7 (γ-η) (γ+η)) (fun _=>(1:ℝ)):=by
  funext x
  simp only[mq,Set.mem_Icc]
  congr 1
  apply propext
  rw[abs_le]; constructor <;> intro h <;> constructor <;> linarith[h.1,h.2]
 rw[e,ek (by linarith),
  MeasureTheory.integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
  o5,fx,di]
 have uj:mb (γ-η) (γ+η) ⊆ i7 (γ-η) (γ+η) ∩ mb a1 a2:=by
  intro x hx; exact ⟨⟨hx.1.le,hx.2⟩,⟨by linarith[hx.1],by linarith[hx.2]⟩⟩
 have hm:=measure_mono (μ:=volume) uj
 rw[Real.volume_Ioc] at hm
 have uq:volume (i7 (γ-η) (γ+η) ∩ mb a1 a2)≠⊤:=
  ne_top_of_le_ne_top (by rw[Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
   (measure_mono Set.inter_subset_left)
 have:=(ENNReal.ofReal_le_iff_le_toReal uq).mp hm
 rw[Measure.real]
 linarith
theorem afl {X:ℕ} (hX:2<=X) {σ η r R a1 a2 Q:ℝ} (hη:0<η) (hr:0<r)
  (ze:r<R) (ha:a1<=a2) (ha1:∀ tn∈i7 a1 a2,R+2<=|tn|)
  (a4j:∀ tn∈i7 a1 a2,∀ ρ:ℂ,riemannZeta ρ=0->σ<=ρ.re->0<ρ.re->
   |ρ.im-tn|<=η->ρ∈closedBall (3+tn*I) r)
  (hQ:∀ θ:ℝ,∫ tn in a1..a2,
   aa (1+‖fz X (circleMap (3+tn*I) R θ)‖^2)<=Q):
  (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+η<=ρ.im∧ρ.im<=a2-η},
      (analyticOrderNatAt riemannZeta ρ:ℝ))*(2*η)*aa (R/r)<=
   Q+(a2-a1)*(2/(X:ℝ)^2):=by
 have hR:0<R:=hr.trans ze
 have ur:0<aa (R/r):=eo (by rw[na hr]; linarith)
 set Z:={ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+η<=ρ.im∧ρ.im<=a2-η}
 have uq:Z.Finite:=by
  apply ((isCompact_closedBall (0:ℂ) (|a1|+|a2|+2)).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0,-,tu,adr,ahn⟩
  refine ⟨?_,h0⟩
  rw[mem_closedBall,l9]
  have h1:ρ.re<1:=by
   by_contra h'; exact ct (not_lt.mp h') h0
  have:=b6 ρ
  rw[a7 tu] at this
  have h2:|ρ.im|<=|a1|+|a2|:=by
   rw[abs_le]
   constructor
   ·linarith[r2 a1,eg a2]
   ·linarith[k6 a2,eg a1]
  linarith
 set F:=uq.toFinset
 rw[bf _ uq]
 set ind:ℂ->ℝ->ℝ:=fun ρ x=>if |ρ.im-x|<=η then (1:ℝ) else 0 with axs
 set Φ:ℝ->ℝ->ℝ:=fun tn θ=>aa (1+‖fz X (circleMap (3+tn*I) R θ)‖^2)
  with hΦ
 set A:ℝ->ℝ:=fun tn=>j4 (fun z=>aa (1+‖fz X z‖^2))
  (3+tn*I) R with hA
 have axt:∀ tn∈i7 a1 a2,(1:ℂ)∉closedBall (3+tn*I) R:=by
  intro tn xe h
  rw[mem_closedBall,b8] at h
  have:=a6 (1-(3+tn*I))
  simp at this
  have:=ha1 tn xe
  linarith
 have wu:∀ tn∈i7 a1 a2,
   ∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*ind ρ tn<=
    (A tn+2/(X:ℝ)^2)/aa (R/r):=by
  intro tn xe
  have hc:=akh hX hr ze (axt tn xe) (c:=3+tn*I) (by simp)
  rw[bl ur]
  refine br ?_ hc
  apply ag _ ur.le
  have a0o:{ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall (3+tn*I) r}.Finite:=by
   apply ((isCompact_closedBall _ _).inter_riemannZetaZeros_finite).subset
   rintro ρ ⟨h0,s8⟩; exact ⟨s8,h0⟩
  rw[bf _ a0o]
  have e:∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*ind ρ tn=
    ∑ ρ∈F.filter (fun ρ=>|ρ.im-tn|<=η),(analyticOrderNatAt riemannZeta ρ:ℝ):=by
   rw[jf]
   refine ai rfl (fun ρ _=>?_)
   simp only[axs]; split_ifs <;> simp
  rw[e]
  apply aq
  ·intro ρ s8
   simp only[ah,F,an,Z,eh] at s8
   rw[an]
   exact ⟨s8.1.1,a4j tn xe ρ s8.1.1 s8.1.2.1 s8.1.2.2.1 s8.2⟩
  ·intro _ _ _; positivity
 have arw:∀ ρ:ℂ,Measurable (ind ρ):=by
  intro ρ
  apply Measurable.ite _ qt qt
  exact measurableSet_le (by fun_prop) qt
 have amq:∀ ρ:ℂ,IntervalIntegrable (ind ρ) volume a1 a2:=by
  intro ρ
  refine (kb (c:=(1:ℝ))).mono_fun' (arw ρ).aestronglyMeasurable
   (bj (fun x=>?_))
  simp only[axs]; split_ifs <;> simp
 have acp:ContinuousOn (px Φ) (i7 a1 a2 ×ˢ i7 0 (2*π)):=by
  have hcm:Continuous (fun p:ℝ × ℝ=>circleMap (3+p.1*I) R p.2):=by
   unfold circleMap; fun_prop
  have wd:q1 (fun p:ℝ × ℝ=>circleMap (3+p.1*I) R p.2)
    (i7 a1 a2 ×ˢ i7 0 (2*π)) ({1}ᶜ:Set ℂ):=by
   intro p hp h
   simp only[Set.mem_compl_iff,rq] at h
   have:=dy Complex.im h
   rw[ad7] at this
   simp at this
   have hs:=sv p.2
   have hs2:=Real.sin_le_one p.2
   have hp1:=ha1 p.1 (Set.mem_prod.mp hp).1
   rcases abs_cases p.1 with ⟨h1,_⟩ | ⟨h1,_⟩ <;> nlinarith
  have hf:=(vq X (U:=({1}ᶜ:Set ℂ)) (by simp)).comp hcm.continuousOn wd
  exact p3 (ez.add (hf.norm.pow 2)) (fun p _=>by positivity)
 have aje:Integrable (px Φ)
   ((volume.restrict (mb a1 a2)).prod (volume.restrict (mb 0 (2*π)))):=by
  rw[Measure.prod_restrict,<- Measure.volume_eq_prod]
  exact (acp.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
   (Set.prod_mono mr mr)
 have axv:∀ tn,A tn=(2*π)⁻¹*∫ θ in mb 0 (2*π),Φ tn θ:=by
  intro tn
  simp only[hA,Real.circleAverage_def,fx]
  rw[ek (by positivity)]
 have att:IntervalIntegrable A volume a1 a2:=by
  rw[m5 ha]
  have:=aje.integral_prod_left
  simp only[px] at this
  refine (this.const_mul (2*π)⁻¹).congr (bj (fun tn=>?_))
  simp only; rw[axv]
 have bd9:∫ tn in a1..a2,A tn<=Q:=by
  rw[ek ha]
  simp_rw[axv]
  rw[ov]
  have hsw:=MeasureTheory.integral_integral_swap aje
  rw[hsw]
  have hb:∀ θ,∫ tn in mb a1 a2,Φ tn θ<=Q:=by
   intro θ
   have:=hQ θ
   rwa[ek ha] at this
  have h2:∫ θ in mb 0 (2*π),∫ tn in mb a1 a2,Φ tn θ<=
    ∫ θ in mb 0 (2*π),Q:=by
   apply MeasureTheory.integral_mono_of_nonneg
   ·exact bj (fun θ=>MeasureTheory.setIntegral_nonneg
     measurableSet_Ioc (fun x _=>bd
      (by nlinarith[aw (fz X (circleMap (3+x*I) R θ))])))
   ·exact integrable_const Q
   ·exact bj hb
  rw[o5,Real.volume_real_Ioc_of_le (by positivity),kg,
   fx] at h2
  calc (2*π)⁻¹*∫ θ in mb 0 (2*π),∫ tn in mb a1 a2,Φ tn θ
    <= (2*π)⁻¹*(2*π*Q):=ab h2 (by positivity)
   _=Q:=by field_simp
 have axw:∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*(2*η)<=
   ∫ tn in a1..a2,∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*ind ρ tn:=by
  rw[intervalIntegral.integral_finset_sum (fun ρ _=>(amq ρ).const_mul _)]
  refine ao (fun ρ s8=>?_)
  rw[cv]
  apply ab _ (by positivity)
  simp only[F,an,Z,eh] at s8
  exact agr hη.le (by linarith[s8.2.2.2.1]) (by linarith[s8.2.2.2.2])
 have aus:IntervalIntegrable
   (fun tn=>∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*ind ρ tn) volume a1 a2:=by
  have:=IntervalIntegrable.sum (μ:=volume) (a:=a1) (b:=a2) F
   (fun ρ _=>(amq ρ).const_mul (analyticOrderNatAt riemannZeta ρ:ℝ))
  refine this.congr ?_
  exact fun x _=>by simp[pz]
 have aqd:∫ tn in a1..a2,∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*ind ρ tn<=
   ∫ tn in a1..a2,(A tn+2/(X:ℝ)^2)/aa (R/r):=by
  apply ff ha aus
  ·exact (att.add kb).div_const _
  ·exact wu
 have heval:∫ tn in a1..a2,(A tn+2/(X:ℝ)^2)/aa (R/r)=
   ((∫ tn in a1..a2,A tn)+(a2-a1)*(2/(X:ℝ)^2))/aa (R/r):=by
  rw[pk,pl att kb,
   intervalIntegral.integral_const,fx]
 rw[heval] at aqd
 have hsum:(∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ))*(2*η)=
   ∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)*(2*η):=g3 _ _ _
 rw[hsum]
 have h3:=axw.trans aqd
 rw[bl ur] at h3
 linarith
end bt.ZD
namespace bt.qf
open Complex Set Filter Topology MeasureTheory intervalIntegral Asymptotics
open scoped Real Interval
noncomputable def pw (v:ℝ):ℝ:=(v^2-v)/2
lemma akk {v:ℝ} (h0:0<=v) (h1:v<=1):|pw v|<=1/8:=by
 unfold pw; rw[abs_le]; constructor <;> nlinarith[c4 (v-1/2)]
lemma y0 (u:ℝ):|pw (ln u)|<=1/8:=
 akk (Int.fract_nonneg u) (Int.fract_lt_one u).le
lemma ae5 {n:ℕ} {u:ℝ} (hu:u∈Icc (n:ℝ) (n+1)):
  pw (ln u)=pw (u-n):=by
 rcases mn hu.2 with h | h
 ·have:ln u=0:=by
   rw[h,show ((n:ℝ)+1)=((n+1:ℕ):ℝ) by push_cast; ring]
   exact Int.fract_natCast _
  rw[this,h]; unfold pw; ring
 ·have hfl:⌊u⌋=(n:ℤ):=by
   rw[Int.floor_eq_iff]; push_cast; exact ⟨hu.1,h⟩
  rw[ln,hfl]; push_cast; rfl
noncomputable def wf (u:ℝ):ℂ:=mq (Ioi 1) (fun u=>((pw (ln u):ℝ):ℂ)) u
noncomputable def y1 (s:ℂ):ℂ:=mellin wf (-s-1)
noncomputable def zf (s:ℂ) (u:ℝ):ℂ:=(u:ℂ)^(-s-2)*((pw (ln u):ℝ):ℂ)
lemma wq:Measurable fun u:ℝ=>((pw (ln u):ℝ):ℂ):=by
 apply Complex.measurable_ofReal.comp
 unfold pw
 have:=(measurable_fract (R:=ℝ))
 fun_prop
lemma acq (s:ℂ) {u:ℝ} (hu:0<u):‖zf s u‖<=1/8*u^(-s.re-2):=by
 unfold zf
 rw[bo,e9 hu,ba,au]
 have:=y0 u
 have h0:0<=u^(-s-2).re:=by positivity
 simp only[sub_re,neg_re,re_ofNat] at h0 ⊢
 nlinarith
lemma yj {s:ℂ} (hσ:-1<s.re):IntegrableOn (zf s) (Ioi 1):=by
 have hint:IntegrableOn (fun u:ℝ=>1/8*u^(-s.re-2)) (Ioi 1):=
  (rd (by linarith) q7).const_mul _
 refine hint.mono' ?_ ?_
 ·have hc:ContinuousOn (fun u:ℝ=>(u:ℂ)^(-s-2)) (Ioi 1):=by
   intro u hu
   apply ie
   exact continuousAt_ofReal_cpow_const u (-s-2) (Or.inr (by linarith[mem_Ioi.mp hu]))
  exact (hc.aestronglyMeasurable k5).mul
   wq.aestronglyMeasurable
 ·refine (ae_restrict_iff' k5).mpr (Eventually.of_forall fun u hu=>?_)
  exact acq s (by linarith[mem_Ioi.mp hu])
lemma ah0 (s:ℂ):y1 s=∫ u in Ioi 1,zf s u:=by
 unfold y1 mellin wf zf
 have e:∀ t:ℝ,(t:ℂ)^(-s-1-1)•mq (Ioi 1)
   (fun u=>((pw (ln u):ℝ):ℂ)) t=
   mq (Ioi 1) (fun u:ℝ=>(u:ℂ)^(-s-2)*((pw (ln u):ℝ):ℂ)) t:=by
  intro t
  by_cases ht:t∈Ioi 1
  ·rw[nn ht,nn ht,fx]
   congr 2; ring
  ·rw[j2 ht,j2 ht,smul_zero]
 simp_rw[e]
 rw[setIntegral_indicator k5,Ioi_inter_Ioi,
  show ((0:ℝ) ⊔ 1)=1 by norm_num]
lemma ad8 {s:ℂ} (hσ:-1<s.re):‖y1 s‖<=1/(8*(s.re+1)):=by
 rw[ah0]
 calc ‖∫ u in Ioi 1,zf s u‖<=∫ u in Ioi (1:ℝ),1/8*u^(-s.re-2):=by
       apply MeasureTheory.norm_integral_le_of_norm_le
       ·exact (rd (by linarith) q7).const_mul _
       ·refine (ae_restrict_iff' k5).mpr (Eventually.of_forall fun u hu=>?_)
        exact acq s (by linarith[mem_Ioi.mp hu])
  _ = 1/(8*(s.re+1)):=by
      rw[ov,integral_Ioi_rpow_of_lt (by linarith) q7,oi]
      have:-s.re-2+1=-(s.re+1):=by ring
      rw[this]
      field_simp
lemma ve (c:ℂ) {u:ℝ} (hu:0<u):
  HasDerivAt (fun y:ℝ=>(y:ℂ)^c) (c*(u:ℂ)^(c-1)) u:=
 ((Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr hu)).hasDerivAt).comp_ofReal
lemma zy {s:ℂ} (hs:s≠1) {a:ℝ} (ha:0<a):
  s*(s+1)*∫ u in a..(a+1),(u:ℂ)^(-s-2)*((pw (u-a):ℝ):ℂ)=
   -((a:ℂ)^(-s)+((a:ℂ)+1)^(-s))/2+
    (((a:ℂ)+1)^(1-s)-(a:ℂ)^(1-s))/(1-s):=by
 have uu:(1:ℂ)-s≠0:=cb.mpr (qg hs)
 set G:ℝ->ℂ:=fun u=>-s*((pw (u-a):ℝ):ℂ)*(u:ℂ)^(-s-1)
     - (((u-a-1/2:ℝ)):ℂ)*(u:ℂ)^(-s)+(u:ℂ)^(1-s)/(1-s) with hG
 have adu:∀ u∈[[a,a+1]],HasDerivAt G
   (s*(s+1)*((u:ℂ)^(-s-2)*((pw (u-a):ℝ):ℂ))) u:=by
  intro u hu
  rw[uIcc_of_le (by linarith)] at hu
  have yf:0<u:=by linarith[hu.1]
  have hpw:HasDerivAt (fun y:ℝ=>((pw (y-a):ℝ):ℂ)) (((u-a-1/2:ℝ)):ℂ) u:=by
   have:HasDerivAt (fun y:ℝ=>pw (y-a)) (u-a-1/2) u:=by
    unfold pw
    have h1:=((po u).sub_const a)
    have h2:=(h1.pow 2).sub h1
    have h3:=h2.div_const 2
    refine (show HasDerivAt (fun y:ℝ=>((y-a)^2-(y-a))/2) _ u from h3).congr_deriv ?_
    first | (norm_num[id]; done) | (norm_num[id]; ring)
   exact this.ofReal_comp
  have ara:HasDerivAt (fun y:ℝ=>(((y-a-1/2:ℝ)):ℂ)) 1 u:=by
   have:=(((po u).sub_const a).sub_const (1/2)).ofReal_comp
   simpa using this
  have h1:=ve (-s-1) yf
  have h2:=ve (-s) yf
  have h3:=ve (1-s) yf
  have hG':=(((hpw.const_mul (-s)).mul h1).sub (ara.mul h2)).add (h3.div_const (1-s))
  refine (show HasDerivAt G _ u from hG').congr_deriv ?_
  rw[show -s-1-1=-s-2 by ring,show (1-s-1:ℂ)=-s by ring]
  have hup:(u:ℂ)^(-s-1)=(u:ℂ)^(-s-2)*(u:ℂ):=by
   rw[show -s-1=(-s-2)+1 by ring,cpow_add _ _ (by exact_mod_cast yf.ne'),cpow_one]
  have a4k:(u:ℂ)^(-s)=(u:ℂ)^(-s-2)*(u:ℂ)^2:=by
   rw[show (u:ℂ)^2=(u:ℂ)^(2:ℂ) by norm_cast,<- cpow_add _ _ (by exact_mod_cast yf.ne')]
   ring_nf
  rw[hup,a4k]
  unfold pw
  push_cast
  field_simp
  ring
 have hint:IntervalIntegrable
   (fun u:ℝ=>s*(s+1)*((u:ℂ)^(-s-2)*((pw (u-a):ℝ):ℂ))) volume a (a+1):=by
  apply el
  intro u hu
  rw[uIcc_of_le (by linarith)] at hu
  have yf:0<u:=by linarith[hu.1]
  apply ie
  apply p4 continuousAt_const
  apply p4
  ·exact continuousAt_ofReal_cpow_const u (-s-2) (Or.inr yf.ne')
  ·unfold pw; fun_prop
 rw[<- cv,integral_eq_sub_of_hasDerivAt adu hint]
 simp only[hG]
 have hpa:pw (a-a)=0:=by unfold pw; ring
 have hpb:pw (a+1-a)=0:=by unfold pw; ring
 rw[hpa,hpb]
 push_cast
 ring
lemma yr {s:ℂ} (hs:s≠1) (hσ:-1<s.re) (N:ℕ):
  s*(s+1)*∫ u in (1:ℝ)..(N+1),zf s u=
   -(∑ n∈bk (N+1),1/((n:ℂ)+1)^s)+(1+((N:ℂ)+1)^(-s))/2+
    (((N:ℂ)+1)^(1-s)-1)/(1-s):=by
 have uu:(1:ℂ)-s≠0:=cb.mpr (qg hs)
 induction N with
 | zero=>simp
 | succ N ih=>
  have hII:∀ a b:ℝ,1<=a->a<=b->IntervalIntegrable (zf s) volume a b:=by
   intro a b ha hab
   rw[m5 hab]
   exact (yj hσ).mono_set (fun u hu=>by
    simp only[mem_Ioi]; linarith[hu.1])
  have hN0:(0:ℝ)<=N:=av N
  rw[<- gz (b:=(N:ℝ)+1)
   (hII 1 _ le_rfl (by linarith)) (hII _ _ (by linarith) (by push_cast; linarith))]
  have aeg:∫ u in ((N:ℝ)+1)..(((N+1:ℕ):ℝ)+1),zf s u=
    ∫ u in ((N:ℝ)+1)..((N:ℝ)+1+1),
     (u:ℂ)^(-s-2)*((pw (u-((N:ℝ)+1)):ℝ):ℂ):=by
   push_cast
   apply ia
   intro u hu
   rw[uIcc_of_le (by linarith)] at hu
   unfold zf
   have:=ae5 (n:=N+1) (u:=u) (by push_cast; exact hu)
   push_cast at this
   rw[this]
  rw[ud,ih,aeg,zy hs (by linarith)]
  rw[dk (fun n:ℕ=>1/((n:ℂ)+1)^s) (N+1)]
  push_cast
  have e1:((N:ℂ)+1+1)^(-s)=1/((N:ℂ)+1+1)^s:=by
   rw[cpow_neg,jz]
  have e2:((N:ℂ)+1)^(-s)=1/((N:ℂ)+1)^s:=by
   rw[cpow_neg,jz]
  rw[e1,e2]
  ring
lemma vf {w:ℂ} (hw:w.re<0):
  Tendsto (fun N:ℕ=>((N:ℂ)+1)^w) atTop (𝓝 0):=by
 rw[o9]
 have e:∀ N:ℕ,‖((N:ℂ)+1)^w‖=((N:ℝ)+1)^w.re:=by
  intro N
  have:=norm_natCast_cpow_of_pos (Nat.succ_pos N) w
  push_cast at this; exact this
 simp_rw[e]
 have h1:Tendsto (fun N:ℕ=>(N:ℝ)+1) atTop atTop:=
  tendsto_atTop_add_const_right _ 1 l6
 have:=(s3 (y:=-w.re) (by linarith)).comp h1
 refine this.congr (fun N=>?_)
 simp only[mx,neg_neg]
lemma yk {s:ℂ} (hσ:1<s.re):
  riemannZeta s=1/(s-1)+1/2-s*(s+1)*y1 s:=by
 have hs:s≠1:=by intro h; rw[h] at hσ; simp at hσ
 have uu:(1:ℂ)-s≠0:=cb.mpr (qg hs)
 have hI:Tendsto (fun N:ℕ=>s*(s+1)*∫ u in (1:ℝ)..(N+1),zf s u) atTop
   (𝓝 (s*(s+1)*y1 s)):=by
  rw[ah0]
  apply Tendsto.const_mul
  exact intervalIntegral_tendsto_integral_Ioi 1 (yj (by linarith))
   (tendsto_atTop_add_const_right _ 1 l6)
 have hS:Tendsto (fun N:ℕ=>∑ n∈bk (N+1),1/((n:ℂ)+1)^s) atTop
   (𝓝 (riemannZeta s)):=by
  rw[og hσ]
  have hsum:Summable fun n:ℕ=>1/((n:ℂ)+1)^s:=by
   have:=(gn 1).mpr (j7.mpr hσ)
   simpa using this
  exact hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
 have hA:=vf (w:=-s) (by simp; linarith)
 have hB:=vf (w:=1-s) (by simp; linarith)
 have hR:Tendsto (fun N:ℕ=>-(∑ n∈bk (N+1),1/((n:ℂ)+1)^s)+
   (1+((N:ℂ)+1)^(-s))/2+(((N:ℂ)+1)^(1-s)-1)/(1-s)) atTop
   (𝓝 (-riemannZeta s+(1+0)/2+(0-1)/(1-s))):=
  ((hS.neg.add ((hA.const_add 1).div_const 2)).add ((hB.sub_const 1).div_const (1-s)))
 have hEq:=ub (hI.congr (fun N=>yr hs (by linarith) N)) hR
 have:(0-1)/(1-s)=1/(s-1):=by
  rw[zero_sub,p9,<- ss,neg_sub]
 rw[this] at hEq
 linear_combination hEq
lemma acr (u:ℝ):‖wf u‖<=1/8:=by
 unfold wf
 by_cases h:u∈Ioi 1
 ·rw[nn h,ba,au]; exact y0 u
 ·rw[j2 h,jw]; norm_num
lemma ac7:Measurable wf:=wq.indicator k5
lemma x3 {s:ℂ} (hσ:-1<s.re):DifferentiableAt ℂ y1 s:=by
 have a4l:LocallyIntegrableOn wf (Ioi 0):=by
  apply LocallyIntegrable.locallyIntegrableOn
  apply (locallyIntegrable_const (((1/8:ℝ)):ℂ)).mono ac7.aestronglyMeasurable
  refine Eventually.of_forall (fun u=>?_)
  rw[ba,au,a7 (by norm_num)]
  exact acr u
 have a4m:wf =O[atTop] (fun u:ℝ=>u^(-(0:ℝ))):=by
  apply IsBigO.of_bound (1/8)
  refine Eventually.of_forall (fun u=>?_)
  simp only[sg,Real.rpow_zero,norm_one,di]
  exact acr u
 have a4n:wf =O[𝓝[>] 0] (fun u:ℝ=>u^(-(-s.re-2))):=by
  apply IsBigO.of_bound 0
  have:∀ᶠ u in 𝓝[>] (0:ℝ),u<1:=nhdsWithin_le_nhds (Iio_mem_nhds q7)
  filter_upwards[this] with u hu
  unfold wf
  rw[j2 (by simp; linarith)]
  simp
 have hm:=mellin_differentiableAt_of_isBigO_rpow a4l a4m (s:=-s-1) (by simp; linarith)
  a4n (by simp)
 show DifferentiableAt ℂ (fun s=>mellin wf (-s-1)) s
 exact hm.comp (f:=fun s:ℂ=>-s-1) s (by fun_prop)
noncomputable def Phi (s:ℂ):ℂ:=1+(s-1)/2-(s-1)*s*(s+1)*y1 s
lemma x4 {s:ℂ} (hσ:-1<s.re):riemannZeta₁ s=Phi s:=by
 set U:Set ℂ:={s:ℂ | -1<s.re} with a0p
 have hU:IsOpen U:=n2 dm f0
 have y7:Convex ℝ U:=s4 (-1)
 have h1:AnalyticOnNhd ℂ riemannZeta₁ U:=
  (bg.differentiableOn).analyticOnNhd hU
 have h2:AnalyticOnNhd ℂ Phi U:=by
  apply pe _ hU
  intro z hz
  have zx:=x3 (s:=z) hz
  apply c3
  unfold Phi
  fun_prop
 have heq:riemannZeta₁ =ᶠ[𝓝 2] Phi:=by
  have:∀ᶠ z in 𝓝 (2:ℂ),1<z.re:=
   (n2 dm f0).mem_nhds (by norm_num)
  filter_upwards[this] with z hz
  have yp:z≠1:=by intro h; rw[h] at hz; simp at hz
  have a4o:z-1≠0:=cb.mpr yp
  have h:=yk hz
  rw[mg yp] at h
  calc riemannZeta₁ z=(z-1)*((z-1)⁻¹*riemannZeta₁ z):=by
        rw[<- gv,mul_inv_cancel₀ a4o,iq]
   _=(z-1)*(1/(z-1)+1/2-z*(z+1)*y1 z):=by rw[h]
   _=Phi z:=by unfold Phi; field_simp
 exact h1.eqOn_of_preconnected_of_eventuallyEq h2 y7.isPreconnected
  (by norm_num[a0p]) heq hσ
theorem ags {s:ℂ} (hσ:-1<s.re) (hs:s≠1):
  riemannZeta s=1/(s-1)+1/2-s*(s+1)*y1 s:=by
 have uu:s-1≠0:=cb.mpr hs
 rw[mg hs,x4 hσ]
 unfold Phi
 field_simp
theorem ad9 {s:ℂ} (hσ:-1<s.re) (hs:s≠1):
  ‖riemannZeta s‖<=1/‖s-1‖+1/2+‖s‖*‖s+1‖/(8*(s.re+1)):=by
 rw[ags hσ hs]
 have hZ:=ad8 hσ
 calc ‖1/(s-1)+1/2-s*(s+1)*y1 s‖
   <= ‖1/(s-1)‖+‖(1/2:ℂ)‖+‖s*(s+1)*y1 s‖:=by
       refine (ej _ _).trans ?_
       gcongr
       exact ds _ _
  _ ≤ 1/‖s-1‖+1/2+‖s‖*‖s+1‖/(8*(s.re+1)):=by
      rw[i4,norm_one,bo,bo]
      have:‖(1/2:ℂ)‖=1/2:=by simp
      rw[this]
      have h0:0<=‖s‖*‖s+1‖:=by positivity
      calc 1/‖s-1‖+1/2+‖s‖*‖s+1‖*‖y1 s‖
        <= 1/‖s-1‖+1/2+‖s‖*‖s+1‖*(1/(8*(s.re+1))):=by gcongr
       _=_:=by ring
theorem wx {s:ℂ} (h1:-9/10<=s.re) (h2:s.re<=4) (ht:1<=|s.im|):
  ‖riemannZeta s‖<=40*s.im^2:=by
 have hs:s≠1:=by intro h; rw[h] at ht; simp at ht; linarith
 have hb:=ad9 (by linarith) hs
 have xb:|s.im|<=‖s-1‖:=by
  have:=a6 (s-1); simpa using this
 have hns:‖s‖<=5*|s.im|:=by
  have:=b6 s
  have:|s.re|<=4:=abs_le.mpr ⟨by linarith,h2⟩
  linarith
 have a4p:‖s+1‖<=6*|s.im|:=by
  have hb1:=b6 (s+1)
  have tu:|(s+1).re|<=5:=by simp; rw[abs_le]; constructor <;> linarith
  have um:(s+1).im=s.im:=by simp
  rw[um] at hb1
  linarith
 have hi1:1/‖s-1‖<=1:=by
  rw[dw (by linarith)]; linarith
 have zr:s.im^2=|s.im|^2:=(sq_abs _).symm
 have ai7:‖s‖*‖s+1‖<=30*s.im^2:=by
  rw[zr]
  have:=a8 hns a4p (aw _) (by positivity)
  nlinarith
 have xo:(8:ℝ)/10<=8*(s.re+1):=by linarith
 have bct:‖s‖*‖s+1‖/(8*(s.re+1))<=38*s.im^2:=by
  rw[ay (by linarith)]
  have:0<=s.im^2:=c4 _
  nlinarith
 have:1<=s.im^2:=by rw[zr]; nlinarith
 linarith
open scoped ArithmeticFunction.Moebius
open Metric
lemma ux {a:ℝ} (ha:0<a) (N:ℕ):
  ∑ n∈bk N,(n:ℝ)^(-(1+a))<=1+1/a:=by
 have u5:∀ M:ℕ,∑ n∈bk (M+2),(n:ℝ)^(-(1+a))<=1+1/a:=by
  intro M
  rw[fq,fq]
  have hint:∑ i∈bk M,((i+1+1:ℕ):ℝ)^(-(1+a))<=
    ∫ u in (1:ℝ)..1+M,u^(-(1+a)):=by
   have:=lx (x₀:=1) (a:=M) (f:=fun u:ℝ=>u^(-(1+a)))
    (by
     intro u hu v _ huv
     exact c1 (by linarith[hu.1]) huv (by linarith))
   refine br (i6 ?_) this
   apply ai rfl
   intro i _
   push_cast; ring_nf
  have hM:(0:ℝ)<=M:=av M
  have hI:∫ u in (1:ℝ)..1+M,u^(-(1+a))=((1+M)^(-a)-1)/(-a):=by
   rw[pn (Or.inr ⟨by linarith,by
    rw[uIcc_of_le (by linarith)]; norm_num⟩)]
   rw[show -(1+a)+1=-a by ring,oi]
  have tj:0<=(1+(M:ℝ))^(-a):=by positivity
  have hI':((1+M)^(-a)-1)/(-a)<=1/a:=by
   rw[ss,<- p9]
   apply a4 (by linarith) ha.le
  have h0:((0:ℕ):ℝ)^(-(1+a))=0:=by
   rw[mw]; exact qu (by linarith)
  have h1:((0+1:ℕ):ℝ)^(-(1+a))=1:=by simp
  rw[h0,h1]
  linarith
 calc ∑ n∈bk N,(n:ℝ)^(-(1+a))
   <= ∑ n∈bk (N+2),(n:ℝ)^(-(1+a)):=
       aq (jn.mpr (by omega))
        (fun _ _ _=>by positivity)
  _<=1+1/a:=u5 N
lemma aam {s:ℂ} (hs:3/2<=s.re):1/3<=‖riemannZeta s‖:=by
 have h1:1<s.re:=by linarith
 have hmul:=qj h1
 rw[rn h1] at hmul
 have af5:Summable fun n:ℕ=>‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖:=
  summable_norm_iff.mpr (mf.mpr h1)
 have vw:∀ n:ℕ,‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖<=(n:ℝ)^(-(1+1/2:ℝ)):=by
  intro n
  rw[r4]
  split_ifs with hn
  ·positivity
  ·have v8:(1:ℝ)<=n:=by exact_mod_cast i8.mpr hn
   have hμ:‖((μ n:ℤ):ℂ)‖<=1:=by
    rw[lf]; exact_mod_cast gg
   calc ‖((μ n:ℤ):ℂ)‖/(n:ℝ)^s.re<=1/(n:ℝ)^s.re:=
         a4 hμ (by positivity)
    _=(n:ℝ)^(-s.re):=by rw[iv (by linarith),jz]
    _<=(n:ℝ)^(-(1+1/2:ℝ)):=al v8 (by linarith)
 have hL:‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖<=3:=by
  calc ‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖<=∑' n,‖dt (fun n:ℕ=>(μ n:ℂ)) s n‖:=gw af5
   _ ≤ ∑' n:ℕ,(n:ℝ)^(-(1+1/2:ℝ)):=
       ks vw af5 (gr.mpr (by norm_num))
   _ ≤ 1+1/(1/2):=
       lh (fun n=>by positivity) (ux (by norm_num))
   _=3:=by norm_num
 have hn:=dy norm hmul
 rw[bo,norm_one] at hn
 by_contra v7
 push_neg at v7
 have h0:0<=‖LSeries (fun n:ℕ=>(μ n:ℂ)) s‖:=aw _
 nlinarith[aw (riemannZeta s)]
lemma u7 {ρ:ℂ} (s8:ρ≠1):AnalyticAt ℂ riemannZeta ρ:=
 s5 ρ s8
export bt.abg (tb)
lemma uw {ρ:ℂ} (s8:ρ≠1):
  analyticOrderAt riemannZeta₁ ρ=analyticOrderAt riemannZeta ρ:=by
 have hev:riemannZeta₁ =ᶠ[𝓝 ρ] (fun s=>s-1)*riemannZeta:=by
  filter_upwards[fw.mem_nhds s8] with s hs
  exact tb hs
 rw[analyticOrderAt_congr hev,o0 (by fun_prop) (u7 s8)]
 have h0:analyticOrderAt (fun s:ℂ=>s-1) ρ=0:=
  fm.mpr (Or.inr (cb.mpr s8))
 rw[h0,jy]
lemma vv {U:Set ℂ} {ρ:ℂ} (s8:ρ≠1) (hU:ρ∈U):
  bn riemannZeta₁ U ρ=(analyticOrderNatAt riemannZeta ρ:ℤ):=by
 have hA:AnalyticAt ℂ riemannZeta₁ ρ:=bg.analyticAt ρ
 have hM:MeromorphicOn riemannZeta₁ U:=
  fun z _=>(bg.analyticAt z).meromorphicAt
 rw[qh hM hU,hA.meromorphicOrderAt_eq,uw s8]
 unfold analyticOrderNatAt
 generalize analyticOrderAt riemannZeta ρ=k
 induction k using n0 <;> simp
theorem ab4 {t:ℝ} (ht:4<=|t|):
  ((∑ᶠ u,bn riemannZeta₁ (closedBall ((3/2:ℂ)+t *I) (11/5)) u:ℤ)
   : ℝ)<=12*aa (1800*t^2):=by
 set c0:ℂ:=(3/2:ℂ)+t *I with t9
 have aod:c0.re=3/2:=by simp[t9]
 have aoe:c0.im=t:=by simp[t9]
 have t8:0< |t|:=by linarith
 have hc1:c0≠1:=by intro h; have:=dy im h; simp[t9] at this; rw[this] at ht; simp at ht; linarith
 have hfc:|t|/3<=‖riemannZeta₁ c0‖:=by
  rw[tb hc1,bo]
  have h1:|t|<=‖c0-1‖:=by
   have:=a6 (c0-1); simpa [aoe] using this
  have h2:=aam (s:=c0) (by rw[aod])
  calc |t|/3=|t| *(1/3):=by ring
   _<=‖c0-1‖*‖riemannZeta c0‖:=a8 h1 h2 (by norm_num) (aw _)
 have te:riemannZeta₁ c0≠0:=by
  intro h; rw[h,jw] at hfc; linarith
 have hbound:∀ z∈sphere c0 |(12/5:ℝ)|,‖riemannZeta₁ z‖<=600*|t|^3:=by
  intro z hz
  rw[mem_sphere,a7 (by norm_num),b8] at hz
  have tu:|z.re-3/2|<=12/5:=by
   have:=cm (z-c0); simp[t9] at this; rw[hz] at this; exact this
  have um:|z.im-t|<=12/5:=by
   have:=a6 (z-c0); simp[t9] at this; rw[hz] at this; exact this
  have a4q:=abs_le.mp tu
  have adr:|t|-12/5<=|z.im|:=by
   have:=de t z.im; rw[jj] at this; linarith
  have ahn:|z.im|<=|t|+12/5:=by
   have:=de z.im t; linarith
  have yp:z≠1:=by
   intro h; rw[h] at adr; simp at adr; linarith
  rw[tb yp,bo]
  have aof:=wx (s:=z) (by linarith) (by linarith) (by linarith)
  have arx:‖z-1‖<=|t|+53/10:=by
   have:=b6 (z-1)
   have h1:|(z-1).re|<=29/10:=by simp; rw[abs_le]; constructor <;> linarith
   have h2:(z-1).im=z.im:=by simp
   rw[h2] at this; linarith
  have zr:z.im^2<=(|t|+12/5)^2:=by
   rw[<- sq_abs]; exact aj (eg _) ahn 2
  have hA:|t|+53/10<=12/5*|t|:=by linarith
  have hB:|t|+12/5<=12/5*|t|:=by linarith
  calc ‖z-1‖*‖riemannZeta z‖<=(12/5*|t|)*(40*(12/5*|t|)^2):=by
        apply a8 (arx.trans hA) _ (aw _) (by positivity)
        calc ‖riemannZeta z‖<=40*z.im^2:=aof
         _ ≤ 40*(12/5*|t|)^2:=by
             have:=aj (by positivity) hB 2
             nlinarith
   _<=600*|t|^3:=by nlinarith[fb t8 3]
 have w6:(1:ℝ)<=600*|t|^3:=by
  have:(64:ℝ)<=|t|^3:=by
   have:=aj (by norm_num) ht 3; norm_num at this; linarith
  linarith
 have J:=p8 (c:=c0) (r:=11/5) (R:=12/5)
  (M:=600*|t|^3) (by norm_num) (by norm_num) w6
  (fun z _=>bg.analyticAt z) te hbound
 rw[a7 (by norm_num:(0:ℝ)<11/5)] at J
 refine J.trans ?_
 have anl:0<‖riemannZeta₁ c0‖:=g7.mpr te
 have aej:aa (600*|t|^3/‖riemannZeta₁ c0‖)<=aa (1800*t^2):=by
  apply a5 (by positivity)
  rw[ay anl,<- sq_abs t]
  nlinarith[fb t8 2]
 have aay:1/12<=aa (12/5/(11/5)):=by
  have:=b5 (show (0:ℝ)<12/5/(11/5) by norm_num)
  norm_num at this ⊢; linarith
 have aax:0<=aa (1800*t^2):=bd (by nlinarith[sq_abs t,fb t8 2])
 calc aa (600*|t|^3/‖riemannZeta₁ c0‖)/aa (12/5/(11/5))
   <= aa (1800*t^2)/aa (12/5/(11/5)):=
       a4 aej (by linarith)
  _ ≤ aa (1800*t^2)/(1/12):=
      bb aax (by norm_num) aay
  _=12*aa (1800*t^2):=by ring
theorem z7 {t:ℝ} (ht:4<=|t|):
  ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall ((3/2:ℂ)+t *I) (11/5)},
   (analyticOrderNatAt riemannZeta ρ:ℝ)<=12*aa (1800*t^2):=by
 set B:=closedBall ((3/2:ℂ)+t *I) (11/5) with hB
 have h1B:(1:ℂ)∉B:=by
  intro h
  rw[hB,dj,b8] at h
  have:=a6 (1-((3/2:ℂ)+t *I))
  simp at this; linarith
 have uq:{ρ:ℂ | riemannZeta ρ=0∧ρ∈B}.Finite:=by
  apply ((isCompact_closedBall _ _).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0,s8⟩
  exact ⟨s8,h0⟩
 rw[bf _ uq]
 have xh:m0 (bn riemannZeta₁ B) ⊆ ↑uq.toFinset:=by
  intro u hu
  have huB:u∈B:=(bn riemannZeta₁ B).supportWithinDomain hu
  have x8:u≠1:=fun h=>h1B (h ▸ huB)
  rw[b9,an]
  refine ⟨?_,huB⟩
  by_contra hz
  apply hu
  rw[vv x8 huB]
  have:analyticOrderAt riemannZeta u=0:=
   fm.mpr (Or.inr hz)
  simp[analyticOrderNatAt,this]
 have J:=ab4 ht
 rw[k7 _ xh] at J
 push_cast at J
 refine br (i6 ?_) J
 apply ai rfl
 intro ρ s8
 rw[an] at s8
 have yd:ρ≠1:=fun h=>h1B (h ▸ s8.2)
 rw[vv yd s8.2]
 push_cast; rfl
end bt.qf
namespace bt.ZD
open Complex Finset Metric MeasureTheory
open scoped Real
noncomputable def FF (X:ℕ) (Y:ℝ) (s:ℂ):ℂ:=
 (riemannZeta₁ s*MX X s-(s-1))/(s+1)*cexp (s^2/(Y:ℂ)^2)
lemma aog {X:ℕ} {Y:ℝ} {s:ℂ} (hs:s≠1):
  FF X Y s=(s-1)/(s+1)*fz X s*cexp (s^2/(Y:ℂ)^2):=by
 unfold FF fz
 rw[bt.qf.tb hs]
 ring
lemma vl (X:ℕ) (Y:ℝ) {s:ℂ} (hs:-1<s.re):
  DifferentiableAt ℂ (FF X Y) s:=by
 have uu:s+1≠0:=by
  intro h; have:=dy kl h; simp at this; linarith
 have h1:DifferentiableAt ℂ (fun s=>riemannZeta₁ s*MX X s-(s-1)) s:=
  ((bg s).mul (vx X s)).sub
   (bu.sub_const 1)
 have h2:DifferentiableAt ℂ (fun s:ℂ=>s+1) s:=bu.add_const 1
 have h3:DifferentiableAt ℂ (fun s:ℂ=>cexp (s^2/(Y:ℂ)^2)) s:=
  ((bu.pow 2).div_const _).cexp
 exact (h1.div h2 uu).mul h3
lemma we (Y:ℝ) (s:ℂ):
  ‖cexp (s^2/(Y:ℂ)^2)‖=af ((s.re^2-s.im^2)/Y^2):=by
 rw[p5]
 congr 1
 have:s^2/(Y:ℂ)^2=s^2*((1/Y^2:ℝ):ℂ):=by push_cast; ring
 rw[this,Complex.mul_re,o8,Complex.ofReal_im,mul_zero,kg]
 simp[sq]
 ring
lemma uy {s:ℂ} (hs:0<=s.re):‖s-1‖<=‖s+1‖:=by
 have h1:‖s-1‖^2=(s.re-1)^2+s.im^2:=by
  rw[<- jo,jl]; simp; ring
 have h2:‖s+1‖^2=(s.re+1)^2+s.im^2:=by
  rw[<- jo,jl]; simp; ring
 have:‖s-1‖^2<=‖s+1‖^2:=by rw[h1,h2]; nlinarith
 exact (d8 (aw _) (aw _) (by norm_num)).mp this
lemma agt {X:ℕ} {s:ℂ} (hs:0<=s.re):‖MX X s‖<=X:=by
 unfold MX
 refine (c5 _ _).trans ?_
 have:∀ d∈Icc 1 X,‖((c8 d:ℤ):ℂ)/(d:ℂ)^s‖<=1:=by
  intro d hd
  rw[ar] at hd
  rw[i4,norm_natCast_cpow_of_pos (by omega),lf]
  have h1:(1:ℝ)<=(d:ℝ)^s.re:=e5 (by exact_mod_cast hd.1) hs
  have h2:|((c8 d:ℤ):ℝ)|<=1:=by
   exact_mod_cast gg
  rw[dw (by linarith)]; linarith
 refine (ao this).trans ?_
 simp
lemma ah1 {X:ℕ} {Y:ℝ} {s:ℂ} (h1:0<=s.re) (h2:s.re<=4)
  (ht:1<=|s.im|):
  ‖FF X Y s‖<=(40*X*s.im^2+1)*af ((s.re^2-s.im^2)/Y^2):=by
 have uu:s≠1:=by intro h; rw[h] at ht; simp at ht; linarith
 have tj:0<‖s+1‖:=g7.mpr (by
  intro h; have:=dy kl h; simp at this; linarith)
 unfold FF
 rw[bo,we,i4]
 gcongr
 rw[ay tj]
 rw[bt.qf.tb uu]
 have hz:=bt.qf.wx (s:=s) (by linarith) h2 ht
 have hM:=agt (X:=X) h1
 have hr:=uy h1
 calc ‖(s-1)*riemannZeta s*MX X s-(s-1)‖
   <= ‖s-1‖*‖riemannZeta s‖*‖MX X s‖+‖s-1‖:=by
       refine (ej _ _).trans ?_; rw[bo,bo]
  _<=‖s-1‖*(40*s.im^2)*X+‖s-1‖:=by gcongr
  _=(40*X*s.im^2+1)*‖s-1‖:=by ring
  _<=(40*X*s.im^2+1)*‖s+1‖:=by gcongr
theorem y2 (X:ℕ) {Y:ℝ} (hY:1<=Y):
  ∃ K:ℝ,0<=K∧∀ s:ℂ,1/4<=s.re->s.re<=2->
   ‖FF X Y s‖^2<=K*af (-(s.im^2/Y^2)):=by
 have xd:0<Y:=by linarith
 set Kc:Set ℂ:=(i7 (1/4:ℝ) 2) ×ℂ (i7 (-1:ℝ) 1) with hKc
 have a4r:IsCompact Kc:=isCompact_Icc.reProdIm isCompact_Icc
 have wv:ContinuousOn (FF X Y) Kc:=by
  intro z hz
  have:z.re∈i7 (1/4:ℝ) 2:=(r9.mp hz).1
  exact (vl X Y (by linarith[this.1])).continuousAt.continuousWithinAt
 obtain ⟨M0,hM0⟩:=a4r.exists_bound_of_continuousOn wv
 set B:ℝ:=(40*X+1)*af (4/Y^2) with hB
 refine ⟨max (M0^2*af 1) (B^2*(2*Y^4+1)*2),le_max_of_le_left (by positivity),
  fun s h1 h2=>?_⟩
 rcases ig (|s.im|) 1 with ht | ht
 ·have hsK:s∈Kc:=r9.mpr ⟨⟨h1,h2⟩,abs_le.mp ht⟩
  have hb:=hM0 s hsK
  have bea:0<=M0:=(aw _).trans hb
  have xm:af (-1)<=af (-(s.im^2/Y^2)):=by
   apply b4.mpr
   have:s.im^2<=1:=by rw[<- sq_abs]; nlinarith[eg s.im]
   have:s.im^2/Y^2<=1:=by
    rw[dw (by positivity)]; nlinarith
   linarith
  calc ‖FF X Y s‖^2<=M0^2:=aj (aw _) hb 2
   _=M0^2*af 1*af (-1):=by rw[gv,<- bs]; simp
   _<=M0^2*af 1*af (-(s.im^2/Y^2)):=by gcongr
   _<=_:=by gcongr; exact bq _ _
 ·have hb:=ah1 (X:=X) (Y:=Y) (by linarith) (by linarith) ht.le
  set t:=s.im
  have ht2:1<=t^2:=by rw[<- sq_abs]; nlinarith
  have hE:af ((s.re^2-t^2)/Y^2)<=
    af (4/Y^2)*af (-(t^2/Y^2)):=by
   rw[<- bs]; apply b4.mpr
   have:s.re^2<=4:=by nlinarith
   rw[show 4/Y^2+-(t^2/Y^2)=(4-t^2)/Y^2 by ring]
   gcongr
  have hX:(40*X*t^2+1)<=(40*X+1)*t^2:=by nlinarith[av (α:=ℝ) X]
  have hF:‖FF X Y s‖<=B*(t^2*af (-(t^2/Y^2))):=by
   calc ‖FF X Y s‖<=(40*X*t^2+1)*af ((s.re^2-t^2)/Y^2):=hb
    _ ≤ ((40*X+1)*t^2)*(af (4/Y^2)*af (-(t^2/Y^2))):=by
        gcongr
    _=_:=by rw[hB]; ring
  have hq:(t^2*af (-(t^2/Y^2)))^2<=
    (2*Y^4+1)*2*af (-(t^2/Y^2)):=by
   set x:=t^2/Y^2 with aa5
   have tp:0<=x:=by positivity
   have hq1:x^2<=2*af x:=by
    have:=Real.quadratic_le_exp_of_nonneg tp; nlinarith
   have hex:af (-x)*af x=1:=by rw[<- bs]; simp
   have beb:0<af (-x):=bx _
   have ht4:t^4=Y^4*x^2:=by rw[aa5]; field_simp
   have h4:t^4*af (-x)<=2*Y^4:=by
    rw[ht4]
    have:x^2*af (-x)<=2:=by
     calc x^2*af (-x)<=2*af x*af (-x):=by gcongr
      _=2:=by rw[gv,gx (af x),hex,di]
    nlinarith[k0 xd.le 4]
   calc (t^2*af (-x))^2=(t^4*af (-x))*af (-x):=by ring
    _<=(2*Y^4)*af (-x):=by gcongr
    _<=_:=by nlinarith[k0 xd.le 4]
  calc ‖FF X Y s‖^2<=(B*(t^2*af (-(t^2/Y^2))))^2:=
        aj (aw _) hF 2
   _=B^2*(t^2*af (-(t^2/Y^2)))^2:=by ring
   _<=B^2*((2*Y^4+1)*2*af (-(t^2/Y^2))):=by gcongr
   _=B^2*(2*Y^4+1)*2*af (-(t^2/Y^2)):=by ring
   _<=_:=by gcongr; exact cd _ _
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory
open scoped Real
theorem ah2:∃ K:ℝ,1<=K∧∀ t:ℝ,
  ‖riemannZeta ((1/2:ℂ)+t *I)‖<=K*(|t|+3)^((9:ℝ)/40):=by
 have wv:ContinuousOn (fun t:ℝ=>riemannZeta ((1/2:ℂ)+t *I)) (i7 (-1024) 1024):=by
  intro t _
  have te:(1/2:ℂ)+t *I≠1:=by
   intro h; have:=dy kl h; simp at this
  have hc:Continuous (fun t:ℝ=>(1/2:ℂ)+t *I):=by fun_prop
  exact ((je te).continuousAt.comp
   (f:=fun t:ℝ=>(1/2:ℂ)+t *I) hc.continuousAt).continuousWithinAt
 obtain ⟨K0,ya⟩:=isCompact_Icc.exists_bound_of_continuousOn wv
 have abh:∀ t:ℝ,1024<=t->‖riemannZeta ((1/2:ℂ)+t *I)‖<=
   8000*(|t|+3)^((9:ℝ)/40):=by
  intro t ht
  have t8:0<t:=by linarith
  have h:=agn ht
  have ur:aa t<=40*t^((1:ℝ)/40):=by
   have:=np t8.le (show (0:ℝ)<1/40 by norm_num)
   linarith[show t^((1:ℝ)/40)/(1/40)=40*t^((1:ℝ)/40) by ring]
  have h5:t^((5:ℕ)⁻¹:ℝ)*t^((1:ℝ)/40)=t^((9:ℝ)/40):=by
   rw[<- c6 t8]; norm_num
  have u6:t^((9:ℝ)/40)<=(|t|+3)^((9:ℝ)/40):=by
   apply dh t8.le _ (by norm_num)
   rw[a7 t8]; linarith
  have hp:0<=t^((5:ℕ)⁻¹:ℝ):=by positivity
  calc ‖riemannZeta ((1/2:ℂ)+t *I)‖<=200*t^((5:ℕ)⁻¹:ℝ)*aa t:=h
   _<=200*t^((5:ℕ)⁻¹:ℝ)*(40*t^((1:ℝ)/40)):=by gcongr
   _=8000*t^((9:ℝ)/40):=by rw[<- h5]; ring
   _<=_:=by gcongr
 refine ⟨max 8000 (max K0 1),by simp,fun t=>?_⟩
 have h1:(1:ℝ)<=(|t|+3)^((9:ℝ)/40):=
  e5 (by linarith[eg t]) (by norm_num)
 have hK8:(8000:ℝ)<=max 8000 (max K0 1):=bq _ _
 rcases ig t (-1024) with ht | ht
 ·have hc:(1/2:ℂ)+t *I=(starRingEnd ℂ) ((1/2:ℂ)+((-t:ℝ):ℂ)*I):=by
   apply kn <;> simp
  rw[hc,riemannZeta_conj,d4]
  have:=abh (-t) (by linarith)
  rw[j1] at this
  calc _<=8000*(|t|+3)^((9:ℝ)/40):=this
   _<=_:=by gcongr
 rcases ig t 1024 with ht' | ht'
 ·have hb:=ya t ⟨ht.le,ht'⟩
  have:K0<=max 8000 (max K0 1):=le_max_of_le_right (bq _ _)
  calc _<=K0:=hb
   _<=max 8000 (max K0 1):=this
   _=max 8000 (max K0 1)*1:=(di _).symm
   _<=_:=by gcongr
 ·calc _<=8000*(|t|+3)^((9:ℝ)/40):=abh t ht'.le
   _<=_:=by gcongr
lemma akl {Y:ℝ} (hY:3<=Y) (t:ℝ):
  (|t|+3)^((9:ℝ)/20)*af (-(t^2/Y^2))<=(2*Y)^((9:ℝ)/20):=by
 have xd:0<Y:=by linarith
 have anw:af (-(t^2/Y^2))<=1:=by
  rw[jt]; have:0<=t^2/Y^2:=by positivity
  linarith
 rcases ig (|t|) Y with ht | ht
 ·have h1:(|t|+3)^((9:ℝ)/20)<=(2*Y)^((9:ℝ)/20):=
   dh (by positivity) (by linarith) (by norm_num)
  calc _<=(2*Y)^((9:ℝ)/20)*1:=by
        apply a8 h1 anw (by positivity) (by positivity)
   _=_:=di _
 ·set x:=|t|/Y with hx
  have x2:1<x:=by rw[hx,na xd]; linarith
  have ht2:t^2/Y^2=x^2:=by rw[hx,l8,sq_abs]
  have h1:|t|+3<=2*Y*x:=by
   have e:2*Y*x=2*|t|:=by rw[hx]; field_simp
   rw[e]; linarith
  have h2:(|t|+3)^((9:ℝ)/20)<=(2*Y)^((9:ℝ)/20)*x:=by
   calc (|t|+3)^((9:ℝ)/20)<=(2*Y*x)^((9:ℝ)/20):=
         dh (by positivity) h1 (by norm_num)
    _ = (2*Y)^((9:ℝ)/20)*x^((9:ℝ)/20):=
        e6 (by positivity) (by linarith)
    _ ≤ (2*Y)^((9:ℝ)/20)*x^(1:ℝ):=by
        gcongr
        ·exact x2.le
        ·norm_num
    _=_:=by rw[fi]
  have h3:x*af (-(x^2))<=1:=by
   rw[kv,<- jx,dw (bx _)]
   have:=cw (x^2)
   nlinarith
  rw[ht2]
  calc (|t|+3)^((9:ℝ)/20)*af (-(x^2))
    <= (2*Y)^((9:ℝ)/20)*x*af (-(x^2)):=by gcongr
   _=(2*Y)^((9:ℝ)/20)*(x*af (-(x^2))):=by ring
   _<=(2*Y)^((9:ℝ)/20)*1:=by gcongr
   _=_:=di _
lemma aep (t:ℝ) (n:ℕ):ee (-psi (t/(2*π)) n)=yi t n:=by
 unfold ee psi yi
 congr 1
 push_cast
 field_simp
lemma amr (X:ℕ) (t:ℝ):
  MX X ((1/2:ℂ)+t *I)=
   ∑ n∈Icc 1 X,(((c8 n:ℤ):ℝ)*(1/ak n):ℝ)*yi t n:=by
 unfold MX
 refine ai rfl (fun n hn=>?_)
 rw[ar] at hn
 rw[jd,ad3 hn.1,aep]
 push_cast; ring
lemma z0 {Y:ℝ} (hY:0<Y) (c:ℝ) (hc:1<=c):
  ∫ t:ℝ,af (-(c/Y^2)*t^2)<=2*Y:=by
 rw[integral_gaussian]
 have:π/(c/Y^2)<=(2*Y)^2:=by
  rw[ml,ay (by positivity)]
  have:=j3
  nlinarith[c4 Y]
 calc ak (π/(c/Y^2))<=ak ((2*Y)^2):=dg this
  _=2*Y:=fk (by linarith)
theorem ah3:∃ K:ℝ,0<=K∧∀ (X:ℕ) (Y:ℝ),1<=X->6<=Y->
  tq (FF X Y) (1/2)<=
   K*((2*Y)^((9:ℝ)/20)*(3*Y*(1+aa X)+18*X)+Y):=by
 obtain ⟨Kz,bec,hKz⟩:=ah2
 refine ⟨8*ak π*Kz^2+4,by positivity,fun X Y hX hY=>?_⟩
 have xd:0<Y:=by linarith
 set w:ℝ->ℝ:=fun t=>af (-(1/Y^2)*t^2) with hw
 set Mt:ℝ->ℂ:=fun t=>∑ n∈Icc 1 X,
  (((c8 n:ℤ):ℝ)*(1/ak n):ℝ)*yi t n with hMt
 have wu:∀ t:ℝ,‖FF X Y ((1/2:ℝ)+t *I)‖^2<=
   2*(2*Kz^2*(2*Y)^((9:ℝ)/20)*(‖Mt t‖^2*w t))+
    2*(2*af (-(2/Y^2)*t^2)):=by
  intro t
  set s:ℂ:=((1/2:ℝ):ℂ)+t *I with hs
  have wm:s.re=1/2:=by simp[hs]
  have afi:s.im=t:=by simp[hs]
  have uu:s≠1:=by intro h; have:=dy kl h; rw[wm] at this; simp at this
  rw[aog uu,bo,bo,we,wm,afi,i4]
  have w0:(s+1).re=3/2:=by rw[Complex.add_re,wm]; norm_num
  have tj:0<‖s+1‖:=g7.mpr (fun h=>by rw[h] at w0; norm_num at w0)
  have ary:‖s-1‖/‖s+1‖<=1:=by
   rw[dw tj]
   exact uy (by rw[wm]; norm_num)
  have hMX:MX X s=Mt t:=by
   rw[hs,show Mt t=MX X ((1/2:ℂ)+t *I) from (amr X t).symm]
   congr 1; push_cast; ring
  have zv:‖fz X s‖^2<=2*(‖riemannZeta s‖^2*‖Mt t‖^2)+2:=by
   unfold fz
   rw[hMX]
   have:=ej (riemannZeta s*Mt t) 1
   rw[bo,norm_one] at this
   nlinarith[aw (riemannZeta s*Mt t-1),aw (riemannZeta s),
    aw (Mt t),c4 (‖riemannZeta s‖*‖Mt t‖-1)]
  have hz:‖riemannZeta s‖<=Kz*(|t|+3)^((9:ℝ)/40):=by
   have:=hKz t
   rwa[show ((1/2:ℂ)+t *I)=s by rw[hs]; push_cast; ring] at this
  have hz2:‖riemannZeta s‖^2<=Kz^2*(|t|+3)^((9:ℝ)/20):=by
   have:=aj (aw _) hz 2
   rw[i5,<- da ((|t|+3)^((9:ℝ)/40)),<- d7
    (by positivity)] at this
   norm_num at this ⊢
   exact this
  have hE:af (((1/2)^2-t^2)/Y^2)^2<=2*af (-(2/Y^2)*t^2):=by
   rw[<- db]
   have:((2:ℕ):ℝ)*(((1/2)^2-t^2)/Y^2)=1/(2*Y^2)+(-(2/Y^2)*t^2):=by
    push_cast; field_simp; ring
   rw[this,bs]
   gcongr
   have hl2:=f6
   have h72:1/(2*Y^2)<=aa 2:=by
    have:1/(2*Y^2)<=1/72:=by
     rw[ax (by positivity) (by norm_num)]; nlinarith
    linarith
   calc af (1/(2*Y^2))<=af (aa 2):=b4.mpr h72
    _=2:=fl (by norm_num)
  have hW:=akl (by linarith:(3:ℝ)<=Y) t
  have hw2:af (-(2/Y^2)*t^2)=af (-(t^2/Y^2))*w t:=by
   rw[hw,<- bs]; congr 1; ring
  set E2:=af (-(2/Y^2)*t^2)
  have hE2:0<=E2:=by positivity
  calc (‖s-1‖/‖s+1‖*‖fz X s‖*af (((1/2)^2-t^2)/Y^2))^2
    <= (1*‖fz X s‖*af (((1/2)^2-t^2)/Y^2))^2:=by gcongr
   _=‖fz X s‖^2*af (((1/2)^2-t^2)/Y^2)^2:=by ring
   _ ≤ (2*(Kz^2*(|t|+3)^((9:ℝ)/20)*‖Mt t‖^2)+2)*(2*E2):=by
       have a4s:‖fz X s‖^2<=2*(Kz^2*(|t|+3)^((9:ℝ)/20)*‖Mt t‖^2)+2:=by
        have:=ag hz2 (c4 ‖Mt t‖)
        linarith
       exact a8 a4s hE (by positivity) (by positivity)
   _ = 2 * (2*Kz^2*(((|t|+3)^((9:ℝ)/20)*af (-(t^2/Y^2)))*
         (‖Mt t‖^2*w t)))+2*(2*E2):=by rw[hw2]; ring
   _ ≤ _:=by
       have h:=ag hW (by positivity:(0:ℝ)<=‖Mt t‖^2*w t)
       have h2:=ab h (by positivity:(0:ℝ)<=2*(2*Kz^2))
       linarith
 have ax0:Integrable (fun t=>‖Mt t‖^2*w t):=by
  have hbd:∀ t,‖Mt t‖^2<=(X:ℝ)^2:=by
   intro t
   apply aj (aw _)
   rw[show Mt t=MX X ((1/2:ℂ)+t *I) from (amr X t).symm]
   exact agt (by simp)
  refine Integrable.mono' ((ib (b:=1/Y^2) (by positivity)).const_mul
   ((X:ℝ)^2)) ?_ (bj (fun t=>?_))
  ·apply kk
   simp only[hMt,hw,yi]
   fun_prop
  ·rw[au,bh (by positivity)]
   simp only[hw]
   exact ag (hbd t) (by positivity)
 have a0q:Integrable (fun t:ℝ=>af (-(2/Y^2)*t^2)):=
  ib (by positivity)
 obtain ⟨K,ya,hK⟩:=y2 X (by linarith:(1:ℝ)<=Y)
 have a0r:Integrable (fun t:ℝ=>‖FF X Y ((1/2:ℝ)+t *I)‖^2):=by
  refine Integrable.mono' ((ib (b:=1/Y^2) (by positivity)).const_mul K)
   ?_ (bj (fun t=>?_))
  ·apply kk
   apply Continuous.pow
   apply Continuous.norm
   have:Continuous (fun t:ℝ=>((1/2:ℝ):ℂ)+t *I):=by fun_prop
   exact ma.mpr (fun t=>(vl X Y (by simp; norm_num)).continuousAt.comp
    this.continuousAt)
  ·rw[au,bh (by positivity)]
   have:=hK ((1/2:ℝ)+t *I) (by simp; norm_num) (by simp; norm_num)
   simp only[add_im,ofReal_im,mul_im,ofReal_re,I_im,di,I_re,mul_zero,ij,
    jy] at this
   calc _<=K*af (-(t^2/Y^2)):=this
    _=_:=by congr 2; ring
 have hmv:=aal (Icc 1 X) (fun n hn=>(ar.mp hn).1)
  (fun n=>((((c8 n:ℤ):ℝ)*(1/ak n):ℝ):ℂ)) hY
 have bed:∫ t,‖Mt t‖^2*w t<=ak π*(3*Y*(1+aa X)+18*X):=by
  refine hmv.trans ?_
  apply ab _ (df _)
  have hb:∀ n∈Icc 1 X,‖((((c8 n:ℤ):ℝ)*(1/ak n):ℝ):ℂ)‖^2*
    (3*Y+18*n)<=3*Y*(1/(n:ℝ))+18:=by
   intro n hn
   rw[ar] at hn
   have t6:(0:ℝ)<n:=by exact_mod_cast hn.1
   rw[ba,au,sq_abs,i5,l8,sf,
    ly t6.le]
   have hmu:(((c8 n:ℤ):ℝ))^2<=1:=by
    have:=gg (n:=n)
    have h':|((c8 n:ℤ):ℝ)|<=1:=by exact_mod_cast this
    nlinarith[eg ((c8 n:ℤ):ℝ),sq_abs ((c8 n:ℤ):ℝ)]
   calc _<=1*(1/(n:ℝ))*(3*Y+18*n):=by gcongr
    _=3*Y*(1/(n:ℝ))+18:=by field_simp
  refine (ao hb).trans (le_of_eq_of_le (by rw[cu,
   <- bc,a9,jv,cp]) ?_)
  have hH:∑ n∈Icc 1 X,1/(n:ℝ)<=1+aa X:=by
   have h:=nb X
   have e:((harmonic X:ℚ):ℝ)=∑ n∈Icc 1 X,1/(n:ℝ):=by
    rw[harmonic,<- cy,dq]
    push_cast
    refine ai (by simp) (fun i _=>?_)
    push_cast; ring
   rw[<- e]; exact_mod_cast h
  simp only[oo]
  nlinarith
 set C:=2*Kz^2*(2*Y)^((9:ℝ)/20) with hC
 have hI1:Integrable (fun t=>2*(C*(‖Mt t‖^2*w t))):=(ax0.const_mul C).const_mul 2
 have hI2:Integrable (fun t:ℝ=>2*(2*af (-(2/Y^2)*t^2))):=
  (a0q.const_mul 2).const_mul 2
 have hint:∫ t:ℝ,‖FF X Y ((1/2:ℝ)+t *I)‖^2<=
   ∫ t:ℝ,(2*(C*(‖Mt t‖^2*w t))+2*(2*af (-(2/Y^2)*t^2))):=
  integral_mono a0r (hI1.add hI2) wu
 rw[integral_add hI1 hI2] at hint
 simp only[integral_const_mul] at hint
 have hg:=z0 xd 2 (by norm_num)
 have hL:tq (FF X Y) (1/2)=∫ t:ℝ,‖FF X Y ((1/2:ℝ)+t *I)‖^2:=by
  unfold tq; push_cast; rfl
 rw[hL]
 refine hint.trans ?_
 have hP:0<=(2*Y)^((9:ℝ)/20):=by positivity
 have hS:=df π
 have a0s:0<=aa X:=rh X
 calc 2*(2*Kz^2*(2*Y)^((9:ℝ)/20)*∫ t,‖Mt t‖^2*w t)+
       2*(2*∫ t:ℝ,af (-(2/Y^2)*t^2))
   ≤ 2 * (2*Kz^2*(2*Y)^((9:ℝ)/20)*
       (ak π*(3*Y*(1+aa X)+18*X)))+2*(2*(2*Y)):=by
       gcongr
  _ = (4*ak π*Kz^2)*((2*Y)^((9:ℝ)/20)*(3*Y*(1+aa X)+18*X))
        + 8*Y:=by ring
  _ ≤ _:=by
      have hQ:0<=(2*Y)^((9:ℝ)/20)*(3*Y*(1+aa X)+18*X):=by positivity
      have bee:1<=ak π:=by
       rw[show (1:ℝ)=ak 1 by simp]
       exact dg (by linarith[jq])
      have hk:1<=Kz^2:=by nlinarith
      have h1:4*ak π*Kz^2<=8*ak π*Kz^2+4:=by nlinarith
      have h2:8<=8*ak π*Kz^2+4:=by nlinarith
      nlinarith[ag h1 hQ,ag h2 xd.le]
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma aqh {n:ℕ} (hn:1<=n) (u t:ℝ):
  1/(n:ℂ)^((u:ℂ)+t *I)=(((n:ℝ)^(-u):ℝ):ℂ)*yi t n:=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hnc:(n:ℂ)≠0:=by exact_mod_cast t6.ne'
 rw[js _ _ hnc]
 have h1:(n:ℂ)^(u:ℂ)=(((n:ℝ)^u:ℝ):ℂ):=by
  rw[lq t6.le]; push_cast; rfl
 have h2:(n:ℂ)^((t:ℂ)*I)=d6 (((t *aa n:ℝ):ℂ)*I):=by
  rw[gq hnc,show (n:ℂ)=((n:ℝ):ℂ) by push_cast; rfl,
   <- j8 t6.le]
  congr 1; push_cast; ring
 rw[h1,h2,iv t6.le]
 unfold yi
 have hs:((((n:ℝ)^u:ℝ)):ℂ)≠0:=by
  exact_mod_cast (dc t6 u).ne'
 rw[neg_mul,Complex.exp_neg]
 push_cast
 field_simp
theorem aip {X:ℕ} (hX:1<=X) {Y:ℝ} (hY:6<=Y) {u:ℝ} (hu:1<u):
  Integrable (fun t:ℝ=>‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2))∧
  ∫ t:ℝ,‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)<=
   2*ak π*(18+3*Y/X)*(1+1/(2*u-2))^4+2:=by
 have xd:0<Y:=by linarith
 have hX0:(0:ℝ)<X:=by exact_mod_cast hX
 set w:ℝ->ℝ:=fun t=>af (-(1/Y^2)*t^2) with hw
 have aoh:Integrable w:=ib (by positivity)
 set D:ℕ->ℝ:=fun n=>(n.divisors.card:ℝ)*(n:ℝ)^(-u) with hD
 have hD0:∀ n,0<=D n:=fun n=>by simp only[hD]; positivity
 have aek:Summable D:=by
  refine summable_of_sum_range_le hD0 (c:=(1+1/(u-1))^2) (fun Z=>?_)
  have h:=an9 hu Z
  calc ∑ n∈range Z,D n<=∑ n∈Icc 1 Z,D n:=by
        rw[sw]
        have:∑ n∈Ico 0 Z,D n=D 0+∑ n∈Ico 1 Z,D n:=by
         rcases c7 Z with h0 | tj
         ·subst h0; simp[hD]
         ·rw[pd tj]
        rw[this]
        have a4t:D 0=0:=by simp[hD]
        rw[a4t,jy]
        exact aq (fun n hn=>by
         simp only[g4,ar] at hn ⊢; omega) (fun n _ _=>hD0 n)
   _=_:=rfl
   _<=_:=h
 set a:ℕ->ℝ->ℂ:=fun n t=>(cX X n:ℂ)/(n:ℂ)^((u:ℂ)+t *I) with ha
 have wm:∀ t:ℝ,1<((u:ℂ)+t *I).re:=fun t=>by simp; exact hu
 have zv:∀ t:ℝ,fz X ((u:ℂ)+t *I)=∑' n,a n t:=fun t=>ae4 (wm t) X
 have haD:∀ n t,‖a n t‖<=D n:=by
  intro n t
  rcases c7 n with h0 | tj
  ·subst h0
   have:((u:ℂ)+t *I)≠0:=fun h=>by have:=dy kl h; simp at this; linarith
   simp[ha,o7 this,hD]
  ·simp only[ha,hD]
   rw[i4,norm_natCast_cpow_of_pos tj,ba,au]
   have hc:=ad6 hX tj
   have tu:((u:ℂ)+t *I).re=u:=by simp
   rw[tu,iv (by positivity),<- jx]
   gcongr
 have a4u:∀ t:ℝ,‖fz X ((u:ℂ)+t *I)‖<=∑' n,D n:=by
  intro t
  rw[zv]
  exact (gw (d9 (fun _=>aw _)
   (fun n=>haD n t) aek)).trans (ks (fun n=>haD n t)
    (d9 (fun _=>aw _) (fun n=>haD n t) aek) aek)
 have wv:Continuous (fun t:ℝ=>fz X ((u:ℂ)+t *I)):=by
  apply ma.mpr
  intro t
  have te:(u:ℂ)+t *I≠1:=fun h=>by
   have:=dy kl h; simp at this; linarith
  have hc:Continuous (fun t:ℝ=>(u:ℂ)+t *I):=by fun_prop
  exact (vq X (U:=({1}ᶜ:Set ℂ)) (by simp)).continuousAt
   (fw.mem_nhds te) |>.comp (f:=fun t:ℝ=>(u:ℂ)+t *I) hc.continuousAt
 have hint:Integrable (fun t:ℝ=>‖fz X ((u:ℂ)+t *I)‖^2*w t):=by
  refine Integrable.mono' (aoh.const_mul ((∑' n,D n)^2)) ?_
   (Eventually.of_forall (fun t=>?_))
  ·exact ((wv.norm.pow 2).mul (by simp only[hw]; fun_prop)).aestronglyMeasurable
  ·rw[au,bh (by simp only[hw]; positivity)]
   exact ag (aj (aw _) (a4u t) 2)
    (by simp only[hw]; positivity)
 refine ⟨hint, ?_⟩
 set ε:ℝ:=1/(2*Y) with hε
 have a4v:0<ε:=by positivity
 obtain ⟨Z,hZ⟩:∃ Z:ℕ,∑' k,D (k+Z)<=ε:=by
  have:=(tendsto_sum_nat_add D).eventually (Iic_mem_nhds a4v)
  obtain ⟨Z,hZ⟩:=this.exists
  exact ⟨Z,hZ⟩
 set P:ℝ->ℂ:=fun t=>∑ n∈Ico 1 Z,((cX X n*(n:ℝ)^(-u):ℝ):ℂ)*yi t n with hP
 have hPa:∀ t:ℝ,P t=∑ n∈range Z,a n t:=by
  intro t
  rw[sw]
  rcases c7 Z with h0 | tj
  ·subst h0; simp[hP]
  rw[pd tj]
  have h0:a 0 t=0:=by
   have:((u:ℂ)+t *I)≠0:=fun h=>by have:=dy kl h; simp at this; linarith
   simp[ha,o7 this]
  rw[h0,jy]
  refine ai rfl (fun n hn=>?_)
  rw[g4] at hn
  simp only[ha]
  rw[jd,aqh hn.1]
  push_cast; ring
 have yc:∀ t:ℝ,‖fz X ((u:ℂ)+t *I)-P t‖<=ε:=by
  intro t
  have hsa:Summable (fun n=>a n t):=
   (d9 (fun _=>aw _) (fun n=>haD n t) aek).of_norm
  have e:=hsa.sum_add_tsum_nat_add Z
  rw[zv,hPa,<- e,j0]
  have hsn:Summable (fun k=>‖a (k+Z) t‖):=
   d9 (fun _=>aw _) (fun k=>haD (k+Z) t)
    ((gn Z).mpr aek)
  exact (gw hsn).trans ((hsn.tsum_le_tsum (fun k=>haD (k+Z) t)
   ((gn Z).mpr aek)).trans hZ)
 have hmv:=aal (Ico 1 Z) (fun n hn=>(g4.mp hn).1)
  (fun n=>((cX X n*(n:ℝ)^(-u):ℝ):ℂ)) hY
 have a0t:∑ n∈Ico 1 Z,‖((cX X n*(n:ℝ)^(-u):ℝ):ℂ)‖^2*(3*Y+18*n)<=
   (18+3*Y/X)*(1+1/(2*u-2))^4:=by
  have hb:∀ n∈Ico 1 Z,‖((cX X n*(n:ℝ)^(-u):ℝ):ℂ)‖^2*(3*Y+18*n)<=
    (18+3*Y/X)*((n.divisors.card:ℝ)^2*(n:ℝ)^(-(2*u-1))):=by
   intro n hn
   rw[g4] at hn
   have t6:(0:ℝ)<n:=by exact_mod_cast hn.1
   rw[ba,au,sq_abs,i5]
   by_cases hnX:n<=X
   ·rw[acn hn.1 hnX]; simp; positivity
   push Not at hnX
   have hc:=ad6 hX hn.1
   have hc2:cX X n^2<=(n.divisors.card:ℝ)^2:=by
    rw[<- sq_abs]; exact aj (eg _) hc 2
   have hpow:((n:ℝ)^(-u))^2=(n:ℝ)^(-(2*u-1))*(n:ℝ)⁻¹:=by
    rw[<- da,<- d7 t6.le,<- o2,<- c6 t6]
    congr 1; push_cast; ring
   have a4w:(X:ℝ)<n:=by exact_mod_cast hnX
   have hinv:(n:ℝ)⁻¹*(3*Y+18*n)<=18+3*Y/X:=by
    have e:(n:ℝ)⁻¹*(3*Y+18*n)=3*Y/n+18:=by field_simp
    rw[e]
    have:3*Y/n<=3*Y/X:=bb (by positivity) hX0 a4w.le
    linarith
   have zc:0<=(n:ℝ)^(-(2*u-1)):=by positivity
   calc cX X n^2*((n:ℝ)^(-u))^2*(3*Y+18*n)
     = cX X n^2*(n:ℝ)^(-(2*u-1))*((n:ℝ)⁻¹*(3*Y+18*n)):=by
         rw[hpow]; ring
    _ ≤ (n.divisors.card:ℝ)^2*(n:ℝ)^(-(2*u-1))*(18+3*Y/X):=by
        gcongr
    _=_:=by ring
  refine (ao hb).trans ?_
  rw[<- bc]
  gcongr
  have h:=ai1 (σ:=2*u-1) (by linarith) Z
  rw[show 2*u-1-1=2*u-2 by ring] at h
  refine br ?_ h
  exact aq (fun n hn=>by
   simp only[g4,ar] at hn ⊢; omega) (fun n _ _=>by positivity)
 have a4x:∀ t:ℝ,‖P t‖<=∑ n∈Ico 1 Z,‖((cX X n*(n:ℝ)^(-u):ℝ):ℂ)‖:=by
  intro t
  refine (c5 _ _).trans (ao (fun n _=>?_))
  rw[bo]
  have:‖yi t n‖=1:=by
   unfold yi; rw[<- ofReal_neg]; exact k9 _
  rw[this,di]
 have ax1:Continuous P:=by simp only[hP,yi]; fun_prop
 have a0u:Integrable (fun t=>‖P t‖^2*w t):=by
  refine Integrable.mono' (aoh.const_mul ((∑ n∈Ico 1 Z,
   ‖((cX X n*(n:ℝ)^(-u):ℝ):ℂ)‖)^2)) ?_ (Eventually.of_forall (fun t=>?_))
  ·exact ((ax1.norm.pow 2).mul (by simp only[hw]; fun_prop)).aestronglyMeasurable
  ·rw[au,bh (by simp only[hw]; positivity)]
   exact ag (aj (aw _) (a4x t) 2)
    (by simp only[hw]; positivity)
 have wu:∀ t:ℝ,‖fz X ((u:ℂ)+t *I)‖^2*w t<=2*(‖P t‖^2*w t)+2*ε^2*w t:=by
  intro t
  have h1:‖fz X ((u:ℂ)+t *I)‖<=‖P t‖+ε:=by
   have:=norm_le_insert' (fz X ((u:ℂ)+t *I)) (P t)
   linarith[yc t]
  have hw0:0<=w t:=by simp only[hw]; positivity
  have h2:‖fz X ((u:ℂ)+t *I)‖^2<=2*‖P t‖^2+2*ε^2:=by
   nlinarith[aw (fz X ((u:ℂ)+t *I)),aw (P t),c4 (‖P t‖-ε)]
  nlinarith
 have hI1:Integrable (fun t:ℝ=>2*(‖P t‖^2*w t)):=a0u.const_mul 2
 have hI2:Integrable (fun t:ℝ=>2*ε^2*w t):=aoh.const_mul (2*ε^2)
 have hI:∫ t:ℝ,‖fz X ((u:ℂ)+t *I)‖^2*w t<=
   ∫ t:ℝ,(2*(‖P t‖^2*w t)+2*ε^2*w t):=integral_mono hint (hI1.add hI2) wu
 rw[integral_add hI1 hI2,integral_const_mul,integral_const_mul] at hI
 have hw2:∫ t:ℝ,w t<=2*Y:=by
  have:=z0 xd 1 le_rfl
  simpa [hw] using this
 have bef:2*ε^2*(2*Y)<=1:=by
  rw[hε]; field_simp; nlinarith
 calc ∫ t:ℝ,‖fz X ((u:ℂ)+t *I)‖^2*w t
       <= (2*∫ t:ℝ,‖P t‖^2*w t)+2*ε^2*(∫ t:ℝ,w t):=hI
  _ ≤ 2*(ak π*((18+3*Y/X)*(1+1/(2*u-2))^4))+2*ε^2*(2*Y):=by
      gcongr
      exact hmv.trans (ab a0t (df _))
  _ ≤ _:=by
      have:0<=ak π*((18+3*Y/X)*(1+1/(2*u-2))^4):=by positivity
      nlinarith
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma y3 {T:ℝ} (hT:1<T):T^(1/aa T)=af 1:=by
 have ua:0<T:=by linarith
 rw[c9 ua]
 congr 1
 have:aa T≠0:=(eo hT).ne'
 field_simp
theorem ah4 {T M J1 J2 u:ℝ} (hT:af 1<=T) (hM:1<=M)
  (hJ1:0<=J1) (hJ2:0<=J2)
  (h1:J1<=M*T^((29:ℝ)/20)*aa T^4) (h2:J2<=M*aa T^4)
  (x8:1/2<=u) (hu2:u<=1+1/aa T):
  J1^((1+1/aa T-u)/(1+1/aa T-1/2))*
   J2^((u-1/2)/(1+1/aa T-1/2))<=
   af 3*M*aa T^4*T^((29:ℝ)/10*(1-u)):=by
 set L:=aa T with hL
 have hT1:1<T:=fj (by have:=cw 1; linarith) hT
 have ua:0<T:=by linarith
 have hL1:1<=L:=by rw[hL,<- kt 1]; exact a5 (bx 1) hT
 set b:=1+1/L with hb
 have hbh : 1 / 2 ≤ b - 1 / 2 := by rw[hb]; have:0<1/L:=by positivity
                                    linarith
 set θ1:=(b-u)/(b-1/2) with zj
 set θ2:=(u-1/2)/(b-1/2) with a4y
 have xo:0<b-1/2:=by linarith
 have a0v:0<=θ1:=fe (by linarith) xo.le
 have a0w:0<=θ2:=fe (by linarith) xo.le
 have hsum:θ1+θ2=1:=by
  rw[zj,a4y,<- add_div,show b-u+(u-1/2)=b-1/2 by ring,div_self xo.ne']
 have hML:0<M*L^4:=by positivity
 have hA:J1^θ1<=(M*L^4)^θ1*(T^((29:ℝ)/20))^θ1:=by
  rw[<- e6 hML.le (by positivity)]
  exact dh hJ1 (by linarith[show M*T^((29:ℝ)/20)*L^4=
   M*L^4*T^((29:ℝ)/20) by ring]) a0v
 have hB:J2^θ2<=(M*L^4)^θ2:=dh hJ2 h2 a0w
 have a0x:θ1<=2*(1-u)+2/L:=by
  rw[zj,ay xo]
  have h0:0<=1-u+1/L:=by rw[hb] at hu2; linarith
  have hp:0<=(1-u+1/L)*(2/L):=b7 h0 (by positivity)
  have e:(2*(1-u)+2/L)*(b-1/2)=(1-u+1/L)+(1-u+1/L)*(2/L):=by
   rw[hb]; ring
  rw[e]
  have e2:b-u=1-u+1/L:=by rw[hb]; ring
  rw[e2]; linarith
 have as8:(T^((29:ℝ)/20))^θ1<=af 3*T^((29:ℝ)/10*(1-u)):=by
  rw[<- d7 ua.le]
  calc T^((29:ℝ)/20*θ1)<=T^((29:ℝ)/10*(1-u)+(29/10)*(1/L)):=by
        apply al hT1.le
        have:=ab a0x (by norm_num:(0:ℝ)<=29/20)
        have e:(29:ℝ)/20*(2*(1-u)+2/L)=29/10*(1-u)+29/10*(1/L):=by
         ring
        linarith
   _ = T^((29:ℝ)/10*(1-u))*(T^(1/L))^((29:ℝ)/10):=by
       rw[c6 ua,<- d7 ua.le]; ring_nf
   _ = T^((29:ℝ)/10*(1-u))*af ((29:ℝ)/10):=by
       rw[hL,y3 hT1,<- Real.exp_mul]; ring_nf
   _ ≤ T^((29:ℝ)/10*(1-u))*af 3:=by
       gcongr; norm_num
   _=_:=by ring
 calc J1^θ1*J2^θ2<=((M*L^4)^θ1*(T^((29:ℝ)/20))^θ1)*(M*L^4)^θ2:=
       a8 hA hB (by positivity) (by positivity)
  _ = (M*L^4)^(θ1+θ2)*(T^((29:ℝ)/20))^θ1:=by
      rw[c6 hML]; ring
  _=M*L^4*(T^((29:ℝ)/20))^θ1:=by rw[hsum,fi]
  _<=M*L^4*(af 3*T^((29:ℝ)/10*(1-u))):=by gcongr
  _=_:=by ring
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma vr (X:ℕ) {Y:ℝ} (hY:1<=Y) {σ:ℝ} (h1:1/4<=σ) (h2:σ<=2):
  Integrable (fun t:ℝ=>‖FF X Y ((σ:ℂ)+t *I)‖^2):=by
 obtain ⟨K,ya,hK⟩:=y2 X hY
 have xd:0<Y:=by linarith
 refine Integrable.mono' ((ib (b:=1/Y^2) (by positivity)).const_mul K)
  ?_ (Eventually.of_forall (fun t=>?_))
 ·apply kk
  apply Continuous.pow
  apply Continuous.norm
  have hc:Continuous (fun t:ℝ=>(σ:ℂ)+t *I):=by fun_prop
  exact ma.mpr (fun t=>(vl X Y (by simp; linarith)).continuousAt.comp
   (f:=fun t:ℝ=>(σ:ℂ)+t *I) hc.continuousAt)
 ·rw[au,bh (by positivity)]
  have:=hK ((σ:ℂ)+t *I) (by simp; linarith) (by simp; linarith)
  have um:((σ:ℂ)+t *I).im=t:=by simp
  rw[um] at this
  calc _<=K*af (-(t^2/Y^2)):=this
   _=_:=by congr 2; ring
lemma aoi (X:ℕ) {Y:ℝ} (hY:1<=Y):∃ M:ℝ,∀ s:ℂ,1/4<=s.re->s.re<=2->
  ‖FF X Y s‖<=M:=by
 obtain ⟨K,ya,hK⟩:=y2 X hY
 refine ⟨ak K,fun s h1 h2=>?_⟩
 have h:=hK s h1 h2
 have hle:af (-(s.im^2/Y^2))<=1:=by
  rw[jt]; have:0<=s.im^2/Y^2:=by positivity
  linarith
 have:‖FF X Y s‖^2<=K:=h.trans (by nlinarith)
 exact ku this
lemma alr {X:ℕ} (hX:1<=X) {Y:ℝ} (hY:6<=Y) {b:ℝ} (hb1:1<b) (hb2:b<=2):
  tq (FF X Y) b<=2*(2*ak π*(18+3*Y/X)*(1+1/(2*b-2))^4+2):=by
 have xd:0<Y:=by linarith
 obtain ⟨hint,hbd⟩:=aip hX hY hb1
 have wu:∀ t:ℝ,‖FF X Y ((b:ℂ)+t *I)‖^2<=
   2*(‖fz X ((b:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)):=by
  intro t
  set s:ℂ:=(b:ℂ)+t *I with hs
  have wm:s.re=b:=by simp[hs]
  have afi:s.im=t:=by simp[hs]
  have uu:s≠1:=by intro h; have:=dy kl h; rw[wm] at this; simp at this; linarith
  rw[aog uu,bo,bo,we,wm,afi,i4]
  have w0:0<‖s+1‖:=g7.mpr (fun h=>by
   have:=dy kl h; simp[hs] at this; linarith)
  have ary:‖s-1‖/‖s+1‖<=1:=by
   rw[dw w0]; exact uy (by rw[wm]; linarith)
  have hE:af ((b^2-t^2)/Y^2)^2<=2*af (-(1/Y^2)*t^2):=by
   rw[<- db]
   have e:((2:ℕ):ℝ)*((b^2-t^2)/Y^2)=
     2*b^2/Y^2+(-(1/Y^2)*t^2+-(t^2/Y^2)):=by
    push_cast; field_simp; ring
   rw[e,bs,bs]
   have h1:af (2*b^2/Y^2)<=2:=by
    have hl2:=f6
    have:2*b^2/Y^2<=aa 2:=by
     have:2*b^2/Y^2<=8/36:=by
      rw[ax (by positivity) (by norm_num)]; nlinarith
     linarith
    calc _<=af (aa 2):=b4.mpr this
     _=2:=fl (by norm_num)
   have h2:af (-(t^2/Y^2))<=1:=by
    rw[jt]; have:0<=t^2/Y^2:=by positivity
    linarith
   have h3:=bx (-(1/Y^2)*t^2)
   calc af (2*b^2/Y^2)*(af (-(1/Y^2)*t^2)*af (-(t^2/Y^2)))
     <= 2*(af (-(1/Y^2)*t^2)*1):=by gcongr
    _=_:=by ring
  calc (‖s-1‖/‖s+1‖*‖fz X s‖*af ((b^2-t^2)/Y^2))^2
    <= (1*‖fz X s‖*af ((b^2-t^2)/Y^2))^2:=by gcongr
   _=‖fz X s‖^2*af ((b^2-t^2)/Y^2)^2:=by ring
   _<=‖fz X s‖^2*(2*af (-(1/Y^2)*t^2)):=by gcongr
   _=_:=by ring
 unfold tq
 calc ∫ t:ℝ,‖FF X Y ((b:ℂ)+t *I)‖^2
   <= ∫ t:ℝ,2*(‖fz X ((b:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)):=
       integral_mono (vr X (by linarith) (by linarith) hb2) (hint.const_mul 2) wu
  _ = 2*∫ t:ℝ,‖fz X ((b:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2):=
      integral_const_mul _ _
  _<=_:=by gcongr
lemma arz {X:ℕ} {Y:ℝ} (hY:0<Y) {s:ℂ} (h0:0<=s.re) (h6:s.re<=6)
  (ht1:6<=|s.im|) (ht2:|s.im|<=Y):‖fz X s‖^2<=15*‖FF X Y s‖^2:=by
 have uu:s≠1:=by intro h; rw[h] at ht1; simp at ht1; linarith
 rw[aog uu,bo,bo,we,i4]
 have um:6<=‖s-1‖:=by
  have:=a6 (s-1); simp at this; linarith
 have hp1:0<‖s+1‖:=fj (by linarith) ((uy h0).trans' um)
 have ary:3/4<=‖s-1‖/‖s+1‖:=by
  rw[bl hp1]
  have:‖s+1‖<=‖s-1‖+2:=by
   calc ‖s+1‖=‖(s-1)+2‖:=by ring_nf
    _<=‖s-1‖+‖(2:ℂ)‖:=ds _ _
    _=‖s-1‖+2:=by norm_num
  linarith
 have hE:af (-1)<=af ((s.re^2-s.im^2)/Y^2):=by
  apply b4.mpr
  have:s.im^2<=Y^2:=by rw[<- sq_abs]; exact aj (eg _) ht2 2
  rw[bl (by positivity)]; nlinarith[c4 s.re]
 have he:af (-1)*af 1=1:=by rw[<- bs]; simp
 have he1:af 1<2.7182818286:=f7
 have tj:0<af (-1):=bx _
 set q:=‖s-1‖/‖s+1‖*af ((s.re^2-s.im^2)/Y^2)
 have hq:3/4*af (-1)<=q:=a8 ary hE tj.le (by positivity)
 have hq2:1<=15*q^2:=by
  have h1:(3/4*af (-1))^2<=q^2:=aj (by positivity) hq 2
  have h2:1<=15*(3/4*af (-1))^2:=by
   have:af (-1)=1/af 1:=by rw[kv,jz]
   rw[this]
   rw[show 15*(3/4*(1/af 1))^2=135/16/af 1^2 by field_simp; ring]
   rw[bl (by positivity)]
   nlinarith[bx 1]
  linarith
 calc ‖fz X s‖^2<=15*q^2*‖fz X s‖^2:=by nlinarith[c4 ‖fz X s‖]
  _=_:=by ring
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma vs {T:ℝ} (hT:af 8<=T):2980<=T∧8<=aa T:=by
 have h8:(2980:ℝ)<=af 8:=by
  have:=cw 1
  have e:af 8=af 1^8:=by rw[<- db]; norm_num
  have h1:(2.7182818283:ℝ)<af 1:=i9
  rw[e]
  calc (2980:ℝ)<=2.7182818283^8:=by norm_num
   _<=af 1^8:=by gcongr
 refine ⟨h8.trans hT, ?_⟩
 rw[<- kt 8]
 exact a5 (bx 8) hT
lemma aoj {T:ℝ} (hT:af 8<=T):
  (2*(T+10))^((9:ℝ)/20)*(3*(T+10)*(1+aa (⌈T⌉₊:ℕ))+18*(⌈T⌉₊:ℕ))
   + (T+10)<=110*T^((29:ℝ)/20)*aa T^4:=by
 obtain ⟨hT1,hL8⟩:=vs hT
 set L:=aa T
 have ua:0<T:=by linarith
 have hX1:(T:ℝ)<=(⌈T⌉₊:ℕ):=f9 T
 have hX2:((⌈T⌉₊:ℕ):ℝ)<T+1:=ef ua.le
 have anc:(0:ℝ)<(⌈T⌉₊:ℕ):=by linarith
 have a0s:aa (⌈T⌉₊:ℕ)<=2*L:=by
  have h1:aa (⌈T⌉₊:ℕ)<=aa (T^2):=a5 anc (by nlinarith)
  rw[cq] at h1; push_cast at h1; linarith
 have hY:2*(T+10)<=4*T:=by linarith
 have hP:(2*(T+10))^((9:ℝ)/20)<=2*T^((9:ℝ)/20):=by
  calc (2*(T+10))^((9:ℝ)/20)<=(4*T)^((9:ℝ)/20):=
        dh (by positivity) hY (by norm_num)
   _=(4:ℝ)^((9:ℝ)/20)*T^((9:ℝ)/20):=e6 (by norm_num) ua.le
   _ ≤ 2*T^((9:ℝ)/20):=by
       gcongr
       calc (4:ℝ)^((9:ℝ)/20)<=(4:ℝ)^((1:ℝ)/2):=
             al (by norm_num) (by norm_num)
        _ = 2:=by
            rw[show (4:ℝ)=2^(2:ℝ) by norm_num,<- d7 (by norm_num)]; norm_num
 have hS:3*(T+10)*(1+aa (⌈T⌉₊:ℕ))+18*(⌈T⌉₊:ℕ)<=54*T*L:=by
  have h0:0<=aa (⌈T⌉₊:ℕ):=rh _
  nlinarith
 have hTT:T^((9:ℝ)/20)*T=T^((29:ℝ)/20):=by
  rw[<- Real.rpow_add_one ua.ne']; norm_num
 have a4z:T<=T^((29:ℝ)/20):=by
  calc T=T^(1:ℝ):=(fi T).symm
   _<=_:=al (by linarith) (by norm_num)
 have hL4:L<=L^4:=by
  have h3:1<=L^3:=dx (by linarith)
  nlinarith
 have tj:0<=T^((9:ℝ)/20):=by positivity
 calc _<=2*T^((9:ℝ)/20)*(54*T*L)+2*T:=
       e8 (a8 hP hS (by positivity) (by positivity)) (by linarith)
  _=108*(T^((9:ℝ)/20)*T)*L+2*T:=by ring
  _ ≤ 108*T^((29:ℝ)/20)*L+2*T^((29:ℝ)/20)*L:=by
      rw[hTT]; nlinarith[a4z,show (1:ℝ)<=L by linarith]
  _=110*T^((29:ℝ)/20)*L:=by ring
  _<=_:=by gcongr
lemma aok {L Y X:ℝ} (hL:8<=L) (hX:0<X) (hYX:3*Y/X<=6) (hY:0<=Y):
  2*(2*ak π*(18+3*Y/X)*(1+L/2)^4+2)<=197*L^4:=by
 have hq4:(1+L/2)^4<=L^4:=aj (by positivity) (by linarith) 4
 have hpi:ak π<=2:=by
  rw[show (2:ℝ)=ak 4 by rw[show (4:ℝ)=2^2 by norm_num,fk (by norm_num)]]
  exact dg (by linarith[j3])
 have h1L:1<=L^4:=dx (by linarith)
 have h0:0<=3*Y/X:=by positivity
 have hA:2*ak π*(18+3*Y/X)<=2*2*24:=
  a8 (by linarith) (by linarith) (by positivity) (by norm_num)
 have hAQ:2*ak π*(18+3*Y/X)*(1+L/2)^4<=(2*2*24)*L^4:=
  a8 hA hq4 (by positivity) (by norm_num)
 linarith
set_option maxHeartbeats 2000000 in
theorem akp:∃ C0:ℝ,0<C0∧∀ T:ℝ,af 8<=T->∀ u t1 t2:ℝ,
  1/2<=u->u<=6->t1<=t2->(6<=t1∨t2<=-6)->-(T+4)<=t1->t2<=T+4->
  ∫ t in t1..t2,‖fz ⌈T⌉₊ ((u:ℂ)+t *I)‖^2<=
   C0*aa T^4*max 1 (T^((29:ℝ)/10*(1-u))):=by
 obtain ⟨K1,a40,hK1⟩:=ah3
 set M:ℝ:=110*K1+197 with hM
 have w6:1<=M:=by rw[hM]; linarith
 have a0y:197<=M:=by rw[hM]; linarith
 refine ⟨15*af 3*M+300,by positivity, ?_⟩
 intro T hT u t1 t2 x8 hu2 afm y8 ht1 ht2
 obtain ⟨hT1,hL8⟩:=vs hT
 set L:=aa T with hL
 set X:ℕ:=⌈T⌉₊ with atu
 set Y:ℝ:=T+10 with agv
 have ua:0<T:=by linarith
 have hX1:(T:ℝ)<=X:=f9 T
 have hX:1<=X:=by
  have:(1:ℝ)<=X:=by linarith
  exact_mod_cast this
 have hY6:6<=Y:=by rw[agv]; linarith
 have xd:0<Y:=by linarith
 have ug:0<L:=by linarith
 have a0z:1<=max 1 (T^((29:ℝ)/10*(1-u))):=bq _ _
 have hL4:0<=L^4:=by positivity
 have akq:∀ t∈ko t1 t2,6<=|t|∧|t|<=T+4:=by
  intro t ht
  rw[gj afm] at ht
  rcases y8 with h | h
  ·rw[a7 (by linarith[ht.1])]; constructor <;> linarith[ht.1,ht.2]
  ·rw[g5 (by linarith[ht.2])]; constructor <;> linarith[ht.1,ht.2]
 have wv:ContinuousOn (fun t:ℝ=>‖fz X ((u:ℂ)+t *I)‖^2) (ko t1 t2):=by
  have hc:Continuous (fun t:ℝ=>(u:ℂ)+t *I):=by fun_prop
  have wd:q1 (fun t:ℝ=>(u:ℂ)+t *I) (ko t1 t2) ({1}ᶜ:Set ℂ):=by
   intro t ht h
   simp only[Set.mem_compl_iff,rq] at h
   have:=dy Complex.im h; simp at this
   have:=(akq t ht).1; rw[‹t=0›] at this; simp at this; linarith
  exact (((vq X (U:=({1}ᶜ:Set ℂ)) (by simp)).comp hc.continuousOn wd).norm).pow 2
 have atv:IntervalIntegrable (fun t:ℝ=>‖fz X ((u:ℂ)+t *I)‖^2) volume t1 t2:=
  wv.intervalIntegrable
 rcases ig (1+1/L) u with hub | hub
 ·
  obtain ⟨hint,hbd⟩:=aip hX hY6 (show 1<u by
   have:0<1/L:=by positivity
   linarith)
  have wu:∀ t∈ko t1 t2,‖fz X ((u:ℂ)+t *I)‖^2<=
    3*(‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)):=by
   intro t ht
   have h:=akq t ht
   have hw:af (-1)<=af (-(1/Y^2)*t^2):=by
    apply b4.mpr
    have:t^2<=Y^2:=by
     rw[<- sq_abs]; exact aj (eg _) (by rw[agv]; linarith[h.2]) 2
    have:1/Y^2*t^2<=1:=by
     rw[ki,iq,dw (by positivity)]; exact this
    linarith
   have he:1<=3*af (-1):=by
    rw[kv]
    have:=f7
    rw[<- jx,bl (bx 1)]; linarith
   nlinarith[c4 ‖fz X ((u:ℂ)+t *I)‖]
  have h1:∫ t in t1..t2,‖fz X ((u:ℂ)+t *I)‖^2<=
    ∫ t in t1..t2,3*(‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)):=
   ff afm atv ((hint.const_mul 3).intervalIntegrable)
    (fun t ht=>wu t (by rw[gj afm]; exact ht))
  have h2:∫ t in t1..t2,3*(‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2))<=
    ∫ t:ℝ,3*(‖fz X ((u:ℂ)+t *I)‖^2*af (-(1/Y^2)*t^2)):=by
   rw[ek afm]
   exact setIntegral_le_integral (hint.const_mul 3) (Eventually.of_forall (fun t=>by positivity))
  rw[integral_const_mul] at h2
  have hq:1/(2*u-2)<=L/2:=by
   have:2/L<=2*u-2:=by
    have:1/L<=u-1:=by linarith
    rw[ay ug] at this ⊢; nlinarith
   have h2L:0<2/L:=by positivity
   rw[ay (by linarith)]
   calc (1:ℝ)=L/2*(2/L):=by field_simp
    _<=L/2*(2*u-2):=by gcongr
  have beg  : 0 < 2 * u - 2 := by have:0<1/L:=by positivity
                                  linarith
  have hq4:(1+1/(2*u-2))^4<=L^4:=by
   apply aj (by positivity); linarith
  have hYX:3*Y/X<=6:=by
   rw[ay (by linarith)]; rw[agv]; linarith
  have hpi:ak π<=2:=by
   rw[show (2:ℝ)=ak 4 by rw[show (4:ℝ)=2^2 by norm_num,fk (by norm_num)]]
   exact dg (by linarith[j3])
  have beh:2*ak π*(18+3*Y/X)*(1+1/(2*u-2))^4+2<=98*L^4:=by
   have h1L:1<=L^4:=dx (by linarith)
   have:2*ak π*(18+3*Y/X)<=2*2*24:=by
    have:0<=ak π:=df _
    have:0<=3*Y/X:=by positivity
    nlinarith
   nlinarith[df π,show 0<=3*Y/X by positivity,
    show 0<=(1+1/(2*u-2))^4 by positivity]
  calc ∫ t in t1..t2,‖fz X ((u:ℂ)+t *I)‖^2<=3*(98*L^4):=by linarith
   _<=300*L^4*1:=by nlinarith
   _ ≤ (15*af 3*M+300)*L^4*max 1 (T^((29:ℝ)/10*(1-u))):=by
       have:0<=15*af 3*M:=by positivity
       nlinarith[ab a0z hL4]
 ·
  set b:=1+1/L with hb
  have h1L:0<1/L:=by positivity
  have hb1:1<b:=by rw[hb]; linarith
  have hb2:b<=9/8:=by
   rw[hb]; have:1/L<=1/8:=by rw[ax ug (by norm_num)]; linarith
   linarith
  obtain ⟨MF,hMF⟩:=aoi X (by linarith:(1:ℝ)<=Y)
  have h3l:=ahw (FF X Y) (a:=1/2) (b:=b) (δ:=1/8) (M:=MF)
   (by linarith) (by norm_num)
   (by
    intro s hs
    exact (vl X Y (by linarith[hs.1])).differentiableWithinAt)
   (fun s h1 h2=>hMF s (by linarith) (by linarith))
   (by simpa using vr X (by linarith:(1:ℝ)<=Y) (σ:=1/2) (by norm_num) (by norm_num))
   (vr X (by linarith:(1:ℝ)<=Y) (by linarith) (by linarith))
   x8 hub.le (T+4)
  have hJ1:tq (FF X Y) (1/2)<=M*T^((29:ℝ)/20)*L^4:=by
   refine (hK1 X Y hX hY6).trans ?_
   have h:=aoj hT
   rw[<- atu] at h
   have:K1*((2*Y)^((9:ℝ)/20)*(3*Y*(1+aa X)+18*X)+Y)<=
     K1*(110*T^((29:ℝ)/20)*L^4):=ab h a40
   have tj:0<=T^((29:ℝ)/20)*L^4:=by positivity
   calc _<=K1*(110*T^((29:ℝ)/20)*L^4):=this
    _=(110*K1)*(T^((29:ℝ)/20)*L^4):=by ring
    _ ≤ M*(T^((29:ℝ)/20)*L^4):=by
        apply ag _ tj; rw[hM]; linarith
    _=_:=by ring
  have hJ2:tq (FF X Y) b<=M*L^4:=by
   refine (alr hX hY6 hb1 (by linarith)).trans ?_
   have e:1/(2*b-2)=L/2:=by rw[hb]; field_simp; ring
   rw[e]
   have hYX:3*Y/X<=6:=by
    rw[ay (by linarith)]; rw[agv]; linarith
   refine (aok hL8 (by linarith) hYX xd.le).trans ?_
   exact ag a0y hL4
  have a41:0<=tq (FF X Y) (1/2):=integral_nonneg (fun _=>c4 _)
  have a42:0<=tq (FF X Y) b:=integral_nonneg (fun _=>c4 _)
  have hia:=ah4 (br (b4.mpr (by norm_num)) hT) w6 a41 a42 hJ1 hJ2 x8 hub.le
  have wu:∀ t∈ko t1 t2,‖fz X ((u:ℂ)+t *I)‖^2<=
    15*‖FF X Y ((u:ℂ)+t *I)‖^2:=by
   intro t ht
   have h:=akq t ht
   exact arz xd (by simp; linarith) (by simp; linarith) (by simpa using h.1)
    (by simp; rw[agv]; linarith[h.2])
  have atw:Integrable (fun t:ℝ=>‖FF X Y ((u:ℂ)+t *I)‖^2):=
   vr X (by linarith) (by linarith) (by linarith)
  have h1:∫ t in t1..t2,‖fz X ((u:ℂ)+t *I)‖^2<=
    ∫ t in t1..t2,15*‖FF X Y ((u:ℂ)+t *I)‖^2:=
   ff afm atv ((atw.const_mul 15).intervalIntegrable)
    (fun t ht=>wu t (by rw[gj afm]; exact ht))
  have h2:∫ t in t1..t2,15*‖FF X Y ((u:ℂ)+t *I)‖^2<=
    15*∫ t in i7 (-(T+4)) (T+4),‖FF X Y ((u:ℂ)+t *I)‖^2:=by
   rw[cv,ek afm]
   refine ab ?_ (by norm_num)
   exact setIntegral_mono_set atw.integrableOn
    (Eventually.of_forall (fun t=>c4 _))
    (mr.trans (Set.Icc_subset_Icc ht1 ht2)).eventuallyLE
  have a00:T^((29:ℝ)/10*(1-u))<=max 1 (T^((29:ℝ)/10*(1-u))):=
   cd _ _
  calc ∫ t in t1..t2,‖fz X ((u:ℂ)+t *I)‖^2
    <= 15*∫ t in i7 (-(T+4)) (T+4),‖FF X Y ((u:ℂ)+t *I)‖^2:=h1.trans h2
   _ ≤ 15*(tq (FF X Y) (1/2)^((b-u)/(b-1/2))*
        tq (FF X Y) b^((u-1/2)/(b-1/2))):=by gcongr
   _<=15*(af 3*M*L^4*T^((29:ℝ)/10*(1-u))):=by gcongr
   _ ≤ (15*af 3*M+300)*L^4*max 1 (T^((29:ℝ)/10*(1-u))):=by
       have tj:0<=af 3*M*L^4:=by positivity
       have:0<=(300:ℝ)*L^4*max 1 (T^((29:ℝ)/10*(1-u))):=by positivity
       nlinarith[ab a00 tj]
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma akr (tn R θ:ℝ):
  circleMap (3+tn*I) R θ=((3+R*fo θ:ℝ):ℂ)+((tn+R*en θ:ℝ):ℂ)*I:=by
 apply kn
 ·rw[akj]; simp[Complex.cos_ofReal_re]
 ·rw[ad7]; simp[Complex.sin_ofReal_re]
lemma aeq (x:ℝ):aa (1+x^2)<=x^2:=by
 have:=bz (show (0:ℝ)<1+x^2 by positivity)
 linarith
theorem aer:∃ C0:ℝ,0<C0∧∀ T:ℝ,af 8<=T->∀ ys a1 a2:ℝ,
  1/2<=ys->ys<=1->a1<=a2->((9<=a1∧a2<=T+1)∨(-(T+1)<=a1∧a2<=-9))->
  ∀ θ:ℝ,∫ tn in a1..a2,
   aa (1+‖fz ⌈T⌉₊ (circleMap (3+tn*I) (3-ys) θ)‖^2)<=
    C0*aa T^4*max 1 (T^((29:ℝ)/10*(1-ys))):=by
 obtain ⟨C0,x9,hC⟩:=akp
 refine ⟨C0,x9,fun T hT ys a1 a2 uu hs2 ha y8 θ=>?_⟩
 obtain ⟨hT1,hL8⟩:=vs hT
 set R:=3-ys with hR
 set u:=3+R*fo θ with hu
 set c:=R*en θ with hc
 have bei:=Real.neg_one_le_cos θ
 have bcu:=Real.cos_le_one θ
 have aro:=sv θ
 have bcv:=Real.sin_le_one θ
 have hR2:2<=R:=by rw[hR]; linarith
 have hR3:R<=5/2:=by rw[hR]; linarith
 have x8:ys<=u:=by rw[hu]; nlinarith
 have hu2:u<=6:=by rw[hu]; nlinarith
 have hcR:|c|<=R:=by
  rw[hc,n4,a7 (by linarith:(0:ℝ)<R)]
  exact mul_le_of_le_one_right (by linarith) (abs_le.mpr ⟨by linarith,by linarith⟩)
 have bcw:=abs_le.mp hcR
 set X:=⌈T⌉₊
 have heq:∀ tn:ℝ,circleMap (3+tn*I) R θ=(u:ℂ)+((tn+c:ℝ):ℂ)*I:=by
  intro tn; rw[akr]
 have te:∀ t:ℝ,6<=|t|->(u:ℂ)+(t:ℂ)*I≠1:=by
  intro t ht h
  have:=dy Complex.im h; simp at this
  rw[this] at ht; simp at ht; linarith
 have akq:∀ tn∈ko a1 a2,6<=|tn+c|:=by
  intro tn xe
  rw[gj ha] at xe
  rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩
  ·rw[a7 (by linarith[xe.1])]; linarith[xe.1]
  ·rw[g5 (by linarith[xe.2])]; linarith[xe.2]
 have wv:ContinuousOn (fun tn:ℝ=>‖fz X ((u:ℂ)+((tn+c:ℝ):ℂ)*I)‖^2)
   (ko a1 a2):=by
  have hcm:Continuous (fun tn:ℝ=>(u:ℂ)+((tn+c:ℝ):ℂ)*I):=by fun_prop
  have wd:q1 (fun tn:ℝ=>(u:ℂ)+((tn+c:ℝ):ℂ)*I) (ko a1 a2)
    ({1}ᶜ:Set ℂ):=fun tn xe=>te _ (akq tn xe)
  exact (((vq X (U:=({1}ᶜ:Set ℂ)) (by simp)).comp hcm.continuousOn wd).norm).pow 2
 have ax7:ContinuousOn (fun tn:ℝ=>aa (1+‖fz X ((u:ℂ)+((tn+c:ℝ):ℂ)*I)‖^2))
   (ko a1 a2):=
  p3 (ez.add wv) (fun _ _=>by positivity)
 simp_rw[heq]
 calc ∫ tn in a1..a2,aa (1+‖fz X ((u:ℂ)+((tn+c:ℝ):ℂ)*I)‖^2)
   <= ∫ tn in a1..a2,‖fz X ((u:ℂ)+((tn+c:ℝ):ℂ)*I)‖^2:=
       ff ha ax7.intervalIntegrable wv.intervalIntegrable
        (fun tn _=>aeq _)
  _ = ∫ t in (a1+c)..(a2+c),‖fz X ((u:ℂ)+(t:ℂ)*I)‖^2:=
      intervalIntegral.integral_comp_add_right (fun t:ℝ=>‖fz X ((u:ℂ)+(t:ℂ)*I)‖^2) c
  _ ≤ C0*aa T^4*max 1 (T^((29:ℝ)/10*(1-u))):=by
      apply hC T hT u (a1+c) (a2+c) (by linarith) hu2 (by linarith)
      ·rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩
       ·left; linarith
       ·right; linarith
      ·rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
      ·rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
  _ ≤ _:=by
      have ax8:1<=T:=by linarith
      have:T^((29:ℝ)/10*(1-u))<=T^((29:ℝ)/10*(1-ys)):=
       al ax8 (by linarith)
      have ar0:max 1 (T^((29:ℝ)/10*(1-u)))<=max 1 (T^((29:ℝ)/10*(1-ys))):=
       max_le_max le_rfl this
      have:0<=C0*aa T^4:=by positivity
      exact ab ar0 this
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma w9 {S S':Set ℂ} (hS':S'.Finite) (h:S ⊆ S'):
  ∑ᶠ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℝ)<=
   ∑ᶠ ρ∈S',(analyticOrderNatAt riemannZeta ρ:ℝ):=by
 have hS:S.Finite:=hS'.subset h
 rw[bf _ hS,bf _ hS']
 apply aq
 ·intro x hx; rw[an] at hx ⊢; exact h hx
 ·intro _ _ _; positivity
lemma vm (σ a1 a2:ℝ):
  {ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1<=ρ.im∧ρ.im<=a2}.Finite:=by
 apply ((isCompact_closedBall (0:ℂ) (|a1|+|a2|+2)).inter_riemannZetaZeros_finite).subset
 rintro ρ ⟨h0,-,tu,adr,ahn⟩
 refine ⟨?_,h0⟩
 rw[mem_closedBall,l9]
 have h1:ρ.re<1:=by
  by_contra h'; exact ct (not_lt.mp h') h0
 have:=b6 ρ
 rw[a7 tu] at this
 have h2:|ρ.im|<=|a1|+|a2|:=by
  rw[abs_le]
  constructor
  ·linarith[r2 a1,eg a2]
  ·linarith[k6 a2,eg a1]
 linarith
set_option maxHeartbeats 2000000 in
theorem aks:∃ C2:ℝ,0<C2∧∀ T:ℝ,af 8<=T->∀ σ:ℝ,
  1/2+2/aa T<=σ->σ<=1->∀ a1 a2:ℝ,a1+2<=a2->
  ((9<=a1∧a2<=T+1)∨(-(T+1)<=a1∧a2<=-9))->
  ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+1<=ρ.im∧ρ.im<=a2-1},
   (analyticOrderNatAt riemannZeta ρ:ℝ)<=
   C2*aa T^6*T^((29:ℝ)/10*(1-σ)):=by
 obtain ⟨C0,x9,hC⟩:=aer
 refine ⟨9/2*(C0*af 3+2),by positivity, ?_⟩
 intro T hT σ abi an7 a1 a2 ha y8
 obtain ⟨hT1,hL8⟩:=vs hT
 set L:=aa T with hL
 have ug:0<L:=by linarith
 set δ:=1/L with uf
 have ahu:0<δ:=by positivity
 have bej:δ<=1/8:=by rw[uf,ax ug (by norm_num)]; linarith
 have a43:2/L=2*δ:=by rw[uf]; ring
 rw[a43] at abi
 set ys:=σ-δ with abl
 set R:=3-ys with hR
 set η:=ak ((3-σ)*δ) with hη
 set r:=ak ((3-σ)^2+η^2) with hr
 have bcx:2<=3-σ:=by linarith
 have bcy:3-σ<=5/2:=by linarith
 have a44:η^2=(3-σ)*δ:=ly (by positivity)
 have bek:0<=η:=df _
 have ank:η<=1:=by
  rw[hη,show (1:ℝ)=ak 1 by simp]
  exact dg (by nlinarith)
 have a01:δ<=η:=by
  rw[hη]
  apply ku
  nlinarith
 have hr2:r^2=(3-σ)^2+η^2:=ly (by positivity)
 have hr0:0<r:=iu.mpr (by positivity)
 have aol:0<R:=by rw[hR,abl]; linarith
 have hR3:R<=3:=by rw[hR,abl]; linarith
 have bel:R^2-r^2=(3-σ)*δ+δ^2:=by
  rw[hr2,a44,hR,abl]; ring
 have ze:r<R:=by
  have:r^2<R^2:=by nlinarith
  exact (pow_lt_pow_iff_left₀ hr0.le aol.le (by norm_num)).mp this
 have ur:δ/9<=aa (R/r):=by
  have h1:=b5 (show 0<R/r by positivity)
  have h2:1-(R/r)⁻¹=(R-r)/R:=by field_simp
  rw[h2] at h1
  have h3:(R-r)*(R+r)=R^2-r^2:=by ring
  have h4:δ/R<=R-r:=by
   rw[ay aol]
   have:(R-r)*(R+r)<=(R-r)*(2*R):=by
    apply ab (by linarith) (by linarith)
   nlinarith
  have h5:δ/9<=(R-r)/R:=by
   rw[ax (by norm_num) aol]
   have:δ/R*R=δ:=by field_simp
   nlinarith
  linarith
 set X:ℕ:=⌈T⌉₊ with atu
 have hX1:(T:ℝ)<=X:=f9 T
 have hX2:2<=X:=by
  have:(2:ℝ)<=X:=by linarith
  exact_mod_cast this
 have a02:1/2<=ys:=by rw[abl]; linarith
 have a03:ys<=1:=by rw[abl]; linarith
 have hQ:=hC T hT ys a1 a2 a02 a03 (by linarith) y8
 have hci:=afl (X:=X) (σ:=σ) (η:=η) (r:=r) (R:=R) (a1:=a1) (a2:=a2)
  hX2 (fj ahu a01) hr0 ze (by linarith)
  (by
   intro tn xe
   rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩
   ·rw[a7 (by linarith[xe.1])]; linarith[xe.1]
   ·rw[g5 (by linarith[xe.2])]; linarith[xe.2])
  (by
   intro tn _ ρ h0 bcz tu um
   rw[mem_closedBall,b8]
   have w0:ρ.re<1:=by
    by_contra h'; exact ct (not_lt.mp h') h0
   have zr:‖ρ-(3+tn*I)‖^2=(ρ.re-3)^2+(ρ.im-tn)^2:=by
    rw[<- jo,jl]; simp; ring
   have h1:(ρ.re-3)^2<=(3-σ)^2:=by nlinarith
   have h2:(ρ.im-tn)^2<=η^2:=by
    rw[<- sq_abs]; exact aj (eg _) um 2
   have:‖ρ-(3+tn*I)‖^2<=r^2:=by rw[zr,hr2]; linarith
   exact (d8 (aw _) hr0.le (by norm_num)).mp this)
  (fun θ=>hQ θ)
 have uj:{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+1<=ρ.im∧ρ.im<=a2-1} ⊆
   {ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+η<=ρ.im∧ρ.im<=a2-η}:=by
  rintro ρ ⟨h0,h1,h2,h3,h4⟩
  exact ⟨h0,h1,h2,by linarith,by linarith⟩
 have u6:=w9 (vm σ (a1+η) (a2-η)) uj
 set N:=∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+1<=ρ.im∧ρ.im<=a2-1},
  (analyticOrderNatAt riemannZeta ρ:ℝ) with hN
 set N':=∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧a1+η<=ρ.im∧ρ.im<=a2-η},
  (analyticOrderNatAt riemannZeta ρ:ℝ) with hN'
 have hN0:0<=N:=by
  rw[hN]; exact lv (fun ρ=>lv (fun _=>by positivity))
 have av7:(a2-a1)*(2/(X:ℝ)^2)<=1:=by
  have h1:a2-a1<=2*T+2:=by rcases y8 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
  have h2:2/(X:ℝ)^2<=2/T^2:=by
   apply bb (by norm_num) (by positivity)
   exact aj (by linarith) hX1 2
  have h3:(2*T+2)*(2/T^2)<=1:=by
   rw[rp,dw (by positivity)]; nlinarith
  calc (a2-a1)*(2/(X:ℝ)^2)<=(2*T+2)*(2/T^2):=
        a8 h1 h2 (by positivity) (by linarith)
   _<=1:=h3
 have ua:0<T:=by linarith
 have hTe:T^((29:ℝ)/10*(1-ys))=af ((29:ℝ)/10)*T^((29:ℝ)/10*(1-σ)):=by
  have e:(29:ℝ)/10*(1-ys)=(29:ℝ)/10*(1-σ)+(29/10)*(1/L):=by
   rw[abl,uf]; ring
  have h2:T^((29:ℝ)/10*(1/L))=af ((29:ℝ)/10):=by
   have h:=y3 (T:=T) (by linarith)
   rw[<- hL] at h
   rw[gx,d7 ua.le,h,Real.exp_one_rpow]
  rw[e,c6 ua,h2]; ring
 have ax8:1<=T^((29:ℝ)/10*(1-σ)):=
  e5 (by linarith) (by linarith)
 have he3:af ((29:ℝ)/10)<=af 3:=b4.mpr (by norm_num)
 have hE1:1<=af ((29:ℝ)/10):=qe (by norm_num)
 set P:=T^((29:ℝ)/10*(1-σ)) with hP
 have ar0:max 1 (T^((29:ℝ)/10*(1-ys)))<=af 3*P:=by
  rw[hTe]
  apply max_le
  ·nlinarith
  ·exact ag he3 (by linarith)
 have hL4:1<=L^4:=dx (by linarith)
 have hQ':C0*L^4*max 1 (T^((29:ℝ)/10*(1-ys)))<=C0*L^4*(af 3*P):=
  ab ar0 (b7 x9.le (by positivity))
 have bem:N'*(2*η)*aa (R/r)<=C0*L^4*(af 3*P)+1:=by
  have:=hci; linarith
 have aah:N*(2*δ^2/9)<=N'*(2*η)*aa (R/r):=by
  have h1:2*δ^2/9<=2*η*aa (R/r):=by
   have:2*δ*(δ/9)<=2*η*aa (R/r):=
    a8 (by linarith) ur (by positivity) (by linarith)
   linarith[show 2*δ*(δ/9)=2*δ^2/9 by ring]
  have h2:N*(2*δ^2/9)<=N*(2*η*aa (R/r)):=
   ab h1 hN0
  have h3:N*(2*η*aa (R/r))<=N'*(2*η*aa (R/r)):=
   ag u6 (b7 (by positivity) (by linarith))
  linarith[show N'*(2*η)*aa (R/r)=N'*(2*η*aa (R/r)) by ring]
 have a45:δ^2*L^2=1:=by rw[uf]; field_simp
 have hP1:1<=L^4*P:=by nlinarith
 have uq:N*(2*δ^2/9)<=(C0*af 3+2)*(L^4*P):=by
  have:C0*L^4*(af 3*P)+1<=(C0*af 3+2)*(L^4*P):=by nlinarith
  linarith
 have hmul:=ab uq (show (0:ℝ)<=9/2*L^2 by positivity)
 have e1:9/2*L^2*(N*(2*δ^2/9))=N*(δ^2*L^2):=by ring
 rw[e1,a45,di] at hmul
 calc N<=9/2*L^2*((C0*af 3+2)*(L^4*P)):=hmul
  _=9/2*(C0*af 3+2)*L^6*P:=by ring
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma vi (σ T:ℝ):
  {ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T}.Finite:=by
 apply (vm σ (-T) T).subset
 rintro ρ ⟨h0,h1,h2,h3⟩
 exact ⟨h0,h1,h2,by linarith[r2 ρ.im],by linarith[k6 ρ.im]⟩
theorem als:∃ Ct:ℝ,0<Ct∧∀ T:ℝ,af 8<=T->
  ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧(0:ℝ)<=ρ.re∧0<ρ.re∧|ρ.im|<=T},
   (analyticOrderNatAt riemannZeta ρ:ℝ)<=Ct *T*aa T:=by
 set S5:={ρ:ℂ | riemannZeta ρ=0∧(0:ℝ)<=ρ.re∧0<ρ.re∧|ρ.im|<=5}
 set K5:=∑ᶠ ρ∈S5,(analyticOrderNatAt riemannZeta ρ:ℝ) with hK5
 have ben:0<=K5:=lv (fun ρ=>lv (fun _=>by positivity))
 refine ⟨K5+108,by positivity,fun T hT=>?_⟩
 obtain ⟨hT1,hL8⟩:=vs hT
 set L:=aa T with hL
 have ua:0<T:=by linarith
 set S:={ρ:ℂ | riemannZeta ρ=0∧(0:ℝ)<=ρ.re∧0<ρ.re∧|ρ.im|<=T} with hS
 have agw:S.Finite:=vi 0 T
 set F:=agw.toFinset
 rw[bf _ agw]
 rw[<- gm F (fun ρ=>|ρ.im|<5)]
 have aah:∑ ρ∈F.filter (fun ρ=>|ρ.im|<5),(analyticOrderNatAt riemannZeta ρ:ℝ)<=K5:=by
  have a04:S5.Finite:=vi 0 5
  rw[hK5,bf _ a04]
  apply aq
  ·intro ρ s8
   simp only[ah,F,an,hS,eh] at s8
   rw[an]
   exact ⟨s8.1.1,s8.1.2.1,s8.1.2.2.1,s8.2.le⟩
  ·intro _ _ _; positivity
 set N:=⌈T⌉₊ with an5
 have hN1:(N:ℝ)<T+1:=ef ua.le
 have hN2:T<=(N:ℝ):=f9 T
 have wd:∀ ρ∈F.filter (fun ρ=>¬ |ρ.im|<5),
   ⌊ρ.im⌋∈q6 (-(N:ℤ)-1) (N:ℤ):=by
  intro ρ s8
  simp only[ah,F,an,hS,eh] at s8
  have hb:=abs_le.mp s8.1.2.2.2
  rw[ar]
  constructor
  ·have h1:((-(N:ℤ)-1:ℤ):ℝ)<=ρ.im:=by push_cast; linarith
   have:=Int.floor_mono h1
   rw[Int.floor_intCast] at this
   omega
  ·have:(⌊ρ.im⌋:ℝ)<=N:=by linarith[pc ρ.im]
   exact_mod_cast this
 rw[<- cx wd]
 have yu:∀ k∈q6 (-(N:ℤ)-1) (N:ℤ),
   ∑ ρ∈(F.filter (fun ρ=>¬ |ρ.im|<5)).filter (fun ρ=>⌊ρ.im⌋=k),
    (analyticOrderNatAt riemannZeta ρ:ℝ)<=36*L:=by
  intro k hk
  by_cases te:((F.filter (fun ρ=>¬ |ρ.im|<5)).filter (fun ρ=>⌊ρ.im⌋=k)).Nonempty
  swap
  ·rw[Finset.not_nonempty_iff_eq_empty.mp te,k8]; positivity
  obtain ⟨ρ0,yw⟩:=te
  simp only[ah,F,an,hS,eh] at yw
  set t:ℝ:=(k:ℝ)+1/2 with ht
  have x1:=pc ρ0.im
  have hk2:=nt ρ0.im
  rw[yw.2] at x1 hk2
  have ht4:4<=|t|:=by
   have h5:=yw.1.2
   push Not at h5
   rcases ig 0 ρ0.im with tj | ae9
   ·rw[bh tj] at h5; rw[a7 (by linarith)]; linarith
   ·rw[g5 ae9] at h5; rw[g5 (by linarith)]; linarith
  have hT4:|t|<=T+2:=by
   rw[ar] at hk
   have h1:((-(N:ℤ)-1:ℤ):ℝ)<=k:=by exact_mod_cast hk.1
   have h2:(k:ℝ)<=N:=by exact_mod_cast hk.2
   push_cast at h1
   rw[abs_le]; constructor <;> linarith
  have hzc:=bt.qf.z7 ht4
  set B:={ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall ((3/2:ℂ)+t *I) (11/5)}
  have a05:B.Finite:=by
   apply ((isCompact_closedBall _ _).inter_riemannZetaZeros_finite).subset
   rintro ρ ⟨h0,s8⟩; exact ⟨s8,h0⟩
  rw[bf _ a05] at hzc
  refine br ?_ (hzc.trans ?_)
  ·apply aq
   ·intro ρ s8
    simp only[ah,F,an,hS,eh] at s8
    rw[an]
    refine ⟨s8.1.1.1, ?_⟩
    rw[mem_closedBall,b8]
    have w0:ρ.re<1:=by
     by_contra h'; exact ct (not_lt.mp h') s8.1.1.1
    have hf1:=pc ρ.im
    have hf2:=nt ρ.im
    rw[s8.2] at hf1 hf2
    have zr:‖ρ-((3/2:ℂ)+t *I)‖^2=(ρ.re-3/2)^2+(ρ.im-t)^2:=by
     rw[<- jo,jl]; simp; ring
    have h1:(ρ.re-3/2)^2<=9/4:=by nlinarith[s8.1.1.2.2.1]
    have h2:(ρ.im-t)^2<=1/4:=by rw[ht]; nlinarith
    have:‖ρ-((3/2:ℂ)+t *I)‖^2<=(11/5)^2:=by rw[zr]; nlinarith
    exact (d8 (aw _) (by norm_num) (by norm_num)).mp this
   ·intro _ _ _; positivity
  ·
   have h1:1800*t^2<=T^3:=by
    have:t^2<=(T+2)^2:=by
     rw[<- sq_abs]; exact aj (eg _) hT4 2
    nlinarith
   have h2:aa (1800*t^2)<=3*L:=by
    have e:aa (T^3)=3*L:=by rw[cq,hL]; push_cast; ring
    rw[<- e]
    have t8:0<t^2:=by
     have:(0:ℝ)< |t|:=by linarith
     rw[<- sq_abs]; positivity
    exact a5 (by positivity) h1
   linarith
 have aom:=ao yu
 rw[a9,ky,cp] at aom
 have hc:(((N:ℤ)+1-(-(N:ℤ)-1)).toNat:ℝ)=2*N+2:=by
  have:((N:ℤ)+1-(-(N:ℤ)-1))=((2*N+2:ℕ):ℤ):=by push_cast; ring
  rw[this,mh]; push_cast; ring
 rw[hc] at aom
 have hTL:1<=T*L:=by nlinarith
 have h3:(2*(N:ℝ)+2)*(36*L)<=108*(T*L):=by nlinarith
 have h4:K5<=K5*(T*L):=by nlinarith
 calc _<=K5+(2*(N:ℝ)+2)*(36*L):=e8 aah aom
  _<=K5*(T*L)+108*(T*L):=by linarith
  _=(K5+108)*T*L:=by ring
end bt.ZD
namespace bt.ZD
open Complex Finset Metric MeasureTheory Filter Topology
open scoped Real
lemma xu {F:Finset ℂ} {S':Set ℂ} (hS':S'.Finite) (h:∀ ρ∈F,ρ∈S'):
  ∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)<=
   ∑ᶠ ρ∈S',(analyticOrderNatAt riemannZeta ρ:ℝ):=by
 rw[bf _ hS']
 apply aq
 ·intro x hx; rw[an]; exact h x hx
 ·intro _ _ _; positivity
lemma aes {T σ:ℝ} (hT:af 8<=T) (hσ:σ<1/2+2/aa T):
  T<=af 6*T^((29:ℝ)/10*(1-σ)):=by
 obtain ⟨hT1,hL8⟩:=vs hT
 have ua:0<T:=by linarith
 set L:=aa T with hL
 have ug:0<L:=by linarith
 have h1:(1:ℝ)-6/L<=(29:ℝ)/10*(1-σ):=by
  have:(29:ℝ)/10*(1-σ)>=(29:ℝ)/10*(1/2-2/L):=by nlinarith
  have h6:6/L<=6/8:=by rw[ax ug (by norm_num)]; linarith
  have e:(29:ℝ)/10*(1/2-2/L)=29/20-(29/5)*(1/L):=by ring
  have e2:(6:ℝ)/L=6*(1/L):=by ring
  have h1L:1/L<=1/8:=by rw[ax ug (by norm_num)]; linarith
  nlinarith[show (0:ℝ)<1/L by positivity]
 have h2:T^((1:ℝ)-6/L)=T*af (-6):=by
  have hTL:=y3 (T:=T) (by linarith)
  rw[<- hL] at hTL
  rw[rg ua,fi,show (6:ℝ)/L=6*(1/L) by ring,gx (6:ℝ),
   d7 ua.le,hTL,Real.exp_one_rpow,jx,kv]
 have h3:T^((1:ℝ)-6/L)<=T^((29:ℝ)/10*(1-σ)):=
  al (by linarith) h1
 rw[h2] at h3
 have he:af 6*af (-6)=1:=by rw[<- bs]; simp
 calc T=af 6*(T*af (-6)):=by rw[gx T,<- gv,he,iq]
  _<=_:=by gcongr
theorem ar1:∃ A:ℝ,A<3∧∃ B C:ℝ,∀ σ T:ℝ,2<=T->
  (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T},
   (analyticOrderNatAt riemannZeta ρ:ℝ))<=C*T^(A*(1-σ))*aa T^B:=by
 obtain ⟨C2,hC2,aya⟩:=aks
 obtain ⟨Ct,hCt,a46⟩:=als
 set S8:={ρ:ℂ | riemannZeta ρ=0∧(0:ℝ)<=ρ.re∧0<ρ.re∧|ρ.im|<=af 8}
 have hS8:S8.Finite:=vi 0 (af 8)
 set K8:=∑ᶠ ρ∈S8,(analyticOrderNatAt riemannZeta ρ:ℝ) with hK8
 have beo:0<=K8:=lv (fun ρ=>lv (fun _=>by positivity))
 refine ⟨29/10,by norm_num,6,10*K8+af 6*Ct+2*C2,fun σ T hT=>?_⟩
 set C:=10*K8+af 6*Ct+2*C2 with hC
 have x9:0<=C:=by positivity
 set S:={ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T} with hS
 have agw:S.Finite:=vi σ T
 have ua:0<T:=by linarith
 have aax:0<=aa T:=bd (by linarith)
 have hB:aa T^(6:ℝ)=aa T^(6:ℕ):=by
  rw[show (6:ℝ)=((6:ℕ):ℝ) by norm_num,da]
 rw[hB]
 by_cases abi:1<=σ
 ·
  have ayb:S=∅:=by
   ext ρ
   simp only[hS,eh,Set.mem_empty_iff_false,iff_false]
   rintro ⟨h0,h1,-,-⟩
   exact ct (by linarith) h0
  rw[ayb,finsum_mem_empty]
  positivity
 push Not at abi
 have hP1:1<=T^((29:ℝ)/10*(1-σ)):=e5 (by linarith) (by linarith)
 rcases si T (af 8) with hTs | hTb
 ·
  have h1:∑ᶠ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℝ)<=K8:=by
   rw[hK8]
   apply w9 hS8
   rintro ρ ⟨h0,h1,h2,h3⟩
   exact ⟨h0,h2.le,h2,by linarith⟩
  have hl2:(1:ℝ)/10<=aa T^6:=by
   have:=f6
   have h2:aa 2<=aa T:=a5 (by norm_num) hT
   have:(0.69:ℝ)^6<=aa T^6:=aj (by norm_num) (by linarith) 6
   have h3:(1:ℝ)/10<=(0.69:ℝ)^6:=by norm_num
   linarith
  have hCK:10*K8<=C:=by rw[hC]; have:=bx 6; nlinarith
  calc _<=K8:=h1
   _=10*K8*(1/10):=by ring
   _ ≤ C*(T^((29:ℝ)/10*(1-σ))*aa T^6):=by
       apply a8 hCK _ (by norm_num) x9
       nlinarith
   _=_:=by ring
 obtain ⟨hT1,hL8⟩:=vs hTb
 set L:=aa T with hL
 have hL6:1<=L^6:=dx (by linarith)
 have hX:1<=L^6*T^((29:ℝ)/10*(1-σ)):=by nlinarith
 rcases si σ (1/2+2/L) with a47 | ayd
 ·
  have h1:∑ᶠ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℝ)<=
    ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧(0:ℝ)<=ρ.re∧0<ρ.re∧|ρ.im|<=T},
     (analyticOrderNatAt riemannZeta ρ:ℝ):=by
   apply w9 (vi 0 T)
   rintro ρ ⟨h0,h1,h2,h3⟩
   exact ⟨h0,h2.le,h2,h3⟩
  have h2:=a46 T hTb
  have h3:=aes hTb a47
  have hLL:L<=L^6:=by
   have:1<=L^5:=dx (by linarith)
   nlinarith
  have h4:Ct *T*L<=(af 6*Ct)*(T^((29:ℝ)/10*(1-σ))*L^6):=by
   have h5:Ct *T<=Ct *(af 6*T^((29:ℝ)/10*(1-σ))):=
    ab h3 hCt.le
   have h6:Ct *T*L<=Ct *(af 6*T^((29:ℝ)/10*(1-σ)))*L^6:=
    a8 h5 hLL (by linarith) (by positivity)
   linarith[show Ct *(af 6*T^((29:ℝ)/10*(1-σ)))*L^6=
    (af 6*Ct)*(T^((29:ℝ)/10*(1-σ))*L^6) by ring]
  have hCe:af 6*Ct<=C:=by rw[hC]; linarith
  calc _<=Ct *T*L:=h1.trans h2
   _<=(af 6*Ct)*(T^((29:ℝ)/10*(1-σ))*L^6):=h4
   _ ≤ C*(T^((29:ℝ)/10*(1-σ))*L^6):=
       ag hCe (by positivity)
   _=_:=by ring
 ·
  set F:=agw.toFinset
  rw[bf _ agw]
  rw[<- gm F (fun ρ=>|ρ.im|<10)]
  rw[<- gm (F.filter (fun ρ=>¬ |ρ.im|<10))
   (fun ρ=>0<ρ.im)]
  have u3:∀ ρ∈F,riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T:=by
   intro ρ s8; rw[an] at s8; exact s8
  have aah:∑ ρ∈F.filter (fun ρ=>|ρ.im|<10),(analyticOrderNatAt riemannZeta ρ:ℝ)<=K8:=by
   rw[hK8]
   apply xu hS8
   intro ρ s8
   rw[ah] at s8
   obtain ⟨h0,h1,h2,h3⟩:=u3 ρ s8.1
   have:(10:ℝ)<=af 8:=by
    have:=(vs (le_refl (af 8))).1; linarith
   exact ⟨h0,h2.le,h2,by linarith[s8.2]⟩
  have tj:=aya T hTb σ ayd abi.le 9 (T+1) (by linarith) (Or.inl ⟨le_rfl,le_rfl⟩)
  have ae9:=aya T hTb σ ayd abi.le (-(T+1)) (-9) (by linarith) (Or.inr ⟨le_rfl,le_rfl⟩)
  have hp:∑ ρ∈(F.filter (fun ρ=>¬ |ρ.im|<10)).filter (fun ρ=>0<ρ.im),
    (analyticOrderNatAt riemannZeta ρ:ℝ)<=C2*L^6*T^((29:ℝ)/10*(1-σ)):=by
   refine br (xu (vm σ (9+1) (T+1-1)) ?_) tj
   intro ρ s8
   simp only[ah] at s8
   obtain ⟨h0,h1,h2,h3⟩:=u3 ρ s8.1.1
   have h10:=s8.1.2
   push Not at h10
   rw[a7 s8.2] at h10 h3
   exact ⟨h0,h1,h2,by linarith,by linarith⟩
  have hn:∑ ρ∈(F.filter (fun ρ=>¬ |ρ.im|<10)).filter (fun ρ=>¬ 0<ρ.im),
    (analyticOrderNatAt riemannZeta ρ:ℝ)<=C2*L^6*T^((29:ℝ)/10*(1-σ)):=by
   refine br (xu (vm σ (-(T+1)+1) (-9-1)) ?_) ae9
   intro ρ s8
   simp only[ah] at s8
   obtain ⟨h0,h1,h2,h3⟩:=u3 ρ s8.1.1
   have h10:=s8.1.2
   push Not at h10
   have a06:ρ.im<=0:=by have:=s8.2; push Not at this; exact this
   rw[abs_of_nonpos a06] at h10 h3
   exact ⟨h0,h1,h2,by linarith,by linarith⟩
  have hCK:K8+2*C2<=C:=by
   rw[hC]; have:=bx 6; nlinarith
  calc _<=K8+(C2*L^6*T^((29:ℝ)/10*(1-σ))+
        C2*L^6*T^((29:ℝ)/10*(1-σ))):=e8 aah (e8 hp hn)
   _<=(K8+2*C2)*(L^6*T^((29:ℝ)/10*(1-σ))):=by nlinarith
   _ ≤ C*(L^6*T^((29:ℝ)/10*(1-σ))):=
       ag hCK (by positivity)
   _=_:=by ring
end bt.ZD
namespace bt.ZD
def alu:Prop:=∃ A:ℝ,A<3∧∃ B C:ℝ,∀ σ T:ℝ,2<=T->
    (∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧σ<=ρ.re∧0<ρ.re∧|ρ.im|<=T},
     (analyticOrderNatAt riemannZeta ρ:ℝ))<=C*T^(A*(1-σ))*aa T^B
theorem aql:alu:=ar1
end bt.ZD
end
section
namespace bt.cz.tx
open Complex Set Filter Topology intervalIntegral MeasureTheory
open scoped Interval Real
noncomputable def va (f:ℂ->ℂ) (a b c d:ℝ):ℂ:=
 (∫ σ:ℝ in a..b,f (σ+c*I))-(∫ σ:ℝ in a..b,f (σ+d*I))
  + I*(∫ t:ℝ in c..d,f (b+t *I))-I*(∫ t:ℝ in c..d,f (a+t *I))
lemma yl {f:ℂ->ℂ} {a b c d:ℝ}
  (hf:DifferentiableOn ℂ f ([[a,b]] ×ℂ [[c,d]])):va f a b c d=0:=by
 have:=integral_boundary_rect_eq_zero_of_differentiableOn f (a+c*I) (b+d*I)
  (by simpa using hf)
 simpa [va,fx] using this
lemma agx (z w:ℂ) (t:ℝ):HasDerivAt (fun t:ℝ=>z+t *w) w t:=by
 have:=((po t).ofReal_comp.mul_const w).const_add z
 simpa using this
lemma vy {z w:ℂ} {u v:ℝ} (hs:∀ t∈[[u,v]],z+t *w∈slitPlane):
  ∫ t in u..v,w/(z+t *w)=log (z+v*w)-log (z+u*w):=by
 have te:∀ t∈[[u,v]],z+t *w≠0:=fun t ht=>slitPlane_ne_zero (hs t ht)
 apply integral_eq_sub_of_hasDerivAt
 ·intro t ht
  have h1:=(Complex.hasDerivAt_log (hs t ht)).comp t (agx z w t)
  have h2:w/(z+t *w)=(z+t *w)⁻¹*w:=by rw[div_eq_inv_mul]
  rw[h2]; exact h1
 ·apply el
  exact ez.div (by fun_prop) te
lemma z8 {z:ℂ} (h:0<z.im):log z-log (-z)=π*I:=by
 apply kn <;> simp[Complex.log_re,Complex.log_im,arg_neg_eq_arg_sub_pi_of_im_pos h]
lemma z9 {z:ℂ} (h:z.im<0):log z-log (-z)=-(π*I):=by
 apply kn <;> simp[Complex.log_re,Complex.log_im,arg_neg_eq_arg_add_pi_of_im_neg h]
lemma agy {a b c d:ℝ} {p:ℂ} (ha:a<p.re) (hb:p.re<b) (hc:c<p.im)
  (hd:p.im<d):va (fun s=>1/(s-p)) a b c d=2*π*I:=by
 set Z1:ℂ:=a+c*I-p
 set Z2:ℂ:=b+c*I-p
 set Z3:ℂ:=b+d*I-p
 set Z4:ℂ:=a+d*I-p
 have hB:∫ σ:ℝ in a..b,1/((σ:ℂ)+c*I-p)=log Z2-log Z1:=by
  have:=vy (z:=c*I-p) (w:=1) (u:=a) (v:=b) (fun t _=>by
   rw[mem_slitPlane_iff]; right; simp; intro h; linarith)
  have e:(fun σ:ℝ=>1/((σ:ℂ)+c*I-p))=fun σ:ℝ=>1/(c*I-p+σ*1):=by
   funext σ; congr 1; ring
  rw[e,this]
  congr 2 <;> ring
 have hT:∫ σ:ℝ in a..b,1/((σ:ℂ)+d*I-p)=log Z3-log Z4:=by
  have:=vy (z:=d*I-p) (w:=1) (u:=a) (v:=b) (fun t _=>by
   rw[mem_slitPlane_iff]; right; simp; intro h; linarith)
  have e:(fun σ:ℝ=>1/((σ:ℂ)+d*I-p))=fun σ:ℝ=>1/(d*I-p+σ*1):=by
   funext σ; congr 1; ring
  rw[e,this]
  congr 2 <;> ring
 have hR:∫ t:ℝ in c..d,1/((b:ℂ)+t *I-p)=-I*(log Z3-log Z2):=by
  have:=vy (z:=b-p) (w:=I) (u:=c) (v:=d) (fun t _=>by
   rw[mem_slitPlane_iff]; left; simp; linarith)
  have e:(fun t:ℝ=>1/((b:ℂ)+t *I-p))=fun t:ℝ=>-I*(I/(b-p+t *I)):=by
   funext t; rw[<- jm,neg_mul,I_mul_I,neg_neg]; congr 1; ring
  rw[e,cv,this]
  congr 3 <;> simp only[Z1,Z2,Z3,Z4] <;> ring
 have hL:∫ t:ℝ in c..d,1/((a:ℂ)+t *I-p)=-I*(log (-Z4)-log (-Z1)):=by
  have:=vy (z:=p-a) (w:=-I) (u:=c) (v:=d) (fun t _=>by
   rw[mem_slitPlane_iff]; left; simp; linarith)
  have e:(fun t:ℝ=>1/((a:ℂ)+t *I-p))=
    fun t:ℝ=>-I*(-I/(p-a+t *-I)):=by
   funext t
   rw[<- jm,neg_mul_neg,I_mul_I,p9,<- ss]
   congr 1; ring
  rw[e,cv,this]
  congr 3 <;> simp only[Z1,Z2,Z3,Z4] <;> ring
 have h4:log Z4-log (-Z4)=π*I:=z8 (by simp[Z4]; linarith)
 have h1:log Z1-log (-Z1)=-(π*I):=z9 (by simp[Z1]; linarith)
 simp only[va]
 rw[hB,hT,hR,hL]
 linear_combination h4-h1+(log (-Z4)-log (-Z1)-(log Z3-log Z2))*I_mul_I
lemma aa7 {f g:ℂ->ℂ} {R:Set ℂ} (P:Finset ℂ) (r:ℂ->ℂ) {γ:ℝ->ℂ}
  (xe:Continuous γ) {u v:ℝ} (ahf:∀ t∈[[u,v]],γ t∈R)
  (hnot:∀ t∈[[u,v]],∀ p∈P,γ t≠p) (hg:ContinuousOn g R)
  (hfg:∀ s∈R,s∉P->f s=g s+∑ p∈P,r p/(s-p)):
  ∫ t in u..v,f (γ t)=(∫ t in u..v,g (γ t))+∑ p∈P,r p*∫ t in u..v,1/(γ t-p):=by
 have h1:∫ t in u..v,f (γ t)=∫ t in u..v,(g (γ t)+∑ p∈P,r p/(γ t-p)):=
  integral_congr (fun t ht=>hfg _ (ahf t ht) (fun hm=>hnot t ht _ hm rfl))
 have hint:∀ p∈P,IntervalIntegrable (fun t=>r p/(γ t-p)) volume u v:=by
  intro p hp
  apply el
  exact ez.div (xe.continuousOn.sub ez)
   (fun t ht=>cb.mpr (hnot t ht p hp))
 rw[h1,pl,intervalIntegral.integral_finsetSum hint]
 ·congr 1
  apply ai rfl
  intro p _
  rw[<- cv]
  congr 1; funext t; rw[m8]
 ·exact (hg.comp xe.continuousOn ahf).intervalIntegrable
 ·apply el
  apply continuousOn_finsetSum
  intro p hp
  exact ez.div (xe.continuousOn.sub ez)
   (fun t ht=>cb.mpr (hnot t ht p hp))
lemma w7 {f g:ℂ->ℂ} {a b c d:ℝ} (P:Finset ℂ) (r:ℂ->ℂ)
  (hP:∀ p∈P,a<p.re∧p.re<b∧c<p.im∧p.im<d)
  (hg:ContinuousOn g ([[a,b]] ×ℂ [[c,d]]))
  (hfg:∀ s∈[[a,b]] ×ℂ [[c,d]],s∉P->f s=g s+∑ p∈P,r p/(s-p)):
  va f a b c d=va g a b c d+2*π*I*∑ p∈P,r p:=by
 have aqm:∀ τ:ℝ,Continuous fun σ:ℝ=>(σ:ℂ)+τ*I:=fun τ=>by fun_prop
 have aqn:∀ τ:ℝ,Continuous fun t:ℝ=>(τ:ℂ)+t *I:=fun τ=>by fun_prop
 have hB:=aa7 P r (aqm c) (u:=a) (v:=b)
  (fun t ht=>by simp[mem_reProdIm,ht]) (fun t _ p hp h=>by
   have:=dy im h; simp at this; linarith[(hP p hp).2.2.1]) hg hfg
 have hT:=aa7 P r (aqm d) (u:=a) (v:=b)
  (fun t ht=>by simp[mem_reProdIm,ht]) (fun t _ p hp h=>by
   have:=dy im h; simp at this; linarith[(hP p hp).2.2.2]) hg hfg
 have hR:=aa7 P r (aqn b) (u:=c) (v:=d)
  (fun t ht=>by simp[mem_reProdIm,ht]) (fun t _ p hp h=>by
   have:=dy re h; simp at this; linarith[(hP p hp).2.1]) hg hfg
 have hL:=aa7 P r (aqn a) (u:=c) (v:=d)
  (fun t ht=>by simp[mem_reProdIm,ht]) (fun t _ p hp h=>by
   have:=dy re h; simp at this; linarith[(hP p hp).1]) hg hfg
 have key:∀ p∈P,(∫ σ:ℝ in a..b,1/((σ:ℂ)+c*I-p))
   - (∫ σ:ℝ in a..b,1/((σ:ℂ)+d*I-p))
   + I*(∫ t:ℝ in c..d,1/((b:ℂ)+t *I-p))
   - I*(∫ t:ℝ in c..d,1/((a:ℂ)+t *I-p))=2*π*I:=by
  intro p hp
  obtain ⟨h1,h2,h3,h4⟩:=hP p hp
  have:=agy h1 h2 h3 h4
  simpa [va] using this
 simp only[va]
 rw[hB,hT,hR,hL]
 have hsum:(∑ p∈P,r p*∫ σ:ℝ in a..b,1/((σ:ℂ)+c*I-p))
   - (∑ p∈P,r p*∫ σ:ℝ in a..b,1/((σ:ℂ)+d*I-p))
   + I*(∑ p∈P,r p*∫ t:ℝ in c..d,1/((b:ℂ)+t *I-p))
   - I*(∑ p∈P,r p*∫ t:ℝ in c..d,1/((a:ℂ)+t *I-p))
   = 2*π*I*∑ p∈P,r p:=by
  rw[bc,bc,<- dn,<- cu,
   <- dn,bc]
  apply ai rfl
  intro p hp
  linear_combination r p*key p hp
 linear_combination hsum
noncomputable def t5 (y c T:ℝ):ℂ:=
 ∫ t:ℝ in (-T)..T,(y:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)
lemma zg {y:ℝ} (hy:0<y) (yt:y≠1) (u v:ℝ):
  ∫ σ in u..v,y^σ=(y^v-y^u)/aa y:=by
 have hL:aa y≠0:=by
  intro h
  rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact yt h; linarith]
 rw[integral_eq_sub_of_hasDerivAt (f:=fun σ=>y^σ/aa y)]
 ·ring
 ·intro σ _
  have:=((Real.hasStrictDerivAt_const_rpow hy σ).hasDerivAt).div_const (aa y)
  rwa[jm,div_self hL,di] at this
 ·exact (dm.rpow ps fun _=>Or.inl hy.ne').intervalIntegrable _ _
lemma uo {y:ℝ} (hy:0<y) (s:ℂ) (B:ℝ) (hB:0<B) (hs:B<=‖s‖):
  ‖(y:ℂ)^s/s‖<=y^s.re/B:=by
 rw[i4,e9 hy]
 exact bb (by positivity) hB hs
lemma vt {y:ℝ} (hy:0<y) (yt:y≠1) {u v τ:ℝ} (huv:u<=v)
  (u0:τ≠0):
  ‖∫ σ:ℝ in u..v,(y:ℂ)^((σ:ℂ)+τ*I)/((σ:ℂ)+τ*I)‖<=
   (y^v-y^u)/(|τ| *aa y):=by
 have ar2:0< |τ|:=ue.mpr u0
 calc _<=∫ σ in u..v,y^σ/|τ|:=by
       apply fc huv
       ·refine Eventually.of_forall (fun σ _=>?_)
        have:=uo hy ((σ:ℂ)+τ*I) |τ| ar2 (by
         have:=a6 ((σ:ℂ)+τ*I); simpa using this)
        simpa using this
       ·exact ((dm.rpow ps fun _=>Or.inl hy.ne').div_const
         _).intervalIntegrable _ _
  _ = (y^v-y^u)/(|τ| *aa y):=by
      rw[pk,zg hy yt]
      field_simp
theorem ab5 {y c T:ℝ} (hy:0<y) (yt:y<1) (hc:0<c) (hT:0<T):
  ‖t5 y c T‖<=2*y^c/(T*(-aa y)):=by
 have hL:aa y<0:=Real.log_neg hy yt
 set f:ℂ->ℂ:=fun s=>(y:ℂ)^s/s
 have hbound:∀ U,c<U->‖t5 y c T‖<=2*y^c/(T*(-aa y))+2*T/U:=by
  intro U hU
  have hU0:0<U:=hc.trans hU
  have acp:va f c U (-T) T=0:=by
   apply yl
   intro s hs
   rw[mem_reProdIm] at hs
   have tu:c<=s.re:=by
    have:=hs.1; rw[uIcc_of_le hU.le] at this; exact this.1
   have xc:s≠0:=fun h=>by rw[h] at tu; simp at tu; linarith
   apply c3
   apply ld _ bu xc
   exact (bu).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  simp only[va,f] at acp
  have hP:I*t5 y c T=(∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+(-T:ℝ)*I)/
    ((σ:ℂ)+(-T:ℝ)*I))-(∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+T*I)/
    ((σ:ℂ)+T*I))+I*∫ t:ℝ in (-T)..T,(y:ℂ)^((U:ℂ)+t *I)/
    ((U:ℂ)+t *I):=by
   unfold t5; linear_combination -acp
  have hB:=vt hy yt.ne hU.le (τ:=-T) (by linarith)
  have z1:=vt hy yt.ne hU.le (τ:=T) (by linarith)
  have hR:‖∫ t:ℝ in (-T)..T,(y:ℂ)^((U:ℂ)+t *I)/((U:ℂ)+t *I)‖<=
    1/U*|T-(-T)|:=by
   apply gs
   intro t _
   have:=uo hy ((U:ℂ)+t *I) U hU0 (by
    have:=cm ((U:ℂ)+t *I); simp at this
    rw[a7 hU0] at this; exact this)
   refine this.trans ?_
   simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
    ij]
   gcongr
   exact Real.rpow_le_one hy.le yt.le hU0.le
  have xj:|T-(-T)|=2*T:=by rw[a7 (by linarith)]; ring
  rw[xj] at hR
  have acs:‖t5 y c T‖=‖I*t5 y c T‖:=by simp
  rw[acs,hP]
  have h1:=ej ((∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+(-T:ℝ)*I)/
    ((σ:ℂ)+(-T:ℝ)*I))) (∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+T*I)/
    ((σ:ℂ)+T*I))
  have h2:=ds ((∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+(-T:ℝ)*I)/
    ((σ:ℂ)+(-T:ℝ)*I))-(∫ σ:ℝ in c..U,(y:ℂ)^((σ:ℂ)+T*I)/
    ((σ:ℂ)+T*I))) (I*∫ t:ℝ in (-T)..T,(y:ℂ)^((U:ℂ)+t *I)/
    ((U:ℂ)+t *I))
  rw[bo,kr,iq] at h2
  have aon:|(-T)|=T:=by rw[j1,a7 hT]
  have akt:|T|=T:=a7 hT
  rw[aon] at hB; rw[akt] at z1
  have hyU:0<=y^U:=by positivity
  have e1:(y^U-y^c)/(T*aa y)<=y^c/(T*(-aa y)):=by
   have hd:0<T*(-aa y):=by nlinarith
   rw[show (y^U-y^c)/(T*aa y)=(y^c-y^U)/(T*(-aa y)) by
    rw[<- neg_div_neg_eq]; ring_nf]
   exact a4 (by linarith) hd.le
  have e2:2*y^c/(T*(-aa y))=y^c/(T*(-aa y))+
    y^c/(T*(-aa y)):=by ring
  have e3:1/U*(2*T)=2*T/U:=by ring
  linarith
 apply ge_of_tendsto (f:=fun U=>2*y^c/(T*(-aa y))+2*T/U) (x:=atTop)
 ·have:=(g6 (x:=2*y^c/(T*(-aa y)))).add
   ((g6 (x:=2*T)).div_atTop tendsto_id)
  simpa using this
 ·filter_upwards[eventually_gt_atTop c] with U hU using hbound U hU
theorem ab6 {y c T:ℝ} (yt:1<y) (hc:0<c) (hT:0<T):
  ‖t5 y c T-2*π‖<=2*y^c/(T*aa y):=by
 have hy:0<y:=by linarith
 have hL:0<aa y:=eo yt
 have hy0:(y:ℂ)≠0:=by exact_mod_cast hy.ne'
 set f:ℂ->ℂ:=fun s=>(y:ℂ)^s/s
 set g:ℂ->ℂ:=dslope (fun s=>(y:ℂ)^s) 0
 have hgd:Differentiable ℂ g:=by
  have:DifferentiableOn ℂ g univ:=(differentiableOn_dslope nj).mpr
   (fun z _=>((bu).const_cpow (Or.inl hy0)).differentiableWithinAt)
  exact fun z=>(this z (mem_univ z)).differentiableAt nj
 have hbound:∀ U,0<U->
   ‖t5 y c T-2*π‖<=2*y^c/(T*aa y)+2*T/U:=by
  intro U hU0
  have ah5:=w7 (f:=f) (g:=g) (a:=-U) (b:=c) (c:=-T) (d:=T)
   {0} (fun _=>1)
   (by
    intro p hp; rw[nx] at hp; subst hp
    simp only[zero_re,zero_im]; exact ⟨by linarith,hc,by linarith,hT⟩)
   hgd.continuous.continuousOn
   (by
    intro s _ hs
    rw[nx] at hs
    simp only[f,g,nw]
    rw[ti _ hs,q8,cpow_zero]
    simp only[kg]
    rw[<- add_div,sub_add_cancel])
  have hg0:va g (-U) c (-T) T=0:=yl hgd.differentiableOn
  rw[hg0,jy,nw] at ah5
  simp only[va,f] at ah5
  set B:=∫ σ:ℝ in (-U)..c,(y:ℂ)^((σ:ℂ)+((-T:ℝ):ℂ)*I)/
      ((σ:ℂ)+((-T:ℝ):ℂ)*I)
  set Tp:=∫ σ:ℝ in (-U)..c,(y:ℂ)^((σ:ℂ)+(T:ℂ)*I)/((σ:ℂ)+(T:ℂ)*I)
  set Lf:=∫ t:ℝ in (-T)..T,(y:ℂ)^(((-U:ℝ):ℂ)+t *I)/(((-U:ℝ):ℂ)+t *I)
  have hP:I*(t5 y c T-2*π)=Tp-B+I*Lf:=by
   unfold t5; linear_combination ah5
  have hB:=vt hy yt.ne' (u:=-U) (v:=c) (by linarith) (τ:=-T)
   (by linarith)
  have z1:=vt hy yt.ne' (u:=-U) (v:=c) (by linarith) (τ:=T)
   (by linarith)
  have hLf:‖Lf‖<=1/U*|T-(-T)|:=by
   apply gs
   intro t _
   have:=uo hy (((-U:ℝ):ℂ)+t *I) U hU0 (by
    have:=cm (((-U:ℝ):ℂ)+t *I); simp at this
    rw[a7 hU0] at this; simpa using this)
   refine this.trans ?_
   simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
    ij]
   gcongr
   exact er yt.le (by linarith)
  have xj:|T-(-T)|=2*T:=by rw[a7 (by linarith)]; ring
  rw[xj] at hLf
  have aon:|(-T)|=T:=by rw[j1,a7 hT]
  have akt:|T|=T:=a7 hT
  rw[aon] at hB; rw[akt] at z1
  have acs:‖t5 y c T-2*π‖=‖I*(t5 y c T-2*π)‖:=by simp
  rw[acs,hP]
  have h1:=ej Tp B
  have h2:=ds (Tp-B) (I*Lf)
  rw[bo,kr,iq] at h2
  have hyU:0<y^(-U):=by positivity
  have e1:(y^c-y^(-U))/(T*aa y)<=y^c/(T*aa y):=
   a4 (by linarith) (by positivity)
  have e2:2*y^c/(T*aa y)=y^c/(T*aa y)+
    y^c/(T*aa y):=by ring
  have e3:1/U*(2*T)=2*T/U:=by ring
  linarith
 apply ge_of_tendsto (f:=fun U=>2*y^c/(T*aa y)+2*T/U) (x:=atTop)
 ·have:=(g6 (x:=2*y^c/(T*aa y))).add
   ((g6 (x:=2*T)).div_atTop tendsto_id)
  simpa using this
 ·filter_upwards[eventually_gt_atTop 0] with U hU using hbound U hU
lemma v9 {y c:ℝ} (hy:0<y) (hc:0<c):
  Continuous fun t:ℝ=>(y:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I):=by
 have hy0:(y:ℂ)≠0:=by exact_mod_cast hy.ne'
 apply Continuous.div
 ·exact Continuous.const_cpow (by fun_prop) (Or.inl hy0)
 ·fun_prop
 ·intro t h
  have:=dy re h
  simp at this; linarith
lemma w1 {y c:ℝ} (hy:0<y) (hc:0<c) (t:ℝ):
  ‖(y:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)‖<=2*y^c/(c+|t|):=by
 have h1:=cm ((c:ℂ)+t *I)
 have h2:=a6 ((c:ℂ)+t *I)
 simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
  ij,add_im,mul_im,jy] at h1 h2
 rw[a7 hc] at h1
 have:=uo hy ((c:ℂ)+t *I) ((c+|t|)/2) (by positivity) (by linarith)
 simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
  ij] at this
 calc _<=y^c/((c+|t|)/2):=this
  _=2*y^c/(c+|t|):=by rw[ml]; ring
lemma ym {c T K:ℝ} (hc:0<c) (hT:0<=T):
  ∫ t in (0:ℝ)..T,K/(c+t)=K*(aa (c+T)-aa c):=by
 rw[integral_eq_sub_of_hasDerivAt (f:=fun t=>K*aa (c+t))]
 ·simp only[ij]; ring
 ·intro t ht
  rw[uIcc_of_le hT] at ht
  have h:=(((hasDerivAt_id' t).const_add c).log (by linarith[ht.1])).const_mul K
  exact h.congr_deriv (by ring)
 ·apply el
  apply ez.div (by fun_prop)
  intro t ht
  rw[uIcc_of_le hT] at ht
  linarith[ht.1]
theorem aoo {y c T:ℝ} (hy:0<y) (hc:0<c) (hT:0<=T):
  ‖t5 y c T‖<=4*y^c*(aa (c+T)-aa c):=by
 set F:ℝ->ℂ:=fun t=>(y:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)
 have hF:Continuous F:=v9 hy hc
 have u8:t5 y c T=(∫ t in (0:ℝ)..T,F (-t))+∫ t in (0:ℝ)..T,F t:=by
  have h1:= oc (a:=0) (b:=T) F
  simp only[sg] at h1
  rw[h1]
  unfold t5
  rw[gz (hF.intervalIntegrable _ _)
   (hF.intervalIntegrable _ _)]
 have hbd:∀ G:ℝ->ℂ,(∀ t,0<=t->‖G t‖<=2*y^c/(c+t))->
   ‖∫ t in (0:ℝ)..T,G t‖<=2*y^c*(aa (c+T)-aa c):=by
  intro G hG
  rw[<- ym hc hT]
  apply fc hT
  ·exact Eventually.of_forall (fun t ht=>hG t ht.1.le)
  ·apply el
   apply ez.div (by fun_prop)
   intro t ht
   rw[uIcc_of_le hT] at ht
   linarith[ht.1]
 have hA:=hbd (fun t=>F (-t)) (fun t ht=>by
  have:=w1 hy hc (-t)
  rwa[j1,bh ht] at this)
 have hB:=hbd F (fun t ht=>by
  have:=w1 hy hc t
  rwa[bh ht] at this)
 rw[u8]
 calc _<=‖∫ t in (0:ℝ)..T,F (-t)‖+‖∫ t in (0:ℝ)..T,F t‖:=ds _ _
  _<=_:=by linarith
open ArithmeticFunction
export bt.qf (ux)
lemma z2 {a:ℝ} (ha:0<a):Summable fun n:ℕ=>(n:ℝ)^(-(1+a)):=
 gr.mpr (by linarith)
lemma aku {a:ℝ} (ha:0<a):∑' n:ℕ,(n:ℝ)^(-(1+a))<=1+1/a:=
 lh (fun n=>by positivity) (ux ha)
lemma w8 {δ:ℝ} (uf:0<δ) (n:ℕ):
  Λ n*(n:ℝ)^(-(1+δ))<=2/δ*(n:ℝ)^(-(1+δ/2)):=by
 rcases c7 n with rfl | hn
 ·simp only[mw,ql,zero_mul]; positivity
 have v8:(0:ℝ)<n:=by exact_mod_cast hn
 have h1:Λ n<=(n:ℝ)^(δ/2)/(δ/2):=
  vonMangoldt_le_log.trans (np v8.le (by linarith))
 have h2:(n:ℝ)^(δ/2)*(n:ℝ)^(-(1+δ))=(n:ℝ)^(-(1+δ/2)):=by
  rw[<- c6 v8]; ring_nf
 calc Λ n*(n:ℝ)^(-(1+δ))<=(n:ℝ)^(δ/2)/(δ/2)*(n:ℝ)^(-(1+δ)):=
       ag h1 (by positivity)
  _=2/δ*(n:ℝ)^(-(1+δ/2)):=by rw[<- h2,ml]; ring
lemma vg {δ:ℝ} (uf:0<δ):
  Summable fun n:ℕ=>Λ n*(n:ℝ)^(-(1+δ)):=
 d9 (fun n=>b7 vonMangoldt_nonneg (by positivity))
  (w8 uf) ((z2 (half_pos uf)).mul_left _)
lemma aan {δ:ℝ} (uf:0<δ):
  ∑' n:ℕ,Λ n*(n:ℝ)^(-(1+δ))<=2/δ*(1+2/δ):=by
 calc _<=∑' n:ℕ,2/δ*(n:ℝ)^(-(1+δ/2)):=
       ks (w8 uf) (vg uf)
        ((z2 (half_pos uf)).mul_left _)
  _=2/δ*∑' n:ℕ,(n:ℝ)^(-(1+δ/2)):=pj
  _ ≤ 2/δ*(1+2/δ):=by
      have:=aku (half_pos uf)
      rw[one_div_div] at this
      exact ab this (by positivity)
lemma aas {x:ℝ} (hx:0<=x) (n:ℕ) (s:ℂ):
  ((x/n:ℝ):ℂ)^s=(x:ℂ)^s/(n:ℂ)^s:=by
 rw[ofReal_div,div_cpow_ofReal_nonneg hx (av n),ofReal_natCast]
theorem ai2 {x c T:ℝ} (hx:0<x) (hc:1<c):
  HasSum (fun n:ℕ=>(Λ n:ℂ)*t5 (x/n) c T)
   (∫ t:ℝ in (-T)..T,LSeries (fun n=>(Λ n:ℂ)) ((c:ℂ)+t *I)*
    ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I))):=by
 have t9:0<c:=by linarith
 set F:ℕ->ℝ->ℂ:=fun n t=>
  (Λ n:ℂ)*(((x/n:ℝ):ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)) with hF
 have hFc:∀ n,Continuous (F n):=by
  intro n
  rcases c7 n with rfl | hn
  ·simp only[hF,ql,ofReal_zero,zero_mul]; exact dm
  ·exact dm.mul
    (v9 (mo hx (by exact_mod_cast hn)) t9)
 have hsum:Summable fun n:ℕ=>Λ n*(x/n)^c/c:=by
  have h1:Summable fun n:ℕ=>Λ n*(n:ℝ)^(-(1+(c-1))):=
   vg (by linarith)
  refine (h1.mul_left (x^c/c)).congr (fun n=>?_)
  rcases c7 n with rfl | hn
  ·simp
  ·have v8:(0:ℝ)<n:=by exact_mod_cast hn
   rw[ri hx.le v8.le,show -(1+(c-1))=-c by ring,iv v8.le]
   field_simp
 have hbound:∀ n:ℕ,∀ t:ℝ,‖F n t‖<=Λ n*(x/n)^c/c:=by
  intro n t
  rcases c7 n with rfl | hn
  ·simp[hF]
  ·have hy:0<x/n:=mo hx (by exact_mod_cast hn)
   have:=uo hy ((c:ℂ)+t *I) c t9 (by
    have:=cm ((c:ℂ)+t *I); simp at this
    rwa[a7 t9] at this)
   simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
    ij] at this
   simp only[hF,bo,ba,au,
    bh (vonMangoldt_nonneg:0<=Λ n)]
   rw[jm]
   exact ab this vonMangoldt_nonneg
 have a48:∀ t:ℝ,HasSum (fun n=>F n t) (LSeries (fun n=>(Λ n:ℂ)) ((c:ℂ)+t *I)*
       ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I))):=by
  intro t
  have hs:1<((c:ℂ)+t *I).re:=by simp; linarith
  have h:=(LSeriesSummable_vonMangoldt hs).hasSum.mul_right
   ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I))
  have e:(fun n=>F n t)=fun i=>dt (fun n=>(Λ n:ℂ)) ((c:ℂ)+t *I) i*
    ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)):=by
   funext n
   rcases c7 n with rfl | hn
   ·simp[hF]
   ·rw[rj hn.ne',hF]
    simp only
    rw[aas hx.le]
    ring
  rw[e]; exact h
 have key:=intervalIntegral.hasSum_integral_of_dominated_convergence (μ:=volume)
  (a:=-T) (b:=T) (F:=F)
  (f := fun t=>LSeries (fun n=>(Λ n:ℂ)) ((c:ℂ)+t *I)*
      ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)))
  (fun n _=>Λ n*(x/n)^c/c)
  (fun n=>(hFc n).aestronglyMeasurable)
  (fun n=>Eventually.of_forall (fun t _=>hbound n t))
  (Eventually.of_forall (fun t _=>hsum))
  kb
  (Eventually.of_forall (fun t _=>a48 t))
 simp only[hF,cv] at key
 exact key
lemma ab7 (M:ℕ):
  ∑ k∈bk M,(1:ℝ)/(k+1)<=1+aa M:=by
 have h:=nb M
 have e:((harmonic M:ℚ):ℝ)=∑ k∈bk M,(1:ℝ)/(k+1):=by
  simp[harmonic,jz]
 linarith
lemma aea (m N:ℕ) (hm:m<=N):
  ∑ n∈bk (N+1),(1:ℝ)/(|(n:ℝ)-m|+1)<=2*(1+aa (N+1)):=by
 rw[<- Finset.sum_range_add_sum_Ico _ (show m<=N+1 by omega)]
 have hH:=ab7 (N+1)
 have u6:∀ M ≤ N+1,∑ k∈bk M,(1:ℝ)/(k+1)<=
   ∑ k∈bk (N+1),(1:ℝ)/(k+1):=
  fun M hM=>aq (jn.mpr hM)
   (fun _ _ _=>by positivity)
 have h1:∑ n∈bk m,(1:ℝ)/(|(n:ℝ)-m|+1)<=
   ∑ k∈bk m,(1:ℝ)/(k+1):=by
  rw[<- q4 (fun n:ℕ=>(1:ℝ)/(|(n:ℝ)-m|+1)) m]
  apply ao
  intro j hj
  rw[bw] at hj
  have:((m-1-j:ℕ):ℝ)=m-1-j:=by
   rw[Nat.sub_sub,il (by omega)]; push_cast; ring
  rw[this,show (m:ℝ)-1-j-m=-(1+j) by ring,j1,
   bh (by positivity)]
  apply dr (by positivity); linarith
 have h2:∑ n∈Finset.Ico m (N+1),(1:ℝ)/(|(n:ℝ)-m|+1)=
   ∑ k∈bk (N+1-m),(1:ℝ)/(k+1):=by
  rw[dq]
  apply ai rfl
  intro k _
  push_cast
  rw[show (m:ℝ)+k-m=k by ring,bh (av k)]
 have h3:=u6 m (by omega)
 have h4:=u6 (N+1-m) (by omega)
 push_cast at hH
 linarith
lemma aop {x:ℝ} (hx:0<=x) (n:ℕ) (h:1<=|(n:ℝ)-x|):
  1/|(n:ℝ)-x|<=3/(|(n:ℝ)-⌊x⌋₊|+1):=by
 have h1:=ju hx
 have h2:=g8 x
 have h3:|(n:ℝ)-⌊x⌋₊|<=|(n:ℝ)-x|+1:=by
  calc |(n:ℝ)-⌊x⌋₊|=|((n:ℝ)-x)+(x-⌊x⌋₊)|:=by ring_nf
   _<=|(n:ℝ)-x|+|x-⌊x⌋₊|:=abs_add_le _ _
   _ ≤ |(n:ℝ)-x|+1:=by
       rw[bh (show (0:ℝ)<=x-⌊x⌋₊ by linarith)]; linarith
 rw[ax (by linarith) (by positivity)]
 linarith
noncomputable def u9 (x:ℝ) (n:ℕ):ℂ:=if (n:ℝ)<=x then 2*(π:ℂ) else 0
lemma aeb (n:ℕ) (P:ℂ) (x:ℝ):
  ‖(Λ n:ℂ)*P-(Λ n:ℂ)*u9 x n‖=Λ n*‖P-u9 x n‖:=by
 rw[<- mul_sub,bo,ba,au,
  bh (vonMangoldt_nonneg:0<=Λ n)]
lemma aye {x c T:ℝ} (hx:0<x) (hc:0<c) (hT:0<T) {n:ℕ} (hn:0<n)
  (xp:(n:ℝ)<=x/2∨2*x<=n):
  ‖t5 (x/n) c T-u9 x n‖<=2*(x/n)^c/(T*aa 2):=by
 have v8:(0:ℝ)<n:=by exact_mod_cast hn
 have hl2:0<aa 2:=eo (by norm_num)
 have hy:0<x/n:=mo hx v8
 rcases xp with h | h
 ·have hj:u9 x n=2*(π:ℂ):=by unfold u9; rw[if_pos (by linarith)]
  have hy2:2<=x/n:=by rw[bl v8]; linarith
  have ur:aa 2<=aa (x/n):=a5 (by norm_num) hy2
  rw[hj]
  refine (ab6 (by linarith) hc hT).trans ?_
  apply bb (by positivity) (by positivity)
  exact ab ur hT.le
 ·have hj:u9 x n=0:=by unfold u9; rw[if_neg (by linarith)]
  have hy2:x/n<=2⁻¹:=by
   rw[ay v8]; linarith
  have ur:aa 2<=-aa (x/n):=by
   have:=a5 hy hy2
   rw[Real.log_inv] at this; linarith
  rw[hj,kg]
  refine (ab5 hy (by linarith) hc hT).trans ?_
  apply bb (by positivity) (by positivity)
  exact ab ur hT.le
lemma ayf {x c T:ℝ} (hx:0<x) (hc:0<c) (hc2:(2:ℝ)^c<=2*af 1)
  (hT:0<T) {n:ℕ} (h1:x/2<n) (h2:(n:ℝ)<2*x) (h3:1<=|(n:ℝ)-x|):
  ‖t5 (x/n) c T-u9 x n‖<=8*af 1*x/(T*|(n:ℝ)-x|):=by
 have v8:(0:ℝ)<n:=by linarith
 have hy:0<x/n:=mo hx v8
 have hd:0< |(n:ℝ)-x|:=by linarith
 have he:0<af 1:=bx 1
 rcases lt_or_gt_of_ne (show (n:ℝ)≠x by intro h; rw[h,i3,abs_zero] at h3; linarith)
  with v7 | hgt
 ·have hj:u9 x n=2*(π:ℂ):=by unfold u9; rw[if_pos v7.le]
  have yt:1<x/n:=by rw[na v8]; linarith
  have hy2:x/n<=2:=by rw[ay v8]; linarith
  have hyc:(x/n)^c<=2*af 1:=
   (dh hy.le hy2 hc.le).trans hc2
  have xj:|(n:ℝ)-x|=x-n:=by rw[jj,a7 (by linarith)]
  have ur:|(n:ℝ)-x|/x<=aa (x/n):=by
   have:=b5 hy
   rw[inv_div] at this
   rw[xj]
   calc (x-n)/x=1-n/x:=by field_simp
    _<=_:=this
  rw[hj]
  refine (ab6 yt hc hT).trans ?_
  calc 2*(x/n)^c/(T*aa (x/n))<=2*(x/n)^c/(T*(|(n:ℝ)-x|/x)):=
        bb (by positivity) (by positivity)
         (ab ur hT.le)
   _=2*(x/n)^c*x/(T*|(n:ℝ)-x|):=by field_simp
   _ ≤ 8*af 1*x/(T*|(n:ℝ)-x|):=by
       apply a4 _ (by positivity)
       nlinarith
 ·have hj:u9 x n=0:=by unfold u9; rw[if_neg (by linarith)]
  have yt:x/n<1:=by rw[div_lt_one v8]; linarith
  have hyc:(x/n)^c<=1:=Real.rpow_le_one hy.le yt.le hc.le
  have xj:|(n:ℝ)-x|=n-x:=a7 (by linarith)
  have ur:|(n:ℝ)-x|/(2*x)<=-aa (x/n):=by
   have:=b5 (mo v8 hx)
   rw[inv_div] at this
   have e:aa (n/x)=-aa (x/n):=by
    rw[<- Real.log_inv,inv_div]
   rw[xj,<- e]
   calc ((n:ℝ)-x)/(2*x)<=((n:ℝ)-x)/n:=
         bb (by linarith) v8 (by linarith)
    _=1-x/n:=by field_simp
    _<=_:=this
  rw[hj,kg]
  refine (ab5 hy yt hc hT).trans ?_
  calc 2*(x/n)^c/(T*-aa (x/n))<=
        2*(x/n)^c/(T*(|(n:ℝ)-x|/(2*x))):=
        bb (by positivity) (by positivity)
         (ab ur hT.le)
   _=4*(x/n)^c*x/(T*|(n:ℝ)-x|):=by field_simp; ring
   _ ≤ 8*af 1*x/(T*|(n:ℝ)-x|):=by
       apply a4 _ (by positivity)
       have:1<=af 1:=by linarith[cw 1]
       nlinarith
lemma auu {x c T:ℝ} (hx:2<=x) (hc:1<=c) (hc2:(2:ℝ)^c<=2*af 1)
  (hT:0<=T) {n:ℕ} (h:|(n:ℝ)-x|<1):
  ‖t5 (x/n) c T-u9 x n‖<=8*af 1*aa (c+T)+2*π:=by
 have xj:=abs_lt.mp h
 have v8:(0:ℝ)<n:=by linarith
 have hy:0<x/n:=mo (by linarith) v8
 have hy2:x/n<=2:=by rw[ay v8]; linarith
 have hyc:(x/n)^c<=2*af 1:=
  (dh hy.le hy2 (by linarith)).trans hc2
 have hP:=aoo hy (by linarith:(0:ℝ)<c) hT
 have hlc:0<=aa c:=bd hc
 have bep:0<=aa (c+T):=bd (by linarith)
 have hj:‖u9 x n‖<=2*π:=by
  unfold u9; split_ifs
  ·simp[a7 du]
  ·simp[du.le]
 calc ‖t5 (x/n) c T-u9 x n‖<=‖t5 (x/n) c T‖+‖u9 x n‖:=ej _ _
  _<=4*(x/n)^c*(aa (c+T)-aa c)+2*π:=e8 hP hj
  _ ≤ 8*af 1*aa (c+T)+2*π:=by
      have h0:0<=(x/n)^c:=by positivity
      nlinarith
noncomputable def ui (x:ℝ):ℝ:=1+1/aa x
lemma aqo {x:ℝ} (hx:0<=x):
  ∑' n:ℕ,(Λ n:ℂ)*u9 x n=2*π*(Chebyshev.psi x:ℂ):=by
 rw[tsum_eq_sum (s:=q6 0 ⌊x⌋₊)]
 ·rw[Chebyshev.psi_eq_sum_Icc]
  push_cast
  rw[bc]
  apply ai rfl
  intro n hn
  have:(n:ℝ)<=x:=by
   have:=(ar.mp hn).2
   exact (Nat.le_floor_iff hx).mp this
  unfold u9; rw[if_pos this]; ring
 ·intro n hn
  have:¬ (n:ℝ)<=x:=by
   intro h
   apply hn
   exact ar.mpr ⟨n5 _,rv h⟩
  unfold u9; rw[if_neg this,mul_zero]
lemma ayg {L e l2:ℝ} (hL:l2<=L) (hl2:0.6931471803<l2) (he:e<2.7182818286)
  (he0:0<e):4*e *L*(1+2*L)/l2<=60*L^2:=by
 have vc:0<L:=by linarith
 rw[ay (by linarith)]
 have h1:1<=1.5*L:=by linarith
 have q:L*(1+2*L)<=3.5*L^2:=by nlinarith
 have q2:4*e *(L*(1+2*L))<=4*2.7182818286*(3.5*L^2):=
  a8 (by linarith) q (by positivity) (by norm_num)
 have q3:60*L^2*0.6931471803<=60*L^2*l2:=
  ab hl2.le (by positivity)
 have:=c4 L
 calc 4*e *L*(1+2*L)=4*e *(L*(1+2*L)):=by ring
  _<=4*2.7182818286*(3.5*L^2):=q2
  _<=60*L^2*0.6931471803:=by linarith
  _<=60*L^2*l2:=q3
lemma ayh {L e A B:ℝ} (hL:0.69<=L) (he:e<2.7182818286) (hA0:0<=A)
  (hA:A<=2*L) (hB0:0<=B) (hB:B<=3*L):48*e *A*(1+B)<=1200*L^2:=by
 have h1:A*(1+B)<=2*L*(4.5*L):=a8 hA (by linarith) (by linarith) (by linarith)
 have h2:0<=A*(1+B):=by positivity
 have h3:e *(A*(1+B))<=2.7182818286*(2*L*(4.5*L)):=
  a8 he.le h1 h2 (by norm_num)
 have:=c4 L
 calc 48*e *A*(1+B)=48*(e *(A*(1+B))):=by ring
  _<=48*(2.7182818286*(2*L*(4.5*L))):=by linarith
  _<=1200*L^2:=by nlinarith
lemma ayi {L e A C p:ℝ} (hL:0.69<=L) (he:e<2.7182818286) (he0:0<e)
  (hp:p<3.15) (zc:0<p) (hA0:0<=A) (hA:A<=2*L) (x9:0<=C) (hC:C<=3*L):
  2*(A*(8*e *C+2*p))<=300*L^2:=by
 have h0:e *C<=2.7182818286*(3*L):=a8 he.le hC x9 (by norm_num)
 have h1:8*e *C+2*p<=75*L:=by nlinarith
 have h2:A*(8*e *C+2*p)<=2*L*(75*L):=
  a8 hA h1 (by positivity) (by linarith)
 nlinarith
set_option maxHeartbeats 1000000 in
theorem aoq {x T:ℝ} (hx:2<=x) (hT:2<=T) (hTx:T<=2*x):
  ‖(∫ t:ℝ in (-T)..T,LSeries (fun n=>(Λ n:ℂ)) ((ui x:ℂ)+t *I)*
      ((x:ℂ)^((ui x:ℂ)+t *I)/((ui x:ℂ)+t *I)))-
   2*π*(Chebyshev.psi x:ℂ)‖<=2500*x*aa x^2/T:=by
 set L:=aa x with acu
 have tp:0<x:=by linarith
 have ua:0<T:=by linarith
 have aay:0.6931471803<aa 2:=f6
 have hL2:aa 2<=L:=a5 (by norm_num) hx
 have vc:0<L:=by linarith
 have he:af 1<2.7182818286:=f7
 have he0:0<af 1:=bx 1
 have hpi:π<3.15:=Real.pi_lt_d2
 set c:=ui x with bc0
 have hc:c=1+1/L:=rfl
 have hiL:0<1/L:=uc.mpr vc
 have ber:1/L<=1.5:=by rw[ay vc]; linarith
 have hc1:1<c:=by rw[hc]; linarith
 have hxc:x^c=af 1*x:=by
  rw[c9 tp,hc,<- acu,ud,di,kh vc.ne',
   bs,fl tp]; ring
 have h2c:(2:ℝ)^c<=2*af 1:=by
  rw[c9 (by norm_num),hc,ud,di,bs,
   fl (by norm_num)]
  gcongr
  rw[m8,dw vc]; exact hL2
 have hA:=ai2 (T:=T) tp hc1
 set m:=⌊x⌋₊ with hm
 set N:=⌊2*x⌋₊ with hN
 have hmx:=ju tp.le
 have hxm:=g8 x
 have hN2:(N:ℝ)<=2*x:=ju (by linarith)
 have an6:2*x<N+1:=g8 (2*x)
 have hmN:m<=N:=Nat.floor_le_floor (by linarith)
 set E:ℕ->ℂ:=fun n=>(Λ n:ℂ)*t5 (x/n) c T-(Λ n:ℂ)*u9 x n with hE
 have hJs:Summable fun n:ℕ=>(Λ n:ℂ)*u9 x n:=by
  apply summable_of_ne_finset_zero (s:=q6 0 m)
  intro n hn
  have:¬ (n:ℝ)<=x:=by
   intro h
   apply hn
   exact ar.mpr ⟨n5 _,rv h⟩
  unfold u9; rw[if_neg this,mul_zero]
 have yc:(∫ t:ℝ in (-T)..T,LSeries (fun n=>(Λ n:ℂ)) ((c:ℂ)+t *I)*
       ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)))-2*π*(Chebyshev.psi x:ℂ)=
   ∑' n,E n:=by
  rw[<- aqo tp.le,<- hA.tsum_eq]
  exact (hA.summable.tsum_sub hJs).symm
 rw[yc]
 set K1:ℝ:=2*x^c/(T*aa 2) with hK1
 set b:ℕ->ℝ:=fun n=>K1*(Λ n*(n:ℝ)^(-(1+1/L))) with hb
 set w:ℕ->ℝ:=fun n=>if x/2<n∧(n:ℝ)<2*x then ‖E n‖ else 0 with hw
 have aqp:0<K1:=by positivity
 have hb0:∀ n,0<=b n:=fun n=>
  b7 aqp.le (b7 vonMangoldt_nonneg (by positivity))
 have hbs:Summable b:=(vg hiL).mul_left K1
 have hws:HasSum w (∑ n∈bk (N+1),w n):=by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw[bw,not_lt] at hn
  have:(N:ℝ)+1<=n:=by exact_mod_cast hn
  simp only[hw]
  rw[if_neg (by intro h; linarith[h.2])]
 have hle:∀ n,‖E n‖<=b n+w n:=by
  intro n
  by_cases yh:x/2<n∧(n:ℝ)<2*x
  ·simp only[hw,if_pos yh]; linarith[hb0 n]
  ·simp only[hw,if_neg yh,ij]
   rcases c7 n with rfl | hn
   ·have:E 0=0:=by simp[hE]
    rw[this,jw]; exact hb0 0
   ·have xp:(n:ℝ)<=x/2∨2*x<=n:=by
     by_cases h:(n:ℝ)<=x/2
     ·exact Or.inl h
     ·right; push_neg at h yh; exact yh h
    simp only[hE]
    rw[aeb]
    have hf:=aye (c:=c) tp (by linarith) ua hn xp
    calc Λ n*‖t5 (x/n) c T-u9 x n‖<=
          Λ n*(2*(x/n)^c/(T*aa 2)):=
          ab hf vonMangoldt_nonneg
     _ = b n:=by
         simp only[hb,hK1]
         rw[ri tp.le (av _),<- hc,
          iv (av _)]
         field_simp
 have u5:=tsum_of_norm_bounded (hbs.hasSum.add hws) hle
 have hbt:∑' n,b n<=K1*(2/(1/L)*(1+2/(1/L))):=by
  simp only[hb]
  rw[pj]
  exact ab (aan hiL) aqp.le
 set A:=aa (2*x) with as5
 set Cc:=aa (c+T) with bc1
 have hA0:0<A:=eo (by linarith)
 have x9:0<=Cc:=bd (by linarith)
 set M1:ℝ:=24*af 1*x*A/T with w6
 set M2:ℝ:=A*(8*af 1*Cc+2*π) with hM2
 have bae:0<=M1:=by positivity
 have baf:0<=M2:=by have:=du; positivity
 have hwn:∀ n∈bk (N+1),w n<=
   M1*(1/(|(n:ℝ)-m|+1))+(if |(n:ℝ)-x|<1 then M2 else 0):=by
  intro n _
  have bes:0<=(if |(n:ℝ)-x|<1 then M2 else 0):=by split_ifs <;> linarith
  by_cases yh:x/2<n∧(n:ℝ)<2*x
  ·simp only[hw,if_pos yh]
   have v8:(0:ℝ)<n:=by linarith[yh.1]
   have hΛ:Λ n<=A:=vonMangoldt_le_log.trans (a5 v8 yh.2.le)
   simp only[hE]
   rw[aeb]
   by_cases ael:|(n:ℝ)-x|<1
   ·rw[if_pos ael]
    have h1:=auu hx hc1.le h2c ua.le ael
    have h2:0<=8*af 1*aa (c+T)+2*π:=by
     have:=du; positivity
    have h3:Λ n*‖t5 (x/n) c T-u9 x n‖<=M2:=
     calc _<=Λ n*(8*af 1*aa (c+T)+2*π):=
           ab h1 vonMangoldt_nonneg
      _ ≤ A*(8*af 1*aa (c+T)+2*π):=
          ag hΛ h2
    have:0<=M1*(1/(|(n:ℝ)-m|+1)):=by positivity
    linarith
   ·rw[if_neg ael,ij]
    push_neg at ael
    have h1:=ayf tp (by linarith) h2c ua yh.1 yh.2 ael
    have h4:=aop tp.le n ael
    have hd:0< |(n:ℝ)-x|:=by linarith
    calc Λ n*‖t5 (x/n) c T-u9 x n‖<=
          Λ n*(8*af 1*x/(T*|(n:ℝ)-x|)):=
          ab h1 vonMangoldt_nonneg
     _ ≤ A*(8*af 1*x/(T*|(n:ℝ)-x|)):=
         ag hΛ (by positivity)
     _=A*8*af 1*x/T*(1/|(n:ℝ)-x|):=by field_simp
     _ ≤ A*8*af 1*x/T*(3/(|(n:ℝ)-m|+1)):=
         ab h4 (by positivity)
     _=M1*(1/(|(n:ℝ)-m|+1)):=by simp only[w6]; field_simp; ring
  ·simp only[hw,if_neg yh]
   have:0<=M1*(1/(|(n:ℝ)-m|+1)):=by positivity
   linarith
 have aa0:((bk (N+1)).filter (fun n:ℕ=>|(n:ℝ)-x|<1)).card<=2:=by
  have uj:(bk (N+1)).filter (fun n:ℕ=>|(n:ℝ)-x|<1) ⊆ {m,m+1}:=by
   intro n hn
   rw[ah] at hn
   have h:=abs_lt.mp hn.2
   have h1:m<n+1:=by exact_mod_cast (by linarith:(m:ℝ)<n+1)
   have h2:n< m+2:=by exact_mod_cast (by linarith:(n:ℝ)< m+2)
   rw[fv,nx]
   omega
  calc _<=({m,m+1}:Finset ℕ).card:=cf uj
   _<=({m+1}:Finset ℕ).card+1:=Finset.card_insert_le _ _
   _=2:=by simp
 have a07:∑ n∈bk (N+1),w n<=
   M1*(2*(1+aa (N+1)))+2*M2:=by
  calc ∑ n∈bk (N+1),w n<=∑ n∈bk (N+1),
        (M1*(1/(|(n:ℝ)-m|+1))+(if |(n:ℝ)-x|<1 then M2 else 0)):=
        ao hwn
   _ = M1*∑ n∈bk (N+1),(1/(|(n:ℝ)-m|+1))+
       ((bk (N+1)).filter (fun n:ℕ=>|(n:ℝ)-x|<1)).card*M2:=by
       rw[cu,<- bc,Finset.sum_ite,Finset.sum_const_zero,
        ij,a9,cp]
   _ ≤ M1*(2*(1+aa (N+1)))+2*M2:=by
       gcongr
       ·exact aea m N hmN
       ·exact_mod_cast aa0
 have bc2:aa (4*x)=2*aa 2+L:=by
  rw[ca (by norm_num) tp.ne',show (4:ℝ)=2^2 by norm_num,cq]
  push_cast; ring
 have hA2:A<=2*L:=by
  rw[as5,ca (by norm_num) tp.ne']; linarith
 have hB3:aa (N+1)<=3*L:=by
  have:=a5 (by positivity) (show (N:ℝ)+1<=4*x by linarith)
  linarith
 have hB0:0<=aa (N+1):=bd (by linarith[(av N:(0:ℝ)<=N)])
 have hC3:Cc<=3*L:=by
  have:=a5 (by linarith) (show c+T<=4*x by rw[hc]; linarith)
  linarith
 set r:=x/T with hr
 have hr0:0<r:=by positivity
 have hr1:1/2<=r:=by rw[hr,bl ua]; linarith
 have e1:K1*(2/(1/L)*(1+2/(1/L)))=r*(4*af 1*L*(1+2*L)/aa 2):=by
  simp only[hK1,hr]; rw[hxc]; field_simp; ring
 have e2:M1*(2*(1+aa (N+1)))=r*(48*af 1*A*(1+aa (N+1))):=by
  simp only[w6,hr]; field_simp; ring
 have b1:=ayg hL2 aay he he0
 have b2:=ayh (L:=L) (e:=af 1) (by linarith) he hA0.le hA2 hB0 hB3
 have b3:=ayi (L:=L) (by linarith) he he0 hpi du hA0.le hA2 x9 hC3
 have af9:2500*x*L^2/T=r*(2500*L^2):=by simp only[hr]; field_simp
 rw[af9]
 have ayk:0<=L^2:=c4 L
 have hrL:1/2*L^2<=r*L^2:=ag hr1 ayk
 calc ‖∑' n,E n‖<=∑' n,b n+∑ n∈bk (N+1),w n:=u5
  _ ≤ K1*(2/(1/L)*(1+2/(1/L)))+(M1*(2*(1+aa (N+1)))+2*M2):=
      e8 hbt a07
  _ ≤ r*(60*L^2)+(r*(1200*L^2)+300*L^2):=by
      rw[e1,e2]
      exact e8 (ab b1 hr0.le)
       (e8 (ab b2 hr0.le) b3)
  _<=r*(2500*L^2):=by linarith
end bt.cz.tx
namespace bt.cz.vj
open Complex Set Filter Topology MeasureTheory intervalIntegral Asymptotics
open scoped Real Interval
export bt.qf (pw)
export bt.qf (akk)
export bt.qf (y0)
export bt.qf (ae5)
export bt.qf (wf)
export bt.qf (y1)
export bt.qf (zf)
export bt.qf (wq)
export bt.qf (acq)
export bt.qf (yj)
export bt.qf (ah0)
export bt.qf (ad8)
export bt.qf (ve)
export bt.qf (zy)
export bt.qf (yr)
export bt.qf (vf)
export bt.qf (yk)
export bt.qf (acr)
export bt.qf (ac7)
export bt.qf (x3)
export bt.qf (Phi)
export bt.qf (x4)
export bt.qf (ags)
export bt.qf (ad9)
export bt.qf (wx)
open scoped ArithmeticFunction.Moebius
open Metric
export bt.qf (ux)
export bt.qf (aam)
export bt.qf (u7)
export bt.abg (tb)
export bt.qf (uw)
export bt.qf (vv)
export bt.qf (ab4)
export bt.qf (z7)
end bt.cz.vj
namespace bt.cz.acv
open Complex Set Filter Topology Metric
export bt.zd (aew)
export bt.zd (yb)
export bt.zd (wc)
theorem ah6 {f:ℂ->ℂ} (hf:Differentiable ℂ f) (uq:∀ ρ,analyticOrderAt f ρ≠⊤)
  {s6:ℂ} (ai9:f s6≠0) (S:Finset ℂ) (zl:∀ ρ∈S,ρ∈closedBall s6 (11/5))
  (aaw:∀ ρ∈closedBall s6 (11/5),f ρ=0->ρ∈S)
  {M:ℝ} (hM:1<=M) (hbound:∀ z∈sphere s6 (12/5),‖f z‖<=M*‖f s6‖)
  {z:ℂ} (hz:z∈closedBall s6 2) (zv:f z≠0):
  ‖logDeriv f z-∑ ρ∈S,(analyticOrderNatAt f ρ:ℂ)/(z-ρ)‖<=
   420*(aa M+(∑ ρ∈S,analyticOrderNatAt f ρ)*aa 11+1):=by
 classical
 obtain ⟨g,hg,hgS,hfg,-⟩:=yb hf uq S
 set m:ℂ->ℕ:=fun ρ=>analyticOrderNatAt f ρ with hm
 set N:ℕ:=∑ ρ∈S,m ρ with hN
 set P:ℂ->ℂ:=fun w=>∏ ρ∈S,(w-ρ)^m ρ with hP
 have aaf:∀ w,f w=P w*g w:=hfg
 have acb:∀ w∈closedBall s6 (11/5),g w≠0:=by
  intro w hw h0
  by_cases hwS:w∈S
  ·exact hgS w hwS h0
  ·exact hwS (aaw w hw (by rw[aaf w,h0,mul_zero]))
 have arc:g s6≠0:=acb s6 (mem_closedBall_self (by norm_num))
 have afa:∀ w∈sphere s6 (12/5),(1/5:ℝ)^N<=‖P w‖:=by
  intro w hw
  simp only[hP,ra,la]
  rw[hN,<- fp]
  apply iy (fun _ _=>by positivity)
  intro ρ s8
  apply aj (by norm_num)
  have h1:=zl ρ s8
  rw[mem_closedBall,b8] at h1
  rw[mem_sphere,b8] at hw
  have:=qs (w-s6) (ρ-s6)
  have e:(w-s6)-(ρ-s6)=w-ρ:=by ring
  rw[e] at this; linarith
 have ard:‖P s6‖<=(11/5:ℝ)^N:=by
  simp only[hP,ra,la]
  rw[hN,<- fp]
  apply iy (fun _ _=>by positivity)
  intro ρ s8
  apply aj (aw _)
  have h1:=zl ρ s8
  rw[mem_closedBall,b8] at h1
  rw[norm_sub_rev]; exact h1
 have anh:∀ w∈closedBall s6 (11/5),‖g w‖<=M*‖f s6‖*5^N:=by
  intro w hw
  apply me (U:=ball s6 (12/5)) isBounded_ball
   hg.diffContOnCl
  ·intro v hv
   rw[frontier_ball _ (by norm_num)] at hv
   have hPv:=afa v hv
   have avy:0<‖P v‖:=fj (by positivity) hPv
   have hfv:‖f v‖=‖P v‖*‖g v‖:=by rw[aaf,bo]
   calc ‖g v‖=‖f v‖/‖P v‖:=by rw[hfv]; field_simp
    _ ≤ M*‖f s6‖/(1/5)^N:=
        su (by positivity) (hbound v hv) (by positivity) hPv
    _=M*‖f s6‖*5^N:=by rw[jz,inv_pow,div_inv_eq_mul]
  ·rw[n3 _ (by norm_num)]
   exact closedBall_subset_closedBall (by norm_num) hw
 have ajr:∀ w∈closedBall s6 (11/5),‖g w‖<=M*11^N*‖g s6‖:=by
  intro w hw
  have a3o:‖f s6‖<=‖g s6‖*(11/5)^N:=by
   rw[aaf,bo,gx]
   exact ab ard (aw _)
  have e:(11:ℝ)^N=(11/5)^N*5^N:=by rw[<- i5]; norm_num
  calc ‖g w‖<=M*‖f s6‖*5^N:=anh w hw
   _<=M*(‖g s6‖*(11/5)^N)*5^N:=by gcongr
   _=M*11^N*‖g s6‖:=by rw[e]; ring
 set φ:ℂ->ℂ:=fun w=>deriv g w/g w with abr
 have hφ:DifferentiableOn ℂ φ (ball s6 (11/5)):=fun w hw=>
  (((hg.analyticAt w).deriv.differentiableAt).div (hg w)
   (acb w (ball_subset_closedBall hw))).differentiableWithinAt
 obtain ⟨h,hh0,hhd⟩:=(hφ.isExactOn_ball).with_val_at s6 0
 have xm:∀ w∈ball s6 (11/5),g w*d6 (-h w)=g s6:=by
  intro w hw
  have yc:DifferentiableOn ℂ (fun w=>g w*d6 (-h w)) (ball s6 (11/5)):=
   fun v hv=>((hg v).mul ((hhd v hv).differentiableAt.neg.cexp)).differentiableWithinAt
  have are:EqOn (deriv fun w=>g w*d6 (-h w)) 0 (ball s6 (11/5)):=by
   intro v hv
   have hd:HasDerivAt (fun w=>g w*d6 (-h w)) _ v:=
    (hg v).hasDerivAt.mul ((hhd v hv).neg.cexp)
   rw[hd.deriv]
   have hgv:=acb v (ball_subset_closedBall hv)
   simp only[abr,om,ru]
   field_simp
   ring
  have:=(isOpen_ball).is_const_of_deriv_eq_zero (convex_ball s6 _).isPreconnected yc are
   hw (mem_ball_self (by norm_num))
  rw[this,hh0,sg,m1,di]
 have tu:∀ w∈ball s6 (11/5),(h w).re<=aa M+N*aa 11:=by
  intro w hw
  have hgw:g w=g s6*d6 (h w):=by
   rw[<- xm w hw,gv,<- jc,neg_add_cancel,m1,di]
  have hn:‖g w‖=‖g s6‖*af (h w).re:=by rw[hgw,bo,p5]
  have hr:=ajr w (ball_subset_closedBall hw)
  rw[hn] at hr
  have ani:0<‖g s6‖:=g7.mpr arc
  have hle:af (h w).re<=M*11^N:=by
   have:=hr; rw[gx (M*11^N)] at this
   exact lg this ani
  have tj:0<M*11^N:=by positivity
  have:=(d5 tj).mpr hle
  rw[ca (by positivity) (by positivity),cq] at this
  exact this
 set A:ℝ:=aa M+N*aa 11+1 with ajs
 have hA:0<A:=by
  have h1:=bd hM
  have h2:0<=(N:ℝ)*aa 11:=
   b7 (av _) (bd (by norm_num))
  linarith
 have hBC:∀ v∈closedBall s6 (21/10),‖h v‖<=42*A:=by
  intro v hv
  set H:ℂ->ℂ:=fun u=>h (s6+u) with hH
  have u3:∀ u∈ball (0:ℂ) (11/5),s6+u∈ball s6 (11/5):=by
   intro u hu
   rw[m3] at hu
   rw[mem_ball,b8,j0]; exact hu
  have hHd:DifferentiableOn ℂ H (ball 0 (11/5)):=fun u hu=>
   (((hhd (s6+u) (u3 u hu)).differentiableAt).comp u
    (bu.const_add s6)).differentiableWithinAt
  have wd:MapsTo H (ball 0 (11/5)) {z | z.re<=A}:=by
   intro u hu
   simp only[o1,hH]
   have:=tu (s6+u) (u3 u hu)
   linarith
  have hH0:H 0=0:=by simp[hH,hh0]
  rw[mem_closedBall,b8] at hv
  have hu:v-s6∈ball (0:ℂ) (11/5):=by
   rw[m3]; linarith
  have hb:=pg hA hHd wd (by norm_num) hu hH0
  simp only[hH,add_sub_cancel] at hb
  refine hb.trans ?_
  have xo:0<11/5-‖v-s6‖:=by linarith
  rw[ay xo]
  nlinarith[aw (v-s6)]
 have ado:z∈ball s6 (11/5):=by
  rw[mem_closedBall] at hz; rw[mem_ball]; linarith
 have ahl:‖deriv h z‖<=42*A/(1/10):=by
  apply gu (by norm_num)
  ·apply i2
   rw[n3 _ (by norm_num)]
   intro v hv
   apply (hhd v ?_).differentiableAt.differentiableWithinAt
   rw[mem_closedBall] at hv hz; rw[mem_ball]
   linarith[pq v z s6]
  ·intro v hv
   apply hBC
   rw[mem_sphere] at hv; rw[mem_closedBall] at hz ⊢
   linarith[pq v z s6]
 have hdz:deriv h z=φ z:=(hhd z ado).deriv
 have hPz:P z≠0:=fun h0=>zv (by rw[aaf,h0,zero_mul])
 have hgz:g z≠0:=acb z (ball_subset_closedBall ado)
 have hPd:DifferentiableAt ℂ P z:=by simp only[hP]; fun_prop
 have ur:logDeriv f z=logDeriv P z+logDeriv g z:=by
  rw[show f=fun w=>P w*g w from funext aaf]
  exact tf z hPz hgz hPd (hg z)
 have anj:logDeriv P z=∑ ρ∈S,(m ρ:ℂ)/(z-ρ):=by
  have te:∀ ρ∈S,(z-ρ)^m ρ≠0:=fun ρ s8=>(ix.mp hPz) ρ s8
  rw[hP,sj (f:=fun ρ w=>(w-ρ)^m ρ) te (fun ρ _=>by fun_prop)]
  exact ai rfl (fun ρ _=>wc ρ z (m ρ))
 have ajt:logDeriv f z-∑ ρ∈S,(analyticOrderNatAt f ρ:ℂ)/(z-ρ)=deriv h z:=by
  rw[hdz,ur,anj]
  simp only[hm,abr,g9]
  ring
 rw[ajt]
 calc ‖deriv h z‖<=42*A/(1/10):=ahl
  _ = 420*(aa M+(∑ ρ∈S,analyticOrderNatAt f ρ)*aa 11+1):=by
      rw[ajs,hN]; push_cast; ring
end bt.cz.acv
namespace bt.cz.vj
open Complex Set Filter Topology Metric bt.cz.acv
lemma acw {t:ℝ} (ht:4<=|t|):
  |t|/3<=‖riemannZeta₁ ((3/2:ℂ)+t *I)‖:=by
 set c0:ℂ:=(3/2:ℂ)+t *I with t9
 have aod:c0.re=3/2:=by simp[t9]
 have aoe:c0.im=t:=by simp[t9]
 have hc1:c0≠1:=by
  intro h; have:=dy im h; simp[t9] at this; rw[this] at ht; simp at ht; linarith
 rw[tb hc1,bo]
 have h1:|t|<=‖c0-1‖:=by
  have:=a6 (c0-1); simpa [aoe] using this
 have h2:=aam (s:=c0) (by rw[aod])
 calc |t|/3=|t| *(1/3):=by ring
  _<=‖c0-1‖*‖riemannZeta c0‖:=a8 h1 h2 (by norm_num) (aw _)
lemma acx {t:ℝ} (ht:4<=|t|):
  ∀ z∈sphere ((3/2:ℂ)+t *I) (12/5),‖riemannZeta₁ z‖<=600*|t|^3:=by
 set c0:ℂ:=(3/2:ℂ)+t *I with t9
 have t8:0< |t|:=by linarith
 intro z hz
 rw[mem_sphere,b8] at hz
 have tu:|z.re-3/2|<=12/5:=by
  have:=cm (z-c0); simp[t9] at this; rw[hz] at this; exact this
 have um:|z.im-t|<=12/5:=by
  have:=a6 (z-c0); simp[t9] at this; rw[hz] at this; exact this
 have a4q:=abs_le.mp tu
 have adr:|t|-12/5<=|z.im|:=by
  have:=de t z.im; rw[jj] at this; linarith
 have ahn:|z.im|<=|t|+12/5:=by
  have:=de z.im t; linarith
 have yp:z≠1:=by
  intro h; rw[h] at adr; simp at adr; linarith
 rw[tb yp,bo]
 have aof:=wx (s:=z) (by linarith) (by linarith) (by linarith)
 have arx:‖z-1‖<=|t|+53/10:=by
  have:=b6 (z-1)
  have h1:|(z-1).re|<=29/10:=by simp; rw[abs_le]; constructor <;> linarith
  have h2:(z-1).im=z.im:=by simp
  rw[h2] at this; linarith
 have hA:|t|+53/10<=12/5*|t|:=by linarith
 have hB:|t|+12/5<=12/5*|t|:=by linarith
 calc ‖z-1‖*‖riemannZeta z‖<=(12/5*|t|)*(40*(12/5*|t|)^2):=by
       apply a8 (arx.trans hA) _ (aw _) (by positivity)
       calc ‖riemannZeta z‖<=40*z.im^2:=aof
        _ ≤ 40*(12/5*|t|)^2:=by
            have h3:z.im^2<=(12/5*|t|)^2:=by
             rw[<- sq_abs]; exact aj (eg _) (ahn.trans hB) 2
            linarith
  _<=600*|t|^3:=by nlinarith[fb t8 3]
export bt.abg (tl)
def wg (t:ℝ):Set ℂ:=
 {ρ:ℂ | riemannZeta ρ=0∧ρ∈closedBall ((3/2:ℂ)+t *I) (11/5)}
lemma ta (t:ℝ):(wg t).Finite:=by
 apply ((isCompact_closedBall _ _).inter_riemannZetaZeros_finite).subset
 rintro ρ ⟨h0,s8⟩
 exact ⟨s8,h0⟩
lemma xv {t:ℝ} (ht:4<=|t|) {r:ℝ} (hr:r<=11/5):
  (1:ℂ)∉closedBall ((3/2:ℂ)+t *I) r:=by
 intro h
 rw[dj,b8] at h
 have:=a6 (1-((3/2:ℂ)+t *I))
 simp at this; linarith
export bt.abg (zm)
theorem adg {t:ℝ} (ht:4<=|t|) {z:ℂ}
  (hz:z∈closedBall ((3/2:ℂ)+t *I) 2) (a49:riemannZeta z≠0):
  ‖logDeriv riemannZeta z-∑ ρ∈(ta t).toFinset,
    (analyticOrderNatAt riemannZeta ρ:ℂ)/(z-ρ)‖<=
   13100*aa (1800*t^2)+421:=by
 classical
 set c0:ℂ:=(3/2:ℂ)+t *I with t9
 set S:=(ta t).toFinset with hS
 have t8:0< |t|:=by linarith
 have yp:z≠1:=fun h=>xv ht (r:=2) (by norm_num) (h ▸ hz)
 have zv:riemannZeta₁ z≠0:=by
  rw[tb yp]; exact k1 (cb.mpr yp) a49
 have aah:|t|/3<=‖riemannZeta₁ c0‖:=acw ht
 have te:riemannZeta₁ c0≠0:=by
  intro h; have h':=aah; rw[h,jw] at h'; linarith
 have zl:∀ ρ∈S,ρ∈closedBall c0 (11/5):=by
  intro ρ s8; rw[hS,an] at s8; exact s8.2
 have aaw:∀ ρ∈closedBall c0 (11/5),riemannZeta₁ ρ=0->ρ∈S:=by
  intro ρ s8 h0
  have yd:ρ≠1:=fun h=>xv ht le_rfl (h ▸ s8)
  rw[tb yd] at h0
  rw[hS,an]
  exact ⟨(rb.mp h0).resolve_left (cb.mpr yd),s8⟩
 have hX0:0<=aa (1800*t^2):=
  bd (by nlinarith[sq_abs t,fb t8 2])
 have hM:(1:ℝ)<=1800*t^2:=by nlinarith[sq_abs t,fb t8 2]
 have hbound:∀ w∈sphere c0 (12/5),‖riemannZeta₁ w‖<=1800*t^2*‖riemannZeta₁ c0‖:=by
  intro w hw
  refine (acx ht w hw).trans ?_
  have:600*|t|^3=1800*t^2*(|t|/3):=by rw[<- sq_abs t]; ring
  rw[this]
  exact ab aah (by positivity)
 have L:=ah6 bg tl te S
  zl aaw hM hbound hz zv
 have ajf:∀ ρ∈S,analyticOrderNatAt riemannZeta₁ ρ=analyticOrderNatAt riemannZeta ρ:=by
  intro ρ s8
  have yd:ρ≠1:=fun h=>xv ht le_rfl (h ▸ zl ρ s8)
  unfold analyticOrderNatAt; rw[uw yd]
 have a08:∑ ρ∈S,analyticOrderNatAt riemannZeta₁ ρ=∑ ρ∈S,analyticOrderNatAt riemannZeta ρ:=
  ai rfl ajf
 have a09:∑ ρ∈S,((analyticOrderNatAt riemannZeta₁ ρ:ℕ):ℂ)/(z-ρ)=
   ∑ ρ∈S,((analyticOrderNatAt riemannZeta ρ:ℕ):ℂ)/(z-ρ):=
  ai rfl (fun ρ s8=>by rw[ajf ρ s8])
 rw[a09,a08] at L
 have apb:((∑ ρ∈S,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)<=12*aa (1800*t^2):=by
  have this:∑ᶠ ρ∈wg t,(analyticOrderNatAt riemannZeta ρ:ℝ)<=
    12*aa (1800*t^2):=z7 ht
  rw[bf _ (ta t)] at this
  push_cast; exact this
 have hev:riemannZeta =ᶠ[𝓝 z] fun w=>riemannZeta₁ w/(w-1):=by
  filter_upwards[fw.mem_nhds yp] with w hw
  have zu:w≠1:=hw
  rw[tb zu,jb _ (cb.mpr zu)]
 have hld:logDeriv riemannZeta z=logDeriv riemannZeta₁ z-1/(z-1):=by
  rw[(oz hev).self_of_nhds,
   tg (f:=riemannZeta₁) (g:=fun w=>w-1) z zv
    (show z-1≠0 from cb.mpr yp) (bg z) (by fun_prop)]
  congr 1
  simp[g9]
 have hinv:‖1/(z-1)‖<=1:=by
  rw[i4,norm_one,dw (g7.mpr (cb.mpr yp))]
  rw[dj,b8] at hz
  have h1:=a6 (z-c0)
  have h2:=a6 (z-1)
  simp[t9] at h1 h2
  have:=de t z.im
  rw[jj] at h1
  linarith
 rw[hld]
 have av8:=zm
 have ast:0<=aa 11:=bd (by norm_num)
 calc ‖logDeriv riemannZeta₁ z-1/(z-1)-∑ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℂ)/(z-ρ)‖
   = ‖(logDeriv riemannZeta₁ z-∑ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℂ)/(z-ρ))
       - 1/(z-1)‖:=by ring_nf
  _ ≤ ‖logDeriv riemannZeta₁ z-∑ ρ∈S,(analyticOrderNatAt riemannZeta ρ:ℂ)/(z-ρ)‖
       + ‖1/(z-1)‖:=ej _ _
  _ ≤ 420*(aa (1800*t^2)+(12*aa (1800*t^2))*(5/2)+1)+1:=by
      refine e8 (L.trans ?_) hinv
      gcongr
  _<=13100*aa (1800*t^2)+421:=by nlinarith
end bt.cz.vj
namespace bt.cz.zh
open Complex Set
open scoped Real
theorem u4 {s:ℂ} (h1:-1<s.re) (h2:s.re<=0):
  riemannZeta s≠0:=by
 by_cases xc:s=0
 ·rw[xc,riemannZeta_zero]; norm_num
 set w:ℂ:=1-s with hw
 have a5a:1<=w.re:=by simp[hw]; linarith
 have bc3:w.re<2:=by simp[hw]; linarith
 have hw1:w≠1:=by intro h; apply xc; rw[hw] at h; linear_combination -h
 have hwn:∀ n:ℕ,w≠-n:=by
  intro n h
  have:=dy re h
  simp at this
  have:(0:ℝ)<=n:=av n
  linarith
 have hFE:=riemannZeta_one_sub hwn hw1
 rw[show 1-w=s by rw[hw]; ring] at hFE
 rw[hFE]
 have hG:Gamma w≠0:=Gamma_ne_zero hwn
 have hz:riemannZeta w≠0:=ct a5a
 have hp:(2*(π:ℂ))^(-w)≠0:=by
  apply (cpow_ne_zero_iff_of_exponent_ne_zero _).mpr
  ·have:(0:ℝ)<2*π:=by positivity
   exact_mod_cast this.ne'
  ·intro h
   have:=dy re h
   simp at this; linarith
 have hc:Complex.cos (π*w/2)≠0:=by
  intro h
  rw[Complex.cos_eq_zero_iff] at h
  obtain ⟨k,hk⟩:=h
  have hk':w=2*k+1:=by
   have hpi:(π:ℂ)≠0:=by exact_mod_cast qd
   field_simp at hk
   exact hk
  have tu:=dy re hk'
  have um:=dy im hk'
  simp at tu um
  have hk0:k=0:=by
   have h1':(0:ℝ)<=k:=by linarith
   have h2':(k:ℝ)<1/2:=by linarith
   have:(0:ℤ)<=k:=by exact_mod_cast h1'
   have:k<1:=by
    have:(k:ℝ)<1:=by linarith
    exact_mod_cast this
   omega
  apply hw1
  rw[hk',hk0]; simp
 exact k1 (k1 (k1 (k1 two_ne_zero hp) hG) hc) hz
theorem afn (G:Finset ℝ) (T:ℝ):
  ∃ T'∈Icc T (T+1),∀ γ∈G,1/(2*((G.card:ℝ)+1))<=|T'-γ|:=by
 by_contra aor
 push_neg at aor
 set n:=G.card with hn
 have xb:(0:ℝ)<(n:ℝ)+1:=by positivity
 set ε:ℝ:=1/(2*((n:ℝ)+1)) with hε
 set t:ℕ->ℝ:=fun k=>T+k/((n:ℝ)+1) with ht
 have u3:∀ k∈bk (n+1),t k∈Icc T (T+1):=by
  intro k hk
  rw[bw] at hk
  have hk':(k:ℝ)<=n:=by exact_mod_cast nc.mp hk
  constructor
  ·simp only[ht]; have:0<=(k:ℝ)/((n:ℝ)+1):=by positivity
   linarith
  ·simp only[ht]
   have:(k:ℝ)/((n:ℝ)+1)<=1:=by rw[dw xb]; linarith
   linarith
 have ahh:∀ k∈bk (n+1),∃ γ∈G,|t k-γ|<ε:=
  fun k hk=>aor (t k) (u3 k hk)
 choose! f hf using ahh
 obtain ⟨x,hx,y,hy,tv,a5b⟩:=Finset.exists_ne_map_eq_of_card_lt_of_maps_to
  (s:=bk (n+1)) (t:=G) (by simp[hn]) (fun k hk=>(hf k hk).1)
 have h1:=(hf x hx).2
 have h2:=(hf y hy).2
 rw[a5b] at h1
 have am7:|t x-t y|<2*ε:=by
  calc |t x-t y|=|(t x-f y)-(t y-f y)|:=by ring_nf
   _<=|t x-f y|+|t y-f y|:=abs_sub _ _
   _<ε+ε:=add_lt_add h1 h2
   _=2*ε:=by ring
 have yc:t x-t y=((x:ℝ)-y)/((n:ℝ)+1):=by simp only[ht]; ring
 have bet:(1:ℝ)<=|(x:ℝ)-y|:=by
  rcases lt_or_gt_of_ne tv with h | h
  ·have:(x:ℝ)+1<=y:=by exact_mod_cast h
   rw[jj,a7 (by linarith)]; linarith
  ·have:(y:ℝ)+1<=x:=by exact_mod_cast h
   rw[a7 (by linarith)]; linarith
 rw[yc,abs_div,a7 xb,hε] at am7
 have:2*(1/(2*((n:ℝ)+1)))=1/((n:ℝ)+1):=by field_simp
 rw[this,div_lt_div_iff_of_pos_right xb] at am7
 linarith
end bt.cz.zh
namespace bt.cz.uk
open Complex Set Filter Topology Metric
open scoped Real Interval
lemma aao {ρ:ℂ} (s8:ρ≠1):analyticOrderAt riemannZeta ρ≠⊤:=by
 rw[<- bt.cz.vj.uw s8]
 exact bt.cz.vj.tl ρ
lemma one_le_mult {ρ:ℂ} (s8:ρ≠1) (h0:riemannZeta ρ=0):
  1<=analyticOrderNatAt riemannZeta ρ:=by
 have hA:=bt.cz.vj.u7 s8
 have te:= aao s8
 have tj:analyticOrderAt riemannZeta ρ≠0:=by
  intro h
  rw[fm] at h
  rcases h with h | h
  ·exact h hA
  ·exact h h0
 by_contra v7
 push_neg at v7
 have:analyticOrderNatAt riemannZeta ρ=0:=by omega
 apply tj
 rw[<- lk te,this]; rfl
lemma agz {K:Set ℂ} (Z:Finset ℂ) (h1Z:(1:ℂ)∉Z)
  (hZK:∀ ρ∈K,ρ≠1->riemannZeta ρ=0->ρ∈Z):
  ∃ G:ℂ->ℂ,Differentiable ℂ G∧(∀ w∈K,G w≠0)∧
   ∀ s,s∉Z->s≠1->riemannZeta s≠0->
    logDeriv riemannZeta s=∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)
     - 1/(s-1)+logDeriv G s:=by
 classical
 obtain ⟨G,hG,hGZ,hfG,-⟩:=bt.cz.acv.yb bg
  bt.cz.vj.tl Z
 have ajf:∀ ρ∈Z,analyticOrderNatAt riemannZeta₁ ρ=analyticOrderNatAt riemannZeta ρ:=by
  intro ρ s8
  have yd:ρ≠1:=fun h=>h1Z (h ▸ s8)
  unfold analyticOrderNatAt; rw[bt.cz.vj.uw yd]
 set P:ℂ->ℂ:=fun w=>∏ ρ∈Z,(w-ρ)^analyticOrderNatAt riemannZeta ρ with hP
 have aos:∀ w,riemannZeta₁ w=P w*G w:=by
  intro w; rw[hfG w,hP]; congr 1
  exact o6 rfl (fun ρ s8=>by rw[ajf ρ s8])
 refine ⟨G,hG, ?_, ?_⟩
 ·intro w hw h0
  have hz:riemannZeta₁ w=0:=by rw[aos,h0,mul_zero]
  have hw1:w≠1:=by intro h; rw[h,riemannZeta₁_one] at hz; exact one_ne_zero hz
  rw[bt.cz.vj.tb hw1] at hz
  have zt:riemannZeta w=0:=(rb.mp hz).resolve_left (cb.mpr hw1)
  exact hGZ w (hZK w hw hw1 zt) h0
 ·intro s hsZ uu a5c
  have hf1:riemannZeta₁ s≠0:=by
   rw[bt.cz.vj.tb uu]; exact k1 (cb.mpr uu) a5c
  have hPs:P s≠0:=fun h0=>hf1 (by rw[aos,h0,zero_mul])
  have hGs:G s≠0:=fun h0=>hf1 (by rw[aos,h0,mul_zero])
  have hev:riemannZeta =ᶠ[𝓝 s] fun w=>riemannZeta₁ w/(w-1):=by
   filter_upwards[fw.mem_nhds uu] with w hw
   have zu:w≠1:=hw
   rw[bt.cz.vj.tb zu,jb _ (cb.mpr zu)]
  have hld:logDeriv riemannZeta s=logDeriv riemannZeta₁ s-1/(s-1):=by
   rw[(oz hev).self_of_nhds,
    tg (f:=riemannZeta₁) (g:=fun w=>w-1) s hf1
     (show s-1≠0 from cb.mpr uu) (bg s) (by fun_prop)]
   congr 1
   simp[g9]
  have hPd:DifferentiableAt ℂ P s:=by simp only[hP]; fun_prop
  have hl1:logDeriv riemannZeta₁ s=logDeriv P s+logDeriv G s:=by
   rw[show riemannZeta₁=fun w=>P w*G w from funext aos]
   exact tf s hPs hGs hPd (hG s)
  have hlP:logDeriv P s=∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ):=by
   have te:∀ ρ∈Z,(s-ρ)^analyticOrderNatAt riemannZeta ρ≠0:=
    fun ρ s8=>(ix.mp hPs) ρ s8
   rw[hP,sj (f:=fun ρ w=>(w-ρ)^analyticOrderNatAt riemannZeta ρ) te
    (fun ρ _=>by fun_prop)]
   exact ai rfl (fun ρ _=>bt.cz.acv.wc ρ s _)
  rw[hld,hl1,hlP]; ring
noncomputable def Ex (x:ℝ) (p:ℂ):ℂ->ℂ:=dslope (fun w:ℂ=>(x:ℂ)^w) p
lemma akx {x:ℝ} {p s:ℂ} (h:s≠p):Ex x p s=((x:ℂ)^s-(x:ℂ)^p)/(s-p):=by
 unfold Ex; rw[ti _ h,q8]
lemma z3 {x:ℝ} (hx:0<x) (p:ℂ):Differentiable ℂ (Ex x p):=by
 have tp:(x:ℂ)≠0:=by exact_mod_cast hx.ne'
 have:DifferentiableOn ℂ (Ex x p) univ:=(differentiableOn_dslope nj).mpr
  (fun z _=>((bu).const_cpow (Or.inl tp)).differentiableWithinAt)
 exact fun z=>(this z (mem_univ z)).differentiableAt nj
lemma ai3 {x:ℝ} {p s a:ℂ} (hp:p≠0) (hsp:s≠p) (hs:s≠0):
  -(a/(s-p))*((x:ℂ)^s/s)=
   (-(a*(x:ℂ)^p/p))/(s-p)+(a/p)/(s-0)-(a/p)*(Ex x p s-Ex x 0 s):=by
 rw[akx hsp,akx hs,cpow_zero]
 have h1:s-p≠0:=cb.mpr hsp
 field_simp
 ring
lemma aky {x:ℝ} (Φ:ℂ->ℂ) {s:ℂ} (hs:s≠0):
  -Φ s*((x:ℂ)^s/s)=
   (-Φ 0)/(s-0)-dslope (fun w=>Φ w*(x:ℂ)^w) 0 s:=by
 rw[ti _ hs,q8,cpow_zero]
 field_simp
 ring
lemma afo {x:ℝ} (P':Finset ℂ) (h0:(0:ℂ)∉P') (a Φ:ℂ->ℂ) {s:ℂ}
  (xc:s≠0) (hsP:s∉P'):
  -(∑ p∈P',a p/(s-p)+Φ s)*((x:ℂ)^s/s)=
   (-(∑ p∈P',(a p/p)*(Ex x p s-Ex x 0 s))-
       dslope (fun w=>Φ w*(x:ℂ)^w) 0 s)+
    ∑ q∈insert 0 P',(if q=0 then (∑ p∈P',a p/p)-Φ 0
     else -(a q*(x:ℂ)^q/q))/(s-q):=by
 classical
 rw[ic h0,if_pos rfl]
 have hP:∀ q∈P',(if q=0 then (∑ p∈P',a p/p)-Φ 0 else -(a q*(x:ℂ)^q/q))
   / (s-q)=(-(a q*(x:ℂ)^q/q))/(s-q):=by
  intro q hq
  rw[if_neg (fun (h:q=0)=>h0 (h ▸ hq))]
 rw[ai rfl hP]
 have vw:∀ p∈P',-(a p/(s-p))*((x:ℂ)^s/s)=
   (-(a p*(x:ℂ)^p/p))/(s-p)+(a p/p)/(s-0)-
    (a p/p)*(Ex x p s-Ex x 0 s):=by
  intro p hp
  exact ai3 (fun (h:p=0)=>h0 (h ▸ hp)) (fun (h:s=p)=>hsP (h ▸ hp)) xc
 have a5d:=aky (x:=x) Φ xc
 have hsum:-(∑ p∈P',a p/(s-p))*((x:ℂ)^s/s)=
   ∑ p∈P',((-(a p*(x:ℂ)^p/p))/(s-p)+(a p/p)/(s-0)-
    (a p/p)*(Ex x p s-Ex x 0 s)):=by
  rw[neg_mul,g3,<- kc]
  apply ai rfl
  intro p hp
  rw[<- vw p hp]; ring
 have u8:∑ p∈P',((-(a p*(x:ℂ)^p/p))/(s-p)+(a p/p)/(s-0)-
       (a p/p)*(Ex x p s-Ex x 0 s))=
   ∑ p∈P',(-(a p*(x:ℂ)^p/p))/(s-p)+(∑ p∈P',a p/p)/(s-0)-
    ∑ p∈P',(a p/p)*(Ex x p s-Ex x 0 s):=by
  rw[dn,cu,ew]
 calc -(∑ p∈P',a p/(s-p)+Φ s)*((x:ℂ)^s/s)
   = -(∑ p∈P',a p/(s-p))*((x:ℂ)^s/s)+-Φ s*((x:ℂ)^s/s):=by ring
  _ = _:=by
      rw[hsum,u8,a5d]
      have:((∑ p∈P',a p/p)-Φ 0)/(s-0)=
        (∑ p∈P',a p/p)/(s-0)+(-Φ 0)/(s-0):=by ring
      rw[this]; ring
end bt.cz.uk
namespace bt.cz.uk
open Complex Set Filter Topology Metric
open scoped Real Interval
export bt.abw (ts)
lemma ab8 {ρ:ℂ} (h:riemannZeta ρ=0) (h1:-1<ρ.re):0<ρ.re:=by
 by_contra h'
 exact bt.cz.zh.u4 h1 (not_lt.mp h') h
lemma y4 {x:ℝ} (hx:1<x):1<bt.cz.tx.ui x:=by
 unfold bt.cz.tx.ui
 have:=eo hx
 have:0<1/aa x:=by positivity
 linarith
theorem ai4 {x T':ℝ} (hx:1<x) (z1:0<T') (Z:Finset ℂ)
  (akz:∀ ρ∈Z,riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<T')
  (aot:∀ ρ,riemannZeta ρ=0->0<ρ.re->|ρ.im|<=T'->ρ∈Z):
  bt.cz.tx.va (fun s=>-logDeriv riemannZeta s*((x:ℂ)^s/s))
    (-1/2) (bt.cz.tx.ui x) (-T') T'=
   2*π*I*((x:ℂ)-∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ
    - logDeriv riemannZeta 0):=by
 classical
 set c:=bt.cz.tx.ui x with hc
 have hc1:1<c:= y4 hx
 have tp:0<x:=by linarith
 set K:Set ℂ:=[[(-1/2:ℝ),c]] ×ℂ [[-T',T']] with hK
 have atz:∀ s:ℂ,s∈K↔-1/2<=s.re∧s.re<=c∧-T'<=s.im∧s.im<=T':=by
  intro s
  rw[hK,mem_reProdIm,uIcc_of_le (by linarith),uIcc_of_le (by linarith)]
  simp only[mem_Icc]; tauto
 have h1Z:(1:ℂ)∉Z:=fun h=>se (akz 1 h).1
 have h0Z:(0:ℂ)∉Z:=fun h=>by have:=(akz 0 h).2.1; simp at this
 have hZK:∀ ρ∈K,ρ≠1->riemannZeta ρ=0->ρ∈Z:=by
  intro ρ s8 _ h0
  rw[atz] at s8
  exact aot ρ h0 (ab8 h0 (by linarith)) (abs_le.mpr ⟨s8.2.2.1,s8.2.2.2⟩)
 have h0K:(0:ℂ)∈K:=(atz 0).mpr
  ⟨by norm_num,by norm_num <;> linarith,by norm_num <;> linarith,by norm_num <;> linarith⟩
 obtain ⟨G,hG,hGK,a5e⟩:=agz Z h1Z hZK
 set U:Set ℂ:={w | G w≠0} with hU
 have hUo:IsOpen U:=isOpen_ne_fun hG.continuous dm
 have hKU:K ⊆ U:=fun w hw=>hGK w hw
 set Φ:ℂ->ℂ:=logDeriv G with hΦ
 have a5f:DifferentiableOn ℂ Φ U:=fun w hw=>
  (((hG.analyticAt w).deriv.differentiableAt).div (hG w) hw).differentiableWithinAt
 set P':Finset ℂ:=insert 1 Z with hP'
 set a:ℂ->ℂ:=fun p=>if p=1 then -1 else (analyticOrderNatAt riemannZeta p:ℂ) with ha
 have aou:(0:ℂ)∉P':=by
  rw[hP',fv,not_or]; exact ⟨zero_ne_one,h0Z⟩
 have a5g:∀ s∈K,s∉P'->riemannZeta s≠0:=by
  intro s hs hsP h0
  rw[hP',fv,not_or] at hsP
  exact hsP.2 (hZK s hs hsP.1 h0)
 have hld:∀ s∈K,s∉P'->logDeriv riemannZeta s=∑ p∈P',a p/(s-p)+Φ s:=by
  intro s hs hsP
  have zt:=a5g s hs hsP
  rw[hP',fv,not_or] at hsP
  rw[a5e s hsP.2 hsP.1 zt,hP',ic h1Z]
  have:∀ ρ∈Z,a ρ/(s-ρ)=(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ):=by
   intro ρ s8
   simp only[ha,if_neg (fun (h:ρ=1)=>h1Z (h ▸ s8))]
  rw[ai rfl this]
  simp only[ha,if_pos rfl]
  ring
 set g:ℂ->ℂ:=fun s=>-(∑ p∈P',(a p/p)*(Ex x p s-Ex x 0 s))-
     dslope (fun w=>Φ w*(x:ℂ)^w) 0 s with hg
 have a5h:(x:ℂ)≠0:=by exact_mod_cast tp.ne'
 have hDd:DifferentiableOn ℂ (dslope (fun w=>Φ w*(x:ℂ)^w) 0) U:=by
  have h0U:U∈𝓝 (0:ℂ):=hUo.mem_nhds (hKU h0K)
  apply (differentiableOn_dslope h0U).mpr
  intro w hw
  exact ((a5f w hw).differentiableAt (hUo.mem_nhds hw) |>.mul
   ((bu).const_cpow (Or.inl a5h))).differentiableWithinAt
 have hgd:DifferentiableOn ℂ g K:=by
  intro w hw
  apply qr
  ·apply DifferentiableWithinAt.neg
   apply c3
   apply mj
   intro p _
   exact ((z3 tp p w).sub (z3 tp 0 w)).const_mul _
  ·exact ((hDd w (hKU hw)).differentiableAt (hUo.mem_nhds (hKU hw))).differentiableWithinAt
 set r:ℂ->ℂ:=fun q=>if q=0 then (∑ p∈P',a p/p)-Φ 0
     else -(a q*(x:ℂ)^q/q) with hr
 have ah5:=bt.cz.tx.w7
  (f:=fun s=>-logDeriv riemannZeta s*((x:ℂ)^s/s)) (g:=g)
  (a:=-1/2) (b:=c) (c:=-T') (d:=T') (insert 0 P') r
  (by
   intro p hp
   rw[fv] at hp
   rcases hp with rfl | hp
   ·exact ⟨by norm_num,by norm_num <;> linarith,by norm_num <;> linarith,
     by norm_num <;> linarith⟩
   rw[hP',fv] at hp
   rcases hp with rfl | hp
   ·exact ⟨by norm_num,by norm_num <;> linarith,by norm_num <;> linarith,
     by norm_num <;> linarith⟩
   ·obtain ⟨h0,tu,um⟩:=akz p hp
    have h1:=ts h0
    have:=abs_lt.mp um
    exact ⟨by linarith,by linarith,this.1,this.2⟩)
  (hgd.continuousOn)
  (by
   intro s hs hsP
   rw[fv,not_or] at hsP
   rw[hld s hs hsP.2]
   exact afo P' aou a Φ hsP.1 hsP.2)
 rw[bt.cz.tx.yl hgd,jy] at ah5
 rw[ah5]
 have hl0:logDeriv riemannZeta 0=-(∑ p∈P',a p/p)+Φ 0:=by
  rw[hld 0 h0K aou]
  simp only[zero_sub,ss,kc]
 have a1a:∑ q∈insert 0 P',r q=
   ((∑ p∈P',a p/p)-Φ 0)+∑ q∈P',-(a q*(x:ℂ)^q/q):=by
  rw[ic aou]
  simp only[hr,if_pos rfl]
  congr 1
  apply ai rfl
  intro q hq
  rw[if_neg (fun (h:q=0)=>aou (h ▸ hq))]
 have ayn:∑ q∈P',-(a q*(x:ℂ)^q/q)=
   (x:ℂ)-∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ:=by
  rw[hP',ic h1Z]
  simp only[ha,if_pos rfl,cpow_one]
  have:∀ ρ∈Z,-((if ρ=1 then (-1:ℂ) else (analyticOrderNatAt riemannZeta ρ:ℂ))*
    (x:ℂ)^ρ/ρ)=-((analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ):=by
   intro ρ s8
   rw[if_neg (fun (h:ρ=1)=>h1Z (h ▸ s8))]
  rw[ai rfl this,kc]
  ring
 rw[a1a,ayn,hl0]
 ring
end bt.cz.uk
namespace bt.cz.uk
open Complex Set Filter Topology Metric bt.cz.vj
open scoped Real Interval
lemma ac8 {x:ℝ} (hx:1<x) {τ a b B:ℝ} (u0:τ≠0) (hab:a<=b) (hB:0<=B)
  (hbound:∀ σ∈Icc a b,‖logDeriv riemannZeta ((σ:ℂ)+τ*I)‖<=B):
  ‖∫ σ:ℝ in a..b,-logDeriv riemannZeta ((σ:ℂ)+τ*I)*
      ((x:ℂ)^((σ:ℂ)+τ*I)/((σ:ℂ)+τ*I))‖<=B*x^b/(|τ| *aa x):=by
 have tp:0<x:=by linarith
 have hL:0<aa x:=eo hx
 have ar2:0< |τ|:=ue.mpr u0
 calc _<=∫ σ in a..b,B*(x^σ/|τ|):=by
       apply fc hab
       ·refine Eventually.of_forall (fun σ hσ=>?_)
        rw[bo,norm_neg]
        have h1:=hbound σ ⟨hσ.1.le,hσ.2⟩
        have h2:=bt.cz.tx.uo tp ((σ:ℂ)+τ*I) |τ| ar2 (by
         have:=a6 ((σ:ℂ)+τ*I); simpa using this)
        simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,
         i3,ij] at h2
        exact a8 h1 h2 (aw _) hB
       ·exact (((dm.rpow ps fun _=>Or.inl tp.ne').div_const
         _).const_mul B).intervalIntegrable _ _
  _ = B/|τ| *((x^b-x^a)/aa x):=by
      rw[<- bt.cz.tx.zg tp (by linarith) a b,
       <- cv]
      congr 1; funext σ; ring
  _ ≤ B*x^b/(|τ| *aa x):=by
      have:0<=x^a:=by positivity
      rw[div_mul_div_comm]
      apply a4 _ (by positivity)
      exact ab (by linarith) hB
lemma y9 {t:ℝ} (ht:4<=|t|):
  ((∑ ρ∈(ta t).toFinset,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)<=
   12*aa (1800*t^2):=by
 have h:∑ᶠ ρ∈wg t,(analyticOrderNatAt riemannZeta ρ:ℝ)<=
   12*aa (1800*t^2):=z7 ht
 rw[bf _ (ta t)] at h
 push_cast; exact h
lemma xf {t:ℝ} (ht:4<=|t|) {s:ℂ}
  (hs:s∈closedBall ((3/2:ℂ)+t *I) 2) (zt:riemannZeta s≠0) {δ:ℝ} (uf:0<δ)
  (hd:∀ ρ∈(ta t).toFinset,δ<=‖s-ρ‖):
  ‖logDeriv riemannZeta s‖<=12*aa (1800*t^2)/δ+13100*aa (1800*t^2)
   + 421:=by
 have hL:=adg ht hs zt
 have hsum:‖∑ ρ∈(ta t).toFinset,
   (analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖<=12*aa (1800*t^2)/δ:=by
  calc _<=∑ ρ∈(ta t).toFinset,‖(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖:=
        c5 _ _
   _ ≤ ∑ ρ∈(ta t).toFinset,(analyticOrderNatAt riemannZeta ρ:ℝ)/δ:=by
       apply ao
       intro ρ s8
       rw[i4,gf]
       exact bb (av _) uf (hd ρ s8)
   _ = ((∑ ρ∈(ta t).toFinset,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)/δ:=by
       rw[<- ew]; push_cast; rfl
   _ ≤ 12*aa (1800*t^2)/δ:=
       a4 (y9 ht) uf.le
 calc ‖logDeriv riemannZeta s‖<=‖logDeriv riemannZeta s-∑ ρ∈(ta t).toFinset,
       (analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖+‖∑ ρ∈(ta t).toFinset,
       (analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖:=norm_le_norm_sub_add _ _
  _<=_:=by linarith
lemma aa8 {t:ℝ} {ρ:ℂ} (s8:ρ∈wg t):0<ρ.re∧ρ.re<1:=by
 obtain ⟨h0,hb⟩:=s8
 rw[dj,b8] at hb
 have:=cm (ρ-((3/2:ℂ)+t *I))
 simp at this
 have h1:=(abs_le.mp (this.trans hb)).1
 exact ⟨ab8 h0 (by linarith),ts h0⟩
lemma ag0 {t:ℝ} {ρ:ℂ} (s8:ρ∈wg t):|ρ.im-t|<=11/5:=by
 obtain ⟨-,hb⟩:=s8
 rw[dj,b8] at hb
 have:=a6 (ρ-((3/2:ℂ)+t *I))
 simp at this
 linarith
lemma afp {t:ℝ} (ht:4<=|t|):
  ‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖<=
   24*aa (1800*t^2)+13100*aa (1800*t^2)+421:=by
 set s:ℂ:=((-1/2:ℝ):ℂ)+t *I with hs
 have hsb:s∈closedBall ((3/2:ℂ)+t *I) 2:=by
  rw[dj,b8,hs]
  have:((-1/2:ℝ):ℂ)+t *I-((3/2:ℂ)+t *I)=-2:=by push_cast; ring
  rw[this]; simp
 have zt:riemannZeta s≠0:=
  bt.cz.zh.u4 (by simp[hs]; norm_num) (by simp[hs]; norm_num)
 have h:=xf ht hsb zt (δ:=1/2) (by norm_num) (by
  intro ρ s8
  rw[an] at s8
  have tu:=(aa8 s8).1
  have:=cm (s-ρ)
  have e:(s-ρ).re=-1/2-ρ.re:=by simp[hs]
  rw[e,g5 (by linarith)] at this
  linarith)
 have e:12*aa (1800*t^2)/(1/2)=24*aa (1800*t^2):=by ring
 linarith
lemma afq:∃ uh:ℝ,0<=uh∧∀ t∈Icc (-4:ℝ) 4,
  ‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖<=uh:=by
 have wv:ContinuousOn (fun t:ℝ=>‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖)
   (Icc (-4) 4):=by
  intro t _
  apply ie
  apply ContinuousAt.norm
  set s:ℂ:=((-1/2:ℝ):ℂ)+t *I with hs
  have uu:s≠1:=by intro h; have:=dy re h; simp[hs] at this; norm_num at this
  have zt:riemannZeta s≠0:=
   bt.cz.zh.u4 (by simp[hs]; norm_num)
    (by simp[hs]; norm_num)
  have hA:=u7 uu
  have hc:ContinuousAt (fun z=>deriv riemannZeta z/riemannZeta z) s:=
   hA.deriv.continuousAt.div hA.continuousAt zt
  exact hc.comp (f:=fun t:ℝ=>((-1/2:ℝ):ℂ)+t *I) (by fun_prop)
 obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn wv
 refine ⟨max K 0,cd _ _,fun t ht=>?_⟩
 have:=hK t ht
 rw[norm_norm] at this
 exact this.trans (bq _ _)
lemma ak0 {x T' Bl:ℝ} (hx:1<x) (z1:0<=T') (hBl:0<=Bl)
  (hbound:∀ t∈Icc (-T') T',‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖<=Bl):
  ‖∫ t:ℝ in (-T')..T',-logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)*
      ((x:ℂ)^(((-1/2:ℝ):ℂ)+t *I)/(((-1/2:ℝ):ℂ)+t *I))‖<=
   4*Bl*x^(-1/2:ℝ)*(aa (1/2+T')-aa (1/2)):=by
 have tp:0<x:=by linarith
 set K:ℝ:=2*Bl*x^(-1/2:ℝ) with hK
 have ya:0<=K:=by positivity
 set g:ℝ->ℝ:=fun t=>K/(1/2+|t|) with hg
 have hgc:Continuous g:=by
  apply Continuous.div dm (by fun_prop)
  intro t; positivity
 have wu:∀ t∈Icc (-T') T',‖-logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)*
   ((x:ℂ)^(((-1/2:ℝ):ℂ)+t *I)/(((-1/2:ℝ):ℂ)+t *I))‖<=g t:=by
  intro t ht
  rw[bo,norm_neg]
  have h1:=cm (((-1/2:ℝ):ℂ)+t *I)
  have h2:=a6 (((-1/2:ℝ):ℂ)+t *I)
  simp at h1 h2
  have h3:=bt.cz.tx.uo tp (((-1/2:ℝ):ℂ)+t *I)
   ((1/2+|t|)/2) (by positivity) (by norm_num at h1 ⊢; linarith)
  simp only[add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,di,i3,
   ij] at h3
  calc _<=Bl*(x^(-1/2:ℝ)/((1/2+|t|)/2)):=
        a8 (hbound t ht) h3 (aw _) hBl
   _=g t:=by simp only[hg,hK]; field_simp
 have hint:∫ t in (-T')..T',g t=2*(K*(aa (1/2+T')-aa (1/2))):=by
  rw[<- gz (b:=0) (hgc.intervalIntegrable _ _)
   (hgc.intervalIntegrable _ _)]
  have h1:= oc (a:=0) (b:=T') g
  simp only[sg] at h1
  rw[<- h1]
  have e1:∫ t in (0:ℝ)..T',g (-t)=∫ t in (0:ℝ)..T',K/(1/2+t):=by
   apply ia
   intro t ht
   rw[uIcc_of_le z1] at ht
   simp only[hg,j1,bh ht.1]
  have e2:∫ t in (0:ℝ)..T',g t=∫ t in (0:ℝ)..T',K/(1/2+t):=by
   apply ia
   intro t ht
   rw[uIcc_of_le z1] at ht
   simp only[hg,bh ht.1]
  rw[e1,e2,bt.cz.tx.ym (by norm_num) z1]
  ring
 calc _<=∫ t in (-T')..T',g t:=by
       apply fc (by linarith)
       ·exact Eventually.of_forall (fun t ht=>wu t ⟨ht.1.le,ht.2⟩)
       ·exact hgc.intervalIntegrable _ _
  _ = 4*Bl*x^(-1/2:ℝ)*(aa (1/2+T')-aa (1/2)):=by
      rw[hint,hK]; ring
lemma ar3 {x T':ℝ} (hx:1<x):
  ∫ t : ℝ in (-T')..T',-logDeriv riemannZeta ((bt.cz.tx.ui x:ℂ)+t *I)*
      ((x:ℂ)^((bt.cz.tx.ui x:ℂ)+t *I)/
       ((bt.cz.tx.ui x:ℂ)+t *I))=
   ∫ t:ℝ in (-T')..T',LSeries (fun n=>(ph n:ℂ))
    ((bt.cz.tx.ui x:ℂ)+t *I)*
    ((x:ℂ)^((bt.cz.tx.ui x:ℂ)+t *I)/
     ((bt.cz.tx.ui x:ℂ)+t *I)):=by
 apply ia
 intro t _
 have hc:= y4 hx
 have hs:1<((bt.cz.tx.ui x:ℂ)+t *I).re:=by simp; linarith
 simp only
 rw[ka hs,g9,p9]
end bt.cz.uk
namespace bt.cz.uk
open Complex Set Filter Topology Metric bt.cz.vj
open scoped Real Interval
lemma afr (t:ℝ):
  ((ta t).toFinset.card:ℝ)<=
   ((∑ ρ∈(ta t).toFinset,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ):=by
 have:(ta t).toFinset.card<=
   ∑ ρ∈(ta t).toFinset,analyticOrderNatAt riemannZeta ρ:=by
  rw[Finset.card_eq_sum_ones]
  apply ao
  intro ρ s8
  rw[an] at s8
  have h0:=s8.1
  have h1:ρ≠1:=fun h=>se (h ▸ h0)
  exact one_le_mult h1 h0
 exact_mod_cast this
lemma wy {ρ:ℂ} {t:ℝ} (h0:riemannZeta ρ=0) (tu:0<ρ.re) (w0:ρ.re<1)
  (um:|ρ.im-t|<=1/2):ρ∈wg t:=by
 refine ⟨h0, ?_⟩
 rw[dj,b8]
 have zr:‖ρ-((3/2:ℂ)+t *I)‖^2=(ρ.re-3/2)^2+(ρ.im-t)^2:=by
  rw[Complex.sq_norm,jl]; simp; ring
 have h1:(ρ.re-3/2)^2<=9/4:=by nlinarith
 have h2:(ρ.im-t)^2<=1/4:=by
  rw[<- sq_abs]; nlinarith[eg (ρ.im-t)]
 nlinarith[aw (ρ-((3/2:ℂ)+t *I))]
def ak1 (T:ℝ):Set ℂ:=
 {ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧T-3<=|ρ.im|∧|ρ.im|<=T+4}
lemma za (T:ℝ):(ak1 T).Finite:=by
 apply ((isCompact_closedBall (0:ℂ) (T+5)).inter_riemannZetaZeros_finite).subset
 rintro ρ ⟨h0,tu,-,um⟩
 refine ⟨?_,h0⟩
 rw[dj,l9]
 have h1:=ts h0
 have:=b6 ρ
 rw[a7 tu] at this
 linarith
lemma ayp {T:ℝ} (hT:10<=T):
  ((za T).toFinset.card:ℝ)<=192*aa (1800*(T+4)^2):=by
 classical
 set tk:ℕ->ℝ:=fun k=>T-3+k with htk
 set C:Finset ℂ:=(bk 8).biUnion
  (fun k=>(ta (tk k)).toFinset ∪ (ta (-(tk k))).toFinset) with hC
 have uj:(za T).toFinset ⊆ C:=by
  intro ρ s8
  rw[an] at s8
  obtain ⟨h0,tu,x8,hu2⟩:=s8
  have w0:=ts h0
  set u:=|ρ.im| with hu
  set v:=u-(T-3)+1/2 with hv
  have hv0:0<=v:=by linarith
  set k:=⌊v⌋₊ with hk
  have x1:(k:ℝ)<=v:=ju hv0
  have hk2:v<k+1:=g8 v
  have hk8:k<8:=by
   have:v<8:=by linarith
   exact (Nat.floor_lt hv0).mpr (by exact_mod_cast this)
  have aat:|u-tk k|<=1/2:=by
   simp only[htk]; rw[abs_le]; constructor <;> linarith
  rw[hC,l5]
  refine ⟨k,bw.mpr hk8, ?_⟩
  rw[p0,an,an]
  rcases ig 0 ρ.im with um | um
  ·left
   apply wy h0 tu w0
   rw[hu,bh um] at aat; exact aat
  ·right
   apply wy h0 tu w0
   rw[hu,g5 um] at aat
   rw[show ρ.im- -tk k=-(-ρ.im-tk k) by ring,j1]; exact aat
 have hL:∀ k∈bk 8,∀ t:ℝ,|t|=tk k->
   ((ta t).toFinset.card:ℝ)<=12*aa (1800*(T+4)^2):=by
  intro k hk t ht
  have hk':(k:ℝ)<=7:=by
   have:=bw.mp hk; exact_mod_cast nc.mp this
  have beu:7<=tk k:=by simp only[htk]; have:(0:ℝ)<=k:=av k; linarith
  have ht4:4<=|t|:=by rw[ht]; linarith
  refine (afr t).trans ((y9 ht4).trans ?_)
  have:1800*t^2<=1800*(T+4)^2:=by
   have h1:t^2=(tk k)^2:=by rw[<- sq_abs,ht]
   have h2:tk k<=T+4:=by simp only[htk]; linarith
   rw[h1]; nlinarith
  have tj:0<1800*t^2:=by
   have h:0< |t|:=by linarith
   have:0<t^2:=by rw[<- sq_abs]; exact fb h 2
   linarith
  have:=a5 tj this
  linarith
 calc ((za T).toFinset.card:ℝ)<=(C.card:ℝ):=by
       exact_mod_cast cf uj
  _ ≤ ∑ k∈bk 8,(((ta (tk k)).toFinset ∪
        (ta (-(tk k))).toFinset).card:ℝ):=by
      rw[hC]; exact_mod_cast kd
  _ ≤ ∑ k∈bk 8,(24*aa (1800*(T+4)^2)):=by
      apply ao
      intro k hk
      have hA:=hL k hk (tk k) (a7 (by simp only[htk]; have:(0:ℝ)<=k:=av k; linarith))
      have hB:=hL k hk (-(tk k)) (by rw[j1]; exact a7 (by simp only[htk]; have:(0:ℝ)<=k:=av k; linarith))
      have:=r8 (ta (tk k)).toFinset (ta (-(tk k))).toFinset
      have:(((ta (tk k)).toFinset ∪ (ta (-(tk k))).toFinset).card:ℝ)<=
        ((ta (tk k)).toFinset.card:ℝ)+((ta (-(tk k))).toFinset.card:ℝ):=by
       exact_mod_cast this
      linarith
  _=192*aa (1800*(T+4)^2):=by simp; ring
lemma aqs {T:ℝ} (hT:10<=T):∃ T'∈Icc T (T+1),∀ ρ∈ak1 T,
  1/(2*(192*aa (1800*(T+4)^2)+1))<=abs (T'-|ρ.im|):=by
 classical
 set G:Finset ℝ:=(za T).toFinset.image (fun ρ=>|ρ.im|) with hG
 obtain ⟨T',z1,xp⟩:=bt.cz.zh.afn G T
 refine ⟨T',z1,fun ρ s8=>?_⟩
 have u3:|ρ.im|∈G:=cr.mpr ⟨ρ,(an _).mpr s8,rfl⟩
 refine br ?_ (xp _ u3)
 have aa0:(G.card:ℝ)<=192*aa (1800*(T+4)^2):=by
  refine br ?_ (ayp hT)
  exact_mod_cast Finset.card_image_le
 apply dr (by positivity)
 linarith
lemma ah7 {T T' t:ℝ} (z1:T'∈Icc T (T+1)) (ht:|t|=T') {ρ:ℂ}
  (s8:ρ∈wg t):ρ∈ak1 T:=by
 have h1:=ag0 s8
 have h2:=(aa8 s8).1
 refine ⟨s8.1,h2, ?_, ?_⟩
 ·have:=de t ρ.im
  rw[jj] at h1
  linarith[z1.1]
 ·have:=de ρ.im t
  linarith[z1.2]
lemma acy {T T' δ:ℝ} (hT:10<=T) (z1:T'∈Icc T (T+1)) (uf:0<δ)
  (xp:∀ ρ∈ak1 T,δ<=abs (T'-|ρ.im|)) {τ:ℝ} (u0:|τ|=T') {σ:ℝ}
  (abi:-1/2<=σ) (an7:σ<=7/2):
  ‖logDeriv riemannZeta ((σ:ℂ)+τ*I)‖<=
   12*aa (1800*τ^2)/δ+13100*aa (1800*τ^2)+421:=by
 have afh:4<=|τ|:=by rw[u0]; linarith[z1.1]
 set s:ℂ:=(σ:ℂ)+τ*I with hs
 have hsb:s∈closedBall ((3/2:ℂ)+τ*I) 2:=by
  rw[dj,b8]
  have:s-((3/2:ℂ)+τ*I)=((σ-3/2:ℝ):ℂ):=by rw[hs]; push_cast; ring
  rw[this,ba,au,abs_le]; constructor <;> linarith
 have hd:∀ ρ∈wg τ,δ<=‖s-ρ‖:=by
  intro ρ s8
  have hW:=ah7 z1 u0 s8
  have h1:=xp ρ hW
  have h2:=a6 (s-ρ)
  have e:(s-ρ).im=τ-ρ.im:=by simp[hs]
  rw[e] at h2
  have h3:=abs_abs_sub_abs_le_abs_sub τ ρ.im
  rw[u0] at h3
  linarith
 have zt:riemannZeta s≠0:=by
  intro h0
  have u3:s∈wg τ:=⟨h0,closedBall_subset_closedBall (by norm_num) hsb⟩
  have:=hd s u3
  rw[i3,jw] at this
  linarith
 exact xf afh hsb zt uf (fun ρ s8=>hd ρ ((an _).mp s8))
lemma alv {x T:ℝ} (hx:1<x) (hT:10<=T) (D:Finset ℂ)
  (hD:∀ ρ∈D,riemannZeta ρ=0∧0<ρ.re∧T< |ρ.im|∧|ρ.im|<=T+1):
  ‖∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=
   24*aa (1800*(T+1/2)^2)*x/T:=by
 classical
 have tp:0<x:=by linarith
 set A:=(ta (T+1/2)).toFinset
 set B:=(ta (-(T+1/2))).toFinset
 have a5i:D ⊆ A ∪ B:=by
  intro ρ s8
  obtain ⟨h0,tu,h1,h2⟩:=hD ρ s8
  have w0:=ts h0
  rw[p0,an,an]
  rcases ig 0 ρ.im with um | um
  ·left; apply wy h0 tu w0
   rw[bh um] at h1 h2; rw[abs_le]; constructor <;> linarith
  ·right; apply wy h0 tu w0
   rw[g5 um] at h1 h2; rw[abs_le]; constructor <;> linarith
 have vw:∀ ρ∈D,‖(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=
   (analyticOrderNatAt riemannZeta ρ:ℝ)*(x/T):=by
  intro ρ s8
  obtain ⟨h0,tu,h1,-⟩:=hD ρ s8
  have w0:=ts h0
  rw[i4,bo,gf,e9 tp,
   jm]
  apply ab _ (av _)
  have hxr:x^ρ.re<=x:=by
   calc x^ρ.re<=x^(1:ℝ):=al hx.le w0.le
    _=x:=fi x
  have hn:T<=‖ρ‖:=by have:=a6 ρ; linarith
  exact su tp.le hxr (by linarith) hn
 have hmA:=y9 (t:=T+1/2) (by rw[a7 (by linarith)]; linarith)
 have hmB:=y9 (t:=-(T+1/2)) (by rw[j1,a7 (by linarith)]; linarith)
 rw[neg_sq] at hmB
 have a1b:((∑ ρ∈D,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)<=
   24*aa (1800*(T+1/2)^2):=by
  have h1:∑ ρ∈D,analyticOrderNatAt riemannZeta ρ<=
    ∑ ρ∈A ∪ B,analyticOrderNatAt riemannZeta ρ:=
   aq a5i (fun _ _ _=>n5 _)
  have h2:=Finset.sum_union_inter (s₁:=A) (s₂:=B) (f:=fun ρ=>analyticOrderNatAt riemannZeta ρ)
  have h3:∑ ρ∈A ∪ B,analyticOrderNatAt riemannZeta ρ<=
    ∑ ρ∈A,analyticOrderNatAt riemannZeta ρ+∑ ρ∈B,analyticOrderNatAt riemannZeta ρ:=by
   omega
  have h4:((∑ ρ∈D,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)<=
    ((∑ ρ∈A,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)+
     ((∑ ρ∈B,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ):=by
   exact_mod_cast h1.trans h3
  linarith
 calc ‖∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖
   <= ∑ ρ∈D,‖(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖:=c5 _ _
  _<=∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℝ)*(x/T):=ao vw
  _ = ((∑ ρ∈D,analyticOrderNatAt riemannZeta ρ:ℕ):ℝ)*(x/T):=by
      rw[<- g3]; push_cast; rfl
  _ ≤ 24*aa (1800*(T+1/2)^2)*(x/T):=
      ag a1b (by positivity)
  _=24*aa (1800*(T+1/2)^2)*x/T:=by ring
end bt.cz.uk
namespace bt.cz.uk
open Complex Set Filter Topology Metric bt.cz.vj
open scoped Real Interval
def a5j (T:ℝ):Set ℂ:={ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T}
lemma tw (T:ℝ):(a5j T).Finite:=by
 apply ((isCompact_closedBall (0:ℂ) (T+1)).inter_riemannZetaZeros_finite).subset
 rintro ρ ⟨h0,tu,um⟩
 refine ⟨?_,h0⟩
 rw[dj,l9]
 have h1:=ts h0
 have:=b6 ρ
 rw[a7 tu] at this
 linarith
lemma afs {x:ℝ} (hx:1<=x) (F:Finset ℂ)
  (hF:∀ ρ∈F,riemannZeta ρ=0∧0<ρ.re):
  ‖∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=
   x*∑ ρ∈F,(analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖:=by
 have tp:0<x:=by linarith
 refine (c5 _ _).trans ?_
 rw[bc]
 apply ao
 intro ρ s8
 obtain ⟨h0,tu⟩:=hF ρ s8
 have w0:=ts h0
 rw[i4,bo,gf,e9 tp]
 have hxr:x^ρ.re<=x:=by
  calc x^ρ.re<=x^(1:ℝ):=al hx w0.le
   _=x:=fi x
 have hn:0<‖ρ‖:=g7.mpr (fun h=>by rw[h] at tu; simp at tu)
 calc (analyticOrderNatAt riemannZeta ρ:ℝ)*x^ρ.re/‖ρ‖
   <= (analyticOrderNatAt riemannZeta ρ:ℝ)*x/‖ρ‖:=by gcongr
  _=x*((analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖):=by ring
lemma ag1 {x:ℝ} (hx:10<=x):2<=aa x:=by
 rw[d5 (by linarith)]
 have he:=f7
 have:af 2=af 1*af 1:=by rw[<- bs]; norm_num
 rw[this]
 have h0:=bx 1
 nlinarith
lemma aaq {x y:ℝ} (hx:10<=x) (hy:1<=y) (hyx:y<=2*x):
  aa (1800*y^2)<=7*aa x:=by
 have hl:=ag1 hx
 have h1:aa (1800*y^2)<=aa (7200*x^2):=
  a5 (by positivity) (by nlinarith)
 have h2:aa (7200*x^2)=aa 7200+2*aa x:=by
  rw[ca (by norm_num) (by positivity),cq]; push_cast; ring
 have h3:aa 7200<9:=by
  rw[m6 (by norm_num)]
  have he:=i9
  have:af 9=af 1^9:=by rw[<- db]; norm_num
  rw[this]
  have:(2.7182818283:ℝ)^9<=af 1^9:=aj (by norm_num) he.le 9
  have:(7200:ℝ)<(2.7182818283:ℝ)^9:=by norm_num
  linarith
 linarith
lemma ag2:aa 5<2:=by
 rw[m6 (by norm_num)]
 have he:=i9
 have:af 2=af 1*af 1:=by rw[<- bs]; norm_num
 rw[this]; nlinarith
lemma ak2 {x:ℝ} (hx:1<x):
  x^bt.cz.tx.ui x=af 1*x:=by
 have tp:0<x:=by linarith
 have hL:0<aa x:=eo hx
 unfold bt.cz.tx.ui
 rw[c9 tp,ud,di,kh hL.ne',bs,
  fl tp]; ring
set_option maxHeartbeats 4000000 in
theorem a1c {uh:ℝ} (aa9:0<=uh)
  (ak3:∀ t∈Icc (-4:ℝ) 4,‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖<=uh)
  {x T:ℝ} (hx:2<=x) (hT:10<=T) (hTx:T<=x):
  ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+∑ ρ∈(tw T).toFinset,
      (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=
   (2700000+8*uh+7*‖logDeriv riemannZeta 0‖)*x*aa x^2/T:=by
 classical
 have aov:10<=x:=br hT hTx
 have x2:1<x:=by linarith
 have tp:0<x:=by linarith
 set tz:=aa x with ayq
 have ajg:2<=tz:=ag1 aov
 have ua:0<T:=by linarith
 set Q:ℝ:=x*tz^2/T with hQ
 have hxT:1<=x/T:=by rw[bl ua]; linarith
 have bc4:(4:ℝ)<=tz^2:=by
  rw[sq]; exact br (by norm_num) (a8 ajg ajg (by norm_num) (by linarith))
 have aqt:2*tz<=tz^2:=by
  rw[sq]; exact ag ajg (by linarith)
 have hQ1:tz^2<=Q:=by
  rw[hQ,gx x,jm]
  have:=ab hxT (c4 tz)
  linarith
 have hQ4:4<=Q:=by linarith
 obtain ⟨T',ak4,xp⟩:=aqs hT
 set ar4:=aa (1800*(T+4)^2) with bc5
 have bav:0<=ar4:=bd (by
  have:(1:ℝ)<=(T+4)^2:=dx (by linarith)
  linarith)
 set δ0:ℝ:=1/(2*(192*ar4+1)) with ahu
 have ab0:0<δ0:=by positivity
 have ar5:T<=T':=ak4.1
 have bev:T'<=T+1:=ak4.2
 have ah8:0<T':=by linarith
 set c:=bt.cz.tx.ui x with hc
 have hc1:1<c:= y4 x2
 have hc2:c<=3/2:=by
  rw[hc]; unfold bt.cz.tx.ui
  rw[<- ayq]
  have:1/tz<=1/2:=dr (by norm_num) ajg
  linarith
 set Z':=(tw T').toFinset with hZ'
 have a1d:∀ ρ:ℂ,riemannZeta ρ=0->0<ρ.re->|ρ.im|≠T':=by
  intro ρ h0 tu heq
  have hW:ρ∈ak1 T:=⟨h0,tu,by linarith,by linarith⟩
  have:=xp ρ hW
  rw[heq,i3,abs_zero] at this
  linarith
 have akz:∀ ρ∈Z',riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<T':=by
  intro ρ s8
  rw[hZ',an] at s8
  exact ⟨s8.1,s8.2.1,lt_of_le_of_ne s8.2.2 (a1d ρ s8.1 s8.2.1)⟩
 have aot:∀ ρ,riemannZeta ρ=0->0<ρ.re->|ρ.im|<=T'->ρ∈Z':=by
  intro ρ h0 tu um
  rw[hZ',an]; exact ⟨h0,tu,um⟩
 have acp:=ai4 x2 ah8 Z' akz aot
 simp only[bt.cz.tx.va] at acp
 set Bot:=∫ σ:ℝ in (-1/2)..c,-logDeriv riemannZeta ((σ:ℂ)+((-T':ℝ):ℂ)*I)*
     ((x:ℂ)^((σ:ℂ)+((-T':ℝ):ℂ)*I)/((σ:ℂ)+((-T':ℝ):ℂ)*I)) with bew
 set Top:=∫ σ:ℝ in (-1/2)..c,-logDeriv riemannZeta ((σ:ℂ)+(T':ℂ)*I)*
     ((x:ℂ)^((σ:ℂ)+(T':ℂ)*I)/((σ:ℂ)+(T':ℂ)*I)) with bex
 set R:=∫ t:ℝ in (-T')..T',-logDeriv riemannZeta ((c:ℂ)+t *I)*
     ((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)) with hR
 set Lf:=∫ t:ℝ in (-T')..T',-logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)*
     ((x:ℂ)^(((-1/2:ℝ):ℂ)+t *I)/(((-1/2:ℝ):ℂ)+t *I)) with hLf
 set wh:=logDeriv riemannZeta 0 with bc6
 set Sz:=∑ ρ∈Z',(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ with hSz
 have abd:2*(π:ℂ)*(((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz)=
   -(R-2*π*((Chebyshev.psi x:ℝ):ℂ))-2*π*wh+I*Bot-I*Top+Lf:=by
  linear_combination (-I)*acp+(R-Lf-2*π*((x:ℂ)-Sz-wh))*I_mul_I
 have hL':aa (1800*T'^2)<=7*tz:=aaq aov (by linarith) (by linarith)
 have bey:0<=aa (1800*T'^2):=bd (by
  have:(1:ℝ)<=T'^2:=dx (by linarith)
  linarith)
 have bax:ar4<=7*tz:=aaq aov (by linarith) (by linarith)
 have ayr:1/δ0<=2690*tz:=by
  rw[ahu,one_div_one_div]; linarith
 set Bh:ℝ:=12*aa (1800*T'^2)/δ0+13100*aa (1800*T'^2)+421
  with hBh
 have ays:0<=Bh:=by positivity
 have ayt:Bh<=320000*tz^2:=by
  have h1:12*aa (1800*T'^2)/δ0<=12*(7*tz)*(2690*tz):=by
   rw[jd]
   apply a8 (by linarith) ayr (by positivity) (by positivity)
  rw[hBh]; linarith
 have ayu:∀ τ:ℝ,|τ|=T'->∀ σ∈Icc (-1/2:ℝ) c,
   ‖logDeriv riemannZeta ((σ:ℂ)+τ*I)‖<=Bh:=by
  intro τ u0 σ hσ
  have:=acy hT ak4 ab0 xp u0 hσ.1 (by linarith[hσ.2])
  have e:τ^2=T'^2:=by rw[<- sq_abs,u0]
  rw[e] at this; exact this
 have hxc:x^c<=3*x:=by
  rw[hc,ak2 x2]
  have:=f7
  exact ag (by linarith) tp.le
 have at2:∀ τ:ℝ,|τ|=T'->Bh*x^c/(|τ| *tz)<=960000*Q:=by
  intro τ u0
  rw[u0]
  have baz:0<tz:=by linarith
  have xo:0<T'*tz:=by positivity
  have h1:Bh*x^c<=960000*x*tz^2:=by
   have:=a8 ayt hxc (by positivity) (by positivity)
   linarith
  have hxl:960000*x*tz<=960000*x*tz^2:=by
   have:=ab (show tz<=tz^2 by linarith) tp.le
   linarith
  calc Bh*x^c/(T'*tz)<=960000*x*tz^2/(T'*tz):=
        a4 h1 xo.le
   _=960000*x*tz/T':=by field_simp
   _<=960000*x*tz/T:=bb (by positivity) ua ar5
   _<=960000*x*tz^2/T:=a4 hxl ua.le
   _=960000*Q:=by rw[hQ]; ring
 have bc7:‖Bot‖<=960000*Q:=by
  have:=ac8 x2 (τ:=-T') (a:=-1/2) (b:=c) (B:=Bh) (by linarith)
   (by linarith) ays (ayu (-T') (by rw[j1,a7 ah8]))
  exact this.trans (at2 (-T') (by rw[j1,a7 ah8]))
 have bc8:‖Top‖<=960000*Q:=by
  have:=ac8 x2 (τ:=T') (a:=-1/2) (b:=c) (B:=Bh) (by linarith)
   (by linarith) ays (ayu T' (a7 ah8))
  exact this.trans (at2 T' (a7 ah8))
 set Bl:ℝ:=uh+13124*aa (1800*T'^2)+421 with hBl
 have a5k:0<=Bl:=by positivity
 have a1e:∀ t∈Icc (-T') T',‖logDeriv riemannZeta (((-1/2:ℝ):ℂ)+t *I)‖<=Bl:=by
  intro t ht
  by_cases h4:|t|<4
  ·have:=ak3 t ⟨by linarith[(abs_lt.mp h4).1],by linarith[(abs_lt.mp h4).2]⟩
   linarith
  ·push_neg at h4
   have h1:=afp h4
   have h2:aa (1800*t^2)<=aa (1800*T'^2):=by
    apply Real.log_le_log (by have:0< |t|:=by linarith
                              have:0<t^2:=by rw[<- sq_abs]; exact fb this 2
                              linarith)
    have:t^2<=T'^2:=by
     rw[<- sq_abs t]; exact aj (eg _) (abs_le.mpr ⟨ht.1,ht.2⟩) 2
    linarith
   linarith
 have bez:‖Lf‖<=(4*uh+738312)*Q:=by
  have h:=ak0 x2 ah8.le a5k a1e
  have hxh:x^(-1/2:ℝ)<=1:=er x2.le (by norm_num)
  have ur:aa (1/2+T')-aa (1/2)<=2*tz:=by
   rw[<- ik (by linarith) (by norm_num)]
   have h5:aa ((1/2+T')/(1/2))<=aa (5*x):=
    a5 (by positivity) (by rw[ay (by norm_num)]; linarith)
   rw[ca (by norm_num) tp.ne'] at h5
   linarith[ag2]
  have aax:0<=aa (1/2+T')-aa (1/2):=by
   rw[<- ik (by linarith) (by norm_num)]
   exact bd (by rw[bl (by norm_num)]; linarith)
  have ba1:Bl<=uh+92289*tz:=by rw[hBl]; linarith
  calc ‖Lf‖<=4*Bl*x^(-1/2:ℝ)*(aa (1/2+T')-aa (1/2)):=h
   _<=4*Bl*1*(2*tz):=by gcongr
   _<=4*(uh+92289*tz)*1*(2*tz):=by gcongr
   _ ≤ (4*uh+738312)*tz^2:=by
       have:=ab aqt aa9
       linarith
   _<=(4*uh+738312)*Q:=ab hQ1 (by positivity)
 have hRP:‖R-2*π*((Chebyshev.psi x:ℝ):ℂ)‖<=2500*Q:=by
  have h1:R=∫ t:ℝ in (-T')..T',LSeries (fun n=>(ph n:ℂ))
    ((c:ℂ)+t *I)*((x:ℂ)^((c:ℂ)+t *I)/((c:ℂ)+t *I)):=ar3 x2
  rw[h1]
  have h2:=bt.cz.tx.aoq hx (by linarith) (show T'<=2*x by linarith)
  refine h2.trans ?_
  calc 2500*x*aa x^2/T'<=2500*x*aa x^2/T:=
        bb (by positivity) ua ar5
   _=2500*Q:=by rw[hQ,ayq]; ring
 have ba2:‖2*(π:ℂ)*wh‖<=7*‖wh‖*Q:=by
  rw[bo,bo,Complex.norm_ofNat,ba,au,
   a7 du]
  have:=Real.pi_lt_d2
  have h0:=aw wh
  have h1:2*π*‖wh‖<=7*‖wh‖:=ag (by linarith) h0
  have h2:‖wh‖*1<=‖wh‖*Q:=ab (by linarith) h0
  linarith
 have uj:(tw T).toFinset ⊆ Z':=by
  intro ρ s8
  rw[an] at s8
  rw[hZ',an]
  exact ⟨s8.1,s8.2.1,br s8.2.2 ar5⟩
 set D:=Z' \ (tw T).toFinset with hD
 have ayv:∀ ρ∈D,riemannZeta ρ=0∧0<ρ.re∧T< |ρ.im|∧|ρ.im|<=T+1:=by
  intro ρ s8
  rw[hD,Finset.mem_sdiff,hZ',an,an] at s8
  obtain ⟨⟨h0,tu,um⟩,hnot⟩:=s8
  refine ⟨h0,tu, ?_,by linarith⟩
  by_contra hle; push_neg at hle
  exact hnot ⟨h0,tu,hle⟩
 have hDb:=alv x2 hT D ayv
 have be0:24*aa (1800*(T+1/2)^2)*x/T<=84*Q:=by
  have h1:aa (1800*(T+1/2)^2)<=7*tz:=aaq aov (by linarith) (by linarith)
  have h2:24*aa (1800*(T+1/2)^2)*x<=84*(x*tz^2):=by
   have:=ag h1 tp.le
   have h3:=ab aqt tp.le
   linarith
  calc 24*aa (1800*(T+1/2)^2)*x/T<=84*(x*tz^2)/T:=
        a4 h2 ua.le
   _=84*Q:=by rw[hQ]; ring
 have u8:∑ ρ∈(tw T).toFinset,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ
   = Sz-∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ:=by
  rw[hSz,hD,<- Finset.sum_sdiff uj]; ring
 have hE:‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz‖<=
   ‖R-2*π*((Chebyshev.psi x:ℝ):ℂ)‖+‖2*(π:ℂ)*wh‖+‖Bot‖+‖Top‖+‖Lf‖:=by
  have hpi:(1:ℝ)<=‖2*(π:ℂ)‖:=by
   rw[bo,Complex.norm_ofNat,ba,au,
    a7 du]
   have:=jq; linarith
  have hn:=dy norm abd
  rw[bo] at hn
  have hX:‖-(R-2*π*((Chebyshev.psi x:ℝ):ℂ))-2*π*wh+I*Bot-I*Top+Lf‖<=
    ‖R-2*π*((Chebyshev.psi x:ℝ):ℂ)‖+‖2*(π:ℂ)*wh‖+‖Bot‖+‖Top‖+‖Lf‖:=by
   have e1:=ds (-(R-2*π*((Chebyshev.psi x:ℝ):ℂ))-2*π*wh+I*Bot
    - I*Top) Lf
   have e2:=ej (-(R-2*π*((Chebyshev.psi x:ℝ):ℂ))-2*π*wh+I*Bot)
    (I*Top)
   have e3:=ds (-(R-2*π*((Chebyshev.psi x:ℝ):ℂ))-2*π*wh) (I*Bot)
   have e4:=ej (-(R-2*π*((Chebyshev.psi x:ℝ):ℂ))) (2*π*wh)
   rw[norm_neg] at e4
   rw[bo,kr,iq] at e2 e3
   linarith
  have h0:‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz‖<=
    ‖2*(π:ℂ)‖*‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz‖:=
   le_mul_of_one_le_left (aw _) hpi
  linarith
 calc ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+∑ ρ∈(tw T).toFinset,
       (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖
   = ‖(((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz)-
       ∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖:=by
       rw[u8]; ring_nf
  _ ≤ ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+Sz‖+
        ‖∑ ρ∈D,(analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖:=ej _ _
  _ ≤ (2500*Q+7*‖wh‖*Q+960000*Q+960000*Q+(4*uh+738312)*Q)+84*Q:=by
      gcongr
      ·linarith
      ·linarith
  _ ≤ (2700000+8*uh+7*‖logDeriv riemannZeta 0‖)*x*aa x^2/T:=by
      have e:(2700000+8*uh+7*‖wh‖)*x*tz^2/T=
        (2700000+8*uh+7*‖wh‖)*Q:=by rw[hQ]; ring
      rw[e]
      have:0<=uh*Q:=b7 aa9 (by linarith)
      linarith
end bt.cz.uk
namespace bt.cz.uk
open Complex Set Filter Topology Metric bt.cz.vj
open scoped Real Interval
theorem a1f {x T:ℝ} (hx:2<=x) (hT2:2<=T) (hT:T<10):
  ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+∑ ρ∈(tw T).toFinset,
      (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=
   30*(7+∑ ρ∈(tw 10).toFinset,(analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖)*
    x*aa x^2/T:=by
 classical
 have tp:0<x:=by linarith
 have ua:0<T:=by linarith
 set M:=∑ ρ∈(tw 10).toFinset,(analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖ with hM
 have uj:(tw T).toFinset ⊆ (tw 10).toFinset:=by
  intro ρ s8
  rw[an] at s8 ⊢
  exact ⟨s8.1,s8.2.1,br s8.2.2 hT.le⟩
 have ahz:∀ ρ∈(tw 10).toFinset,ρ∉(tw T).toFinset->
   0<=(analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖:=fun _ _ _=>by positivity
 have hM0:0<=M:=cj (fun _ _=>by positivity)
 have hS:‖∑ ρ∈(tw T).toFinset,
   (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=x*M:=by
  refine (afs (by linarith) _ (fun ρ s8=>by
   rw[an] at s8; exact ⟨s8.1,s8.2.1⟩)).trans ?_
  exact ab (aq uj ahz) tp.le
 have hψ:Chebyshev.psi x<=6*x:=by
  have h1:=Chebyshev.psi_le_const_mul_self tp.le
  have h2:aa 4<2:=by
   rw[show (4:ℝ)=2^2 by norm_num,cq]
   have:=Real.log_two_lt_d9; push_cast; linarith
  nlinarith
 have a5l:=Chebyshev.psi_nonneg x
 have acs:‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+∑ ρ∈(tw T).toFinset,
   (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=x*(7+M):=by
  have e1:=ds (((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)) (∑ ρ∈(tw T).toFinset,
   (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ)
  have e2:=ej ((Chebyshev.psi x:ℝ):ℂ) (x:ℂ)
  rw[ba,au,bh a5l,ba,
   au,a7 tp] at e2
  linarith
 have hl:0.69<aa x:=by
  have:=a5 (by norm_num) hx
  have:=f6; linarith
 have hl2:(1:ℝ)<=3*aa x^2:=by nlinarith
 refine acs.trans ?_
 have h3:x*(7+M)<=x*(7+M)*(3*aa x^2):=by
  have:0<=x*(7+M):=by positivity
  nlinarith
 have h4:x*(7+M)*(3*aa x^2)*1<=x*(7+M)*(3*aa x^2)*(10/T):=
  ab (by rw[bl ua]; linarith) (by positivity)
 calc x*(7+M)<=x*(7+M)*(3*aa x^2)*(10/T):=by linarith
  _=30*(7+M)*x*aa x^2/T:=by ring
theorem ar6:∃ C:ℝ,∀ x T:ℝ,2<=x->2<=T->T<=x->
  ‖((Chebyshev.psi x:ℝ):ℂ)-(x:ℂ)+
   ∑ᶠ ρ∈{ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T},
    (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ‖<=C*x*aa x^2/T:=by
 obtain ⟨uh,aa9,ak3⟩:=afq
 set M:=∑ ρ∈(tw 10).toFinset,(analyticOrderNatAt riemannZeta ρ:ℝ)/‖ρ‖
 set CA:ℝ:=30*(7+M)
 set CB:ℝ:=2700000+8*uh+7*‖logDeriv riemannZeta 0‖
 refine ⟨max CA CB,fun x T hx hT hTx=>?_⟩
 have uq:({ρ:ℂ | riemannZeta ρ=0∧0<ρ.re∧|ρ.im|<=T}:Set ℂ).Finite:=tw T
 rw[bf _ uq]
 have tp:0<x:=by linarith
 have ua:0<T:=by linarith
 have tj:0<=x*aa x^2/T:=by positivity
 have u6:∀ C:ℝ,C<=max CA CB->C*x*aa x^2/T<=max CA CB*x*aa x^2/T:=by
  intro C hC
  have:=ag hC tj
  calc C*x*aa x^2/T=C*(x*aa x^2/T):=by ring
   _<=max CA CB*(x*aa x^2/T):=this
   _=max CA CB*x*aa x^2/T:=by ring
 by_cases ar7:T<10
 ·exact (a1f hx hT ar7).trans (u6 CA (bq _ _))
 ·push_neg at ar7
  exact (a1c aa9 ak3 hx ar7 hTx).trans (u6 CB (cd _ _))
end bt.cz.uk
end
section
namespace bt.ar8
open Complex Finset bt.ZD
open scoped Real
def ES (A D:ℕ):Prop:=
 ∃ c:ℝ,0<c∧∃ K:ℝ,∃ w2:ℕ,∃ vd:ℝ,∀ t:ℝ,vd<=t->
  ∀ N N':ℕ,w2<=N->(N:ℝ)<t->N'<=2*N->
   ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*I))‖<=
    af (K/(aa N/aa t)^D)*
     (N:ℝ)^(1-c*(aa N/aa t)^A)
lemma ae6 {n:ℕ} (hn:1<=n) (t:ℝ):
  (n:ℂ)^(-((t:ℂ)*I))=ee (-psi (t/(2*π)) n):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hnc:(n:ℂ)≠0:=by exact_mod_cast t6.ne'
 rw[gq hnc,show (n:ℂ)=((n:ℝ):ℂ) by push_cast; rfl,
  <- j8 t6.le]
 unfold ee psi
 congr 1
 push_cast
 field_simp
lemma ag3 {n:ℕ} (hn:1<=n) (σ t:ℝ):
  1/(n:ℂ)^((σ:ℂ)+t *I)=
   (((n:ℝ)^(-σ):ℝ):ℂ)*ee (-psi (t/(2*π)) n):=by
 have t6:(0:ℝ)<n:=by exact_mod_cast hn
 have hnc:(n:ℂ)≠0:=by exact_mod_cast t6.ne'
 rw[<- ae6 hn,jz,<- Complex.cpow_neg,neg_add,js _ _ hnc,
  lq t6.le]
 push_cast
 rfl
lemma ai5 (f:ℕ->ℂ) (N:ℕ) {uh:ℝ} (aa9:0<=uh)
  (h:∀ p q:ℕ,1<=p->p<=q->q<2*p->q<=N->‖∑ n∈Icc p q,f n‖<=uh):
  ‖∑ n∈Icc 1 N,f n‖<=uh*(ed 2 N+1):=by
 rw[<- cx (g:=fun n=>ed 2 n) (t:=range (ed 2 N+1))
  (by
   intro n hn
   simp only[ar] at hn
   exact bw.mpr (o3 (ja hn.2)))]
 refine (c5 _ _).trans ?_
 have yu:∀ j,‖∑ n∈(Icc 1 N).filter (fun n=>ed 2 n=j),f n‖<=uh:=by
  intro j
  set G:=(Icc 1 N).filter (fun n=>ed 2 n=j) with hG
  rcases G.eq_empty_or_nonempty with he | te
  ·rw[he,k8,jw]; exact aa9
  have y7:∀ a∈G,∀ b∈G,∀ m,a<=m->m<=b->m∈G:=by
   intro a ha b hb m ham hmb
   simp only[hG,ah,ar] at ha hb ⊢
   refine ⟨⟨by omega,by omega⟩, ?_⟩
   have:=ja (b:=2) ham
   have:=ja (b:=2) hmb
   omega
  rw[zo G te y7]
  set p:=G.min' te
  set q:=G.max' te
  have hp:=z6 N j p (G.min'_mem te)
  have hq:=z6 N j q (G.max'_mem te)
  have hpq:p<=q:=G.min'_le _ (G.max'_mem te)
  have hpG:=G.min'_mem te
  have hqG:=G.max'_mem te
  simp only[hG,ah,ar] at hpG hqG
  refine h p q hpG.1.1 hpq ?_ hqG.1.2
  have:2^(j+1)=2*2^j:=by ring
  omega
 calc ∑ j∈range (ed 2 N+1),‖∑ n∈(Icc 1 N).filter (fun n=>ed 2 n=j),f n‖
   <= ∑ j∈range (ed 2 N+1),uh:=ao (fun j _=>yu j)
  _=_:=by rw[a9,fa,cp]; push_cast; ring
lemma y5 {σ:ℝ} (hσ:0<σ) (t:ℝ) {p q:ℕ} (hp:1<=p) (hpq:p<=q) {Kb:ℝ}
  (hW:∀ m,p<=m->m<=q->‖∑ n∈Icc p m,ee (-psi (t/(2*π)) n)‖<=Kb):
  ‖∑ n∈Icc p q,1/(n:ℂ)^((σ:ℂ)+t *I)‖<=(p:ℝ)^(-σ)*Kb:=by
 have vw:∀ n∈Icc p q,1/(n:ℂ)^((σ:ℂ)+t *I)=
   (((n:ℝ)^(-σ):ℝ):ℂ)*ee (-psi (t/(2*π)) n):=by
  intro n hn
  rw[ar] at hn
  exact ag3 (by omega) σ t
 rw[ai rfl vw]
 exact agj (fun n=>(n:ℝ)^(-σ)) (fun n=>ee (-psi (t/(2*π)) n)) hpq
  (fun n _ _=>by positivity)
  (fun n hn _=>by
   have h0:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
   exact c1 h0 (by push_cast; linarith) (by linarith))
  hW
lemma alw {A D:ℕ} (hA:1<=A) {c K M ρ lam:ℝ} (hc:0<c) (hK:0<=K)
  (w6:1<=M) (hMc:2<=c*M) (hMK:2*K<=c*M) (s8:1<=ρ) (hx:M<=ρ*lam):
  K/lam^D+(ρ/ρ^(A+D+1)-c*lam^A)*(lam*ρ^(A+D+1))<=0:=by
 have yw:0<ρ:=by linarith
 have vu:0<lam:=by
  by_contra h
  push Not at h
  nlinarith
 have hE:ρ^(A+D+1)≠0:=by positivity
 set x:=ρ*lam with aa5
 have x2:1<=x:=by linarith
 have e1:ρ/ρ^(A+D+1)*(lam*ρ^(A+D+1))=x:=by
  rw[aa5]; field_simp
 have e2:c*lam^A*(lam*ρ^(A+D+1))=c*x^A*(x*ρ^D):=by
  rw[aa5]; ring
 have e3:K/lam^D=K*ρ^D/x^D:=by
  rw[aa5,i5]
  have:lam^D≠0:=by positivity
  have:ρ^D≠0:=by positivity
  field_simp
 rw[sub_mul,e1,e2,e3]
 have hxD:1<=x^D:=dx x2
 have a5m:1<=ρ^D:=dx s8
 have hxA:x<=x^A:=le_self_pow₀ x2 (by omega)
 have h1:K*ρ^D/x^D<=K*ρ^D:=div_le_self (by positivity) hxD
 have h4:c*x<=c*x^A:=ab hxA hc.le
 have h4':c*M<=c*x:=ab hx hc.le
 set y:=c*x^A
 have hy2:2<=y:=by linarith
 have hyK:2*K<=y:=by linarith
 have ayw:0<=x*ρ^D:=by positivity
 have f1:0<=(y-2)*(x*ρ^D):=b7 (by linarith) ayw
 have f2:0<=(y-2*K)*(x*ρ^D):=b7 (by linarith) ayw
 have f3:0<=K*(x*ρ^D-ρ^D):=b7 hK (by nlinarith)
 have f4:x<=x*ρ^D:=le_mul_of_one_le_right (by linarith) a5m
 nlinarith
lemma aqu {t θ p:ℝ} (ht:1<=t) (hθ:θ<=3/10) (hp:t<=p):
  p^(θ-1)*ak (2000*p*(t^((5:ℕ)⁻¹:ℝ))^2)<=45:=by
 have t8:0<t:=by linarith
 have zc:0<p:=by linarith
 set τ:=t^((5:ℕ)⁻¹:ℝ) with u0
 have vh:0<τ:=dc t8 _
 rw[mv (by positivity),mv (by norm_num),fk vh.le]
 have h45:ak 2000<=45:=by
  calc ak 2000<=ak (45^2):=dg (by norm_num)
   _=45:=fk (by norm_num)
 have e1:p^(θ-1)*ak p=p^(θ-1/2):=by
  rw[ft,<- c6 zc]; congr 1; ring
 have h2:p^(θ-1/2)<=t^(θ-1/2):=
  c1 t8 hp (by linarith)
 have h3:t^(θ-1/2)<=t^(-(1/5:ℝ)):=
  al ht (by linarith)
 have h4:τ*t^(-(1/5:ℝ))=1:=by
  rw[u0,<- c6 t8]; norm_num
 have tj:0<=p^(θ-1/2):=by positivity
 calc p^(θ-1)*(ak 2000*ak p*τ)
   = ak 2000*(τ*(p^(θ-1)*ak p)):=by ring
  _=ak 2000*(τ*p^(θ-1/2)):=by rw[e1]
  _ ≤ 45*(τ*t^(-(1/5:ℝ))):=by
      gcongr
      exact h2.trans h3
  _=45:=by rw[h4,di]
lemma ar9 {A D:ℕ} (hA:1<=A) {c K:ℝ} (hc:0<c) (hK:0<=K) {w2:ℕ} {t:ℝ}
  (hES:∀ N N':ℕ,w2<=N->1<=N->(N:ℝ)<t->N'<=2*N->
   ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*I))‖<=
    af (K/(aa N/aa t)^D)*
     (N:ℝ)^(1-c*(aa N/aa t)^A))
  {M ρ σ:ℝ} (w6:1<=M) (hMc:2<=c*M) (hMK:2*K<=c*M) (s8:1<=ρ)
  (ht:1024<=t) (hL:ρ^(A+D+1)=aa t) (hθ:ρ/aa t<=3/10)
  (hσ:1-ρ/aa t<=σ) {p q:ℕ} (hp:1<=p) (hpq:p<=q) (hq:q<2*p)
  (wu:(p:ℝ)<=2*t^2):
  ‖∑ n∈Icc p q,1/(n:ℂ)^((σ:ℂ)+t *I)‖<=
   max (max 45 (w2:ℝ)) (af M):=by
 have t8:0<t:=by linarith
 have ug:0<aa t:=eo (by linarith)
 have am9:0<=ρ/aa t:=by positivity
 have abl:0<σ:=by linarith
 have zc:(0:ℝ)<p:=by exact_mod_cast hp
 have hp1:(1:ℝ)<=p:=by exact_mod_cast hp
 have hw:(p:ℝ)^(-σ)<=(p:ℝ)^(ρ/aa t-1):=
  al hp1 (by linarith)
 have h45:(45:ℝ)<=max (max 45 (w2:ℝ)) (af M):=
  (bq _ _).trans (bq _ _)
 have aa2:‖∑ n∈Icc p q,1/(n:ℂ)^((σ:ℂ)+t *I)‖<=
   (p:ℝ)^(ρ/aa t):=by
  have:=y5 abl t hp hpq (Kb:=p) (fun m hm1 hm2=>by
   refine (uz (Icc p m) (fun n=>-psi (t/(2*π)) n)).trans ?_
   rw[jv]
   have:m+1-p<=p:=by omega
   exact_mod_cast this)
  refine this.trans ?_
  calc (p:ℝ)^(-σ)*p<=(p:ℝ)^(ρ/aa t-1)*p:=by gcongr
   _=(p:ℝ)^(ρ/aa t):=by
    rw[Real.rpow_sub_one zc.ne']; field_simp
 rcases ig t p with abh | wz
 ·
  have abk:(t^((5:ℕ)⁻¹:ℝ))^5=t:=g2 t8.le (by norm_num)
  have vh:0<t^((5:ℕ)⁻¹:ℝ):=dc t8 _
  have afh:4<=t^((5:ℕ)⁻¹:ℝ):=by
   have:(4:ℝ)^5<=(t^((5:ℕ)⁻¹:ℝ))^5:=by rw[abk]; norm_num; linarith
   exact (d8 (by norm_num) vh.le (by norm_num)).mp this
  have:=y5 abl t hp hpq
   (Kb:=ak (2000*p*(t^((5:ℕ)⁻¹:ℝ))^2)) (fun m hm1 hm2=>by
    have e:∑ n∈Icc p m,ee (-psi (t/(2*π)) n)=
      (starRingEnd ℂ) (∑ n∈Icc p m,ee (psi (t/(2*π)) n)):=by
     rw[m9]; exact ai rfl (fun n _=>adw _)
    rw[e,d4]
    apply ku
    have hb:=abj afh hp hm1 (by omega) (by
     rw[show (t^((5:ℕ)⁻¹:ℝ))^10=((t^((5:ℕ)⁻¹:ℝ))^5)^2 by ring,abk]
     exact wu)
    rw[abk] at hb
    exact hb)
  refine this.trans ((ag hw (df _)).trans ?_)
  exact (aqu (by linarith) hθ abh).trans h45
 rcases si p w2 with hsm | a1g
 ·
  refine aa2.trans ?_
  have h1:(p:ℝ)^(ρ/aa t)<=(p:ℝ)^(1:ℝ):=
   al hp1 (by linarith)
  rw[fi] at h1
  have hpN:(p:ℝ)<=w2:=by exact_mod_cast hsm.le
  exact h1.trans (hpN.trans ((cd _ _).trans (bq _ _)))
 set lam:=aa p/aa t with vu
 have a1h:aa p=lam*ρ^(A+D+1):=by
  rw[hL,vu]; field_simp
 have ayx:ρ/aa t *aa p=ρ*lam:=by rw[vu]; ring
 rcases si (ρ*lam) M with v7 | hge
 ·
  refine aa2.trans ?_
  rw[c9 zc]
  refine (b4.mpr ?_).trans (cd _ _)
  rw[gx,ayx]; exact v7.le
 ·
  have a5n:∀ m,p<=m->m<=q->‖∑ n∈Icc p m,ee (-psi (t/(2*π)) n)‖<=
    1+af (K/lam^D)*(p:ℝ)^(1-c*lam^A):=by
   intro m hm1 hm2
   rw[<- Finset.Ioc_insert_left hm1,ic (by simp)]
   refine (ds _ _).trans (e8 (i6 (w5 _)) ?_)
   have e:∑ n∈Ioc p m,ee (-psi (t/(2*π)) n)=
     ∑ n∈Ioc p m,(n:ℂ)^(-((t:ℂ)*I)):=
    ai rfl (fun n hn=>(ae6 (by simp at hn; omega) t).symm)
   rw[e]
   exact hES p m a1g hp wz (by omega)
  have hKb:0<=1+af (K/lam^D)*(p:ℝ)^(1-c*lam^A):=by positivity
  refine (y5 abl t hp hpq a5n).trans
   ((ag hw hKb).trans ?_)
  have xm:=alw (D:=D) hA hc hK w6 hMc hMK s8 hge
  rw[<- a1h,hL] at xm
  have e3:(p:ℝ)^(ρ/aa t-1)*(p:ℝ)^(1-c*lam^A)=
    af ((ρ/aa t-c*lam^A)*aa p):=by
   rw[<- c6 zc,c9 zc]; congr 1; ring
  have h1:(p:ℝ)^(ρ/aa t-1)<=1:=
   er hp1 (by linarith)
  calc (p:ℝ)^(ρ/aa t-1)*(1+af (K/lam^D)*(p:ℝ)^(1-c*lam^A))
    = (p:ℝ)^(ρ/aa t-1)+af (K/lam^D)*
        ((p:ℝ)^(ρ/aa t-1)*(p:ℝ)^(1-c*lam^A)):=by ring
   _ = (p:ℝ)^(ρ/aa t-1)+
         af (K/lam^D+(ρ/aa t-c*lam^A)*aa p):=by
       rw[e3,bs]
   _ ≤ 1+af 0:=by
       gcongr
   _<=max (max 45 (w2:ℝ)) (af M):=by rw[Real.exp_zero]; linarith
theorem ah9 {A D:ℕ} (hA:1<=A) {c K:ℝ} (hc:0<c) (hK:0<=K) {w2:ℕ}
  {t:ℝ}
  (hES:∀ N N':ℕ,w2<=N->1<=N->(N:ℝ)<t->N'<=2*N->
   ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*I))‖<=
    af (K/(aa N/aa t)^D)*
     (N:ℝ)^(1-c*(aa N/aa t)^A))
  {M ρ σ:ℝ} (w6:1<=M) (hMc:2<=c*M) (hMK:2*K<=c*M) (s8:4<=ρ)
  (ht:1024<=t) (hL:ρ^(A+D+1)=aa t) (hσ:1-ρ/aa t<=σ)
  (be1:σ<=3):
  ‖riemannZeta ((σ:ℂ)+t *I)‖<=
   max (max 45 (w2:ℝ)) (af M)*(4*aa t)+5:=by
 have t8:0<t:=by linarith
 have ug:0<aa t:=eo (by linarith)
 have hθ:ρ/aa t<=1/4:=by
  have h1:ρ<=ρ^(A+D):=le_self_pow₀ (by linarith) (by omega)
  have h2:ρ^(A+D+1)=ρ^(A+D)*ρ:= ob _ _
  rw[ay ug,<- hL,h2]; nlinarith
 set uh:=max (max 45 (w2:ℝ)) (af M) with aa9
 have ak5:0<=uh:=br (by norm_num) ((bq 45 (w2:ℝ)).trans (bq _ _))
 set N:ℕ:=⌈t^2⌉₊ with an5
 have hN1:t^2<=N:=f9 _
 have hN2:(N:ℝ)<t^2+1:=ef (by positivity)
 have ht2:(1:ℝ)<=t^2:=by nlinarith
 have t7:0<N:=by
  have:(0:ℝ)<N:=by linarith
  exact_mod_cast this
 have hNR:(0:ℝ)<N:=by exact_mod_cast t7
 have ayy:(1:ℝ)<=N:=by exact_mod_cast t7
 set s:ℂ:=(σ:ℂ)+t *I with hs
 have wm:s.re=σ:=by simp[hs]
 have afi:s.im=t:=by simp[hs]
 have bc9:3/4<=σ:=by linarith
 have hsU:s∈vn:=⟨by rw[wm]; linarith,by rw[afi]; linarith⟩
 rw[ab2 hsU t7]
 have hsum:∑ k∈range N,1/((k:ℂ)+1)^s=∑ n∈Icc 1 N,1/(n:ℂ)^s:=by
  rw[<- cy,dq,
   show N+1-1=N by omega]
  refine ai rfl (fun k _=>?_)
  push_cast; ring_nf
 have u5:‖∑ k∈range N,1/((k:ℂ)+1)^s‖<=uh*(ed 2 N+1):=by
  rw[hsum]
  refine ai5 _ N ak5 (fun p q hp hpq hq hqN=>?_)
  have hpN:(p:ℝ)<=N:=by exact_mod_cast (hpq.trans hqN)
  exact ar9 hA hc hK hES w6 hMc hMK (by linarith) ht hL (by linarith) hσ hp hpq hq
   (by linarith)
 have a0g:6<=aa t:=by
  have h1:af 6<=1024:=by
   have:=f7
   have e:af 6=af 1^6:=by rw[<- db]; norm_num
   rw[e]
   calc af 1^6<=(2.7182818286:ℝ)^6:=by gcongr
    _<=1024:=by norm_num
  rw[d5 t8]; linarith
 have aay:(2:ℝ)/3<aa 2:=by
  have:=f6; linarith
 have a0h:(ed 2 N:ℝ)*aa 2<=aa 2+2*aa t:=by
  have hp:2^ed 2 N<=N:=n6 2 t7.ne'
  have x6:((2:ℝ)^ed 2 N)<=N:=by exact_mod_cast hp
  have:=a5 (by positivity) x6
  rw[cq] at this
  have an6:(N:ℝ)<=2*t^2:=by nlinarith
  have:=this.trans (a5 hNR an6)
  rw[ca (by norm_num) (by positivity),cq] at this
  push_cast at this; linarith
 have ap3:(ed 2 N:ℝ)+1<=4*aa t:=by
  have h0:(0:ℝ)<=ed 2 N:=by positivity
  have:(ed 2 N:ℝ)<=1+3*aa t:=by
   by_contra hc
   push Not at hc
   have:(1+3*aa t)*aa 2<(ed 2 N:ℝ)*aa 2:=
    sh hc (by linarith)
   nlinarith
  linarith
 have ahv:t<=ak N:=by
  have:ak (t^2)<=ak N:=dg hN1
  rwa[fk t8.le] at this
 have yh:‖(N:ℂ)^(1-s)/(s-1)‖<=1:=by
  rw[i4,norm_natCast_cpow_of_pos t7]
  have tu:(1-s).re=1-σ:=by simp[hs]
  rw[tu]
  have um:t<=‖s-1‖:=by
   have:=a6 (s-1)
   have e:(s-1).im=t:=by simp[hs]
   rw[e,a7 t8] at this; exact this
  have h1:(N:ℝ)^(1-σ)<=(N:ℝ)^((3:ℕ)⁻¹:ℝ):=
   al ayy (by norm_num; linarith)
  have h2:(N:ℝ)^((3:ℕ)⁻¹:ℝ)<=(t^3)^((3:ℕ)⁻¹:ℝ):=
   dh hNR.le (by nlinarith) (by norm_num)
  rw[Real.pow_rpow_inv_natCast t8.le (by norm_num)] at h2
  rw[ay (by linarith)]; linarith
 have a0f:‖s*∑' k,cn s (k+N)‖<=4:=by
  refine (ad1 (by rw[wm]; linarith) t7).trans ?_
  rw[wm]
  have hsn:‖s‖<=2*t:=by
   rw[hs]
   refine (ds _ _).trans ?_
   rw[bo,kr,di,ba,ba,
    au,au,a7 t8,a7 (by linarith:0<σ)]
   linarith
  have hNi:(N:ℝ)^(-σ)<=1/t:=by
   have h1:(N:ℝ)^(-σ)<=(N:ℝ)^(-(1/2:ℝ)):=
    al ayy (by linarith)
   have h2:(N:ℝ)^(-(1/2:ℝ))<=1/t:=by
    rw[iv hNR.le,<- ft,<- jz]
    exact dr t8 ahv
   exact h1.trans h2
  calc ‖s‖*((N:ℝ)^(-σ)/σ)<=(2*t)*((1/t)/(3/4)):=by gcongr
   _=8/3:=by field_simp; ring
   _<=4:=by norm_num
 calc ‖∑ k∈range N,1/((k:ℂ)+1)^s+(N:ℂ)^(1-s)/(s-1)-
       s*∑' k,cn s (k+N)‖
   <= ‖∑ k∈range N,1/((k:ℂ)+1)^s‖+‖(N:ℂ)^(1-s)/(s-1)‖+
       ‖s*∑' k,cn s (k+N)‖:=by
       refine (ej _ _).trans ?_
       gcongr
       exact ds _ _
  _<=uh*(ed 2 N+1)+1+4:=by gcongr
  _ ≤ uh*(4*aa t)+5:=by
      have:=ab ap3 ak5
      linarith
theorem asa {A D:ℕ} (hA:1<=A) (h:ES A D):
  ∃ α<1,∃ B vd,bt.abg.GB α B vd:=by
 obtain ⟨c,hc,K',w2,vd,hES⟩:=h
 set K:=max K' 0 with as7
 have hK:0<=K:=cd _ _
 set M:=max (max 1 (2/c)) (2*K/c) with af1
 have w6:1<=M:=(bq _ _).trans (bq _ _)
 have hMc:2<=c*M:=by
  have:2/c<=M:=(cd _ _).trans (bq _ _)
  have:=ab this hc.le
  rwa[qa _ hc.ne'] at this
 have hMK:2*K<=c*M:=by
  have:2*K/c<=M:=cd _ _
  have:=ab this hc.le
  rwa[qa _ hc.ne'] at this
 set uh:=max (max 45 (w2:ℝ)) (af M) with aa9
 set E:ℕ:=A+D+1 with hE
 have hE0:(0:ℝ)<(E:ℝ):=by positivity
 set a5o:=max (max vd 1024) (af (max ((4:ℝ)^E) (4*uh+5))) with bda
 refine ⟨1 - 1 / (E : ℝ), by have:0<1/(E:ℝ):=by positivity
                             linarith,2,a5o, ?_⟩
 intro s hs tu arh
 set t:=|s.im| with at3
 have af6:vd<=t:=((bq _ _).trans (bq _ _)).trans hs
 have ht:1024<=t:=((cd _ _).trans (bq _ _)).trans hs
 have t8:0<t:=by linarith
 have at4:max ((4:ℝ)^E) (4*uh+5)<=aa t:=by
  rw[d5 t8]; exact (cd _ _).trans hs
 have hL4:(4:ℝ)^E<=aa t:=(bq _ _).trans at4
 have hLK:4*uh+5<=aa t:=(cd _ _).trans at4
 have ug:0<aa t:=eo (by linarith)
 set ρ:=aa t^((E:ℝ)⁻¹) with ba9
 have yw:0<=ρ:=ei ug.le _
 have hL:ρ^E=aa t:=g2 ug.le (by omega)
 have a5p:4<=ρ:=by
  have:(4:ℝ)^E<=ρ^E:=by rw[hL]; exact hL4
  exact (d8 (by norm_num) yw (by omega)).mp this
 have hθ:aa t^(-(1-1/(E:ℝ)))=ρ/aa t:=by
  rw[show -(1-1/(E:ℝ))=(E:ℝ)⁻¹-1 by ring,rg ug,fi]
 rw[hθ] at tu
 have a5q:∀ N N':ℕ,w2<=N->1<=N->(N:ℝ)<t->N'<=2*N->
   ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*I))‖<=
    af (K/(aa N/aa t)^D)*
     (N:ℝ)^(1-c*(aa N/aa t)^A):=by
  intro N N' h1 h1' h2 h3
  refine (hES t af6 N N' h1 h2 h3).trans ?_
  have hN1:(1:ℝ)<=N:=by exact_mod_cast h1'
  have hy:0<=(aa N/aa t)^D:=
   k0 (fe (bd hN1) ug.le) D
  have:K'/(aa N/aa t)^D<=K/(aa N/aa t)^D:=
   a4 (bq _ _) hy
  exact ag (b4.mpr this) (by positivity)
 have hz:=ah9 (D:=D) hA hc hK a5q w6 hMc hMK a5p ht hL tu arh
 have heq:‖riemannZeta s‖=‖riemannZeta ((s.re:ℂ)+t *I)‖:=by
  rcases ig 0 s.im with um | um
  ·rw[at3,bh um,Complex.re_add_im]
  ·have e:(s.re:ℂ)+t *I=(starRingEnd ℂ) s:=by
    apply kn <;> simp[at3,g5 um]
   rw[e,riemannZeta_conj,d4]
 rw[heq,Real.rpow_two]
 refine hz.trans ?_
 have ak5:0<=uh:=br (by norm_num) ((bq 45 (w2:ℝ)).trans (bq _ _))
 nlinarith
theorem aqw {A D:ℕ} (hA:1<=A) (h:ES A D):bt.abg.ZFR:=
 bt.abg.apt (asa hA h)
theorem aft {A D:ℕ} (hA:1<=A) (h:ES A D):bt.abw.ZFR:=
 (show bt.abg.ZFR↔bt.abw.ZFR from Iff.rfl).mp (aqw hA h)
end bt.ar8
end
section
namespace bt.aow
open Finset bt.au4
noncomputable def vk (x:ℝ):ℝ:=|x-round x|
lemma zb (x:ℝ):0<=vk x:=eg _
lemma aec (x:ℝ):vk x<=1/2:=abs_sub_round x
noncomputable def wt (H θ:ℝ):ℝ:=
 if vk θ=0 then 2*H else min (2*H) (1/(2*vk θ))
lemma ais (H θ:ℝ):wt H θ<=2*H:=by
 unfold wt
 split_ifs
 ·exact le_rfl
 ·exact min_le_left _ _
lemma aqx {H θ:ℝ} (h:0<vk θ):wt H θ<=1/(2*vk θ):=by
 unfold wt
 rw[if_neg h.ne']
 exact min_le_right _ _
lemma aba {H:ℝ} (hH:0<=H) (θ:ℝ):0<=wt H θ:=by
 unfold wt
 split_ifs
 ·linarith
 ·exact le_min (by linarith) (by have:=zb θ; positivity)
lemma ag4 (S:Finset ℤ) (D:ℝ) (hD:∀ g∈S,∀ g'∈S,|((g-g':ℤ):ℝ)|<=D):
  S.card<=⌊D⌋₊+1:=by
 classical
 rcases S.eq_empty_or_nonempty with rfl | te
 ·simp
 set g₀:=S.min' te with hg₀
 have wd:q1 (fun g:ℤ=>(g-g₀).toNat) S (range (⌊D⌋₊+1)):=by
  intro g hg
  rw[b9] at hg
  rw[b9,bw]
  have h1:g₀<=g:=S.min'_le g hg
  have h2:=hD g hg g₀ (S.min'_mem te)
  have h3:((g-g₀).toNat:ℝ)<=D:=by
   have e:(((g-g₀).toNat:ℕ):ℤ)=g-g₀:=ll (by omega)
   have e':(((g-g₀).toNat:ℕ):ℝ)=((g-g₀:ℤ):ℝ):=by exact_mod_cast e
   rw[e']
   exact br (k6 _) h2
  have h4:=rv h3
  exact o3 h4
 have hinj:oh (fun g:ℤ=>(g-g₀).toNat) S:=by
  intro a ha b hb hab
  rw[b9] at ha hb
  have h1:g₀<=a:=S.min'_le a ha
  have h2:g₀<=b:=S.min'_le b hb
  simp only at hab
  omega
 have:=ck _ wd hinj
 rwa[fa] at this
lemma ak6 (x:ℝ):|((round x:ℤ):ℝ)|<=|x|+1/2:=by
 have h:=abs_sub_round x
 have:=de (round x:ℝ) x
 rw[jj] at h
 linarith
lemma afu (α:ℝ) (hα:α≠0) (H:ℕ) (a b:ℝ) (hab:a<=b):
  (((Ioo (-(H:ℤ)) H).filter fun g:ℤ=>a<=vk (α*g)∧vk (α*g)<b).card:ℝ)<=
   4*(H*|α|+3)*((b-a)/|α|+1):=by
 classical
 have xw:0< |α|:=ue.mpr hα
 set W:=(Ioo (-(H:ℤ)) H).filter fun g:ℤ=>a<=vk (α*g)∧vk (α*g)<b with hW
 set f:ℤ->ℤ × Bool:=fun g=>(round (α*g),decide (0<=α*g-round (α*g))) with hf
 set R:ℤ:=⌈(H:ℝ)*|α|⌉+1 with hR
 have yu:∀ c∈W.image f,(W.filter fun g=>f g=c).card<=⌊(b-a)/|α|⌋₊+1:=by
  intro c _
  apply ag4
  intro g hg g' hg'
  rw[ah,hW,ah] at hg hg'
  have hfe:f g=f g':=hg.2.trans hg'.2.symm
  simp only[hf,j5,decide_eq_decide] at hfe
  obtain ⟨hr,hs⟩:=hfe
  have hga:=hg.1.2.1
  have hgb:=hg.1.2.2
  have asb:=hg'.1.2.1
  have asc:=hg'.1.2.2
  simp only[vk] at hga hgb asb asc
  have yc:|α*g-α*g'|<=b-a:=by
   rw[hr] at hga hgb
   by_cases h0:0<=α*g-round (α*g')
   ·have h0':0<=α*g'-round (α*g'):=by
     have:=hs.mp (by rw[hr] at *; exact h0)
     exact this
    rw[bh h0] at hga hgb
    rw[bh h0'] at asb asc
    rw[abs_le]; constructor <;> linarith
   ·push_neg at h0
    have h0':α*g'-round (α*g')<0:=by
     by_contra hc
     push_neg at hc
     apply absurd (hs.mpr hc)
     rw[hr]
     linarith
    rw[g5 h0] at hga hgb
    rw[g5 h0'] at asb asc
    rw[abs_le]; constructor <;> linarith
  have:|α| *|((g-g':ℤ):ℝ)|<=b-a:=by
   rw[<- n4]; push_cast; rw[mul_sub]; exact yc
  rw[bl xw]
  linarith
 have ae8:W.image f ⊆ (Icc (-R) R) ×ˢ (univ:Finset Bool):=by
  intro c hc
  rw[cr] at hc
  obtain ⟨g,hg,rfl⟩:=hc
  rw[hW,ah,kp] at hg
  simp only[hf]
  rw[bm,ar]
  refine ⟨?_,ng _⟩
  have h1:=ak6 (α*g)
  have h2:|α*(g:ℝ)|<=|α| *H:=by
   rw[n4]
   apply ab _ (eg _)
   rw[abs_le]
   constructor
   ·have:(-(H:ℤ):ℝ)<g:=by exact_mod_cast hg.1.1
    push_cast at this; linarith
   ·have:(g:ℝ)<(H:ℤ):=by exact_mod_cast hg.1.2
    push_cast at this; linarith
  have h3:(H:ℝ)*|α|<=⌈(H:ℝ)*|α|⌉:=Int.le_ceil _
  have h4:|((round (α*g):ℤ):ℝ)|<(R:ℝ):=by
   rw[hR]; push_cast; linarith
  have h5:|round (α*g)|<R:=by exact_mod_cast h4
  rw[abs_lt] at h5
  constructor <;> omega
 have asd:((W.image f).card:ℝ)<=2*(2*((H:ℝ)*|α|)+5):=by
  have h1:=cf ae8
  rw[iz,ky,i1,Fintype.card_bool] at h1
  have h2:((R+1- -R).toNat:ℝ)<=2*((H:ℝ)*|α|)+5:=by
   have h3:(0:ℤ)<=R+1- -R:=by
    have:(0:ℤ)<=⌈(H:ℝ)*|α|⌉:=Int.ceil_nonneg (by positivity)
    omega
   have e:(((R+1- -R).toNat:ℕ):ℤ)=R+1- -R:=ll h3
   have e':(((R+1- -R).toNat:ℕ):ℝ)=((R+1- -R:ℤ):ℝ):=by exact_mod_cast e
   rw[e',hR]
   push_cast
   have:=Int.ceil_lt_add_one ((H:ℝ)*|α|)
   linarith
  have h4:((W.image f).card:ℝ)<=((R+1- -R).toNat:ℝ)*2:=by exact_mod_cast h1
  linarith
 have u5:=e7 W _ yu
 have hfl:((⌊(b-a)/|α|⌋₊:ℕ):ℝ)<=(b-a)/|α|:=
  ju (fe (by linarith) xw.le)
 calc (W.card:ℝ)<=((⌊(b-a)/|α|⌋₊+1:ℕ):ℝ)*((W.image f).card:ℝ):=by
       exact_mod_cast u5
  _ ≤ ((b-a)/|α|+1)*(2*(2*((H:ℝ)*|α|)+5)):=by
      apply a8 _ asd (av _) (by positivity)
      push_cast; linarith
  _ ≤ 4*(H*|α|+3)*((b-a)/|α|+1):=by
      have:0<=(b-a)/|α|+1:=by
       have:=fe (show 0<=b-a by linarith) xw.le
       linarith
      nlinarith
theorem aqy (α:ℝ) (ak7:α≠0) (hα:|α|<=1/2) (H:ℕ) (hH:1<=H*|α|):
    ∑ g∈Ioo (-(H:ℤ)) H,wt H (α*g)<=100*(H:ℝ)^2*|α| *(1+aa (1/|α|)):=by
  classical
  have xw:0< |α|:=ue.mpr ak7
  have hH0:(0:ℝ)<=H:=av _
  set G:=Ioo (-(H:ℤ)) H with hG
  set K':=⌊1/(2*|α|)⌋₊ with hK'
  set ι:ℤ->ℕ:=fun g=>⌊vk (α*g)/|α|⌋₊ with hι
  have wd:∀ g∈G,ι g∈range (K'+1):=by
    intro g _
    rw[bw,nc]
    apply Nat.floor_le_floor
    rw[ax xw (by positivity)]
    have:=aec (α*g)
    nlinarith
  rw[<- cx wd]
  have a5r:∀ i:ℕ,(((G.filter fun g=>ι g=i).card:ℝ))<=8*(H*|α|+3):=by
    intro i
    have uj:G.filter (fun g=>ι g=i) ⊆ G.filter fun g:ℤ=>
        (i:ℝ)*|α|<=vk (α*g)∧vk (α*g)<((i:ℝ)+1)*|α|:=by
      intro g hg
      rw[ah] at hg ⊢
      refine ⟨hg.1, ?_⟩
      have h0:0<=vk (α*g)/|α|:=fe (zb _) xw.le
      have h1:=(Nat.floor_eq_iff h0).mp hg.2
      rw[bl xw,div_lt_iff₀ xw] at *
      exact ⟨h1.1,h1.2⟩
    have h:=afu α ak7 H ((i:ℝ)*|α|) (((i:ℝ)+1)*|α|) (by nlinarith)
    have e:(((i:ℝ)+1)*|α|-(i:ℝ)*|α|)/|α|+1=2:=by field_simp; ring
    rw[e] at h
    calc (((G.filter fun g=>ι g=i).card:ℝ))<=((G.filter fun g:ℤ=>
          (i:ℝ)*|α|<=vk (α*g)∧vk (α*g)<((i:ℝ)+1)*|α|).card:ℝ):=by
          exact_mod_cast cf uj
      _<=4*(H*|α|+3)*2:=h
      _=8*(H*|α|+3):=by ring
  have aj2:∀ i∈range (K'+1),∑ g∈G.filter (fun g=>ι g=i),wt H (α*g)<=
      8*(H*|α|+3)*(if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=by
    intro i _
    have hb:∀ g∈G.filter (fun g=>ι g=i),
        wt H (α*g)<=(if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=by
      intro g hg
      split_ifs with hi0
      · exact ais _ _
      · rw[ah] at hg
        have h0:0<=vk (α*g)/|α|:=fe (zb _) xw.le
        have h1:=(Nat.floor_eq_iff h0).mp hg.2
        have hi:(1:ℝ)<=i:=by exact_mod_cast i8.mpr hi0
        have h2:(i:ℝ)*|α|<=vk (α*g):=by
          have:=h1.1; rwa[bl xw] at this
        have h3:0<vk (α*g):=fj (by positivity) h2
        refine (aqx h3).trans ?_
        rw[ax (by positivity) (by positivity)]
        nlinarith
    have a5s:0<=(if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=by
      split_ifs <;> positivity
    calc ∑ g∈G.filter (fun g=>ι g=i),wt H (α*g)
        <= ∑ _g∈G.filter (fun g=>ι g=i),(if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=
          ao hb
      _ = ((G.filter fun g=>ι g=i).card:ℝ)*
            (if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=by
          rw[a9,cp]
      _ ≤ 8*(H*|α|+3)*(if i=0 then 2*(H:ℝ) else 1/(2*i*|α|)):=
          ag (a5r i) a5s
  refine (ao aj2).trans ?_
  rw[<- bc,fq]
  simp only[Nat.succ_ne_zero,if_false,if_true]
  have a1i:∑ i∈range K',1/(2*((i+1:ℕ):ℝ)*|α|)=
      (harmonic K':ℝ)/(2*|α|):=by
    rw[harmonic,Rat.cast_sum,ew]
    apply ai rfl
    intro i _
    push_cast
    field_simp
  rw[a1i]
  have vc:0<=aa (1/|α|):=bd (by rw[bl xw]; linarith)
  have bdb:aa K'<=aa (1/|α|):=by
    rcases c7 K' with h0 | h0
    · rw[h0,mw,Real.log_zero]; exact vc
    · apply a5 (by exact_mod_cast h0)
      have:=ju (show 0<=1/(2*|α|) by positivity)
      rw[<- hK'] at this
      calc (K':ℝ)<=1/(2*|α|):=this
        _<=1/|α|:=by
          apply bb (by norm_num) xw (by linarith)
  have hh:=nb K'
  have hinv:1/(2*|α|)<=(H:ℝ)/2:=by
    rw[ax (by positivity) (by norm_num)]; nlinarith
  have ayz:0<=(harmonic K':ℝ):=by
    rw[harmonic]; push_cast; positivity
  have bbc:(harmonic K':ℝ)/(2*|α|)<=((H:ℝ)/2)*(1+aa (1/|α|)):=by
    rw[jd,gx]
    apply a8 hinv (by linarith) ayz (by positivity)
  have hHa:(H:ℝ)*|α|+3<=4*((H:ℝ)*|α|):=by linarith
  calc 8*((H:ℝ)*|α|+3)*((harmonic K':ℝ)/(2*|α|)+2*(H:ℝ))
      <= 8*(4*((H:ℝ)*|α|))*(((H:ℝ)/2)*(1+aa (1/|α|))+2*(H:ℝ)):=by
        have h0:0<=(harmonic K':ℝ)/(2*|α|)+2*(H:ℝ):=by positivity
        apply a8 (by linarith) (by linarith) h0 (by positivity)
    _=16*(H:ℝ)^2
 * |α| *(1+aa (1/|α|))+64*(H:ℝ)^2*|α|:=by ring
    _ ≤ 100*(H:ℝ)^2*|α| *(1+aa (1/|α|)):=by
        have:0<=(H:ℝ)^2*|α|:=by positivity
        nlinarith
noncomputable def eR (x:ℝ):ℂ:=d6 (lu*((2*c2*x:ℝ):ℂ))
lemma ab9 (x y:ℝ):eR (x+y)=eR x*eR y:=by
 unfold eR
 rw[<- jc]
 congr 1
 push_cast
 ring
lemma auv:eR 0=1:=by simp[eR]
lemma y6 (x:ℝ):‖eR x‖=1:=by
 unfold eR
 rw[gx,k9]
lemma aqz (x:ℝ):eR (-x)=(starRingEnd ℂ) (eR x):=by
 unfold eR
 rw[<- m2,qb,n1,lr]
 congr 1
 push_cast
 ring
lemma ay0 (n:ℤ):eR n=1:=by
 unfold eR
 rw[ke]
 exact ⟨n,by push_cast; ring⟩
lemma aq0 {ι:Type*} (t:Finset ι) (f:ι->ℝ):eR (∑ i∈t,f i)=∏ i∈t,eR (f i):=by
 classical
 refine n7 t ?_ ?_
 ·simp[auv]
 ·intro i t hi ih
  rw[ic hi,os hi,ab9,ih]
lemma aox (θ:ℝ) (n:ℕ):eR (n*θ)=eR θ^n:=by
 unfold eR
 rw[<- n9]
 congr 1
 push_cast
 ring
lemma aed (H:ℕ):(Ioo (-(H:ℤ)) H).card=2*H-1:=by
 rw[Int.card_Ioo]; omega
lemma aoy (H:ℕ) (f:ℤ->ℂ):
  ∑ g∈Ioo (-(H:ℤ)) H,f g=∑ j∈range (2*H-1),f ((j:ℤ)-(H-1)):=by
 symm
 apply Finset.sum_bij' (fun (j:ℕ) _=>(j:ℤ)-(H-1)) (fun (g:ℤ) _=>(g+(H-1)).toNat)
 ·intro j hj; rw[bw] at hj; rw[kp]; omega
 ·intro g hg; rw[kp] at hg; rw[bw]; omega
 ·intro j _; omega
 ·intro g hg; rw[kp] at hg; omega
 ·intro j _; rfl
lemma ak8 (θ:ℝ):4*vk θ<=‖eR θ-1‖:=by
 set x:=θ-round θ with aa5
 have hzx:eR θ=eR x:=by
  rw[aa5,ro,ab9,
   show -((round θ:ℤ):ℝ)=((-round θ:ℤ):ℝ) by push_cast; ring,ay0,di]
 have acs:‖eR x-1‖=2*|en (c2*x)|:=by
  unfold eR
  rw[Complex.norm_exp_I_mul_ofReal_sub_one,au,n4,abs_two,
   show 2*c2*x/2=c2*x by ring]
 have hx:|x|<=1/2:=aec θ
 have aro:2*|x|<=|en (c2*x)|:=by
  have h1:0<=c2*|x|:=by positivity
  have h2:c2*|x|<=c2/2:=by nlinarith[du]
  have h3:=Real.mul_le_sin h1 h2
  have h4:2/c2*(c2*|x|)=2*|x|:=by field_simp
  rw[h4] at h3
  rcases ig 0 x with tp | tp
  ·rw[bh tp] at h3 ⊢
   rw[bh (by linarith)]
   exact h3
  ·rw[g5 tp] at h3 ⊢
   have e:en (c2*x)=-en (c2*-x):=by
    rw[mul_neg,Real.sin_neg,neg_neg]
   rw[e,j1,bh (by linarith)]
   exact h3
 have:vk θ=|x|:=rfl
 rw[hzx,acs,this]
 linarith
theorem ak9 (H:ℕ) (θ:ℝ):‖∑ g∈Ioo (-(H:ℤ)) H,eR (θ*g)‖<=wt H θ:=by
 have aa2:‖∑ g∈Ioo (-(H:ℤ)) H,eR (θ*g)‖<=2*H:=by
  refine (c5 _ _).trans ?_
  simp only[y6,a9,cp,di]
  rw[aed]
  have:((2*H-1:ℕ):ℝ)<=2*H:=by
   have:2*H-1<=2*H:=Nat.sub_le _ _
   exact_mod_cast this
  exact this
 unfold wt
 split_ifs with h0
 ·exact aa2
 ·refine le_min aa2 ?_
  have hν:0<vk θ:=lt_of_le_of_ne (zb θ) (qg h0)
  rw[aoy H]
  have a5t:∀ j:ℕ,eR (θ*(((j:ℤ)-(H-1):ℤ):ℝ))=
    eR (θ*(-(H:ℝ)+1))*eR θ^j:=by
   intro j
   rw[<- aox,<- ab9]
   congr 1
   push_cast
   ring
  simp_rw[a5t]
  rw[<- bc,bo,y6,iq]
  have hz:=ak8 θ
  have yp:eR θ≠1:=by
   intro h; rw[h,i3,jw] at hz; linarith
  rw[geom_sum_eq yp,i4]
  have be2:‖eR θ^(2*H-1)-1‖<=2:=by
   refine (ej _ _).trans ?_
   rw[la,y6,sf,norm_one]
   norm_num
  have xo:0<‖eR θ-1‖:=by linarith
  rw[ax xo (by positivity)]
  nlinarith
def ip {k:ℕ} (θ:Fin k->ℝ) (v:Fin k->ℤ):ℝ:=∑ j,θ j*(v j:ℝ)
lemma ay1 {k:ℕ} {ι:Type*} (θ:Fin k->ℝ) (t:Finset ι) (v:ι->Fin k->ℤ):
  ip θ (∑ i∈t,v i)=∑ i∈t,ip θ (v i):=by
 unfold ip
 simp only[pz,Int.cast_sum,bc]
 rw[d0]
lemma ay2 {k:ℕ} (θ:Fin k->ℝ) (a b:Fin k->ℤ):ip θ (a-b)=ip θ a-ip θ b:=by
 unfold ip
 simp only[rt,Int.cast_sub,mul_sub,dn]
noncomputable def W (k:ℕ) (X:Finset ℤ) (θ:Fin k->ℝ):ℂ:=∑ y∈X,eR (ip θ (phi k y))
lemma a1j (k s:ℕ) (X:Finset ℤ) (θ:Fin k->ℝ):
  W k X θ^s=∑ x∈tc s X,eR (ip θ (sig k s x)):=by
 simp_rw[abn,ay1,aq0]
 rw[W,<- Fin.prod_const,jk]
def Dd (k s:ℕ) (q:(Fin s->ℤ) × (Fin s->ℤ)):Fin k->ℤ:=sig k s q.1-sig k s q.2
lemma ait (k s:ℕ) (X:Finset ℤ) (θ:Fin k->ℝ):
  ((‖W k X θ‖^(2*s):ℝ):ℂ)=∑ q∈tc s X ×ˢ tc s X,eR (ip θ (Dd k s q)):=by
 have h1:((‖W k X θ‖^(2*s):ℝ):ℂ)=W k X θ^s*(starRingEnd ℂ) (W k X θ^s):=by
  rw[km,la]
  push_cast
  ring
 rw[h1,a1j,m9,f8,ep]
 apply ai rfl
 intro x _
 apply ai rfl
 intro x' _
 rw[<- aqz,<- ab9,Dd,ay2]
 ring_nf
noncomputable def Jh (k s:ℕ) (X:Finset ℤ) (h:Fin k->ℤ):ℕ:=
 ((tc s X ×ˢ tc s X).filter fun q=>Dd k s q=h).card
lemma aee {M:Type*} [AddCommMonoid M] [Module ℕ M] (k s:ℕ) (X:Finset ℤ)
  (f:(Fin k->ℤ)->M):
  ∑ q∈tc s X ×ˢ tc s X,f (Dd k s q)=
   ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),Jh k s X h•f h:=by
 classical
 rw[<- cx (g:=Dd k s)
  (t:=(tc s X ×ˢ tc s X).image (Dd k s)) (fun q hq=>dv _ hq)]
 apply ai rfl
 intro h _
 rw[ai rfl (g:=fun _=>f h) (fun q hq=>by rw[(ah.mp hq).2]),
  a9,Jh]
lemma amz (k s:ℕ) (X:Finset ℤ) (h:Fin k->ℤ):Jh k s X h<=J k s X:=
 x5 k s X h
def vz {k:ℕ} (α:Fin k->ℝ) (h:Fin k->ℤ):Fin k->ℝ:=fun j=>α j*h j
theorem ala (k s:ℕ) (X:Finset ℤ) (α:Fin k->ℝ):
  ∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s)<=
   ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),(Jh k s X h:ℝ)*‖W k X (vz α h)‖:=by
 have hip:∀ (m:ℤ) (h:Fin k->ℤ),
   ip (fun j=>α j*(m:ℝ)^(j.val+1)) h=ip (vz α h) (phi k m):=by
  intro m h
  unfold ip vz phi
  apply ai rfl
  intro j _
  push_cast
  ring
 have hC:((∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s):ℝ):ℂ)=
   ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),(Jh k s X h:ℂ)*W k X (vz α h):=by
  push_cast
  simp_rw[<- Complex.ofReal_pow,ait]
  rw[d0]
  simp_rw[hip]
  have:=aee k s X (fun h=>∑ m∈X,eR (ip (vz α h) (phi k m)))
  rw[this]
  apply ai rfl
  intro h _
  rw[cp,W]
 have a1k:∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s)=
   ‖∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),(Jh k s X h:ℂ)*W k X (vz α h)‖:=by
  rw[<- hC,ba,au,bh (by positivity)]
 rw[a1k]
 refine (c5 _ _).trans (i6 ?_)
 apply ai rfl
 intro h _
 rw[bo,gf]
theorem aoz (k s:ℕ) (X:Finset ℤ) (α:Fin k->ℝ) (Hb:Fin k->ℕ)
  (ae7:∀ q∈tc s X ×ˢ tc s X,∀ j,|Dd k s q j|<Hb j):
  ∑ h∈dz (fun j=>Ioo (-(Hb j:ℤ)) (Hb j)),‖W k X (vz α h)‖^(2*s)<=
   (J k s X:ℝ)*∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=by
 classical
 set Box:=dz (fun j=>Ioo (-(Hb j:ℤ)) (Hb j)) with a5u
 have xm:((∑ h∈Box,‖W k X (vz α h)‖^(2*s):ℝ):ℂ)=
   ∑ q∈tc s X ×ˢ tc s X,∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),
    eR ((α j*(Dd k s q j:ℝ))*g):=by
  push_cast
  simp_rw[<- Complex.ofReal_pow,ait]
  rw[d0]
  apply ai rfl
  intro q _
  rw[jk]
  apply ai rfl
  intro h _
  unfold ip vz
  rw[aq0]
  apply o6 rfl
  intro j _
  congr 1
  ring
 have hle:∑ h∈Box,‖W k X (vz α h)‖^(2*s)<=
   ∑ q∈tc s X ×ˢ tc s X,∏ j,wt (Hb j) (α j*(Dd k s q j:ℝ)):=by
  have h1:∑ h∈Box,‖W k X (vz α h)‖^(2*s)=
    ‖((∑ h∈Box,‖W k X (vz α h)‖^(2*s):ℝ):ℂ)‖:=by
   rw[ba,au,bh (by positivity)]
  rw[h1,xm]
  refine (c5 _ _).trans (ao fun q _=>?_)
  rw[ra]
  apply iy (fun j _=>aw _)
  intro j _
  exact ak9 (Hb j) _
 refine hle.trans ?_
 have ay4:∀ (j:Fin k) (g:ℤ),0<=wt (Hb j) (α j*g):=
  fun j g=>aba (av _) _
 rw[aee (M:=ℝ) k s X (fun h=>∏ j,wt (Hb j) (α j*(h j:ℝ)))]
 calc ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),Jh k s X h•∏ j,wt (Hb j) (α j*(h j:ℝ))
   <= ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),(J k s X:ℝ)*∏ j,wt (Hb j) (α j*(h j:ℝ)):=by
       apply ao
       intro h _
       rw[cp]
       apply ag _ (l1 fun j _=>ay4 j _)
       exact_mod_cast amz k s X h
  _ ≤ ∑ h∈Box,(J k s X:ℝ)*∏ j,wt (Hb j) (α j*(h j:ℝ)):=by
      apply aq
      ·intro h hh
       rw[cr] at hh
       obtain ⟨q,hq,rfl⟩:=hh
       rw[a5u,gd]
       intro j
       have:=ae7 q hq j
       rw[abs_lt] at this
       rw[kp]
       exact this
      ·intro h _ _
       exact b7 (av _) (l1 fun j _=>ay4 j _)
  _ = (J k s X:ℝ)*∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=by
      rw[<- bc,jk]
theorem ase {ι:Type*} (t:Finset ι) (w a:ι->ℝ) (hw:∀ i∈t,0<=w i)
  (ha:∀ i∈t,0<=a i) (s:ℕ) (hs:1<=s):
  (∑ i∈t,w i*a i)^(2*s)<=
   (∑ i∈t,w i)^(2*s-2)*(∑ i∈t,w i^2)*(∑ i∈t,a i^(2*s)):=by
 set Wt:=∑ i∈t,w i with hWt
 have hW0:0<=Wt:=cj hw
 rcases hW0.eq_or_lt with h0 | tj
 ·have hz:∀ i∈t,w i=0:=(Finset.sum_eq_zero_iff_of_nonneg hw).mp h0.symm
  have:∑ i∈t,w i*a i=0:=Finset.sum_eq_zero fun i hi=>by rw[hz i hi,zero_mul]
  rw[this,zero_pow (by omega)]
  apply b7 (b7 (k0 hW0 _) (cj fun i _=>c4 _))
  exact cj fun i hi=>k0 (ha i hi) _
 have hpm:=Real.pow_arith_mean_le_arith_mean_pow t (fun i=>w i/Wt) a
  (fun i hi=>fe (hw i hi) hW0) (by rw[<- ew,div_self tj.ne'])
  ha s
 have e1:∑ i∈t,w i/Wt *a i=(∑ i∈t,w i*a i)/Wt:=by
  rw[ew]; apply ai rfl; intro i _; ring
 have e2:∑ i∈t,w i/Wt *a i^s=(∑ i∈t,w i*a i^s)/Wt:=by
  rw[ew]; apply ai rfl; intro i _; ring
 rw[e1,e2,l8,ax (fb tj _) tj] at hpm
 have h1:(∑ i∈t,w i*a i)^s<=Wt^(s-1)*∑ i∈t,w i*a i^s:=by
  have e:Wt^s=Wt^(s-1)*Wt:=by rw[<- ob]; congr 1; omega
  rw[e] at hpm
  nlinarith[fb tj (s-1)]
 have hS0:0<=∑ i∈t,w i*a i:=cj fun i hi=>b7 (hw i hi) (ha i hi)
 have hcs:=Finset.sum_mul_sq_le_sq_mul_sq t w (fun i=>a i^s)
 calc (∑ i∈t,w i*a i)^(2*s)=((∑ i∈t,w i*a i)^s)^2:=by ring
  _ ≤ (Wt^(s-1)*∑ i∈t,w i*a i^s)^2:=
      aj (k0 hS0 _) h1 2
  _ = Wt^(2*s-2)*(∑ i∈t,w i*a i^s)^2:=by
      rw[i5,<- ox]; congr 2; omega
  _ ≤ Wt^(2*s-2)*((∑ i∈t,w i^2)*∑ i∈t,(a i^s)^2):=
      ab hcs (k0 hW0 _)
  _ = Wt^(2*s-2)*(∑ i∈t,w i^2)*(∑ i∈t,a i^(2*s)):=by
      rw[gv]; congr 2
      apply ai rfl; intro i _; ring
lemma aq1 (k s:ℕ) (X:Finset ℤ):
  ∑ h∈(tc s X ×ˢ tc s X).image (Dd k s),(Jh k s X h:ℝ)=
   ((tc s X ×ˢ tc s X).card:ℝ):=by
 have:=aee (M:=ℝ) k s X (fun _=>(1:ℝ))
 simp only[cp,di,a9] at this
 rw[<- this]
theorem asf (k s:ℕ) (hs:1<=s) (X:Finset ℤ) (α:Fin k->ℝ) (Hb:Fin k->ℕ)
  (ae7:∀ q∈tc s X ×ˢ tc s X,∀ j,|Dd k s q j|<Hb j):
  (∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s))^(2*s)<=
   (((tc s X ×ˢ tc s X).card:ℝ))^(2*s-1)*(J k s X:ℝ)^2*
    ∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=by
 classical
 set Img:=(tc s X ×ˢ tc s X).image (Dd k s) with a5v
 set Ct:=((tc s X ×ˢ tc s X).card:ℝ) with hCt
 have xd:0<=∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s):=
  cj fun _ _=>by positivity
 have hV4:=ala k s X α
 have hH:=ase Img (fun h=>(Jh k s X h:ℝ)) (fun h=>‖W k X (vz α h)‖)
  (fun _ _=>av _) (fun _ _=>aw _) s hs
 have hJ2:∑ h∈Img,(Jh k s X h:ℝ)^2<=(J k s X:ℝ)*Ct:=by
  calc ∑ h∈Img,(Jh k s X h:ℝ)^2<=∑ h∈Img,(J k s X:ℝ)*(Jh k s X h:ℝ):=by
        apply ao
        intro h _
        rw[sq]
        apply ag _ (av _)
        exact_mod_cast amz k s X h
   _=(J k s X:ℝ)*Ct:=by rw[<- bc,aq1]
 have a1l:∑ h∈Img,‖W k X (vz α h)‖^(2*s)<=
   (J k s X:ℝ)*∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=by
  refine br ?_ (aoz k s X α Hb ae7)
  apply aq
  ·intro h hh
   rw[a5v,cr] at hh
   obtain ⟨q,hq,rfl⟩:=hh
   rw[gd]
   intro j
   have:=ae7 q hq j
   rw[abs_lt] at this
   rw[kp]
   exact this
  ·intro _ _ _; positivity
 have hP0:0<=∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=
  l1 fun j _=>cj fun g _=>aba (av _) _
 have a5w:0<=Ct:=av _
 have hJ0:(0:ℝ)<=J k s X:=av _
 calc (∑ m∈X,‖W k X (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s))^(2*s)
   <= (∑ h∈Img,(Jh k s X h:ℝ)*‖W k X (vz α h)‖)^(2*s):=
       aj xd hV4 _
  _ ≤ (∑ h∈Img,(Jh k s X h:ℝ))^(2*s-2)*(∑ h∈Img,(Jh k s X h:ℝ)^2)*
        (∑ h∈Img,‖W k X (vz α h)‖^(2*s)):=hH
  _ ≤ Ct^(2*s-2)*((J k s X:ℝ)*Ct)*
       ((J k s X:ℝ)*∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g)):=by
      rw[aq1]
      apply a8 (ab hJ2 (k0 a5w _)) a1l
       (cj fun _ _=>by positivity) (by positivity)
  _ = Ct^(2*s-1)*(J k s X:ℝ)^2*
       ∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=by
      rw[show 2*s-1=(2*s-2)+1 by omega,ob]
      ring
noncomputable def ψ (t x:ℝ):ℝ:=-(t/(2*c2))*aa x
lemma acz (t:ℝ) {n:ℕ} (hn:1<=n):
  (n:ℂ)^(-((t:ℂ)*lu))=eR (ψ t n):=by
 have t6:(n:ℂ)≠0:=by exact_mod_cast (show n≠0 by omega)
 rw[gq t6,eR,ψ]
 have ur:Complex.log (n:ℂ)=((aa n:ℝ):ℂ):=by
  rw[<- m7,j8 (av n)]
 rw[ur]
 congr 1
 have hpi:(c2:ℂ)≠0:=by exact_mod_cast qd
 push_cast
 field_simp
lemma telescope (g:ℕ->ℂ) (N N':ℕ) (h:N<=N'):
  ∑ n∈Ioc N N',(g n-g (n+1))=g (N+1)-g (N'+1):=by
 induction N',h using Nat.le_induction with
 | base=>simp
 | succ m hm ih=>
  rw[Finset.sum_Ioc_succ_top hm,ih]
  ring
theorem shift_le (f:ℕ->ℂ) (hf:∀ n,‖f n‖<=1) (N N' y:ℕ):
  ‖∑ n∈Ioc N N',f n-∑ n∈Ioc N N',f (n+y)‖<=2*y:=by
 induction y with
 | zero=>simp
 | succ y ih=>
  have h1:‖∑ n∈Ioc N N',f (n+y)-∑ n∈Ioc N N',f (n+(y+1))‖<=2:=by
   rcases ig N N' with h | h
   ·rw[<- dn]
    have e:∀ n,f (n+y)-f (n+(y+1))=(fun m=>f (m+y)) n-(fun m=>f (m+y)) (n+1):=by
     intro n; simp only; ring_nf
    simp_rw[e]
    rw[telescope _ N N' h]
    refine (ej _ _).trans ?_
    linarith[hf (N+1+y),hf (N'+1+y)]
   ·rw[s0 (by omega)]
    simp
  calc ‖∑ n∈Ioc N N',f n-∑ n∈Ioc N N',f (n+(y+1))‖
    <= ‖∑ n∈Ioc N N',f n-∑ n∈Ioc N N',f (n+y)‖+
        ‖∑ n∈Ioc N N',f (n+y)-∑ n∈Ioc N N',f (n+(y+1))‖:=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
   _<=2*y+2:=e8 ih h1
   _=2*((y+1:ℕ):ℝ):=by push_cast; ring
noncomputable def vb (t:ℝ) (k:ℕ) (n:ℝ):Fin k->ℝ:=
 fun j=>-(t/(2*c2))*(-1)^(j.val)/((j.val+1)*n^(j.val+1))
theorem ao0 (t:ℝ) (k:ℕ) {n y:ℝ} (hn:0<n) (hy:0<=y) (hyn:2*y<=n):
  |ψ t (n+y)-ψ t n-∑ j:Fin k,vb t k n j*y^(j.val+1)|<=
   |t|/c2*(y/n)^(k+1):=by
 set x:=-(y/n) with hx
 have hxa:|x|=y/n:=by rw[hx,j1,bh (fe hy hn.le)]
 have hx2:|x|<=1/2:=by rw[hxa,ay hn]; linarith
 have x2:|x|<1:=by linarith
 have hT:=Real.abs_log_sub_add_sum_range_le x2 k
 have ur:aa (n+y)=aa n+aa (1-x):=by
  rw[<- ca hn.ne' (by rw[hx]; have:=fe hy hn.le; linarith)]
  congr 1
  rw[hx]; field_simp; ring
 have hsum:∑ j:Fin k,vb t k n j*y^(j.val+1)=
   (t/(2*c2))*∑ i∈range k,x^(i+1)/(i+1):=by
  rw[bc,
   <- md (fun i=>t/(2*c2)*(x^(i+1)/(i+1))) k]
  apply ai rfl
  intro i _
  simp only[vb]
  rw[hx,neg_pow (y/n),l8 y n]
  field_simp
  ring
 have abd:ψ t (n+y)-ψ t n-∑ j:Fin k,vb t k n j*y^(j.val+1)=
   -(t/(2*c2))*((∑ i∈range k,x^(i+1)/(i+1))+aa (1-x)):=by
  rw[hsum,ψ,ψ,ur]
  ring
 rw[abd,n4,j1,abs_div,a7 (by positivity:(0:ℝ)<2*c2)]
 have hpi:=du
 have h2:|x|^(k+1)/(1-|x|)<=2*(y/n)^(k+1):=by
  rw[ay (by linarith),<- hxa]
  have:0<=|x|^(k+1):=by positivity
  nlinarith
 calc |t|/(2*c2)*|(∑ i∈range k,x^(i+1)/(i+1))+aa (1-x)|
   <= |t|/(2*c2)*(2*(y/n)^(k+1)):=
       ab (hT.trans h2) (by positivity)
  _=|t|/c2*(y/n)^(k+1):=by field_simp
lemma ag6 (x:ℝ):‖eR x-1‖<=2*c2*|x|:=by
 unfold eR
 have:=Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*c2*x)
 rw[au,n4,a7 (by positivity:(0:ℝ)<2*c2)] at this
 exact this
theorem ai6 (t:ℝ) (k M:ℕ) {n:ℝ} (hn:0<n) (hM:2*(M:ℝ)^2<=n):
  ‖∑ m₁∈Icc (1:ℤ) M,∑ m₂∈Icc (1:ℤ) M,eR (ψ t (n+(m₁:ℝ)*m₂))‖<=
   ∑ m₁∈Icc (1:ℤ) M,‖W k (Icc 1 M) (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖+
    (M:ℝ)^2*(2*|t| *((M:ℝ)^2/n)^(k+1)):=by
 set X:=Icc (1:ℤ) M with hX
 have u3:∀ m∈X,(1:ℝ)<=m∧(m:ℝ)<=M:=by
  intro m hm
  rw[hX,ar] at hm
  exact ⟨by exact_mod_cast hm.1,by exact_mod_cast hm.2⟩
 have hR:∀ m₁∈X,∀ m₂∈X,
   ‖eR (ψ t (n+(m₁:ℝ)*m₂))-eR (ψ t n)*
    eR (ip (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1)) (phi k m₂))‖<=
    2*|t| *((M:ℝ)^2/n)^(k+1):=by
  intro m₁ h₁ m₂ h₂
  obtain ⟨a1,a2⟩:=u3 m₁ h₁
  obtain ⟨b1,b2⟩:=u3 m₂ h₂
  set y:=(m₁:ℝ)*m₂ with hy
  have hy0:0<=y:=by positivity
  have hyM:y<=(M:ℝ)^2:=by rw[hy,sq]; exact a8 a2 b2 (by linarith) (by linarith)
  have hyn:2*y<=n:=by linarith
  have hT:=ao0 t k hn hy0 hyn
  have hip:ip (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1)) (phi k m₂)=
    ∑ j:Fin k,vb t k n j*y^(j.val+1):=by
   unfold ip phi
   apply ai rfl
   intro j _
   rw[hy,i5]
   push_cast
   ring
  rw[hip,<- ab9]
  set r:=ψ t (n+y)-ψ t n-∑ j:Fin k,vb t k n j*y^(j.val+1) with hr
  have e:ψ t (n+y)=(ψ t n+∑ j:Fin k,vb t k n j*y^(j.val+1))+r:=by
   rw[hr]; ring
  rw[e,ab9,<- mul_sub_one,bo,y6,iq]
  refine (ag6 r).trans ?_
  have a5x:(y/n)^(k+1)<=((M:ℝ)^2/n)^(k+1):=
   aj (fe hy0 hn.le) (a4 hyM hn.le) _
  have hpi:=du
  calc 2*c2*|r|<=2*c2*(|t|/c2*(y/n)^(k+1)):=
        ab hT (by positivity)
   _=2*|t| *(y/n)^(k+1):=by field_simp
   _ ≤ 2*|t| *((M:ℝ)^2/n)^(k+1):=
       ab a5x (by positivity)
 have u8:∑ m₁∈X,∑ m₂∈X,eR (ψ t (n+(m₁:ℝ)*m₂))=
   eR (ψ t n)*∑ m₁∈X,W k X (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))+
   ∑ m₁∈X,∑ m₂∈X,(eR (ψ t (n+(m₁:ℝ)*m₂))-eR (ψ t n)*
    eR (ip (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1)) (phi k m₂))):=by
  simp only[W,bc,dn]
  ring
 rw[u8]
 refine (ds _ _).trans (e8 ?_ ?_)
 ·rw[bo,y6,iq]
  exact c5 _ _
 ·refine (c5 _ _).trans ?_
  calc ∑ m₁∈X,‖∑ m₂∈X,(eR (ψ t (n+(m₁:ℝ)*m₂))-eR (ψ t n)*
        eR (ip (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1)) (phi k m₂)))‖
    <= ∑ m₁∈X,∑ a1m∈X,2*|t| *((M:ℝ)^2/n)^(k+1):=by
        apply ao
        intro m₁ h₁
        refine (c5 _ _).trans (ao fun m₂ h₂=>hR m₁ h₁ m₂ h₂)
   _ = (M:ℝ)^2*(2*|t| *((M:ℝ)^2/n)^(k+1)):=by
       rw[a9,a9,hX,ky,cp,cp]
       simp only[add_sub_cancel_right,mh]
       ring
noncomputable def Bn (n:ℕ):ℝ:=((4*n:ℕ):ℝ)^(8*n^3)
lemma aef {n:ℕ} (hn:1<=n):1<=Bn n:=by
 unfold Bn
 apply dx
 exact_mod_cast (by omega:1<=4*n)
lemma auw {n n':ℕ} (hn:1<=n) (h:n<=n'):Bn n<=Bn n':=by
 unfold Bn
 calc ((4*n:ℕ):ℝ)^(8*n^3)<=((4*n':ℕ):ℝ)^(8*n^3):=
       aj (av _) (by exact_mod_cast (by omega:4*n<=4*n')) _
  _ ≤ ((4*n':ℕ):ℝ)^(8*n'^3):=by
      apply fy (by exact_mod_cast (by omega:1<=4*n'))
      have:=ec h 3
      omega
lemma a5y (k s:ℕ) (hk:1<=k):
  ((k^k)^(k+s))^2*(k^k)^(4*(k+s)^2)<=(4*(k+s))^(8*(k+s)^3):=by
 have e:((k^k)^(k+s))^2*(k^k)^(4*(k+s)^2)=
   k^(k*(k+s)*2+k*(4*(k+s)^2)):=by
  rw[<- ox,<- ox,<- ox,<- oy]; ring_nf
 rw[e]
 calc k^(k*(k+s)*2+k*(4*(k+s)^2))
   <= (4*(k+s))^(k*(k+s)*2+k*(4*(k+s)^2)):=
       ec (by omega) _
  _ ≤ (4*(k+s))^(8*(k+s)^3):=by
      apply ga (by omega)
      have h1:k<=k+s:=by omega
      have h2:1<=k+s:=by omega
      have h3:k*(k+s)<=(k+s)^2:=by rw[sq]; exact gb _ h1
      have h4:k*(k+s)^2<=(k+s)^3:=by
       rw[show (k+s)^3=(k+s)*(k+s)^2 by ring]
       exact gb _ h1
      have h5:(k+s)^2<=(k+s)^3:=ga h2 (by norm_num)
      nlinarith
lemma a5z (k s:ℕ) (hk:2<=k) (hs:1<=s):
  ((k+s).factorial)^2*k.factorial*4^(2*s+k*(k-1)/2)*4^(4*(k+s)^2)<=
   (4*(k+s))^(8*(k+s)^3):=by
 obtain ⟨n,hn⟩:∃ n,n=k+s:=⟨_,rfl⟩
 rw[<- hn]
 have hn3:3<=n:=by omega
 have hf:n.factorial<=(4*n)^n:=
  (nq n).trans (ec (by omega) _)
 have hkf:k.factorial<=(4*n)^n:=(Nat.factorial_le (by omega)).trans hf
 have h4:∀ a:ℕ,4^a<=(4*n)^a:=fun a=>ec (by omega) a
 have ha:2*s+k*(k-1)/2<=2*n^2:=by
  have h1:k*(k-1)/2<=k*(k-1):=lj _ _
  have h2:k*(k-1)<=n*n:=gl (by omega) (by omega)
  have h3:s<=n:=by omega
  have h5:2*n<=n*n:=by nlinarith
  rw[sq]; omega
 calc (n.factorial)^2*k.factorial*4^(2*s+k*(k-1)/2)*4^(4*n^2)
   <= ((4*n)^n)^2*(4*n)^n*(4*n)^(2*n^2)*(4*n)^(4*n^2):=
       gl (gl (gl (ec hf 2) hkf)
        ((h4 _).trans (ga (by omega) ha))) (h4 _)
  _ = (4*n)^(n*2+n+2*n^2+4*n^2):=by
      rw[<- ox,<- oy,<- oy,<- oy]
  _ ≤ (4*n)^(8*n^3):=by
      apply ga (by omega)
      have h5:3*n<=n^2:=by nlinarith
      have h6:3*n^2<=n^3:=by
       rw[show n^3=n*n^2 by ring]; exact gb _ hn3
      nlinarith
lemma a50 (k s:ℕ) (hk:2<=k) (hs:1<=s):
  4^(k-1)*((k-1)*2)^(k+s)*k.factorial<=(4*(k+s))^(8*(k+s)^3):=by
 obtain ⟨n,hn⟩:∃ n,n=k+s:=⟨_,rfl⟩
 rw[<- hn]
 have hn3:3<=n:=by omega
 have hf:k.factorial<=(4*n)^n:=
  (nq k).trans ((ec (by omega) _).trans
   (ga (by omega) (by omega)))
 calc 4^(k-1)*((k-1)*2)^n*k.factorial
   <= (4*n)^n*(4*n)^n*(4*n)^n:=
       gl (gl
        ((ec (show 4<=4*n by omega) _).trans
         (ga (by omega) (show k-1<=n by omega)))
        (ec (show (k-1)*2<=4*n by omega) n)) hf
  _=(4*n)^(n+n+n):=by rw[<- oy,<- oy]
  _ ≤ (4*n)^(8*n^3):=by
      apply ga (by omega)
      have h5:n<=n^3:=Nat.le_self_pow (by norm_num) n
      omega
theorem asg {k s:ℕ} {Δ C:ℝ} (hk:2<=k) (hs:1<=s) (a51:0<=Δ)
  (hΔ:Δ<=(k:ℝ)^2) (hC:0<=C):aau k s Δ C<=3*Bn (k+s)*(C+1):=by
 have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
 have hsR:(1:ℝ)<=s:=by exact_mod_cast hs
 set n:=k+s with hn
 have hnR:(n:ℝ)=k+s:=by rw[hn]; push_cast; ring
 set Δ':=max ((1-1/(k:ℝ))*Δ) ((k:ℝ)*(k-1)/2-(s+1)/k) with ana
 have t9:0<=1-1/(k:ℝ):=by rw[oa,dw (by linarith)]; linarith
 have hc1:1-1/(k:ℝ)<=1:=by linarith[show (0:ℝ)<=1/(k:ℝ) by positivity]
 have hD0:0<=Δ':=br (b7 t9 a51) (bq _ _)
 have hD1:Δ'<=(k:ℝ)^2:=by
  apply max_le
  ·nlinarith
  ·have:0<=((s:ℝ)+1)/k:=by positivity
   nlinarith
 have he:|2*((k+s:ℕ):ℝ)-k*(k+1)/2+Δ'|<=((4*n^2:ℕ):ℝ):=by
  push_cast
  rw[abs_le]
  constructor <;> nlinarith
 have hes:|2*(s:ℝ)-k*(k+1)/2+Δ|<=((4*n^2:ℕ):ℝ):=by
  push_cast
  rw[abs_le]
  constructor <;> nlinarith
 have hP0:(1:ℝ)<=((k^k:ℕ):ℝ):=by exact_mod_cast qv _ _ (by omega)
 have ht1:((k^k:ℕ):ℝ)^|2*((k+s:ℕ):ℝ)-k*(k+1)/2+Δ'|<=
   ((k^k:ℕ):ℝ)^(4*n^2):=by
  rw[<- da _ (4*n^2)]
  exact al hP0 he
 have ht2:(4:ℝ)^|2*(s:ℝ)-k*(k+1)/2+Δ|<=(4:ℝ)^(4*n^2):=by
  rw[<- da _ (4*n^2)]
  exact al (by norm_num) hes
 have hA:(((k^k:ℕ):ℝ)^(k+s))^2*((k^k:ℕ):ℝ)^(4*n^2)<=Bn n:=by
  unfold Bn
  exact_mod_cast a5y k s (by omega)
 have hB:((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)*
   (4:ℝ)^(4*n^2)<=Bn n:=by
  unfold Bn
  exact_mod_cast a5z k s hk hs
 have hCc:(4:ℝ)^(k-1)*(((k-1:ℕ):ℝ)*2)^(k+s)*k.factorial<=Bn n:=by
  unfold Bn
  exact_mod_cast a50 k s hk hs
 have hB1:1<=Bn n:=aef (by omega)
 unfold aau
 rw[<- ana]
 have t1:(((k^k:ℕ):ℝ)^(k+s))^2*((k^k:ℕ):ℝ)^
   |2*((k+s:ℕ):ℝ)-k*(k+1)/2+Δ'|<=Bn n:=
  br (ab ht1 (by positivity)) hA
 have t2:((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)*
   (C*(4:ℝ)^|2*(s:ℝ)-k*(k+1)/2+Δ|)<=Bn n*C:=by
  have:=ab ht2
   (show (0:ℝ)<=((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)
    by positivity)
  calc ((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)*
        (C*(4:ℝ)^|2*(s:ℝ)-k*(k+1)/2+Δ|)
    = C*(((k+s).factorial:ℝ)^2*k.factorial*(4:ℝ)^(2*s+k*(k-1)/2)*
        (4:ℝ)^|2*(s:ℝ)-k*(k+1)/2+Δ|):=by ring
   _<=C*Bn n:=ab (this.trans hB) hC
   _=Bn n*C:=by ring
 nlinarith
noncomputable def yo (k:ℕ):ℕ->ℝ
 | 0=>k.factorial
 | τ+1=>aau k (k*(τ+1)) (wb k τ) (yo k τ)
lemma alb {k s:ℕ} {Δ C:ℝ} (hC:0<=C):0<=aau k s Δ C:=by
 unfold aau
 apply add_nonneg (add_nonneg (by positivity) (b7 (by positivity)
  (b7 hC (by positivity)))) (by positivity)
theorem aiu (k:ℕ) (hk:2<=k):∀ τ:ℕ,0<=yo k τ∧∀ P:ℕ,1<=P->
  (J k (k*(τ+1)) (Icc 1 (P:ℤ)):ℝ)<=
   yo k τ*(P:ℝ)^(2*((k*(τ+1):ℕ):ℝ)-k*(k+1)/2+wb k τ):=by
 intro τ
 induction τ with
 | zero=>
  refine ⟨by simp only[yo]; positivity,fun P _=>?_⟩
  have h:=avx k P
  simp only[yo,wb,jy,di]
  have xm:2*(k:ℝ)-k*(k+1)/2+(k:ℝ)*(k-1)/2=(k:ℝ):=by ring
  rw[xm,da]
  exact_mod_cast h
 | succ τ ih=>
  obtain ⟨h0,h1⟩:=ih
  refine ⟨alb h0, ?_⟩
  have h:=apc hk (by nlinarith) h0 h1
  rw[show k+k*(τ+1)=k*(τ+1+1) by ring] at h
  exact h
lemma auy (k:ℕ) (hk:2<=k):∀ τ:ℕ,
  yo k τ+1<=(4*Bn (k*(τ+2)))^τ*((k.factorial:ℝ)+1):=by
 intro τ
 induction τ with
 | zero=>simp[yo]
 | succ τ ih=>
  have hb:=aae k hk τ
  have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
  have a52:wb k τ<=(k:ℝ)^2:=by nlinarith[hb.2]
  have x9:=(aiu k hk τ).1
  have hs:=asg (s:=k*(τ+1)) hk (by nlinarith) hb.1 a52 x9
  rw[show k+k*(τ+1)=k*(τ+2) by ring] at hs
  have hB1:1<=Bn (k*(τ+2)):=aef (by nlinarith)
  have u6:Bn (k*(τ+2))<=Bn (k*(τ+1+2)):=auw (by nlinarith) (by nlinarith)
  have aeg:yo k (τ+1)+1<=4*Bn (k*(τ+2))*(yo k τ+1):=by
   show aau k (k*(τ+1)) (wb k τ) (yo k τ)+1<=_
   nlinarith
  have hpow:(4*Bn (k*(τ+2)))^τ<=(4*Bn (k*(τ+1+2)))^τ:=
   aj (by linarith) (by linarith) _
  have hf:(0:ℝ)<=(k.factorial:ℝ)+1:=by positivity
  calc yo k (τ+1)+1<=4*Bn (k*(τ+2))*(yo k τ+1):=aeg
   _ ≤ 4*Bn (k*(τ+1+2))*((4*Bn (k*(τ+1+2)))^τ*((k.factorial:ℝ)+1)):=by
       apply a8 (by linarith) (ih.trans (ag hpow hf))
        (by linarith[x9]) (by linarith)
   _=(4*Bn (k*(τ+1+2)))^(τ+1)*((k.factorial:ℝ)+1):=by ring
theorem alc (k:ℕ) (hk:2<=k):∃ s:ℕ,∃ C:ℝ,1<=s∧s<=4*k^3∧0<=C∧
  aa (C+1)<=100000*(k:ℝ)^14∧∀ P:ℕ,1<=P->
   (J k s (Icc 1 (P:ℤ)):ℝ)<=C*(P:ℝ)^(2*(s:ℝ)-k*(k+1)/2+1):=by
 have hkR:(2:ℝ)<=k:=by exact_mod_cast hk
 have x1:(1:ℝ)<=k:=by linarith
 set D:=(k:ℝ)*(k-1)/2 with hD
 set τ:=s9 D+2*k^2 with u0
 have hDk:D<=((k^2:ℕ):ℝ):=by push_cast; nlinarith
 have bdc:s9 D<=k^2:=Nat.ceil_le.mpr hDk
 have a1n:τ<=3*k^2:=by omega
 have be3:wb k τ<=1:=by
  have h:=ane k hk (2*k^2)
  rw[<- hD,<- u0] at h
  refine h.trans ?_
  have t9:0<=1-1/(k:ℝ):=by rw[oa,dw (by linarith)]; linarith
  have h1:1-1/(k:ℝ)<=af (-(1/(k:ℝ))):=by
   have:=cw (-(1/(k:ℝ))); linarith
  have h2:(1-1/(k:ℝ))^(2*k^2)<=af (-(2*(k:ℝ))):=by
   calc (1-1/(k:ℝ))^(2*k^2)<=(af (-(1/(k:ℝ))))^(2*k^2):=
         aj t9 h1 _
    _=af (((2*k^2:ℕ):ℝ)*(-(1/(k:ℝ)))):=(db _ _).symm
    _ = af (-(2*(k:ℝ))):=by
        congr 1; push_cast; field_simp
  have h3:D<=af (2*(k:ℝ)):=by
   have e1:=cw (k:ℝ)
   have e2:af (2*(k:ℝ))=af k*af k:=by
    rw[<- bs]; ring_nf
   rw[e2,hD]
   nlinarith[bx (k:ℝ)]
  have hD0:0<=D:=by rw[hD]; nlinarith
  calc (1-1/(k:ℝ))^(2*k^2)*D<=af (-(2*(k:ℝ)))*af (2*(k:ℝ)):=
        a8 h2 h3 hD0 (bx _).le
   _=1:=by rw[<- bs]; simp
 obtain ⟨x9,hJ⟩:=aiu k hk τ
 refine ⟨k*(τ+1),yo k τ,by nlinarith, ?_,x9, ?_,fun P hP=>?_⟩
 ·have:k*(τ+1)<=k*(3*k^2+1):=fu _ (by omega)
  nlinarith
 ·
  have hCs:=auy k hk τ
  set n:=k*(τ+2) with hn
  have xb:1<=n:=by nlinarith
  have hnk:(n:ℝ)<=5*(k:ℝ)^3:=by
   have:n<=k*(3*k^2+2):=fu _ (by omega)
   have h':(n:ℝ)<=(k:ℝ)*(3*(k:ℝ)^2+2):=by exact_mod_cast this
   nlinarith
  have a53:(τ:ℝ)<=3*(k:ℝ)^2:=by exact_mod_cast a1n
  have hB1:=aef xb
  have tj:0<(4*Bn n)^τ*((k.factorial:ℝ)+1):=by positivity
  have aej:aa (yo k τ+1)<=aa ((4*Bn n)^τ*((k.factorial:ℝ)+1)):=
   a5 (by linarith) hCs
  rw[ca (by positivity) (by positivity),cq] at aej
  have a1o:aa (4*Bn n)<=3+20000*(k:ℝ)^12:=by
   rw[ca (by norm_num) (by linarith),Bn,cq]
   have h4:aa 4<=3:=by
    have:=bz (show (0:ℝ)<4 by norm_num); linarith
   have h4n:aa ((4*n:ℕ):ℝ)<=4*(n:ℝ):=by
    have:=bz (show (0:ℝ)<((4*n:ℕ):ℝ) by
     exact_mod_cast (by omega:0<4*n))
    push_cast at this ⊢; linarith
   have t6:(0:ℝ)<=n:=av _
   have hn4:(n:ℝ)^4<=(5*(k:ℝ)^3)^4:=aj t6 hnk 4
   push_cast
   have:((8*n^3:ℕ):ℝ)*aa ((4*n:ℕ):ℝ)<=32*(n:ℝ)^4:=by
    push_cast
    have a54:aa (4*(n:ℝ))<=4*(n:ℝ):=by push_cast at h4n; exact h4n
    have:=ab a54 (show (0:ℝ)<=8*(n:ℝ)^3 by positivity)
    nlinarith
   push_cast at this
   nlinarith
  have bdd:aa ((k.factorial:ℝ)+1)<=1+(k:ℝ)^2:=by
   have hf:((k.factorial:ℝ)+1)<=2*(k:ℝ)^k:=by
    have h1:(k.factorial:ℝ)<=(k:ℝ)^k:=by exact_mod_cast nq k
    have h2:(1:ℝ)<=(k:ℝ)^k:=dx x1
    linarith
   have hl:=a5 (by positivity) hf
   rw[ca (by norm_num) (by positivity),cq] at hl
   have h2:aa 2<=1:=by
    have:=bz (show (0:ℝ)<2 by norm_num); linarith
   have hk':aa (k:ℝ)<=k:=by
    have:=bz (show (0:ℝ)<k by linarith); linarith
   have:(k:ℝ)*aa k<=(k:ℝ)*k:=ab hk' (by linarith)
   nlinarith
  have ash:(k:ℝ)^2<=(k:ℝ)^14:=fy x1 (by norm_num)
  have bbk:(τ:ℝ)*aa (4*Bn n)<=3*(k:ℝ)^2*(3+20000*(k:ℝ)^12):=by
   have hl0:0<=aa (4*Bn n):=bd (by linarith)
   exact a8 a53 a1o hl0 (by positivity)
  have e:3*(k:ℝ)^2*(3+20000*(k:ℝ)^12)=9*(k:ℝ)^2+60000*(k:ℝ)^14:=by
   ring
  nlinarith
 ·have hPr:(1:ℝ)<=P:=by exact_mod_cast hP
  refine (hJ P hP).trans (ab ?_ x9)
  apply al hPr
  linarith
lemma asi (x:ℝ):eR x=bt.ZD.ee x:=by
 unfold eR bt.ZD.ee
 rw[gx]
lemma ag7 (t:ℝ) {n:ℕ} (hn:1<=n):
  (n:ℂ)^(-((t:ℂ)*lu))=
   (starRingEnd ℂ) (bt.ZD.ee (bt.ZD.psi (t/(2*c2)) n)):=by
 rw[acz t hn,<- asi,<- aqz]
 congr 1
 unfold ψ bt.ZD.psi
 ring
theorem ald {t:ℝ} (ht:1024<=t) {N N':ℕ} (hN:1<=N) (hNt:(N:ℝ)<t)
  (hN':N'<=2*N):
  ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*lu))‖<=
   64*ak N*t^((1:ℝ)/5):=by
 have t8:0<t:=by linarith
 set τ:=t^((1:ℝ)/5) with u0
 have abk:τ^5=t:=by
  rw[u0,<- da,<- d7 t8.le]; norm_num
 have afh:4<=τ:=by
  have:(4:ℝ)=(1024:ℝ)^((1:ℝ)/5):=by
   rw[show (1024:ℝ)=4^(5:ℝ) by norm_num,<- d7 (by norm_num)]; norm_num
  rw[this,u0]
  exact dh (by norm_num) ht (by norm_num)
 have hR0:0<=64*ak N*τ:=by positivity
 rcases ig N' N with hle | v7
 ·rw[s0 (by omega)]
  simp only[k8,jw]
  exact hR0
 have a55:Ioc N N'=Icc (N+1) N':=by
  ext n; simp only[kq,ar]; omega
 rw[a55]
 have a1p:∑ n∈Icc (N+1) N',(n:ℂ)^(-((t:ℂ)*lu))=
   (starRingEnd ℂ) (∑ n∈Icc (N+1) N',bt.ZD.ee (bt.ZD.psi (τ^5/(2*c2)) n)):=by
  rw[m9]
  apply ai rfl
  intro n hn
  rw[ar] at hn
  rw[abk,ag7 t (by omega)]
 rw[a1p,d4]
 have hb:=bt.ZD.abj afh (P:=N+1) (m:=N') (by omega) (by omega) (by omega)
  (by
   have h2:τ^10=t^2:=by rw[show τ^10=(τ^5)^2 by ring,abk]
   rw[h2]; push_cast; nlinarith)
 have hN1:(1:ℝ)<=N:=by exact_mod_cast hN
 have hP:(((N+1:ℕ):ℝ))<=2*N:=by push_cast; linarith
 have zr:‖∑ n∈Icc (N+1) N',bt.ZD.ee (bt.ZD.psi (τ^5/(2*c2)) n)‖^2<=
   (64*ak N*τ)^2:=by
  refine hb.trans ?_
  have hs:ak N^2=N:=ly (by linarith)
  have:(64*ak N*τ)^2=4096*N*τ^2:=by rw[i5,i5,hs]; ring
  rw[this]
  have be4:0<=τ^2:=by positivity
  nlinarith
 by_contra aor
 push_neg at aor
 have h0:=aw (∑ n∈Icc (N+1) N',bt.ZD.ee (bt.ZD.psi (τ^5/(2*c2)) n))
 nlinarith
theorem a56 (t:ℝ) (k M N N':ℕ) (hM:1<=M) (hN':N'<=2*N) (hMN:2*(M:ℝ)^2<=N):
  ‖∑ n∈Ioc N N',eR (ψ t n)‖<=
   (∑ n∈Ioc N N',∑ m₁∈Icc (1:ℤ) M,
    ‖W k (Icc 1 M) (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖)/(M:ℝ)^2+
   N*(2*|t| *((M:ℝ)^2/N)^(k+1))+2*(M:ℝ)^2:=by
 classical
 set X:=Icc (1:ℤ) M with hX
 set S:=∑ n∈Ioc N N',eR (ψ t n) with hS
 have xi:(0:ℝ)<M:=by exact_mod_cast hM
 have hN0:(0:ℝ)<N:=by nlinarith
 have ag8:X.card=M:=by rw[hX,ky]; simp
 have agh:((Ioc N N').card:ℝ)<=N:=by
  rw[rz]; exact_mod_cast (by omega:N'-N<=N)
 have u3:∀ m∈X,1<=m∧m<=M:=fun m hm=>by rw[hX,ar] at hm; exact hm
 have adh:∀ m₁∈X,∀ m₂∈X,
   ‖S-∑ n∈Ioc N N',eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂))‖<=2*(M:ℝ)^2:=by
  intro m₁ h₁ m₂ h₂
  obtain ⟨a1,a2⟩:=u3 m₁ h₁
  obtain ⟨b1,b2⟩:=u3 m₂ h₂
  have hy0:0<=m₁*m₂:=by positivity
  have aq3:(((m₁*m₂).toNat:ℕ):ℝ)=(m₁:ℝ)*m₂:=by
   have:(((m₁*m₂).toNat:ℕ):ℤ)=m₁*m₂:=ll hy0
   exact_mod_cast this
  have h:=shift_le (fun n=>eR (ψ t n)) (fun n=>i6 (y6 _)) N N' (m₁*m₂).toNat
  have e:∀ n:ℕ,eR (ψ t ((n+(m₁*m₂).toNat:ℕ):ℝ))=
    eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)):=by
   intro n; push_cast; rw[aq3]
  simp only[e] at h
  refine h.trans ?_
  rw[aq3]
  have ha:(m₁:ℝ)<=M:=by exact_mod_cast a2
  have hb:(m₂:ℝ)<=M:=by exact_mod_cast b2
  have ha1:(1:ℝ)<=m₁:=by exact_mod_cast a1
  have hb1:(1:ℝ)<=m₂:=by exact_mod_cast b1
  have:(m₁:ℝ)*m₂<=(M:ℝ)^2:=by
   rw[sq]; exact a8 ha hb (by linarith) (by linarith)
  linarith
 have auz:((M:ℂ)^2)*S=
   ∑ m₁∈X,∑ m₂∈X,(S-∑ n∈Ioc N N',eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)))+
   ∑ n∈Ioc N N',∑ m₁∈X,∑ m₂∈X,eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)):=by
  have h1:∑ m₁∈X,∑ m₂∈X,∑ n∈Ioc N N',eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂))=
    ∑ n∈Ioc N N',∑ m₁∈X,∑ m₂∈X,eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)):=by
   calc ∑ m₁∈X,∑ m₂∈X,∑ n∈Ioc N N',eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂))
     = ∑ m₁∈X,∑ n∈Ioc N N',∑ m₂∈X,eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)):=
         ai rfl (fun m₁ _=>d0)
    _=_:=d0
  rw[<- h1]
  simp only[dn,a9,ag8,cp]
  ring
 have hE:∀ n∈Ioc N N',‖∑ m₁∈X,∑ m₂∈X,eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂))‖<=
   ∑ m₁∈X,‖W k X (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖+
    (M:ℝ)^2*(2*|t| *((M:ℝ)^2/N)^(k+1)):=by
  intro n hn
  rw[kq] at hn
  have hnN:(N:ℝ)<n:=by exact_mod_cast hn.1
  have t6:(0:ℝ)<n:=by linarith
  refine (ai6 t k M t6 (by linarith)).trans ?_
  apply e8 le_rfl
  apply ab _ (by positivity)
  apply ab _ (by positivity)
  apply aj (by positivity)
  exact bb (by positivity) hN0 hnN.le
 have u5:(M:ℝ)^2*‖S‖<=(M:ℝ)^2*(2*(M:ℝ)^2)+
   ((∑ n∈Ioc N N',∑ m₁∈X,‖W k X (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖)+
    N*((M:ℝ)^2*(2*|t| *((M:ℝ)^2/N)^(k+1)))):=by
  have hn:‖((M:ℂ)^2)*S‖=(M:ℝ)^2*‖S‖:=by
   rw[bo,la,gf]
  rw[<- hn,auz]
  refine (ds _ _).trans (e8 ?_ ?_)
  ·refine (c5 _ _).trans ?_
   calc ∑ m₁∈X,‖∑ m₂∈X,(S-∑ n∈Ioc N N',eR (ψ t ((n:ℝ)+(m₁:ℝ)*m₂)))‖
     <= ∑ m₁∈X,∑ a1m∈X,2*(M:ℝ)^2:=by
         apply ao
         intro m₁ h₁
         exact (c5 _ _).trans (ao fun m₂ h₂=>adh m₁ h₁ m₂ h₂)
    _ = (M:ℝ)^2*(2*(M:ℝ)^2):=by
        simp only[a9,ag8,cp]; ring
  ·refine (c5 _ _).trans ?_
   refine (ao hE).trans ?_
   rw[cu,a9,cp]
   apply e8 le_rfl
   apply ag agh (by positivity)
 have hM2:(0:ℝ)<(M:ℝ)^2:=by positivity
 have:‖S‖<=2*(M:ℝ)^2+((∑ n∈Ioc N N',∑ m₁∈X,
   ‖W k X (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖)/(M:ℝ)^2+
   N*(2*|t| *((M:ℝ)^2/N)^(k+1))):=by
  rw[<- mul_le_mul_iff_of_pos_left hM2]
  calc (M:ℝ)^2*‖S‖<=_:=u5
   _ = (M:ℝ)^2*(2*(M:ℝ)^2+((∑ n∈Ioc N N',∑ m₁∈X,
       ‖W k X (fun j=>vb t k n j*(m₁:ℝ)^(j.val+1))‖)/(M:ℝ)^2+
       N*(2*|t| *((M:ℝ)^2/N)^(k+1)))):=by
       field_simp
 linarith
theorem asj (s:ℕ) (hs:1<=s) (I:Finset ℕ) (X:Finset ℤ) (a:ℕ->ℤ->ℝ)
  (ha:∀ n m,0<=a n m) (Yb:ℝ) (hY:∀ n∈I,∑ m∈X,a n m^(2*s)<=Yb):
  (∑ n∈I,∑ m∈X,a n m)^(2*s)<=
   ((I.card:ℝ)*X.card)^(2*s-1)*((I.card:ℝ)*Yb):=by
 rw[<- Finset.sum_product']
 have hj:=q9 (s:=I ×ˢ X) (f:=fun p=>a p.1 p.2)
  (fun p _=>ha _ _) (2*s-1)
 rw[show 2*s-1+1=2*s by omega,iz] at hj
 push_cast at hj
 rcases (show (0:ℝ)<=(I.card:ℝ)*X.card by positivity).eq_or_lt with h0 | tj
 ·have hc:(I ×ˢ X).card=0:=by
   rw[iz]; exact_mod_cast h0.symm
  rw[n8.mp hc,k8,zero_pow (by omega)]
  rw[<- h0,zero_pow (by omega),zero_mul]
 rw[ay (fb tj _)] at hj
 have hsum:∑ p∈I ×ˢ X,a p.1 p.2^(2*s)<=(I.card:ℝ)*Yb:=by
  rw[ep]
  calc ∑ n∈I,∑ m∈X,a n m^(2*s)<=∑ _n∈I,Yb:=ao hY
   _=(I.card:ℝ)*Yb:=by rw[a9,cp]
 calc (∑ p∈I ×ˢ X,a p.1 p.2)^(2*s)<=
       (∑ p∈I ×ˢ X,a p.1 p.2^(2*s))*((I.card:ℝ)*X.card)^(2*s-1):=hj
  _ ≤ ((I.card:ℝ)*Yb)*((I.card:ℝ)*X.card)^(2*s-1):=
      ag hsum (by positivity)
  _=_:=by ring
lemma ay5 (k s M:ℕ) (hs:1<=s):
  ∀ q∈tc s (Icc (1:ℤ) M) ×ˢ tc s (Icc (1:ℤ) M),∀ j:Fin k,
   |Dd k s q j|<((s*M^(j.val+1):ℕ):ℤ):=by
 intro q hq j
 rw[bm] at hq
 have hb:∀ x∈tc s (Icc (1:ℤ) M),(s:ℤ)<=sig k s x j∧
   sig k s x j<=(s:ℤ)*(M:ℤ)^(j.val+1):=by
  intro x hx
  have hxi:∀ i,1<=x i∧x i<=M:=fun i=>by
   have:=td.mp hx i; rw[ar] at this; exact this
  unfold sig
  constructor
  ·calc (s:ℤ)=∑ _i:Fin s,(1:ℤ):=by simp
    _<=∑ i,x i^(j.val+1):=ao fun i _=>dx (hxi i).1
  ·calc ∑ i,x i^(j.val+1)<=∑ _i:Fin s,(M:ℤ)^(j.val+1):=
         ao fun i _=>aj (by linarith[(hxi i).1]) (hxi i).2 _
    _=(s:ℤ)*(M:ℤ)^(j.val+1):=by simp
 obtain ⟨h1,h2⟩:=hb q.1 hq.1
 obtain ⟨h3,h4⟩:=hb q.2 hq.2
 have hs':(1:ℤ)<=s:=by exact_mod_cast hs
 unfold Dd
 rw[rt,abs_lt]
 push_cast
 constructor <;> linarith
lemma alx (H:ℕ) (α:ℝ):
  ∑ g∈Ioo (-(H:ℤ)) H,wt H (α*g)<=4*(H:ℝ)^2:=by
 calc ∑ g∈Ioo (-(H:ℤ)) H,wt H (α*g)<=∑ _g∈Ioo (-(H:ℤ)) H,2*(H:ℝ):=
       ao fun g _=>ais _ _
  _=((2*H-1:ℕ):ℝ)*(2*H):=by rw[a9,aed,cp]
  _ ≤ (2*H)*(2*H):=by
      apply ag _ (by positivity)
      have:2*H-1<=2*H:=Nat.sub_le _ _
      exact_mod_cast this
  _=4*(H:ℝ)^2:=by ring
lemma ale (n:ℕ):∑ i∈range n,2*(i+1)=n*(n+1):=by
 induction n with
 | zero=>simp
 | succ n ih=>rw[dk,ih]; ring
lemma au0 (k s M:ℕ):
  ∏ j:Fin k,4*(((s*M^(j.val+1):ℕ):ℝ))^2=
   (4:ℝ)^k*(s:ℝ)^(2*k)*(M:ℝ)^(k*(k+1)):=by
 have e:∀ j:Fin k,4*(((s*M^(j.val+1):ℕ):ℝ))^2=
   (4*(s:ℝ)^2)*(M:ℝ)^(2*(j.val+1)):=by
  intro j; push_cast; ring
 simp_rw[e]
 rw[my,mi,fp,i1,
  jr,i5,<- ox]
 congr 2
 rw[md (fun i=>2*(i+1)) k]
 exact ale k
theorem a1q (k s M:ℕ) (hs:1<=s) (hM:1<=M) (α:Fin k->ℝ) {C e:ℝ} (hC:0<=C)
  (hJ:(J k s (Icc (1:ℤ) M):ℝ)<=C*(M:ℝ)^e)
  (w3 w4:Fin k) (hj:w3≠w4) {g₁ g₂:ℝ} (ao1:0<=g₁) (ao2:0<=g₂)
  (ajh:∑ g∈Ioo (-((s*M^(w3.val+1):ℕ):ℤ)) ((s*M^(w3.val+1):ℕ):ℤ),
    wt ((s*M^(w3.val+1):ℕ):ℝ) (α w3*g)<=
    4*(((s*M^(w3.val+1):ℕ):ℝ))^2*g₁)
  (aji:∑ g∈Ioo (-((s*M^(w4.val+1):ℕ):ℤ)) ((s*M^(w4.val+1):ℕ):ℤ),
    wt ((s*M^(w4.val+1):ℕ):ℝ) (α w4*g)<=
    4*(((s*M^(w4.val+1):ℕ):ℝ))^2*g₂):
  (∑ m∈Icc (1:ℤ) M,‖W k (Icc 1 M) (fun j=>α j*(m:ℝ)^(j.val+1))‖^(2*s))^(2*s)<=
   (M:ℝ)^((((2*s)*(2*s-1)+k*(k+1):ℕ):ℝ)+2*e)*
    (C^2*((4:ℝ)^k*(s:ℝ)^(2*k))*(g₁*g₂)):=by
 classical
 set Hb:Fin k->ℕ:=fun j=>s*M^(j.val+1) with hHb
 have hY:=asf k s hs (Icc (1:ℤ) M) α Hb (ay5 k s M hs)
 have aa0:((tc s (Icc (1:ℤ) M) ×ˢ tc s (Icc (1:ℤ) M)).card:ℝ)=(M:ℝ)^(2*s):=by
  rw[iz]
  have h1:=aca s M
  push_cast[h1]
  ring
 rw[aa0] at hY
 set G:Fin k->ℝ:=fun j=>(if j=w3 then g₁ else 1)*(if j=w4 then g₂ else 1) with hG
 have hFG:∀ j:Fin k,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g)<=
   4*((Hb j:ℕ):ℝ)^2*G j:=by
  intro j
  by_cases h1:j=w3
  ·subst h1
   simp only[hG,if_pos rfl,if_neg hj,di]
   exact ajh
  ·by_cases h2:j=w4
   ·subst h2
    simp only[hG,if_neg h1,if_pos rfl,iq]
    exact aji
   ·simp only[hG,if_neg h1,if_neg h2,di]
    exact alx _ _
 have ay7:∏ j,G j=g₁*g₂:=by
  rw[hG,my,r5,r5]
 have ai7:∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g)<=
   ((4:ℝ)^k*(s:ℝ)^(2*k)*(M:ℝ)^(k*(k+1)))*(g₁*g₂):=by
  calc ∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g)
    <= ∏ j,(4*((Hb j:ℕ):ℝ)^2*G j):=by
        apply iy
        ·intro j _
         exact cj fun g _=>aba (av _) _
        ·intro j _; exact hFG j
   _=(∏ j:Fin k,4*((Hb j:ℕ):ℝ)^2)*∏ j,G j:=my
   _ = ((4:ℝ)^k*(s:ℝ)^(2*k)*(M:ℝ)^(k*(k+1)))*(g₁*g₂):=by
       rw[ay7,hHb,au0]
 have xi:(0:ℝ)<M:=by exact_mod_cast hM
 have hJ0:(0:ℝ)<=J k s (Icc (1:ℤ) M):=av _
 have hJ2:((J k s (Icc (1:ℤ) M):ℝ))^2<=C^2*(M:ℝ)^(2*e):=by
  calc ((J k s (Icc (1:ℤ) M):ℝ))^2<=(C*(M:ℝ)^e)^2:=aj hJ0 hJ 2
   _ = C^2*(M:ℝ)^(2*e):=by
       rw[i5,<- da ((M:ℝ)^e) 2,<- d7 xi.le]
       push_cast; ring_nf
 have hP0:0<=∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g):=
  l1 fun j _=>cj fun g _=>aba (av _) _
 refine hY.trans ?_
 calc ((M:ℝ)^(2*s))^(2*s-1)*((J k s (Icc (1:ℤ) M):ℝ))^2*
       ∏ j,∑ g∈Ioo (-(Hb j:ℤ)) (Hb j),wt (Hb j) (α j*g)
   ≤ ((M:ℝ)^(2*s))^(2*s-1)*(C^2*(M:ℝ)^(2*e))*
       (((4:ℝ)^k*(s:ℝ)^(2*k)*(M:ℝ)^(k*(k+1)))*(g₁*g₂)):=by
       apply a8 (ab hJ2 (by positivity)) ai7 hP0 (by positivity)
  _ = (M:ℝ)^((((2*s)*(2*s-1)+k*(k+1):ℕ):ℝ)+2*e)*
        (C^2*((4:ℝ)^k*(s:ℝ)^(2*k))*(g₁*g₂)):=by
      rw[c6 xi,da,oy,ox]
      ring
lemma au1 {t:ℝ} (ht:0<t) (k:ℕ) {n:ℝ} (hn:0<n) (j:Fin k):
  |vb t k n j|=t/(2*c2*((j.val:ℝ)+1)*n^(j.val+1)):=by
 unfold vb
 rw[abs_div,n4,j1,abs_pow,j1,abs_one,sf,di,
  a7 (by positivity:(0:ℝ)<t/(2*c2)),
  a7 (by positivity:(0:ℝ)<((j.val:ℝ)+1)*n^(j.val+1))]
 field_simp
lemma am1 (H:ℕ) {α B HB:ℝ} (ak7:α≠0) (hα:|α|<=1/2) (hH:1<=H*|α|)
  (hB:|α|<=B) (hHB:(H:ℝ)<=HB):
  ∑ g∈Ioo (-(H:ℤ)) H,wt H (α*g)<=4*(H:ℝ)^2*(25*B*(1+aa HB)):=by
 have h:=aqy α ak7 hα H hH
 have xw:0< |α|:=ue.mpr ak7
 have hH0:(0:ℝ)<H:=by
  by_contra h0; push_neg at h0
  have:(H:ℝ)=0:=le_antisymm h0 (av _)
  rw[this,zero_mul] at hH; linarith
 have hl:aa (1/|α|)<=aa HB:=by
  apply a5 (by positivity)
  rw[ay xw]
  nlinarith
 have vc:0<=aa (1/|α|):=bd (by rw[bl xw]; linarith)
 calc ∑ g∈Ioo (-(H:ℤ)) H,wt H (α*g)
   <= 100*(H:ℝ)^2*|α| *(1+aa (1/|α|)):=h
  _ ≤ 100*(H:ℝ)^2*B*(1+aa HB):=by
      apply a8 (ab hB (by positivity)) (by linarith)
       (by linarith) (by nlinarith)
  _=4*(H:ℝ)^2*(25*B*(1+aa HB)):=by ring
lemma ag9 {x:ℝ} (hx:0<=x):aa x<=2*ak x:=by
 have h:=np hx (show (0:ℝ)<1/2 by norm_num)
 rw[<- ft] at h
 linarith
lemma aha:(4:ℝ)<=af 2:=by
 have he:=i9
 have:af 2=af 1*af 1:=by rw[<- bs]; norm_num
 nlinarith
lemma afv {q:ℝ} (hq:1<=q):8*q<=af (3*q):=by
 have h1:af (3*q)=af q^3:=by
  rw[<- db]; norm_num
 have h2:1+q<=af q:=by have:=cw q; linarith
 have h3:(1+q)^3<=af q^3:=aj (by linarith) h2 3
 have h4:0<=q^2+4*q-1:=by nlinarith
 have h5:=b7 (oa.mpr hq) h4
 have h6:(1+q)^3-8*q=(q-1)*(q^2+4*q-1):=by ring
 linarith
lemma ahb {t L u x:ℝ} {N M s k n:ℕ} (j:Fin k) (t8:0<t) (vc:0<L)
  (t7:(0:ℝ)<N) (aaa:(N:ℝ)=af L) (ac0:t=af (u*L))
  (hxe:x=af (49/100*L)) (hx2:2<=x) (ao3:x/2<=M) (aar:(1:ℝ)<=s)
  (hnR:(N:ℝ)<n) (ao4:(n:ℝ)<=2*N) (hu2:20/9<=u)
  (hqu:u<=(j.val:ℝ)+1) (a57:(j.val:ℝ)+1<=u+2)
  (hqL:5*((j.val:ℝ)+1)<=6/1000*L):
  vb t k n j≠0∧|vb t k n j|<=1/2∧
   1<=((s*M^(j.val+1):ℕ):ℝ)*|vb t k n j|∧
   |vb t k n j|<=t/(N:ℝ)^(j.val+1):=by
 have t6:(0:ℝ)<n:=by linarith
 have xj:=au1 t8 k t6 j
 set q:=j.val+1 with a1r
 have hqR:(q:ℝ)=(j.val:ℝ)+1:=by rw[a1r]; push_cast; ring
 have hpi:=du
 have hq1:(1:ℝ)<=(j.val:ℝ)+1:=by have:=av (α:=ℝ) j.val; linarith
 have hc1:2<=2*c2*((j.val:ℝ)+1):=by nlinarith[jq]
 have a58:(N:ℝ)^q<=(n:ℝ)^q:=aj t7.le hnR.le q
 have ay8:(0:ℝ)<(n:ℝ)^q:=fb t6 q
 have xo:(n:ℝ)^q<=2*c2*((j.val:ℝ)+1)*(n:ℝ)^q:=by
  have:=ag hc1 ay8.le
  linarith
 have htq:t<=(N:ℝ)^q:=by
  rw[ac0,aaa,<- db]
  apply b4.mpr
  rw[hqR]
  exact ag hqu vc.le
 have au2:|vb t k n j|<=t/(N:ℝ)^q:=by
  rw[xj]
  apply bb t8.le (by positivity)
  exact a58.trans xo
 refine ⟨?_, ?_, ?_,au2⟩
 ·intro h0
  have h1:|vb t k n j|=0:=by rw[h0,abs_zero]
  rw[xj] at h1
  have:0<t/(2*c2*((j.val:ℝ)+1)*(n:ℝ)^q):=by positivity
  linarith
 ·rw[xj,ay (by positivity)]
  have:=ag hc1 ay8.le
  linarith
 ·rw[xj]
  have hMq:(x/2)^q<=(M:ℝ)^q:=aj (by linarith) ao3 q
  have hnq:(n:ℝ)^q<=(2*N)^q:=aj t6.le ao4 q
  have ay9:(0:ℝ)<2^q:=by positivity
  have h4q:(2:ℝ)^q*2^q<=af ((q:ℝ)*2):=by
   rw[<- i5,db]
   exact aj (by norm_num) (by norm_num; exact aha) q
  have a59:2*c2*((j.val:ℝ)+1)<=af (3*q):=by
   have h1:2*c2*((j.val:ℝ)+1)<=8*(q:ℝ):=by
    rw[hqR]; nlinarith[j3]
   exact h1.trans (afv (by rw[hqR]; exact hq1))
  have xm:3*(q:ℝ)+(q:ℝ)*2+q*L<=u*L+q*(49/100*L):=by
   rw[hqR]
   have h1:=ag a57 vc.le
   have h2:=ag hu2 vc.le
   nlinarith
  have abd:2*c2*((j.val:ℝ)+1)*(2*(N:ℝ))^q<=t *(x/2)^q:=by
   have e1:(2*(N:ℝ))^q=2^q*af (q*L):=by
    rw[i5,aaa,<- db]
   have e2:(x/2)^q=af (q*(49/100*L))/2^q:=by
    rw[l8,hxe,<- db]
   rw[e1,e2,ac0,rp,bl ay9]
   calc 2*c2*((j.val:ℝ)+1)*(2^q*af (q*L))*2^q
     = (2*c2*((j.val:ℝ)+1))*af (q*L)*(2^q*2^q):=by ring
    _ ≤ af (3*q)*af (q*L)*af ((q:ℝ)*2):=by
        apply a8 (ag a59 (bx _).le) h4q
         (by positivity) (by positivity)
    _ = af (3*q+(q:ℝ)*2+q*L):=by
        rw[<- bs,<- bs]; ring_nf
    _<=af (u*L+q*(49/100*L)):=b4.mpr (by linarith)
    _=af (u*L)*af (q*(49/100*L)):=bs _ _
  have bde:2*c2*((j.val:ℝ)+1)*(n:ℝ)^q<=t *(M:ℝ)^q:=by
   calc 2*c2*((j.val:ℝ)+1)*(n:ℝ)^q
     <= 2*c2*((j.val:ℝ)+1)*(2*(N:ℝ))^q:=
         ab hnq (by positivity)
    _<=t *(x/2)^q:=abd
    _<=t *(M:ℝ)^q:=ab hMq t8.le
  rw[rp,bl (by positivity),iq]
  push_cast
  have a6a:0<=(M:ℝ)^q:=by positivity
  have:t *(M:ℝ)^q<=(s:ℝ)*(M:ℝ)^q*t:=by
   have:=ag aar (b7 a6a t8.le)
   linarith
  linarith
theorem aly {t:ℝ} {N N':ℕ} (hN2:2<=N) (hNt:(N:ℝ)<t) (hN':N'<=2*N)
  (vu:aa N/aa t<=9/20)
  (hL:10^50*(aa t/aa N)^14<=aa N):
  ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*lu))‖<=
   (N:ℝ)^(1-(1/10^18)*(aa N/aa t)^6):=by
 classical
 have hNR:(2:ℝ)<=N:=by exact_mod_cast hN2
 have t7:(0:ℝ)<N:=by linarith
 have t8:0<t:=by linarith
 set L:=aa N with acu
 set T:=aa t with ace
 have vc:0<L:=eo (by linarith)
 have hLT:L<T:=Real.log_lt_log t7 hNt
 have ua:0<T:=by linarith
 set u:=T/L with hu
 have x8:1<=u:=by rw[hu,bl vc]; linarith
 have hu2:20/9<=u:=by
  rw[hu,bl vc]
  have:=vu; rw[ay ua] at this; linarith
 have a1s:L/T=1/u:=by rw[hu]; field_simp
 have be5:1<=u^14:=dx x8
 have a6b:(10:ℝ)^50<=L:=br (by linarith) hL
 have aem:∀ a:ℝ,(N:ℝ)^a=af (a*L):=by
  intro a; rw[c9 t7,gx]
 have ac0:t=af (u*L):=by
  rw[hu,qc _ vc.ne',ace,fl t8]
 have aaa:(N:ℝ)=af L:=by rw[acu,fl t7]
 set k:ℕ:=⌈50*u⌉₊+100 with hk
 have hk2:2<=k:=by omega
 have a6c:50*u+100<=(k:ℝ):=by
  rw[hk]; push_cast; linarith[f9 (50*u)]
 have aza:(k:ℝ)<=150*u:=by
  rw[hk]; push_cast
  have:=ef (show 0<=50*u by linarith)
  linarith
 have x1:(1:ℝ)<=k:=by linarith
 have hLk:10^19*(k:ℝ)^14<=L:=by
  have h1:(k:ℝ)^14<=(150*u)^14:=aj (by linarith) aza 14
  have h2:(150*u)^14=150^14*u^14:=by ring
  have h3:(10:ℝ)^19*150^14<=10^50:=by norm_num
  have h4:=ag h3 (show (0:ℝ)<=u^14 by positivity)
  have h5:=ab h1 (show (0:ℝ)<=10^19 by norm_num)
  rw[h2] at h5
  linarith
 have ash:(k:ℝ)<=(k:ℝ)^14:=by
  calc (k:ℝ)=(k:ℝ)^1:=(pow_one _).symm
   _<=(k:ℝ)^14:=fy x1 (by norm_num)
 obtain ⟨s,C,uu,hs4,x9,a1t,hJ⟩:=alc k hk2
 have aar:(1:ℝ)<=s:=by exact_mod_cast uu
 have asl:(s:ℝ)<=4*(k:ℝ)^3:=by exact_mod_cast hs4
 set x:=(N:ℝ)^((49:ℝ)/100) with hx
 have hxe:x=af (49/100*L):=aem _
 have hx2:2<=x:=by
  rw[hxe]; have:=cw (49/100*L); linarith
 set M:ℕ:=⌊x⌋₊ with hM
 have anp:(M:ℝ)<=x:=ju (by linarith)
 have ao3:x/2<=M:=by
  have:=g8 x
  rw[<- hM] at this
  linarith
 have asm:(1:ℝ)<=M:=by linarith
 have w6:1<=M:=by exact_mod_cast asm
 have xi:(0:ℝ)<M:=by linarith
 have anq:aa M<=49/100*L:=by
  have:=a5 xi anp
  rwa[hxe,kt] at this
 have hM2:(M:ℝ)^2<=af (98/100*L):=by
  calc (M:ℝ)^2<=x^2:=aj (by linarith) anp 2
   _=af (98/100*L):=by rw[hxe,<- db]; congr 1; push_cast; ring
 have hMN:2*(M:ℝ)^2<=N:=by
  rw[aaa]
  have h1:af L=af (98/100*L)*af (2/100*L):=by
   rw[<- bs]; ring_nf
  have h2:2<=af (2/100*L):=by
   have:=cw (2/100*L); linarith
  rw[h1]
  have:=ab h2 (bx (98/100*L)).le
  linarith
 set p₀:ℕ:=⌈u⌉₊ with bdf
 have alf:u<=p₀:=f9 u
 have am2:(p₀:ℝ)<u+1:=ef (by linarith)
 have bbt:2<=p₀:=by
  have:(2:ℝ)<p₀:=by linarith
  exact_mod_cast this.le
 have azc:p₀+1<k:=by
  have:((p₀+1:ℕ):ℝ)<k:=by push_cast; linarith
  exact_mod_cast this
 set w3:Fin k:=⟨p₀-1,by omega⟩ with at8
 set w4:Fin k:=⟨p₀,by omega⟩ with at9
 have hj:w3≠w4:=by
  intro h; have:=dy Fin.val h; simp[at8,at9] at this; omega
 have aua:w3.val+1=p₀:=by simp[at8]; omega
 have aub:w4.val+1=p₀+1:=by simp[at9]
 have alg:(w3.val:ℝ)+1=p₀:=by exact_mod_cast aua
 have alh:(w4.val:ℝ)+1=p₀+1:=by exact_mod_cast aub
 have aq4:5*((p₀:ℝ)+1)<=6/1000*L:=by
  have:(p₀:ℝ)+1<=k:=by
   have:((p₀+1:ℕ):ℝ)<=k:=by exact_mod_cast azc.le
   push_cast at this; exact this
  linarith
 set Λ:=1+aa (((s*M^k:ℕ):ℝ)) with hΛ
 have a6d:(1:ℝ)<=((s*M^k:ℕ):ℝ):=by
  push_cast; exact qm aar (dx asm)
 have azd:1<=Λ:=by have:=bd a6d; linarith
 have a1u:Λ<=(k:ℝ)*L:=by
  rw[hΛ]
  push_cast
  rw[ca (by linarith) (by positivity),cq]
  have h1:aa s<=s:=by
   have:=bz (show (0:ℝ)<s by linarith); linarith
  have h2:(k:ℝ)*aa M<=(k:ℝ)*(49/100*L):=
   ab anq (by linarith)
  have be6:(k:ℝ)^3<=(k:ℝ)^15:=fy x1 (by norm_num)
  have bdg:(1:ℝ)<=(k:ℝ)^15:=dx x1
  have hkL:=ab hLk (show (0:ℝ)<=k by linarith)
  have e:(k:ℝ)*(10^19*(k:ℝ)^14)=10^19*(k:ℝ)^15:=by ring
  rw[e] at hkL
  linarith
 have aze:((s*M^(w3.val+1):ℕ):ℝ)<=((s*M^k:ℕ):ℝ)∧
   ((s*M^(w4.val+1):ℕ):ℝ)<=((s*M^k:ℕ):ℝ):=by
  constructor <;> push_cast <;> apply ab _ (by linarith) <;>
   apply fy asm <;> omega
 have hNq:t<=(N:ℝ)^p₀:=by
  rw[ac0,aaa,<- db]
  apply b4.mpr
  exact ag alf vc.le
 set X:=Icc (1:ℤ) M with hX
 set g₁:ℝ:=25*1*Λ with ao1
 set g₂:ℝ:=25*(1/(N:ℝ))*Λ with ao2
 set e:ℝ:=2*(s:ℝ)-k*(k+1)/2+1 with he
 set EM:ℝ:=(((2*s)*(2*s-1)+k*(k+1):ℕ):ℝ)+2*e with hEM
 have a6e:EM=4*(s:ℝ)^2+2*s+2:=by
  rw[hEM,he]
  have:(((2*s)*(2*s-1)+k*(k+1):ℕ):ℝ)=
    2*(s:ℝ)*(2*s-1)+k*(k+1):=by
   rw[Nat.cast_add,pb,il (by omega)]; push_cast; ring
  rw[this]; ring
 set Q:ℝ:=(C+1)^2*((4:ℝ)^k*(s:ℝ)^(2*k))*(g₁*g₂) with hQ
 have azf:0<Λ:=by linarith only[azd]
 have hC1:0<C+1:=by linarith only[x9]
 have ahc:0<g₁:=by rw[ao1]; positivity
 have ahd:0<g₂:=by rw[ao2]; positivity
 have hA1:0<(C+1)^2:=fb hC1 2
 have hA2:(0:ℝ)<(4:ℝ)^k:=by positivity
 have hA3:(0:ℝ)<(s:ℝ)^(2*k):=fb (by linarith only[aar]) _
 have hQ0:0<Q:=by rw[hQ]; exact ji (ji hA1 (ji hA2 hA3)) (ji ahc ahd)
 set δ:ℝ:=1/(400*(s:ℝ)^2) with uf
 have a6f:aa g₁=aa 25+aa Λ:=by
  rw[show g₁=25*Λ by rw[ao1]; ring,ca (by norm_num) azf.ne']
 have a6g:aa g₂=aa 25+aa Λ-L:=by
  rw[show g₂=25*Λ/N by rw[ao2]; ring,ik (by positivity) t7.ne',
   ca (by norm_num) azf.ne',acu]
 have a1v:aa Q=2*aa (C+1)+k*aa 4+2*k*aa s+
   2*aa 25+2*aa Λ-L:=by
  rw[hQ,ca (ji hA1 (ji hA2 hA3)).ne' (ji ahc ahd).ne',
   ca hA1.ne' (ji hA2 hA3).ne',ca hA2.ne' hA3.ne',
   ca ahc.ne' ahd.ne',a6f,a6g,cq,cq,cq]
  push_cast; ring
 have abd:2*aa M+aa Q+L/100+4*(s:ℝ)^2*aa 3<=0:=by
  rw[a1v]
  have l4:aa 4<=3:=by
   have:=bz (show (0:ℝ)<4 by norm_num); linarith only[this]
  have l3:aa 3<=2:=by
   have:=bz (show (0:ℝ)<3 by norm_num); linarith only[this]
  have l25:aa 25<=24:=by
   have:=bz (show (0:ℝ)<25 by norm_num); linarith only[this]
  have ls:aa s<=4*(k:ℝ)^3:=by
   have:=bz (show (0:ℝ)<s by linarith only[aar])
   linarith only[this,asl]
  have lΛ:aa Λ<=L/1000:=by
   refine (ag9 (by linarith only[azd])).trans ?_
   have h1:Λ<=((L/2000)^2):=by
    have a6h:(k:ℝ)<=L/(4*10^6):=by
     rw[bl (by norm_num)]; linarith only[hLk,ash,x1]
    have h2:=ag a6h vc.le
    have e:L/(4*10^6)*L=(L/2000)^2:=by ring
    linarith only[h2,e,a1u]
   have h2:=dg h1
   rw[fk (by linarith only[vc])] at h2
   linarith only[h2]
  have hk4:(k:ℝ)^4<=(k:ℝ)^14:=fy x1 (by norm_num)
  have hk6:(k:ℝ)^6<=(k:ℝ)^14:=fy x1 (by norm_num)
  have hs2:(s:ℝ)^2<=16*(k:ℝ)^6:=by
   have:=aj (by linarith only[aar]) asl 2
   have e:(4*(k:ℝ)^3)^2=16*(k:ℝ)^6:=by ring
   linarith only[this,e]
  have hks:(k:ℝ)*aa s<=(k:ℝ)*(4*(k:ℝ)^3):=
   ab ls (by linarith only[x1])
  have a6i:=bd (show (1:ℝ)<=3 by norm_num)
  have a1w:(s:ℝ)^2*aa 3<=16*(k:ℝ)^6*2:=
   a8 hs2 l3 a6i (by positivity)
  have a6j:(k:ℝ)*aa 4<=(k:ℝ)*3:=
   ab l4 (by linarith only[x1])
  have a6k:(k:ℝ)*(4*(k:ℝ)^3)=4*(k:ℝ)^4:=by ring
  linarith only[a1t,a6j,hks,a6k,l25,lΛ,a1w,hk4,hk6,ash,x1,hLk,anq,vc]
 have ahu:0<δ:=by rw[uf]; positivity
 have a6l:δ<=1/400:=by
  rw[uf,ax (by positivity) (by norm_num)]
  have:=dx (n:=2) aar
  linarith only[this]
 have a6m:(N:ℝ)*(2*|t| *((M:ℝ)^2/N)^(k+1))<=2:=by
  have h1:(M:ℝ)^2/N<=af (-(2/100*L)):=by
   rw[ay t7,aaa,<- bs]
   refine hM2.trans (i6 ?_)
   congr 1; ring
  have h2:((M:ℝ)^2/N)^(k+1)<=af (-(2/100*L))^(k+1):=
   aj (by positivity) h1 _
  rw[<- db] at h2
  rw[a7 t8]
  have h3:(N:ℝ)*t *af (((k+1:ℕ):ℝ)*-(2/100*L))<=1:=by
   rw[aaa,ac0,<- bs,<- bs]
   apply jt.mpr
   push_cast
   have:=ag a6c vc.le
   linarith only[this,vc]
  calc (N:ℝ)*(2*t *((M:ℝ)^2/N)^(k+1))
    <= (N:ℝ)*(2*t *af (((k+1:ℕ):ℝ)*-(2/100*L))):=by
        apply ab _ t7.le
        exact ab h2 (by positivity)
   _=2*((N:ℝ)*t *af (((k+1:ℕ):ℝ)*-(2/100*L))):=by ring
   _<=2:=by linarith only[h3]
 have au3:2+2*(M:ℝ)^2<=2/3*af ((1-δ)*L):=by
  have h1:af ((1-δ)*L)>=af (98/100*L)*10:=by
   have h2:(1-δ)*L>=98/100*L+175/10000*L:=by
    have:=ag a6l vc.le
    linarith only[this]
   have h3:af (175/10000*L)>=10:=by
    have:=cw (175/10000*L); linarith only[this,a6b]
   calc af ((1-δ)*L)>=af (98/100*L+175/10000*L):=
         b4.mpr h2
    _=af (98/100*L)*af (175/10000*L):=bs _ _
    _ ≥ af (98/100*L)*10:=
        ab h3 (bx _).le
  have h4:1<=af (98/100*L):=qe (by positivity)
  linarith only[h1,h4,hM2]
 have a6n:(1/10^18)*(aa N/aa t)^6<=δ:=by
  rw[<- acu,<- ace,a1s,uf,one_div_pow,one_div_mul_one_div]
  have hs2:(s:ℝ)^2<=16*150^6*u^6:=by
   have h1:(s:ℝ)<=4*(150*u)^3:=
    asl.trans (ab
     (aj (by linarith only[x1]) aza 3) (by norm_num))
   have h2:=aj (by linarith only[aar]) h1 2
   have e:(4*(150*u)^3)^2=16*150^6*u^6:=by ring
   linarith only[h2,e]
  apply dr (by positivity)
  have h3:(400:ℝ)*(16*150^6)<=10^18:=by norm_num
  have h4:=ag h3 (show (0:ℝ)<=u^6 by positivity)
  linarith only[h4,hs2]
 have uq:af ((1-δ)*L)<=
   (N:ℝ)^(1-(1/10^18)*(aa N/aa t)^6):=by
  rw[aem]
  apply b4.mpr
  have:=ag a6n vc.le
  linarith only[this]
 have hJM:(J k s (Icc (1:ℤ) M):ℝ)<=(C+1)*(M:ℝ)^e:=by
  have h1:=hJ M w6
  have hMe:0<=(M:ℝ)^(2*(s:ℝ)-k*(k+1)/2+1):=ei xi.le _
  rw[he]
  have e2:(C+1)*(M:ℝ)^(2*(s:ℝ)-k*(k+1)/2+1)=
    C*(M:ℝ)^(2*(s:ℝ)-k*(k+1)/2+1)+
     (M:ℝ)^(2*(s:ℝ)-k*(k+1)/2+1):=by ring
  linarith only[h1,hMe,e2]
 have hYn:∀ n∈Ioc N N',
   (∑ m∈X,‖W k X (fun j=>vb t k n j*(m:ℝ)^(j.val+1))‖^(2*s))^(2*s)<=
    (M:ℝ)^EM*Q:=by
  intro n hn
  rw[kq] at hn
  have hnR:(N:ℝ)<n:=by exact_mod_cast hn.1
  have ao4:(n:ℝ)<=2*N:=by exact_mod_cast (br hn.2 hN')
  obtain ⟨a0,a1,a2,a3⟩:=ahb (s:=s) (M:=M) w3 t8 vc t7 aaa ac0 hxe hx2
   ao3 aar hnR ao4 hu2 (by rw[alg]; exact alf) (by rw[alg]; linarith only[am2])
   (by rw[alg]; linarith only[aq4])
  obtain ⟨b0,b1,b2,b3⟩:=ahb (s:=s) (M:=M) w4 t8 vc t7 aaa ac0 hxe hx2
   ao3 aar hnR ao4 hu2 (by rw[alh]; linarith only[alf]) (by rw[alh]; linarith only[am2])
   (by rw[alh]; exact aq4)
  have hB1:|vb t k n w3|<=1:=by
   refine a3.trans ?_
   rw[dw (by positivity),aua]
   exact hNq
  have hB2:|vb t k n w4|<=1/(N:ℝ):=by
   refine b3.trans ?_
   rw[aub,ob,ax (by positivity) t7,iq]
   exact ag hNq t7.le
  have ajh:=am1 (s*M^(w3.val+1)) a0 a1 a2 hB1 aze.1
  have aji:=am1 (s*M^(w4.val+1)) b0 b1 b2 hB2 aze.2
  rw[<- hΛ] at ajh aji
  exact a1q k s M uu w6 (vb t k n) hC1.le hJM w3 w4 hj ahc.le ahd.le ajh aji
 set Yb:ℝ:=af ((EM*aa M+aa Q)/(2*s)) with hYb
 have azg:aa ((M:ℝ)^EM*Q)=EM*aa M+aa Q:=by
  rw[ca (dc xi _).ne' hQ0.ne',oj xi]
 have a6o:∀ n∈Ioc N N',
   ∑ m∈X,‖W k X (fun j=>vb t k n j*(m:ℝ)^(j.val+1))‖^(2*s)<=Yb:=by
  intro n hn
  set Yv:=∑ m∈X,‖W k X (fun j=>vb t k n j*(m:ℝ)^(j.val+1))‖^(2*s) with hYv
  have a6p:0<=Yv:=cj fun _ _=>by positivity
  rcases a6p.eq_or_lt with h0 | tj
  ·rw[<- h0]; exact (bx _).le
  ·have h1:=a5 (fb tj _) (hYn n hn)
   rw[cq,azg] at h1
   have h2:aa Yv<=(EM*aa M+aa Q)/(2*s):=by
    rw[bl (by positivity)]; push_cast at h1; linarith only[h1]
   calc Yv=af (aa Yv):=(fl tj).symm
    _<=Yb:=b4.mpr h2
 set Z:=∑ n∈Ioc N N',∑ m∈X,‖W k X (fun j=>vb t k n j*(m:ℝ)^(j.val+1))‖ with hZ
 have a1x:=asj s uu (Ioc N N') X
  (fun n m=>‖W k X (fun j=>vb t k n j*(m:ℝ)^(j.val+1))‖) (fun _ _=>aw _)
  Yb a6o
 have aq5:((Ioc N N').card:ℝ)<=N:=by
  rw[rz]; exact_mod_cast (by omega:N'-N<=N)
 have ag8:(X.card:ℝ)=M:=by rw[hX,ky]; simp
 have azh:Z^(2*s)<=((N:ℝ)*M)^(2*s-1)*((N:ℝ)*Yb):=by
  refine a1x.trans ?_
  rw[ag8]
  apply a8 (aj (b7 (av _) xi.le)
   (ag aq5 xi.le) _)
   (ag aq5 (bx _).le)
   (b7 (av _) (bx _).le)
   (k0 (b7 t7.le xi.le) _)
 have a6q:Z<=af ((1-δ)*L+2*aa M-aa 3):=by
  have hZ0:0<=Z:=cj fun _ _=>cj fun _ _=>aw _
  rcases hZ0.eq_or_lt with h0 | tj
  ·rw[<- h0]; exact (bx _).le
  have h1:=a5 (fb tj _) azh
  rw[cq,ca (by positivity) (by positivity),cq,
   ca t7.ne' xi.ne',ca t7.ne' (bx _).ne',
   kt,<- acu] at h1
  have xc:(0:ℝ)<s:=by linarith only[aar]
  have azi:(1-δ)*L+2*aa M-aa 3-
    (((2*s-1:ℕ):ℝ)*(L+aa M)+(L+(EM*aa M+aa Q)/(2*s)))/
     ((2*s:ℕ):ℝ)=
    -(2*aa M+aa Q+L/100+4*(s:ℝ)^2*aa 3)/
     (4*(s:ℝ)^2):=by
   rw[a6e,uf,il (by omega)]
   push_cast
   field_simp
   ring
  have hdiv:0<=-(2*aa M+aa Q+L/100+4*(s:ℝ)^2*aa 3)/
    (4*(s:ℝ)^2):=fe (by linarith only[abd]) (by positivity)
  have h2:aa Z<=(((2*s-1:ℕ):ℝ)*(L+aa M)+
    (L+(EM*aa M+aa Q)/(2*s)))/((2*s:ℕ):ℝ):=by
   rw[bl (by positivity)]
   push_cast at h1 ⊢
   linarith only[h1]
  have a1y:aa Z<=(1-δ)*L+2*aa M-aa 3:=by
   linarith only[h2,azi,hdiv]
  calc Z=af (aa Z):=(fl tj).symm
   _<=_:=b4.mpr a1y
 have hS:=a56 t k M N N' w6 hN' hMN
 have a6r:∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*lu))=∑ n∈Ioc N N',eR (ψ t n):=by
  apply ai rfl
  intro n hn
  rw[kq] at hn
  exact acz t (by omega)
 rw[a6r]
 have hZM:Z/(M:ℝ)^2<=af ((1-δ)*L)/3:=by
  rw[ay (by positivity)]
  refine a6q.trans (i6 ?_)
  rw[Real.exp_sub,bs,fl (by norm_num:(0:ℝ)<3),
   show 2*aa M=aa ((M:ℝ)^2) by rw[cq]; push_cast; ring,
   fl (by positivity)]
  ring
 linarith only[hS,hZM,a6m,au3,uq]
lemma afw (t:ℝ) (N N':ℕ) (hN':N'<=2*N):
  ‖∑ n∈Ioc N N',(n:ℂ)^(-((t:ℂ)*lu))‖<=N:=by
 refine (c5 _ _).trans ?_
 have h:∀ n∈Ioc N N',‖(n:ℂ)^(-((t:ℂ)*lu))‖=1:=by
  intro n hn
  rw[kq] at hn
  rw[acz t (by omega),y6]
 rw[ai rfl h,a9,cp,di,rz]
 exact_mod_cast (by omega:N'-N<=N)
theorem aq6:bt.ar8.ES 6 14:=by
 refine ⟨1/10^18,by positivity,10^50,⌈af 2000⌉₊,0,fun t _ N N' hN hNt hN'=>?_⟩
 have hNe:af 2000<=N:=Nat.ceil_le.mp hN
 have hNR:(2:ℝ)<=N:=by
  have:=cw (2000:ℝ); linarith
 have hN2:2<=N:=by exact_mod_cast hNR
 have t7:(0:ℝ)<N:=by linarith
 have t8:0<t:=by linarith
 set L:=aa N with acu
 set T:=aa t with ace
 have vc:0<L:=eo (by linarith)
 have hLT:L<T:=Real.log_lt_log t7 hNt
 have ua:0<T:=by linarith
 have bb8:2000<=L:=by
  have h2:=a5 (bx _) hNe
  rwa[kt] at h2
 set lam:=L/T with vu
 have ajc:0<lam:=mo vc ua
 have a1z:lam<=1:=by rw[vu,dw ua]; linarith
 have bdh:lam^6<=1:=pow_le_one₀ ajc.le a1z
 have aem:∀ a:ℝ,(N:ℝ)^a=af (a*L):=by
  intro a; rw[c9 t7,gx]
 have hE1:1<=af (10^50/lam^14):=qe (by positivity)
 have azj:0<=(N:ℝ)^(1-1/10^18*lam^6):=ei t7.le _
 have af9:∀ B:ℝ,B<=(N:ℝ)^(1-1/10^18*lam^6)->
   B<=af (10^50/lam^14)*(N:ℝ)^(1-1/10^18*lam^6):=by
  intro B hB
  nlinarith
 by_cases abh:lam<=9/20
 ·by_cases u5:10^50*(T/L)^14<=L
  ·exact af9 _ (aly hN2 hNt hN' abh u5)
  ·
   push_neg at u5
   refine (afw t N N' hN').trans ?_
   have hTL:(T/L)^14=1/lam^14:=by rw[vu,l8,l8]; field_simp
   have h1:(N:ℝ)=(N:ℝ)^(1/10^18*lam^6)*(N:ℝ)^(1-1/10^18*lam^6):=by
    rw[<- c6 t7]; norm_num
   have h2:(N:ℝ)^(1/10^18*lam^6)<=af (10^50/lam^14):=by
    rw[aem]
    apply b4.mpr
    have:10^50/lam^14=10^50*(T/L)^14:=by rw[hTL]; ring
    rw[this]
    nlinarith
   calc (N:ℝ)=(N:ℝ)^(1/10^18*lam^6)*(N:ℝ)^(1-1/10^18*lam^6):=h1
    _<=_:=ag h2 azj
 ·
  push_neg at abh
  apply af9
  have azk:(1024:ℝ)<=t:=by
   have:(1024:ℝ)<=N:=by
    have:=cw (2000:ℝ); linarith
   linarith
  refine (ald azk (by omega) hNt hN').trans ?_
  have zr:ak N=af (L/2):=by
   rw[ft,aem]; ring_nf
  have ht5:t^((1:ℝ)/5)=af (T/5):=by
   rw[c9 t8,<- ace]; ring_nf
  have hTL:T<=20/9*L:=by
   have:=abh; rw[vu,na ua] at this; linarith
  rw[zr,ht5,aem]
  have h64:(64:ℝ)<=af (L/25):=by
   have:=cw (L/25); linarith
  calc 64*af (L/2)*af (T/5)
    <= af (L/25)*af (L/2)*af (T/5):=by
        gcongr
   _=af (L/25+L/2+T/5):=by rw[<- bs,<- bs]
   _ ≤ af ((1-1/10^18*lam^6)*L):=by
       apply b4.mpr
       nlinarith
end bt.aow
theorem bt.aow.ao5:bt.abw.ZFR:=
 bt.ar8.aft (by norm_num) bt.aow.aq6
end

theorem OMA.solution : OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.H1 :=
  bt.abw.aen bt.aow.ao5 bt.ZD.aql bt.cz.uk.ar6

