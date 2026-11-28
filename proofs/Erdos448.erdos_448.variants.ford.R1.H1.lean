import OMAReductions.R_Erdos448_erdos_448_variants_ford_R1
open Finset Filter Real MeasureTheory
open scoped Pointwise Topology BigOperators Classical
namespace Ford448
noncomputable section
abbrev O:=ℝ
abbrev dv:=Nat.primesLE
abbrev dw:=Nat.choose
abbrev dz:=ArithmeticFunction.moebius
lemma _P{p:Prop}(h:p:=by positivity):p:=h
lemma _O{p:Prop}(h:p:=by omega):p:=h
lemma _N{p:Prop}(h:p:=by norm_num):p:=h
lemma _L{p:Prop}(h:p:=by linarith):p:=h
lemma _R{p:Prop}(h:p:=by ring):p:=h
lemma _Q{p:Prop}(h:p:=by nlinarith):p:=h
lemma _M{p q:Prop}(e:q)(h:q->p:=by intro h;exact_mod_cast h):p:=h e
set_option maxHeartbeats 800000 in
lemma _l{p q:Prop}(e:q)(h:q->p:=by intro h;linarith):p:=h e
alias dA:=mul_le_mul_of_nonneg_left
alias dB:=mem_filter
alias dC:=sum_le_sum_of_subset_of_nonneg
alias dD:=Nat.prime_of_mem_primeFactors
alias dE:=mul_le_mul_of_nonneg_right
alias dF:=sum_congr
alias dG:=sum_le_sum
alias dH:=Nat.pow_le_pow_right
alias dI:=div_le_div_of_nonneg_right
alias dJ:=mem_univ
alias dK:=Nat.cast_nonneg
alias dL:=div_le_div_of_nonneg_left
alias dM:=log_le_log
alias dN:=mem_range
alias dO:=measurable_pi_apply
alias dP:=mul_sum
alias dQ:=Fin.ext
alias dR:=Nat.mul_le_mul_left
alias dS:=Nat.dvd_of_mem_primeFactors
alias dT:=mem_Icc
alias dU:=Nat.prime_of_mem_primesLE
alias dV:=true_and
alias dW:=Finset.mem_image
alias dX:=one_div_le_one_div_of_le
alias dY:=Nat.mod_lt
alias dZ:=Nat.le_div_iff_mul_le
alias e0:=Finset.mem_union_left
alias e3:=nsmul_eq_mul
alias e5:=Fintype.mem_piFinset
alias e6:=Nat.factorial_succ
alias e7:=Nat.mem_primesLE
alias e8:=mul_comm
alias e9:=lt_of_lt_of_le
alias ea:=sum_nonneg
alias eb:=Finset.disjoint_left
alias ec:=ENNReal.ofReal_ne_top
alias ed:=div_nonneg
alias ee:=pow_add
alias ef:=Nat.dvd_of_mem_divisors
alias eg:=Finset.mem_singleton
alias eh:=Finset.sum_filter_add_sum_filter_not
alias ei:=Nat.cast_sub
alias ej:=Nat.support_factorization
alias ek:=mul_nonneg
alias el:=Nat.le_of_dvd
alias em:=Nat.pos_of_mem_divisors
alias en:=mul_le_mul
alias eo:=le_max_left
alias ep:=le_max_right
alias er:=card_le_card
alias es:=Fin.mk.inj
alias et:=log_pos
alias eu:=Finset.mem_union_right
alias ev:=Finset.mem_insert_self
alias ew:=Nat.prod_factorization_pow_eq_self
alias ex:=sum_const
alias ey:=Finset.prod_filter_mul_prod_filter_not
alias ez:=exp_pos
alias eA:=dif_neg
alias eB:=Finset.mem_coe
alias eC:=Nat.mul_div_cancel'
alias eD:=Nat.div_mul_le_self
alias eE:=Nat.mul_le_mul_right
alias eF:=Nat.cast_one
alias eG:=dif_pos
alias eH:=Nat.mul_le_mul
alias eI:=Nat.prime_dvd_prime_iff_eq
alias eK:=rpow_natCast
alias eL:=Set.mem_preimage
alias eM:=Set.mem_ofPred_eq
alias eN:=Nat.sub_add_cancel
alias eO:=zero_le_one
alias eP:=mul_pow
alias eQ:=Set.mem_iUnion
alias eR:=le_rfl
alias eS:=mem_powerset
alias eT:=rpow_le_rpow_of_exponent_le
alias eU:=measurable_pi_lambda
alias eV:=measurable_const
alias eW:=Finset.induction
alias eX:=exp_log
alias eY:=log_le_sub_one_of_pos
alias eZ:=ENNReal.toReal_ofReal
alias f0:=mul_assoc
alias f1:=log_nonneg
alias f2:=sum_sub_distrib
alias f3:=mem_Ico
alias f4:=measure_mono
alias f5:=Measure.prod_prod
alias f6:=Nat.lt_floor_add_one
alias f7:=Nat.choose_mul_factorial_mul_factorial
alias f8:=sum_filter
alias f9:=prod_congr
alias fa:=Finset.mem_insert_of_mem
alias fb:=sum_union_inter
alias fc:=pow_succ
alias fd:=add_le_add
alias fe:=Nat.le_induction
alias ff:=Finset.mem_union
alias fg:=Finset.mem_sigma
alias fh:=sum_bij
alias fi:=single_le_sum
alias fj:=filter_subset
alias fk:=Chebyshev.theta_eq_sum_primesLE_log
alias fl:=one_sub_inv_le_log_of_pos
alias fm:=log_pow
alias fo:=zpow_natCast
alias fp:=pow_succ'
alias fq:=Finset.notMem_empty
alias fr:=sum_image
alias fs:=card_image_of_injective
alias ft:=Nat.coprime_primes
alias fu:=Nat.cast_prod
alias fv:=mul_one
alias fw:=mem_Ioc
alias fx:=rpow_le_rpow
alias fy:=card_range
alias fz:=ne_top_of_le_ne_top
alias fA:=Nat.pow_le_pow_left
alias fB:=add_one_le_exp
alias fC:=Nat.floor_le
alias fD:=sum_add_distrib
alias fE:=Finset.card_insert_of_notMem
alias fF:=Set.mem_Ico
alias fG:=Sigma.mk.inj_iff
alias fH:=Fintype.card_fin
alias fI:=MeasurableSet.iInter
alias fJ:=Finset.add_sum_erase
alias fK:=pow_nonneg
alias fL:=Nat.Coprime.prod_right
alias fM:=ENNReal.toReal_mono
alias fN:=prod_insert
alias fO:=geom_sum_eq
alias fP:=Nat.mul_pos
alias fQ:=rpow_def_of_pos
alias fR:=Nat.eq_of_mul_eq_mul_left
alias fS:=List.rel_of_pairwise_cons
alias fT:=congr_arg
alias fU:=mem_powersetCard
alias fV:=measurableSet_le
alias fW:=Nat.mem_divisors
alias fX:=Nat.pos_of_ne_zero
alias fY:=Nat.one_le_two_pow
alias fZ:=List.mem_cons_self
alias g0:=Finset.sum_eq_zero
alias g1:=MeasureTheory.measure_biUnion_finset_le
alias g2:=Nat.le_floor
alias g3:=Nat.cast_mul
alias g4:=mem_biUnion
alias g5:=Nat.zero_le
alias g6:=Nat.le_ceil
alias g7:=Nat.cast_ofNat
alias g8:=Equiv.coe_fn_symm_mk
alias g9:=one_div
alias ga:=Finset.mem_insert
alias gb:=Nat.mul_div_cancel_left
alias gc:=if_neg
alias gd:=Nat.ordProj_dvd
alias gf:=le_trans
alias gg:=exp_nat_mul
alias gh:=hasDerivAt_id
alias gi:=Nat.mod_eq_of_lt
alias gj:=Finset.mem_sdiff
alias gk:=mul_prod_erase
alias gl:=mul_div_assoc'
alias gm:=div_mul_eq_mul_div
alias gn:=Nat.add_sub_cancel
alias go:=Nat.primeFactors_prod
alias gp:=Nat.factorial_ne_zero
alias gq:=card_biUnion_le
alias gr:=Nat.two_pow_pos
alias gs:=Nat.div_le_self
alias gu:=Nat.div_add_mod
alias gv:=Prod.mk.inj
alias gw:=min_le_right
alias gx:=Nat.cast_pow
alias gy:=List.mem_cons_of_mem
alias gz:=one_mul
alias gA:=card_image_of_injOn
alias gB:=Nat.pow_log_le_self
alias gC:=Nat.lt_two_pow_self
alias gD:=Finset.insert_erase
alias gE:=rpow_mul
alias gF:=rpow_add
alias gG:=sum_empty
alias gH:=congr_fun
alias gI:=lt_or_gt_of_ne
alias gJ:=lt_of_le_of_lt
alias gK:=Finset.le_max'
alias gL:=prod_inv_distrib
alias gM:=prod_div_distrib
alias gN:=div_pos
alias gO:=Nat.succ_pos
alias gP:=Nat.mod_mod_of_dvd
alias gQ:=MeasurableEquiv.coe_mk
alias gR:=sq_nonneg
alias gS:=mem_erase
alias gT:=exp_one_lt_d9
alias gU:=Nat.lt_irrefl
alias gV:=Measure.pi_pi
alias gW:=log_div
alias gX:=exp_add
alias gY:=Finset.sum_sigma'
alias gZ:=Nat.factorization_factorial
alias hG:=Filter.Eventually.of_forall
alias hH:=sum_comm
alias hJ:=prod_bij
alias hK:=mul_zero
alias hO:=card_bij
alias i0:=add_zero
alias i3:=sum_insert
alias i4:=Nat.sub_le
alias i5:=zero_lt_one
alias i6:=one_div_pow
alias i7:=min_le_left
alias i8:=le_antisymm
alias i9:=Subtype.ext
alias ia:=Nat.div_pos
alias ib:=lt_of_le_of_ne
alias ic:=div_eq_mul_inv
alias ie:=Finset.le_inf'
alias ig:=Real.log_le_rpow_div
alias ii:=Nat.eq_of_mul_eq_mul_right
alias ij:=div_pow
alias ik:=sqrt_eq_rpow
alias il:=Set.mem_prod
alias im:=Finset.prod_le_prod
alias io:=Finset.notMem_erase
alias ip:=add_comm
alias iq:=Prod.ext
alias ir:=dvd_mul_right
alias it:=pow_mul
alias iu:=log_exp
alias iw:=sum_neg_distrib
alias ix:=Real.volume_Ico
alias iy:=div_le_one
alias iz:=Nat.lt_div_mul_add
alias iA:=ENNReal.mul_ne_top
alias iB:=MeasureTheory.integrable_finsetSum
alias iC:=iff_false
alias iD:=heq_eq_eq
alias iE:=mul_one_div
alias iF:=prod_dvd_prod_of_subset
alias iG:=Set.mem_empty_iff_false
alias iH:=MeasurableEquiv.symm_mk
alias iI:=Finset.sum_sdiff_eq_sub
alias iJ:=Finset.sum_Ico_succ_top
alias iK:=Finset.sum_Icc_succ_top
alias iL:=Finset.mem_image_of_mem
alias iM:=if_pos
alias iN:=pow_pos
alias iO:=mem_sort
alias iP:=log_prod
alias iQ:=erase_insert
alias iR:=measurable_snd
alias iS:=biUnion_insert
alias iT:=setIntegral_const
alias iU:=measurableSet_Ico
alias iV:=Nat.factorial_pos
alias iW:=Nat.add_sub_of_le
alias iX:=Measurable.prodMk
alias iY:=MeasureTheory.integral_indicator
alias iZ:=MeasureTheory.integral_finsetSum
alias j3:=Nat.pos_of_dvd_of_pos
alias j4:=Nat.factorization_mul
alias j5:=card_univ
alias j6:=hasDerivAt_const
alias j7:=Nat.succ_ne_zero
alias j8:=Finset.disjoint_singleton_left
alias j9:=prod_univ_sum
alias ja:=card_image_le
alias jb:=Prod.mk.injEq
alias jc:=Nat.cast_zero
alias jd:=List.sum_cons
alias je:=List.map_cons
alias jf:=prod_pos
alias jg:=pow_ne_zero
alias jh:=Nat.primeFactors_mul
alias ji:=dvd_prod_of_mem
alias jj:=Nat.pow_dvd_pow
alias jk:=List.foldr_cons
alias jl:=filter_eq_empty_iff
alias jm:=Nat.ceil_lt_add_one
alias jn:=sum_mul
alias jo:=min_eq_right
alias jp:=Nat.cast_sum
alias jq:=List.get_mem
alias jr:=sum_union
alias js:=one_le_div
alias jt:=sum_range_succ
alias ju:=integrableOn_const
alias jw:=Nat.div_mul_cancel
alias jx:=ENNReal.ofReal_mul
alias jy:=Finset.disjoint_empty_left
alias jz:=Nat.floor_natCast
alias jA:=sum_singleton
alias jB:=sq_pos_of_pos
alias jC:=lt_trichotomy
alias jD:=card_union_le
alias jE:=abs_of_nonneg
alias jF:=Nat.find_spec
alias jG:=sum_fiberwise_of_maps_to
alias jH:=integrable_indicator_iff
alias jI:=div_pos_iff_of_pos_right
alias jJ:=Nat.lt_pow_succ_log_self
alias jK:=Nat.exists_prime_and_dvd
alias jL:=Nat.exists_eq_add_of_le'
alias jM:=ArithmeticFunction.moebius_apply_of_squarefree
alias jN:=List.cons_ne_nil
alias jO:=Fintype.card_coe
alias jP:=Fin.val_ne_of_ne
alias jQ:=one_pow
alias jR:=prod_image
alias jS:=log_lt_log
alias jT:=add_nonneg
alias jU:=max_eq_right
alias jV:=card_biUnion
alias jW:=Nat.find_min
alias jX:=Nat.cast_add
alias jY:=sum_image_le_of_nonneg
alias jZ:=le_mul_of_one_le_right
alias k3:=Nat.le_mul_of_pos_left
alias k4:=Finset.insert_ne_empty
alias k5:=rpow_pos_of_pos
alias k6:=Set.mem_biUnion
alias k7:=log_lt_sub_one_of_pos
alias k8:=le_of_mul_le_mul_left
alias k9:=Nat.primeFactors_mono
alias ka:=MeasurableSet.univ_pi
alias kb:=Finset.prod_const_one
alias kc:=Fin.sum_univ_castSucc
alias kd:=MeasureTheory.measure_preimage_add_right
alias ke:=Fintype.bijective_iff_injective_and_card
alias kf:=sub_zero
alias kg:=max'_mem
alias kh:=sum_biUnion
alias ki:=mem_product
alias kj:=log_le_log_iff
alias kk:=Nat.lt_add_one
alias kl:=sum_le_exp_of_nonneg
alias km:=Nat.le_log_of_pow_le
alias kn:=List.mem_of_mem_take
alias ko:=mul_pos
alias kp:=lt_irrefl
alias kq:=prod_pow_eq_pow_sum
alias kr:=add_right_injective
alias ks:=Nat.div_eq_of_lt_le
alias kt:=MeasurableSet.inter
alias ku:=Fintype.card_finset
alias kw:=Finset.prod_biUnion
alias kx:=Nat.factorization_eq_zero_of_not_dvd
alias ky:=log_two_lt_d9
alias kz:=log_two_gt_d9
alias kA:=Set.mem_union
alias kB:=List.mem_cons
alias kC:=max_le
alias kD:=prod_union
alias kE:=setIntegral_nonneg
alias kF:=integral_const_mul
alias kG:=Real.mul_self_sqrt
alias kH:=Nat.one_lt_two_pow
alias kI:=MeasurableSet.univ
alias kJ:=Finset.sum_mul_sum
alias kK:=ENNReal.toReal_sum
alias kL:=Nat.Prime.factorization_pos_of_dvd
alias kM:=sum_div
alias kN:=sq_sqrt
alias kO:=div_one
alias kP:=zero_mul
alias kQ:=pow_zero
alias kR:=log_rpow
alias kS:=dvd_mul_left
alias kT:=Nat.card_Ico
alias kU:=measurableSet_Icc
alias kV:=card_erase_of_mem
alias kW:=Set.mem_inter_iff
alias kX:=Set.disjoint_left
alias kY:=Nat.gcd_dvd_right
alias kZ:=Nat.add_mod_right
alias l3:=Measure.map_apply
alias l4:=Nat.Coprime.gcd_mul_right_cancel
alias l5:=measurableSet_lt
alias l6:=continuous_apply
alias l7:=Set.mem_setOf_eq
alias l8:=Nat.gcd_dvd_left
alias l9:=List.length_cons
alias la:=Finset.card_pair
alias lb:=Finset.sum_eq_sum_Ico_succ_bot
alias lc:=sum_product
alias ld:=sqrt_nonneg
alias lf:=smul_eq_mul
alias lg:=prod_subset
alias lh:=pi_gt_three
alias li:=min_eq_left
alias lj:=max_eq_left
alias lk:=length_sort
alias ll:=MeasureTheory.integral_nonneg
alias lm:=Chebyshev.theta_le_log4_mul_x
alias lp:=interior_subset
alias lq:=continuousAt_id
alias lr:=Set.mem_univ_pi
alias lu:=Nat.totient_mul
alias lv:=Nat.not_lt_zero
alias lw:=Nat.gcd_eq_left
alias lx:=MeasureTheory.measure_iUnion
alias ly:=neg_div
alias lz:=exp_neg
alias lA:=abs_mul
alias lB:=MeasureTheory.measure_union
alias lC:=zero_pow
alias lD:=rpow_neg
alias lE:=exp_zero
alias lF:=div_lt_one
alias lG:=squarefree_one
alias lH:=mul_right_comm
alias lI:=measurable_fst
alias lJ:=add_neg_cancel
alias lK:=Set.mem_iInter
alias lL:=Nat.mul_div_le
alias lM:=Nat.choose_pos
alias lN:=Finset.sum_Ico_consecutive
alias lO:=Filter.eventually_ge_atTop
alias lP:=prod_fiberwise_of_maps_to
alias lQ:=Stirling.stirlingSeq'_pos
alias lR:=Set.iUnion_iUnion_eq_left
alias lS:=Nat.lt_of_mul_lt_mul_left
alias lT:=Nat.add_mul_mod_self_left
alias lU:=Finset.exists_mem_eq_inf'
alias lV:=Finset.abs_sum_le_sum_abs
alias lW:=pairwise_sort
alias lX:=exp_one_gt_d9
alias lY:=Measure.pi_eq
alias lZ:=add_pos_of_nonneg_of_pos
alias m3:=eq_of_subset_of_card_le
alias m5:=Set.indicator_of_notMem
alias m6:=Nat.le_mul_of_pos_right
alias m7:=Finsupp.single_eq_of_ne
alias m8:=Finset.sum_Ioc_succ_top
alias m9:=pow_le_pow_left₀
alias ma:=le_div_iff₀
alias mb:=div_le_div_iff₀
alias mc:=div_le_iff₀
alias md:=Nat.mem_primeFactors
alias me:=exp_le_exp
alias mf:=Finset.nonempty_iff_ne_empty
alias mg:=pow_le_pow_right₀
alias mh:=Fin.mk_le_mk
alias mi:=prod_ne_zero_iff
alias mj:=div_le_div₀
alias ml:=List.pairwise_cons
alias mm:=div_lt_iff₀
alias mn:=Nat.isUnit_iff
alias mo:=one_le_pow₀
alias mq:=Nat.squarefree_mul_iff
alias mr:=Nat.cast_le
alias ms:=abs_le
alias mu:=ENNReal.sum_ne_top
alias mv:=Finset.image_subset_iff
alias mw:=Nat.totient_pos
alias mx:=Nat.lt_succ_iff
alias my:=Nat.ceil_le
alias mz:=inv_lt_comm₀
alias mA:=card_eq_zero
alias mB:=List.mem_map
alias mC:=mul_div_cancel₀
alias mD:=Nat.coprime_list_prod_right_iff
alias mE:=zpow_sub₀
alias mF:=exp_lt_exp
alias mG:=le_self_pow₀
alias mH:=Finsupp.notMem_support_iff
alias mI:=not_nonempty_iff_eq_empty
alias mJ:=zpow_le_one_of_nonpos₀
alias mK:=inv_mul_cancel_right₀
alias mL:=inv_lt_one_of_one_lt₀
lemma a3:(1/2:O)< log 2:=by have h:=kz;linarith
lemma a4:log 2< 1:=by have h:=ky;linarith
lemma a5:log 4=2*log 2:=by
 rw[show (4:O)=2^2 by norm_num,fm]
 ring
lemma a6 (n:ℕ) :
 sqrt (2*π*(n:O))*((n:O)/exp 1)^n<=(n.factorial:O):=
 Stirling.le_factorial_stirling n
lemma a7 (n:ℕ) (l:1<=n) :
 (n.factorial:O)<=exp 1*sqrt (n:O)*((n:O)/exp 1)^n:=by
 obtain⟨m,rfl⟩:=jL l;have d:log (Stirling.stirlingSeq (m+1))<=log (Stirling.stirlingSeq 1):=Stirling.log_stirlingSeq'_antitone (g5 m);have i:0< Stirling.stirlingSeq (m+1):=lQ m;have e:0< Stirling.stirlingSeq 1:=lQ 0;have b:Stirling.stirlingSeq (m+1)<=Stirling.stirlingSeq 1:=(kj i e).mp d;rw[Stirling.stirlingSeq_one]at b;unfold Stirling.stirlingSeq at b;have c :
  0< sqrt (2*((m+1:ℕ):O))*(((m+1:ℕ):O)/exp 1)^(m+1):=by
  positivity
 rw[mc c]at b;have h:sqrt (2*((m+1:ℕ):O))=sqrt 2*sqrt ((m+1:ℕ):O):=sqrt_mul _N _;rw[h]at b;have j:sqrt 2≠0:=_P
 calc ((m+1).factorial:O)
     <= exp 1/sqrt 2 *(sqrt 2*sqrt ((m+1:ℕ):O) *(((m+1:ℕ):O)/exp 1)^(m+1)):=b
   _=exp 1*sqrt ((m+1:ℕ):O) *(((m+1:ℕ):O)/exp 1)^(m+1):=by field_simp [j]
lemma a8 (N:ℕ) :
 ∑n∈Icc 1 N,(1:O)/(n:O)=(harmonic N:O):=by
 induction N with
 | zero=>simp[harmonic]
 | succ n ih=>
  rw[iK _O,ih,harmonic_succ];push_cast;ring
lemma a9 (N:ℕ) :
 ∑n∈Icc 1 N,(1:O)/(n:O)<=1+log (N:O):=by
 rw[a8];exact harmonic_le_one_add_log N
lemma aa (N:ℕ) :
 log ((N+1:ℕ):O)<=∑n∈Icc 1 N,(1:O)/(n:O):=by
 rw[a8];exact log_add_one_le_harmonic N
lemma ab (A B:ℕ) (j:1<=A) :
 ∑n∈Ioc A B,(1:O)/((n:O)^2)<=1/(A:O):=by
 by_cases e:A<=B
 · calc ∑n∈Ioc A B,(1:O)/((n:O)^2)
       <= ∑n∈Ioc A B,((1:O)/((n-1:ℕ):O)-(1:O)/(n:O)):=by
         refine dG fun n i=>?_
         rw[fw]at i;have h:(1:O)<=(n-1:ℕ):=_M (_O :1<=n-1);have b:((n-1:ℕ):O)=(n:O)-1:=(by rw[ei (_O :1<=n),eF]);rw[b];have c:0< (n:O)-1:=_L;have d:0< (n:O):=_L;rw[div_sub_div _ _ c.ne' d.ne',mb _P _P];nlinarith
     _=1/(A:O)-1/(B:O):=by
         induction B,e using fe with
         | base=>simp
         | succ m hm ih=>
           rw[m8 hm,ih];simp only[gn];ring
     _<=1/(A:O):=by
         have:(0:O)<=1/(B:O):=_P
         linarith
 · rw[Finset.Ioc_eq_empty _O]
   simp only[gG];positivity
set_option maxHeartbeats 800000 in
lemma ac (A B:ℕ) (y:1<=A) :
 ∑n∈Ioc A B,(1:O)/((n:O)*sqrt (n:O))<=2/sqrt (A:O):=by
 by_cases q:A<=B
 · calc ∑n∈Ioc A B,(1:O)/((n:O)*sqrt (n:O))
       <= ∑n∈Ioc A B,(2/sqrt ((n-1:ℕ):O)-2/sqrt (n:O)):=by
         refine dG fun n w=>?_
         rw[fw]at w;have u:(1:O)<=((n-1:ℕ):O):=_M (_O :1<=n-1);have d:(0:O)< (n:O):=_M (_O :0< n);have e:((n-1:ℕ):O)=(n:O)-1:=(by rw[ei (_O :1<=n),eF]);have c:0< sqrt ((n-1:ℕ):O):=sqrt_pos.mpr _L;have b:0< sqrt (n:O):=sqrt_pos.mpr d;have l:sqrt ((n-1:ℕ):O)<=sqrt (n:O):=sqrt_le_sqrt (by rw[e];linarith);have o:sqrt (n:O)^2-sqrt ((n-1:ℕ):O)^2=1:=(by rw[kN d.le,kN _L,e];ring);have i:(sqrt (n:O)-sqrt ((n-1:ℕ):O)) *(sqrt (n:O)+sqrt ((n-1:ℕ):O))=1:=_Q;have h:sqrt ((n-1:ℕ):O)*sqrt (n:O) *(sqrt (n:O)+sqrt ((n-1:ℕ):O)) <=2*((n:O)*sqrt (n:O)):=(by have v:sqrt (n:O)*sqrt (n:O)=(n:O):=kG d.le;nlinarith);rw[div_sub_div _ _ c.ne' b.ne',mb (ko d b) (ko c b)]
         have j:1*(sqrt ((n-1:ℕ):O)*sqrt (n:O)) *(sqrt (n:O)+sqrt ((n-1:ℕ):O)) <=(2*sqrt (n:O)-sqrt ((n-1:ℕ):O)*2) *((n:O)*sqrt (n:O))*(sqrt (n:O)+sqrt ((n-1:ℕ):O)):=by
           calc 1*(sqrt ((n-1:ℕ):O)*sqrt (n:O)) *
                 (sqrt (n:O)+sqrt ((n-1:ℕ):O))
               = sqrt ((n-1:ℕ):O)*sqrt (n:O) *(sqrt (n:O)+sqrt ((n-1:ℕ):O)):=_R
             _<=2*((n:O)*sqrt (n:O)):=h
             _=2*((sqrt (n:O)-sqrt ((n-1:ℕ):O)) *(sqrt (n:O)+sqrt ((n-1:ℕ):O))) *((n:O)*sqrt (n:O)):=by rw[i];ring
             _=(2*sqrt (n:O)-sqrt ((n-1:ℕ):O)*2) *((n:O)*sqrt (n:O))*(sqrt (n:O)+sqrt ((n-1:ℕ):O)):=_R
         exact le_of_mul_le_mul_right j (add_pos b c)
     _=2/sqrt (A:O)-2/sqrt (B:O):=by
         induction B,q using fe with
         | base=>simp
         | succ m hm ih=>
           rw[m8 hm,ih];simp only[gn];ring
     _<=2/sqrt (A:O):=by
         have:(0:O)<=2/sqrt (B:O):=_P
         linarith
 · rw[Finset.Ioc_eq_empty _O]
   simp only[gG];positivity
lemma ad (S f:ℕ->O) (a b:ℕ) (_ha:1<=a) (c:a<=b) :
 ∑m∈Icc a b,(S m-S (m-1))*f m =S b*f b-S (a-1)*f a +∑m∈Ico a b,S m*(f m-f (m+1)):=by
 induction b,c using fe with
 | base=>
  simp[Finset.Icc_self];ring
 | succ n hn ih=>
  rw[iK _O,iJ hn,ih];simp only[gn];ring
set_option maxHeartbeats 800000 in
lemma ae (n:ℕ) (hn:1000000<=n) :
 (n:O)/5<=Chebyshev.theta ((2*n:ℕ):O)-Chebyshev.theta (n:O):=by
 have hd:0< 2*n:=_O;have b:0< dw (2*n) n:=lM _O;have q:(4:O)^n<=((2*n+1:ℕ):O)*(dw (2*n) n:O):=by
  have he:∑k∈range (2*n+1),dw (2*n) k=2^(2*n):=Nat.sum_range_choose (2*n);have hf:∀k∈range (2*n+1),dw (2*n) k<=dw (2*n) n:=(by intro k _;simpa[gb n (_N :0< 2)] using Nat.choose_le_middle k (2*n));have i:2^(2*n)<=(2*n+1)*dw (2*n) n:=by
   calc 2^(2*n)=∑k∈range (2*n+1),dw (2*n) k:=he.symm
     _<=∑_k∈range (2*n+1),dw (2*n) n:=dG hf
     _=(2*n+1)*dw (2*n) n:=by simp
  have h4:(4:ℕ)^n=2^(2*n):=(by rw[show (4:ℕ)=2^2 by norm_num,<- it]);rw[<- h4]at i;exact_mod_cast i
 have C:(n:O)*log 4-log ((2*n+1:ℕ):O) <=log (dw (2*n) n:O):=by have A:log ((4:O)^n) <=log (((2*n+1:ℕ):O)*(dw (2*n) n:O)):=dM _P q;rw[fm,log_mul _P (_M b.ne')]at A;linarith
 have u:log (dw (2*n) n:O) =∑p∈dv (2*n),((dw (2*n) n).factorization p:O)*log (p:O):=by
  have Q:∏p∈(dw (2*n) n).primeFactors,p^((dw (2*n) n).factorization p)=dw (2*n) n:=(by have h:=ew b.ne';rw[Finsupp.prod]at h;simpa[ej] using h);have v:(dw (2*n) n).primeFactors⊆dv (2*n):=(by intro p j;rw[e7];have d:=dD j;have hg:=dS j;refine⟨?_,d⟩;by_contra c;push Not at c;have R:¬ p∣(2*n).factorial:=(by rw[d.dvd_factorial];omega);have S:dw (2*n) n∣(2*n).factorial:=(by have hm:=f7 (_O :n<=2*n);exact⟨n.factorial*(2*n-n).factorial,_L⟩);exact R (hg.trans S));have H:∏p∈dv (2*n),(p:O)^((dw (2*n) n).factorization p)=(dw (2*n) n:O):=by
   have hh:∏p∈dv (2*n),p^((dw (2*n) n).factorization p)=dw (2*n) n:=by
    have D:∏p∈(dw (2*n) n).primeFactors,p^((dw (2*n) n).factorization p) =∏p∈dv (2*n),p^((dw (2*n) n).factorization p):=by
     apply lg v
     intro p _ h9;have T:(dw (2*n) n).factorization p=0:=mH.mp (by simpa[ej] using h9);simp[T]
    rw[<- D,Q]
   exact_mod_cast hh
  rw[<- H,iP (fun p j=>
   jg _ (_M (dU j).ne_zero))]
  refine dF rfl fun p _=>fm _ _
 have J:∀p∈dv (2*n),((dw (2*n) n).factorization p:O)*log (p:O) <=if n< p then log (p:O)
   else if 2*n/3< p then 0
   else if p*p<=2*n then log ((2*n:ℕ):O)
   else log (p:O):=by
  intro p j;have d:p.Prime:=dU j;have hj:p<=2*n:=Nat.le_of_mem_primesLE j;have E:0<=log (p:O):=f1 (_M d.one_le);have F:p^((dw (2*n) n).factorization p)<=2*n:=by
   have hk:=Nat.factorization_choose_le_log (p:=p) (n:=2*n) (k:=n);by_cases h0:(dw (2*n) n).factorization p=0
   ·simp[h0];omega
   ·exact (dH d.pos hk).trans (gB p _O)
  have e:p*p > 2*n -> (dw (2*n) n).factorization p=(2*n)/p-2*(n/p):=by
   intro c;have U:Nat.log p (2*n)=1:=by
    apply i8
    ·exact mx.mp (Nat.log_lt_of_lt_pow (by omega) (by simpa[sq] using c))
    ·exact km d.one_lt (by simpa using hj)
   have hl:(2*n).factorial.factorization p=(2*n)/p:=(by rw[gZ d (kk (Nat.log p (2*n))),U];simp);have hs:n.factorial.factorization p=n/p:=by
    by_cases hz:p<=n
    ·have W:Nat.log p n=1:=by
      apply i8
      ·exact mx.mp (Nat.log_lt_of_lt_pow (by omega)
        (by simpa[sq] using (_O :n< p*p)))
      ·exact km d.one_lt (by simpa using hz)
     rw[gZ d (kk (Nat.log p n)),W];simp
    ·have w:n/p=0:=Nat.div_eq_of_lt _O;rw[w];exact kx (by rw[d.dvd_factorial];omega)
   have ho:dw (2*n) n*(n.factorial*n.factorial)=(2*n).factorial:=by
    have h:=f7 (_O :n<=2*n);rw[show 2*n-n=n by omega]at h
    linarith
   have hA:(dw (2*n) n).factorization p +2*n.factorial.factorization p=(2*n).factorial.factorization p:=(by have A:=fT (fun m=>m.factorization p) ho;rw[j4 b.ne' (mul_ne_zero (gp n) (gp n)),j4 (gp n) (gp n)]at A;simp only[Finsupp.coe_add,Pi.add_apply]at A;omega);omega
  split_ifs with A h2 h3
  ·have c:p*p > 2*n:=(by nlinarith);have hv:=e c;have y:(2*n)/p=1:=(by apply ks <;> omega);have w:n/p=0:=Nat.div_eq_of_lt A;rw[hv,y,w];simp
  ·have c:p*p > 2*n:=by
    have ht:3*p>=2*n:=_O;nlinarith
   have hv:=e c;have X:(2*n)/p=2:=(by apply ks <;> omega);have y:n/p=1:=(by apply ks <;> omega);rw[hv,X,y];simp
  ·rw[<- fm];exact dM (iN (_M d.pos) _) (_M F)
  ·have c:p*p > 2*n:=(by omega);have hv:=e c;have hq:(2*n)/p-2*(n/p)<=1:=by
    have hD:=iz d.pos (a:=n);have:2*n< (2*(n/p)+2)*p:=_Q;have:(2*n)/p< 2*(n/p)+2:=(Nat.div_lt_iff_lt_mul d.pos).mpr this;omega
   have hw:((dw (2*n) n).factorization p:O)<=1:=(by exact_mod_cast (hv.symm ▸ hq));nlinarith
 have hr:log (dw (2*n) n:O) <=(Chebyshev.theta ((2*n:ℕ):O)-Chebyshev.theta (n:O)) +Chebyshev.theta ((2*n/3:ℕ):O) +sqrt ((2*n:ℕ):O)*log ((2*n:ℕ):O):=by
  rw[u];have K:∑p∈dv (2*n),((dw (2*n) n).factorization p:O)*log (p:O) <=(∑p∈(dv (2*n)).filter (fun p=>n< p),log (p:O)) +(∑p∈(dv (2*n)).filter (fun p=>p<=2*n/3),log (p:O)) +(∑p∈(dv (2*n)).filter (fun p=>p*p<=2*n),log ((2*n:ℕ):O)):=by
   have A:=dG J;refine A.trans ?_
   rw[f8,f8,f8,<- fD,<- fD];refine dG fun p j=>?_
   have E:0<=log (p:O):=f1 (_M (dU j).one_le);have l:0<=log ((2*n:ℕ):O):=f1 (_M (_O :1<=2*n));by_cases c:n< p
   ·simp only[c,↓reduceIte,not_le.mpr (_O :2*n/3< p)];split_ifs <;> linarith
   ·by_cases G:2*n/3< p
    ·simp only[c,G,↓reduceIte,not_le.mpr G];split_ifs <;> linarith
    ·have i:p<=2*n/3:=(by omega);simp only[c,G,i,↓reduceIte];split_ifs <;> linarith
  refine K.trans ?_
  have M:∑p∈(dv (2*n)).filter (fun p=>n< p),log (p:O) =Chebyshev.theta ((2*n:ℕ):O)-Chebyshev.theta (n:O):=by
   rw[fk,fk];have v:dv n⊆dv (2*n):=by intro p j;rw[e7]at j ⊢;exact⟨by omega,j.2⟩
   have Z:(dv (2*n)).filter (fun p=>n< p) =dv (2*n) \ dv n:=by
    ext p;simp only[dB,gj,e7];constructor
    ·rintro⟨⟨i,j⟩,c⟩;exact⟨⟨i,j⟩,fun h=>by omega⟩
    ·rintro⟨⟨i,j⟩,hnot⟩;refine⟨⟨i,j⟩,?_⟩;by_contra hC;exact hnot ⟨by omega,j⟩
   rw[Z,iI v]
  have N:∑p∈(dv (2*n)).filter (fun p=>p<=2*n/3),log (p:O) =Chebyshev.theta ((2*n/3:ℕ):O):=by
   rw[fk];congr 1;ext p;simp only[dB,e7];constructor
   ·rintro⟨⟨_,j⟩,i⟩;exact⟨i,j⟩
   ·rintro⟨i,j⟩;exact⟨⟨by omega,j⟩,i⟩
  have hu:∑p∈(dv (2*n)).filter (fun p=>p*p<=2*n),log ((2*n:ℕ):O) <=sqrt ((2*n:ℕ):O)*log ((2*n:ℕ):O):=by
   rw[ex,e3];have l:0<=log ((2*n:ℕ):O):=f1 (_M (_O :1<=2*n));refine dE ?_ l;have v:(dv (2*n)).filter (fun p=>p*p<=2*n) ⊆
    Icc 1 (Nat.sqrt (2*n)):=by
    intro p j;simp only[dB,e7,dT]at j ⊢;exact⟨j.1.2.one_le,Nat.le_sqrt.mpr j.2⟩
   have h5:((dv (2*n)).filter (fun p=>p*p<=2*n)).card <=Nat.sqrt (2*n):=(by simpa using er v);have hx:(Nat.sqrt (2*n):O)<=sqrt ((2*n:ℕ):O):=(by rw[Real.le_sqrt _P _P,sq];exact_mod_cast Nat.sqrt_le (2*n));exact (mr.mpr h5).trans hx
  rw[M,N];linarith
 have h6:Chebyshev.theta ((2*n/3:ℕ):O)<=log 4*((2*n:O)/3):=by
  have A:=lm (x:=((2*n/3:ℕ):O)) _P;have h2:((2*n/3:ℕ):O)<=(2*n:O)/3:=by
   have:(2*n/3)*3<=2*n:=eD (2*n) 3
   have hR:((2*n/3:ℕ):O)*3<=(2*n:O):=_M this;linarith
  have ha:0<=log 4:=f1 _N;nlinarith
 have hy:(2000000:O)<=((2*n:ℕ):O):=_M (_O :2000000<=2*n);have o:(0:O)< ((2*n:ℕ):O):=_L;have z:log ((2*n:ℕ):O)<=6*((2*n:ℕ):O)^((1:O)/6):=by have h:=ig o.le (_N :(0:O)< 1/6);linarith
 have B:(125:O)<=((2*n:ℕ):O)^((1:O)/3):=by
  have A:(125:O)^(3:O)<=((2*n:ℕ):O):=by have hB:(125:O)^(3:O)=1953125:=_N;linarith
  calc (125:O)=((125:O)^(3:O))^((1:O)/3):=by
        rw[<- gE _N];norm_num
    _<=((2*n:ℕ):O)^((1:O)/3):=fx _P A _N
 have h7:sqrt ((2*n:ℕ):O)*log ((2*n:ℕ):O)<=(n:O)/10:=by
  have A:sqrt ((2*n:ℕ):O)*log ((2*n:ℕ):O) <=6*((2*n:ℕ):O)^((2:O)/3):=by
   calc sqrt ((2*n:ℕ):O)*log ((2*n:ℕ):O)
       <= sqrt ((2*n:ℕ):O)*(6*((2*n:ℕ):O)^((1:O)/6)):=dA z (ld _)
     _=6*(((2*n:ℕ):O)^((1:O)/2)*((2*n:ℕ):O)^((1:O)/6)):=by rw[ik];ring
     _=6*((2*n:ℕ):O)^((2:O)/3):=by rw[<- gF o];norm_num
  have h2:((2*n:ℕ):O)^((2:O)/3)*125<=((2*n:ℕ):O):=by
   calc ((2*n:ℕ):O)^((2:O)/3)*125
       <= ((2*n:ℕ):O)^((2:O)/3)*((2*n:ℕ):O)^((1:O)/3):=dA B _P
     _=((2*n:ℕ):O):=by rw[<- gF o];norm_num
  have hb:((2*n:ℕ):O)=2*(n:O):=(by push_cast;ring);linarith
 have P:log ((2*n+1:ℕ):O)<=(n:O)/100:=by have A:log ((2*n+1:ℕ):O)<=2*sqrt ((2*n+1:ℕ):O):=(by have h:=ig (x:=((2*n+1:ℕ):O)) _P (_N :(0:O)< 1/2);rw[<- ik]at h;linarith);have h2:sqrt ((2*n+1:ℕ):O)<=(n:O)/200:=(by rw[sqrt_le_left _P];have hE:(1000000:O)<=(n:O):=_M hn;have h8:((2*n+1:ℕ):O)=2*(n:O)+1:=(by push_cast;ring);rw[h8];nlinarith);linarith
 have hc:(1:O)< log 4:=by rw[a5];linarith[a3]
 nlinarith
lemma af (U:O) (F:2000000<=U) :
 1/(20*log (2*U)) <=∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O):=by
 let n:ℕ:=⌊U⌋₊;have m:1000000<=n:=by
  have:2000000<=n:=g2 (by norm_num;linarith)
  omega
 have v:(n:O)<=U:=fC _L;have u:U< (n:O)+1:=f6 U;have i:2*n<=⌊2*U⌋₊:=g2 (by push_cast;linarith);have B:=ae n m;have d:Chebyshev.theta ((2*n:ℕ):O)-Chebyshev.theta (n:O) =∑p∈(Ioc n (2*n)).filter Nat.Prime,log (p:O):=by
  rw[fk,fk];have e:dv n⊆dv (2*n):=by intro p b;rw[e7]at b ⊢;exact⟨by omega,b.2⟩
  rw[<- iI e];congr 1;ext p;simp only[gj,e7,dB,fw];constructor
  ·rintro⟨⟨hle,b⟩,hnot⟩;refine⟨⟨?_,hle⟩,b⟩;by_contra C;exact hnot ⟨by omega,b⟩
  ·rintro⟨⟨hgt,hle⟩,b⟩;exact⟨⟨hle,b⟩,fun h=>by omega⟩
 rw[d]at B;have w:(0:O)< 2*U:=_L;have j:0< log (2*U):=et _L;have y:∑p∈(Ioc n (2*n)).filter Nat.Prime,log (p:O) <=(2*U*log (2*U)) *∑p∈(Ioc n (2*n)).filter Nat.Prime,(1:O)/(p:O):=by
  rw[dP];refine dG fun p b=>?_
  simp only[dB,fw]at b;have c:(0:O)< (p:O):=_M b.2.pos;have o:(p:O)<=2*U:=by
   have:(p:O)<=(2*n:ℕ):=_M b.1.2
   push_cast at this;linarith
  have z:log (p:O)<=log (2*U):=dM c o;rw[iE,ma c];have A:0<=log (p:O):=f1 (_M b.2.one_le);nlinarith
 have e:(Ioc n (2*n)).filter Nat.Prime ⊆ (Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime:=by intro p b;simp only[dB,fw]at b ⊢;exact⟨⟨b.1.1,b.1.2.trans i⟩,b.2⟩
 have q:∑p∈(Ioc n (2*n)).filter Nat.Prime,(1:O)/(p:O) <=∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O):=dC e fun _ _ _=>_P;have l:U/2<=(n:O):=_L;have D:U/10<=(2*U*log (2*U)) *∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O):=by have E:(2*U*log (2*U)) *∑p∈(Ioc n (2*n)).filter Nat.Prime,(1:O)/(p:O) <=(2*U*log (2*U)) *∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O):=dA q _P;linarith
 rw[mc _P];nlinarith
lemma ag (U:O) (l:2000000<=U) :
 U/(20*log (2*U)) <=(((Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime).card:O):=by
 have c:=af U l;have b:0< U:=_L;have d:0< log (2*U):=et _L;have e:∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O) <=(((Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime).card:O)/U:=by
  calc ∑p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/(p:O)
      <= ∑_p∈(Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime,(1:O)/U:=by
        refine dG fun p j=>?_
        simp only[dB,fw]at j;have h:U<=(p:O):=(by have e : ⌊U⌋₊+1<=p:=j.1.1;have i:U< (⌊U⌋₊ : O)+1:=f6 U;have m:((⌊U⌋₊ : O)+1)<=(p:O):=_M e;linarith);exact dX b h
    _=(((Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime).card:O)/U:=by rw[ex,e3,iE]
 have i:1/(20*log (2*U)) <=(((Ioc ⌊U⌋₊ ⌊2*U⌋₊).filter Nat.Prime).card:O)/U:=c.trans e;rw[mb _P b]at i;rw[mc _P];linarith
lemma ah (x:O) (q:4<=x) :
 (Nat.primeCounting ⌊x⌋₊ : O)<=6*x/log x:=by
 have d:1< x:=_L;have b:0< log x:=et d;have l:=Chebyshev.pi_le_log4_mul_div d;rw[Real.log_sqrt _L]at l;have c:log 4< 2:=by rw[a5];linarith[a4]
 have i:log 4*x/(log x/2)<=4*x/log x:=by rw[div_div_eq_mul_div,mb b b];nlinarith[ko (_L :(0:O)< x) b]
 have j:sqrt x<=2*x/log x:=by
  rw[ma b];have e:log x<=2*sqrt x:=by have h:=ig (x:=x) _L (_N :(0:O)< 1/2);rw[<- ik]at h;linarith
  have o:sqrt x*sqrt x=x:=kG _L;nlinarith[ld x]
 have m:4*x/log x+2*x/log x=6*x/log x:=_R;linarith
lemma ai (U C:O) (v:4<=U) (w:1<=C) :
 ∑p∈(Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime,(1:O)/(p:O) <=6*C/log U:=by
 have b:0< U:=_L;have j:4<=C*U:=_Q;have d:0< log U:=et _L;have c:log U<=log (C*U):=dM b (by nlinarith);have o:∑p∈(Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime,(1:O)/(p:O) <=∑_p∈(Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime,(1:O)/U:=by
  refine dG fun p i=>?_
  simp only[dB,dT]at i;have l:U<=(p:O):=(g6 U).trans (_M i.1.1);exact dX b l
 rw[ex,e3]at o;have e:(((Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime).card:O) <=(Nat.primeCounting ⌊C*U⌋₊ : O):=by
  have h:((Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime).card<=Nat.primeCounting ⌊C*U⌋₊:=by
   rw[Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range];refine er fun p i=>?_
   simp only[dB,dT,dN]at i ⊢;exact⟨by omega,i.2⟩
  exact_mod_cast h
 have m:=ah (C*U) j;have q:(Nat.primeCounting ⌊C*U⌋₊ : O)*(1/U)<=6*C/log (C*U):=by
  calc (Nat.primeCounting ⌊C*U⌋₊ : O)*(1/U)
      <= (6*(C*U)/log (C*U))*(1/U):=dE m _P
    _=6*C/log (C*U):=by field_simp [b.ne']
 have u:6*C/log (C*U)<=6*C/log U:=dL _P d c
 calc ∑p∈(Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime,(1:O)/(p:O)
     <= (((Icc ⌈U⌉₊ ⌊C*U⌋₊).filter Nat.Prime).card:O)*(1/U):=o
   _<=(Nat.primeCounting ⌊C*U⌋₊ : O)*(1/U):=dE e _P
   _<=6*C/log U:=q.trans u
set_option maxHeartbeats 800000 in
lemma aj (N:ℕ) (M:1<=N) :
 ∑p∈dv N,log (p:O)/(p:O)<=log (N:O)+log 4:=by
 have w:(0:O)< N:=_P;have j:(N.factorial:O)<=(N:O)^N:=_M (Nat.factorial_le_pow N);have b:log (N.factorial:O)<=(N:O)*log N:=by
  calc log (N.factorial:O)<=log ((N:O)^N):=
        dM (_M (iV N)) j
    _=(N:O)*log N:=fm (N:O) N
 have o:∀p∈dv N,N/p<=N.factorial.factorization p:=by
  intro p c;have l:p.Prime:=dU c;have H:p<=N:=Nat.le_of_mem_primesLE c;rw[gZ l (kk (Nat.log p N))];have A:1∈Ico 1 (Nat.log p N+1):=by rw[f3];refine⟨eR,Nat.lt_add_one_iff.mpr ?_⟩;exact km l.one_lt (by simpa using H)
  calc N/p=N/p^1:=by simp
    _<=∑i∈Ico 1 (Nat.log p N+1),N/p^i:=fi (f:=fun i=>N/p^i) (fun _ _=>g5 _) A
 have d:(∏p∈dv N,p^(N/p))∣N.factorial:=by
  rw[<- Nat.factorization_le_iff_dvd
   (mi.mpr fun p c=>
    jg _ (dU c).ne_zero) (gp N)]
  intro q;rw[Nat.factorization_prod (fun p c=>
   jg _ (dU c).ne_zero)]
  simp only[Finsupp.finsetSum_apply,Nat.factorization_pow,Finsupp.smul_apply,lf];by_cases G:q∈dv N
  ·rw[Finset.sum_eq_single q]
   ·rw[(dU G).factorization_self,fv];exact o q G
   ·intro p c B;rw[(dU c).factorization,m7 (Ne.symm B),hK]
   ·intro h;exact absurd G h
  ·rw[g0]
   ·exact g5 _
   ·intro p c;have B:p≠q:=fun h=>G (h ▸ c);rw[(dU c).factorization,m7 (Ne.symm B),hK]
 have m:(∏p∈dv N,(p:O)^(N/p))<=(N.factorial:O):=by exact_mod_cast el (iV N) d
 have u:∑p∈dv N,((N/p:ℕ):O)*log p<=(N:O)*log N:=by
  have e:∑p∈dv N,((N/p:ℕ):O)*log p =log (∏p∈dv N,(p:O)^(N/p)):=by
   rw[iP (fun p c=>
    jg _ (_M (dU c).ne_zero))]
   exact dF rfl fun p _=>(fm _ _).symm
  rw[e];exact (dM (jf fun p c=>
   iN (_M (dU c).pos) _) m).trans
   b
 have y:∀p∈dv N,((N:O)/(p:O)-1)*log p<=((N/p:ℕ):O)*log p:=by
  intro p c;have l:p.Prime:=dU c;have z:(0:O)< p:=_M l.pos;have v:0<=log (p:O):=f1 (_M l.one_le);have E:N< (N/p+1)*p:=by
   have:=iz l.pos (a:=N)
   linarith
  have C:(N:O)/(p:O)-1<=((N/p:ℕ):O):=(by have J:(N:O)< (((N/p:ℕ):O)+1)*(p:O):=_M E;rw[sub_le_iff_le_add,mc z];linarith);exact dE C v
 have K:(N:O)*(∑p∈dv N,log p/(p:O)) -∑p∈dv N,log p<=(N:O)*log N:=by
  calc (N:O)*(∑p∈dv N,log p/(p:O)) -
          ∑p∈dv N,log p
      = ∑p∈dv N,((N:O)/(p:O)-1)*log p:=by rw[dP,<- f2];exact dF rfl fun p _=>_R
    _<=∑p∈dv N,((N/p:ℕ):O)*log p:=dG y
    _<=(N:O)*log N:=u
 have F:∑p∈dv N,log p<=log 4*(N:O):=by rw[<- fk];exact lm (dK N)
 have D:(N:O)*(∑p∈dv N,log p/(p:O)) <=(N:O)*(log N+log 4):=_L;exact k8 D w
set_option maxHeartbeats 800000 in
lemma ak (N:ℕ) (hN:1<=N) :
 log (N:O)-9<=∑p∈dv N,log (p:O)/(p:O):=by
 have d:(0:O)< N:=_P;have b:(N:O)*log (N:O)-(N:O)<=log (N.factorial:O):=by
  have Q:=a6 N;have y:(1:O)<=sqrt (2*π*(N:O)):=(by rw[Real.le_sqrt _N _P];have h5:(3:O)< π:=lh;have h6:(1:O)<=N:=_M hN;nlinarith);have l:((N:O)/exp 1)^N<=(N.factorial:O):=by
   calc ((N:O)/exp 1)^N=1*((N:O)/exp 1)^N:=by ring
     _<=sqrt (2*π*(N:O))*((N:O)/exp 1)^N:=dE y _P
     _<=(N.factorial:O):=Q
  have h1:=dM _P l;rw[fm,gW d.ne' (ez 1).ne',iu]at h1;linarith
 have c:log (N.factorial:O) =∑p∈dv N,((N.factorial.factorization p:ℕ):O)*log (p:O):=by
  have D:∏p∈N.factorial.primeFactors,p^(N.factorial.factorization p)=N.factorial:=(by have h:=ew (gp N);rw[Finsupp.prod]at h;simpa[ej] using h);have o:N.factorial.primeFactors⊆dv N:=(by intro p j;rw[e7];have e:=dD j;exact⟨e.dvd_factorial.mp (dS j),e⟩);have z:∏p∈dv N,(p:O)^(N.factorial.factorization p) =(N.factorial:O):=by
   have K:∏p∈dv N,p^(N.factorial.factorization p)=N.factorial:=by
    have q:∏p∈N.factorial.primeFactors,p^(N.factorial.factorization p) =∏p∈dv N,p^(N.factorial.factorization p):=by
     apply lg o
     intro p _ J;have E:N.factorial.factorization p=0:=mH.mp (by simpa[ej] using J);simp[E]
    rw[<- q,D]
   exact_mod_cast K
  rw[<- z,iP (fun p j=>
   jg _ (_M (dU j).ne_zero))]
  exact dF rfl fun p _=>fm _ _
 have F:∀p∈dv N,((N.factorial.factorization p:ℕ):O) <=(N:O)/(p:O)+(N:O)/((p:O)*((p:O)-1)):=by
  intro p j;have e:p.Prime:=dU j;have R:(2:O)<=p:=_M e.two_le;have A:(0:O)< p:=_L;have u:(0:O)< (p:O)-1:=_L;rw[gZ e (kk (Nat.log p N))];push_cast
  calc ∑i∈Ico 1 (Nat.log p N+1),((N/p^i:ℕ):O)
      <= ∑i∈Ico 1 (Nat.log p N+1),(N:O)/(p:O)^i:=by
        refine dG fun i _=>?_
        rw[ma _P];exact_mod_cast eD N (p^i)
    _=(N:O)*∑i∈Ico 1 (Nat.log p N+1),((p:O)⁻¹)^i:=by rw[dP];refine dF rfl fun i _=>by rw[inv_pow,ic]
    _<=(N:O)*((1/(p:O))+1/((p:O)*((p:O)-1))):=by
        refine dA ?_ d.le
        have hr:(p:O)⁻¹< 1:=mL _L;have v:0< 1-(p:O)⁻¹:=_L;have h3:∑i∈Ico 1 (Nat.log p N+1),((p:O)⁻¹)^i <=(p:O)⁻¹/(1-(p:O)⁻¹):=(by have G:∑i∈Ico 1 (Nat.log p N+1),((p:O)⁻¹)^i =(∑i∈range (Nat.log p N+1),((p:O)⁻¹)^i)-1:=(by have h0:=lb (f:=fun i=>((p:O)⁻¹)^i) (gO (Nat.log p N));rw[Finset.range_eq_Ico,h0];simp);rw[G,fO hr.ne];have h7:(0:O)<=((p:O)⁻¹)^(Nat.log p N+1):=_P;have S:(((p:O)⁻¹)^(Nat.log p N+1)-1)/((p:O)⁻¹ - 1)-1 =((p:O)⁻¹ - ((p:O)⁻¹)^(Nat.log p N+1))/(1-(p:O)⁻¹):=(by have C:(p:O)⁻¹ - 1≠0:=_L;rw[div_sub_one C,div_eq_div_iff C v.ne'];ring);rw[S];exact dI _L v.le);have h4:(p:O)⁻¹/(1-(p:O)⁻¹) =1/(p:O)+1/((p:O)*((p:O)-1)):=(by field_simp [A.ne',u.ne',v.ne'];ring);linarith
    _=(N:O)/(p:O)+(N:O)/((p:O)*((p:O)-1)):=_R
 have T:∑p∈dv N,log (p:O)/((p:O)*((p:O)-1))<=8:=by
  have o:dv N⊆Ioc 1 (max 1 N):=(by intro p j;rw[e7]at j;rw[fw];exact⟨j.2.one_lt,gf j.1 (ep 1 N)⟩);have h1:∑p∈dv N,log (p:O)/((p:O)*((p:O)-1)) <=4*∑m∈Ioc 1 (max 1 N),(1:O)/((m:O)*sqrt (m:O)):=by
   calc ∑p∈dv N,log (p:O)/((p:O)*((p:O)-1))
       <= ∑p∈dv N,(4:O)/((p:O)*sqrt (p:O)):=by
         refine dG fun p j=>?_
         have e:=dU j;have R:(2:O)<=p:=_M e.two_le;have w:log (p:O)<=2*sqrt (p:O):=(by have h:=ig (x:=(p:O)) _L (_N :(0:O)< 1/2);rw[<- ik]at h;linarith);have U:sqrt (p:O)*sqrt (p:O)=(p:O):=kG _L;have H:(0:O)< (p:O):=_L;have W:(0:O)< (p:O)-1:=_L;have X:0< sqrt (p:O):=sqrt_pos.mpr H;rw[mb (ko H W) (ko H X)];have M:log (p:O)*((p:O)*sqrt (p:O)) <=(2*sqrt (p:O))*((p:O)*sqrt (p:O)):=dE w _P
         have P:(2*sqrt (p:O))*((p:O)*sqrt (p:O))=2*(p:O)*(p:O):=by
           calc _=2*(p:O)*(sqrt (p:O)*sqrt (p:O)):=by ring
             _=2*(p:O)*(p:O):=by rw[U]
         nlinarith
     _<=∑m∈Ioc 1 (max 1 N),(4:O)/((m:O)*sqrt (m:O)):=dC o fun _ _ _=>_P
     _=4*∑m∈Ioc 1 (max 1 N),(1:O)/((m:O)*sqrt (m:O)):=by rw[dP];exact dF rfl fun _ _=>_R
  have h2:=ac 1 (max 1 N) eR;simp only[eF,sqrt_one,kO]at h2;linarith
 have Z:(N:O)*log (N:O)-(N:O) <=(N:O)*(∑p∈dv N,log (p:O)/(p:O))+(N:O)*8:=by
  calc (N:O)*log (N:O)-(N:O)
      <= log (N.factorial:O):=b
    _=∑p∈dv N,((N.factorial.factorization p:ℕ):O)*log (p:O):=c
    _<=∑p∈dv N,((N:O)/(p:O)+(N:O)/((p:O)*((p:O)-1)))*log (p:O):=by
        refine dG fun p j=>
          dE (F p j) (f1 (_M (dU j).one_le))
    _=(N:O)*(∑p∈dv N,log (p:O)/(p:O)) +(N:O)*(∑p∈dv N,log (p:O)/((p:O)*((p:O)-1))):=by rw[dP,dP,<- fD];exact dF rfl fun p _=>_R
    _<=(N:O)*(∑p∈dv N,log (p:O)/(p:O))+(N:O)*8:=_Q
 have B:(N:O)*(log (N:O)-9) <=(N:O)*(∑p∈dv N,log (p:O)/(p:O)):=_L;exact k8 B d
lemma al (N:ℕ) (c:1<=N) :
 |∑p∈dv N,log (p:O)/(p:O)-log (N:O)|<=9:=by
 rw[ms];have d:=aj N c;have e:=ak N c;have b:log 4< 2:=by rw[a5];linarith[a4]
 constructor <;> linarith
set_option maxHeartbeats 800000 in
lemma am (N:ℕ) (v:2<=N) :
 ∑p∈dv N,(1:O)/(p:O) =(∑p∈dv N,log (p:O)/(p:O))/log (N:O) +∑m∈Ico 2 N,(∑p∈dv m,log (p:O)/(p:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹):=by
 let S:ℕ->O:=fun m=>∑p∈dv m,log (p:O)/(p:O);let f:ℕ->O:=fun m=>(log (m:O))⁻¹;have d:∀m:ℕ,2<=m -> S m-S (m-1)=if m.Prime then log (m:O)/(m:O) else 0:=by
  intro m q;have i:dv m =(if m.Prime then {m} else ∅)∪dv (m-1):=by
   ext p;simp only[e7,ff];split_ifs with hmp
   ·simp only[eg];constructor
    ·rintro⟨hple,b⟩;by_cases l:p=m
     ·exact Or.inl l
     ·exact Or.inr ⟨by omega,b⟩
    ·rintro (rfl | ⟨hple,b⟩)
     ·exact⟨eR,hmp⟩
     ·exact⟨by omega,b⟩
   ·simp only[fq,false_or];constructor
    ·rintro⟨hple,b⟩;have l:p≠m:=fun h=>hmp (h ▸ b);exact⟨by omega,b⟩
    ·rintro⟨hple,b⟩;exact⟨by omega,b⟩
  have j:Disjoint (if m.Prime then ({m}:Finset ℕ) else ∅) (dv (m-1)):=by
   split_ifs
   ·rw[j8,e7];intro h;omega
   ·exact jy _
  change (∑p∈dv m,log (p:O)/(p:O)) -(∑p∈dv (m-1),log (p:O)/(p:O))=_;rw[i,jr j,add_sub_cancel_right];split_ifs <;> simp
 have c:∑p∈dv N,(1:O)/(p:O) =∑m∈Icc 2 N,(S m-S (m-1))*f m:=by
  have u:∑m∈Icc 2 N,(S m-S (m-1))*f m =∑m∈(Icc 2 N).filter Nat.Prime,(1:O)/(m:O):=by
   rw[f8];refine dF rfl fun m q=>?_
   rw[dT]at q;rw[d m q.1];split_ifs with hmp
   ·have e:log (m:O)≠0:=(et (_M hmp.one_lt)).ne';simp only[f];field_simp [e]
   ·simp
  rw[u];congr 1;ext p;simp only[e7,dB,dT];constructor
  ·rintro⟨hple,b⟩;exact⟨⟨b.two_le,hple⟩,b⟩
  ·rintro⟨⟨_,hple⟩,b⟩;exact⟨hple,b⟩
 rw[c,ad S f 2 N _O v];have o:S 1=0:=by simp only[S];apply g0;intro p b;rw[e7]at b;exact absurd b.2.two_le _O
 rw[show 2-1=1 by rfl,o]
 simp only[kP,kf,f,S,ic]
set_option maxHeartbeats 800000 in
lemma an (N:ℕ) (Z:3<=N) :
 |∑p∈dv N,(1:O)/(p:O)-log (log (N:O))|<=35:=by
 rw[am N _O];have o:0< log 2:=_l a3;have b:∀m∈Ico 2 N,
  |log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O)))| <=4/((m:O)^2):=by
  intro m v;rw[f3]at v;have J:(2:O)<=m:=_M v.1;have d:0< log (m:O):=et _L;have e:0< log ((m+1:ℕ):O):=et (by push_cast;linarith);have y:log (m:O)<=log ((m+1:ℕ):O):=dM _L (by push_cast;linarith);have E:log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) =1-log (m:O)/log ((m+1:ℕ):O):=(by field_simp [d.ne',e.ne']);have h2:log (log ((m+1:ℕ):O))-log (log (m:O)) =log (log ((m+1:ℕ):O)/log (m:O)):=(gW e.ne' d.ne').symm;rw[E,h2];have F:1-log (m:O)/log ((m+1:ℕ):O) <=log (log ((m+1:ℕ):O)/log (m:O)):=by have h:=fl (gN e d);rwa[inv_div]at h
  have z:log (log ((m+1:ℕ):O)/log (m:O)) <=log ((m+1:ℕ):O)/log (m:O)-1:=eY (gN e d);have i:log ((m+1:ℕ):O)-log (m:O)<=1/(m:O):=(by rw[<- gW _P _P];have h:=eY (_P :(0:O)< ((m+1:ℕ):O)/(m:O));have h5:((m+1:ℕ):O)/(m:O)-1=1/(m:O):=(by push_cast;field_simp [(_L :(m:O)≠0)];linarith);linarith);have j:0<=log ((m+1:ℕ):O)-log (m:O):=_L;have h0:(log ((m+1:ℕ):O)/log (m:O)-1) -(1-log (m:O)/log ((m+1:ℕ):O))<=4/((m:O)^2):=by
   have K:(log ((m+1:ℕ):O)/log (m:O)-1) -(1-log (m:O)/log ((m+1:ℕ):O)) =(log ((m+1:ℕ):O)-log (m:O))^2 /(log (m:O)*log ((m+1:ℕ):O)):=(by field_simp [d.ne',e.ne']);rw[K];have G:(log ((m+1:ℕ):O)-log (m:O))^2<=(1/(m:O))^2:=m9 j i 2;have H:(1/4:O)<=log (m:O)*log ((m+1:ℕ):O):=by have M:(1/2:O)<=log (m:O):=gf a3.le (dM _N J);have h6:(1/2:O)<=log ((m+1:ℕ):O):=gf M y;nlinarith
   calc (log ((m+1:ℕ):O)-log (m:O))^2 /
           (log (m:O)*log ((m+1:ℕ):O))
       <= (1/(m:O))^2/(1/4:O):=mj _P G _N H
     _=4/((m:O)^2):=_R
  rw[ms];constructor <;> linarith
 have w : |∑m∈Ico 2 N,((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)|<=18:=by
  have c:∀m∈Ico 2 N,0<=(log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹:=by intro m v;rw[f3]at v;have hx:0< log (m:O):=et (_M (_O :1< m));have y:log (m:O)<=log ((m+1:ℕ):O):=dM (_M (_O :0< m)) (by push_cast;linarith);have:=inv_anti₀ hx y;linarith
  calc |∑m∈Ico 2 N,
          ((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)|
      <= ∑m∈Ico 2 N,
          |((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)|:=
        lV _ _
    _<=∑m∈Ico 2 N,9*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹):=by
        refine dG fun m v=>?_
        rw[lA,jE (c m v)];have P:1<=m:=(by rw[f3]at v;omega);exact dE (al m P) (c m v)
    _=9*((log (2:O))⁻¹ - (log (N:O))⁻¹):=by
        rw[<- dP];congr 1;have A:2<=N:=_O;clear Z b c;induction N,A using fe with
        | base=>simp
        | succ k hk ih=>
          rw[iJ hk,ih];ring
    _<=18:=by have Q:0< log (N:O):=et (_M (_O :1< N));have R:0<=(log (N:O))⁻¹:=_P;have S:(log (2:O))⁻¹<=2:=(by rw[inv_le_comm₀ o _N];linarith[a3]);linarith
 have q:∑m∈Ico 2 N,(log (log ((m+1:ℕ):O))-log (log (m:O))) =log (log (N:O))-log (log (2:O)):=by
  have A:2<=N:=_O;clear Z b w;induction N,A using fe with
  | base=>simp
  | succ k hk ih=>
   rw[iJ hk,ih];ring
 have C : |∑m∈Ico 2 N,(log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O))))|<=4:=by
  calc _<=∑m∈Ico 2 N,
          |log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O)))|:=
        lV _ _
    _<=∑m∈Ico 2 N,4/((m:O)^2):=dG b
    _<=∑m∈Ioc 1 N,4/((m:O)^2):=by
        refine dC ?_ (fun _ _ _=>by positivity)
        intro m v;rw[f3]at v;rw[fw];omega
    _=4*∑m∈Ioc 1 N,(1:O)/((m:O)^2):=by rw[dP];exact dF rfl fun _ _=>_R
    _<=4:=by
        have:=ab 1 N eR
        simp only[eF,kO]at this;linarith
 have D:(1:O)< log (N:O):=by
  have h3:exp 1< (N:O):=by
   have he:exp 1< 3:=by
    have:=gT
    linarith
   have h7:(3:O)<=(N:O):=_M Z;linarith
  have:=jS (ez 1) h3
  rwa[iu]at this
 have T : |(∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1|<=9:=by have E:(∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1 =(∑p∈dv N,log (p:O)/(p:O)-log (N:O))/log (N:O):=(by field_simp [(_L :log (N:O)≠0)]);rw[E,abs_div,abs_of_pos (_L :0< log (N:O))];have h2:=al N _O;rw[mc (_L :0< log (N:O))];linarith
 have h4 : |log (log 2)|<=1:=by
  rw[ms];have E:exp (-1)< log 2:=by
   have he:exp (-1)< 1/2:=(by rw[lz,mz (ez 1) _N];have:=lX;linarith);linarith[a3]
  have F : -1< log (log 2):=by
   have:=jS (ez (-1)) E
   rwa[iu]at this
  have z:log (log 2)< 0:=log_neg o a4;constructor <;> linarith
 have u : (∑p∈dv N,log (p:O)/(p:O))/log (N:O) +(∑m∈Ico 2 N,(∑p∈dv m,log (p:O)/(p:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)) -log (log (N:O)) =((∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1)+1 -log (log (2:O)) +(∑m∈Ico 2 N,((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)) +(∑m∈Ico 2 N,(log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O))))):=by
  have l :
   (∑m∈Ico 2 N,((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)) +
   (∑m∈Ico 2 N,(log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O))))) =
   (∑m∈Ico 2 N,(∑p∈dv m,log (p:O)/(p:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)) -
   (∑m∈Ico 2 N,(log (log ((m+1:ℕ):O))-log (log (m:O)))):=by
   rw[<- fD,<- f2];exact dF rfl fun m _=>_R
  rw[q]at l;linarith
 rw[u];have U:=abs_add_le
  (((∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1)+1 -log (log (2:O)) +(∑m∈Ico 2 N,((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹)))
  (∑m∈Ico 2 N,(log (m:O)*((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹) -(log (log ((m+1:ℕ):O))-log (log (m:O)))))
 have W:=abs_add_le
  (((∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1)+1 -log (log (2:O)))
  (∑m∈Ico 2 N,((∑p∈dv m,log (p:O)/(p:O))-log (m:O)) *((log (m:O))⁻¹ - (log ((m+1:ℕ):O))⁻¹))
 have X:=abs_sub (((∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1)+1) (log (log (2:O)));have B:=abs_add_le ((∑p∈dv N,log (p:O)/(p:O))/log (N:O)-1) 1;simp only[abs_one]at B;linarith
lemma ao (N:ℕ) (b:3<=N) :
 ∑p∈dv N,(1:O)/(p:O)<=log (log (N:O))+35:=by
 have h:=(ms.mp (an N b)).2;linarith
lemma ap (N:ℕ) (b:3<=N) :
 log (log (N:O))-35<=∑p∈dv N,(1:O)/(p:O):=by
 have h:=(ms.mp (an N b)).1;linarith
set_option maxHeartbeats 800000 in
lemma aq (N:ℕ) (H:3<=N) :
 1/(exp 38*log (N:O)) <=∏p∈dv N,(1-(1:O)/(p:O)) /\
 ∏p∈dv N,(1-(1:O)/(p:O)) <=exp 36/log (N:O):=by
 have b:∀p∈dv N,0< 1-(1:O)/(p:O):=by intro p j;have v:(2:O)<=p:=_M (dU j).two_le;have:(1:O)/(p:O)<=1/2:=dX _N v;linarith
 have d:0< ∏p∈dv N,(1-(1:O)/(p:O)):=jf b;have e:log (∏p∈dv N,(1-(1:O)/(p:O))) =∑p∈dv N,log (1-(1:O)/(p:O)):=iP fun p j=>(b p j).ne';have l:∀p∈dv N,log (1-(1:O)/(p:O))<=-(1:O)/(p:O):=by intro p j;have h:=eY (b p j);rw[ly];linarith
 have o:∀p∈dv N,-(1:O)/(p:O)-2/((p:O)^2)<=log (1-(1:O)/(p:O)):=by
  intro p j;have v:(2:O)<=p:=_M (dU j).two_le;have J:=fl (b p j);have w:=b p j;have y:1-(1-(1:O)/(p:O))⁻¹=-(1:O)/((p:O)-1):=by field_simp [(_L :(p:O)≠0),(_L :(p:O)-1≠0),w.ne'];ring
  rw[y]at J;have B : -(1:O)/(p:O)-2/((p:O)^2)<=-(1:O)/((p:O)-1):=by have C:0< (p:O)-1:=_L;have D:0< (p:O):=_L;rw[ly,ly,sub_le_iff_le_add,neg_add_eq_sub,le_sub_iff_add_le];have:(1:O)/((p:O)-1)-1/(p:O)=1/((p:O)*((p:O)-1)):=(by field_simp [D.ne',C.ne'];ring);have G:1/((p:O)*((p:O)-1))<=2/((p:O)^2):=(by rw[mb _P _P];nlinarith);linarith
  linarith
 have z:∑p∈dv N,(2:O)/((p:O)^2)<=2:=by
  have A:dv N⊆Ioc 1 N:=by intro p j;rw[e7]at j;rw[fw];exact⟨j.2.one_lt,j.1⟩
  calc ∑p∈dv N,(2:O)/((p:O)^2)
      <= ∑m∈Ioc 1 N,(2:O)/((m:O)^2):=dC A fun _ _ _=>_P
    _=2*∑m∈Ioc 1 N,(1:O)/((m:O)^2):=by rw[dP];exact dF rfl fun _ _=>_R
    _<=2:=by
        have:=ab 1 N eR
        simp only[eF,kO]at this;linarith
 have c:0< log (N:O):=et (_M (_O :1< N));have E:=ao N H;have F:=ap N H;constructor
 ·have q : -log (log (N:O))-38 <=log (∏p∈dv N,(1-(1:O)/(p:O))):=by
   rw[e]
   calc -log (log (N:O))-38
       <= -(∑p∈dv N,(1:O)/(p:O)) -∑p∈dv N,(2:O)/((p:O)^2):=_L
     _=∑p∈dv N,(-(1:O)/(p:O)-2/((p:O)^2)):=by rw[<- iw,<- f2];exact dF rfl fun _ _=>_R
     _<=∑p∈dv N,log (1-(1:O)/(p:O)):=dG o
  have i:=me.mpr q;rw[eX d,exp_sub,lz,eX c]at i;have K:(log (N:O))⁻¹/exp 38=1/(exp 38*log (N:O)):=(by field_simp [c.ne',(ez 38).ne']);linarith
 ·have u:log (∏p∈dv N,(1-(1:O)/(p:O))) <=36-log (log (N:O)):=by
   rw[e]
   calc ∑p∈dv N,log (1-(1:O)/(p:O))
       <= ∑p∈dv N,(-(1:O)/(p:O)):=dG l
     _=-(∑p∈dv N,(1:O)/(p:O)):=by rw[<- iw];exact dF rfl fun _ _=>_R
     _<=36-log (log (N:O)):=_L
  have i:=me.mpr u;rw[eX d,exp_sub,eX c]at i;exact i
def ar (N:ℕ):O:=∑p∈dv N,(1:O)/(p:O)
lemma au:Monotone ar:=by
 intro a b c;unfold ar;refine dC ?_ (fun _ _ _=>by positivity)
 intro p d;rw[e7]at d ⊢;exact⟨d.1.trans c,d.2⟩
lemma av:ar 1=0:=by unfold ar;apply g0;intro p b;rw[e7]at b;exact absurd b.2.two_le _O
lemma aw (n:ℕ) :
 ar (n+1)=ar n+if (n+1).Prime then (1:O)/((n+1:ℕ):O) else 0:=by
 unfold ar;have b:dv (n+1) =(if (n+1).Prime then {n+1} else ∅)∪dv n:=by
  ext p;simp only[e7,ff];split_ifs with hmp
  ·simp only[eg];constructor
   ·rintro⟨hple,hp⟩;by_cases d:p=n+1
    ·exact Or.inl d
    ·exact Or.inr ⟨by omega,hp⟩
   ·rintro (rfl | ⟨hple,hp⟩)
    ·exact⟨eR,hmp⟩
    ·exact⟨by omega,hp⟩
  ·simp only[fq,false_or];constructor
   ·rintro⟨hple,hp⟩;have d:p≠n+1:=fun h=>hmp (h ▸ hp);exact⟨by omega,hp⟩
   ·rintro⟨hple,hp⟩;exact⟨by omega,hp⟩
 have c:Disjoint (if (n+1).Prime then ({n+1}:Finset ℕ) else ∅) (dv n):=by
  split_ifs
  ·rw[j8,e7];intro h;omega
  ·exact jy _
 rw[b,jr c,ip];split_ifs <;> simp
lemma ax (M:O):∃N:ℕ,M< ar N:=by
 let N:ℕ:=max 3 ⌈exp (exp (max 0 M+36))⌉₊;refine⟨N,?_⟩;have d:3<=N:=eo _ _;have j:=ap N d;have b:exp (exp (max 0 M+36))<=(N:O):=(g6 _).trans (_M (ep 3 _));have c:exp (max 0 M+36)<=log (N:O):=by have h:=dM (ez _) b;rwa[iu]at h
 have i:max 0 M+36<=log (log (N:O)):=by have h:=dM (ez _) c;rwa[iu]at h
 have e:M<=max 0 M:=ep 0 M;change M< ∑p∈dv N,(1:O)/(p:O);linarith
def ay (m:ℕ):ℕ:=Nat.find (ax (ar m+log 2))-1
def az:ℕ->ℕ
 | 0=>1
 | j+1=>ay (az j)
def aA (j:ℕ):Finset ℕ:=
 if j=0 then ∅ else (Ioc (az (j-1)) (az j)).filter Nat.Prime
lemma aB (m:ℕ) (A:1<=m) :
 m< ay m /\
 ar (ay m)-ar m<=log 2 /\
 log 2< ar (ay m+1)-ar m /\
 (ay m+1).Prime:=by
 classical
 let k:=Nat.find (ax (ar m+log 2));have u:ar m+log 2< ar k:=jF (ax (ar m+log 2));have l:m< k:=by by_contra i;push Not at i;have v:=au i;linarith[a3]
 have q:1<=k:=_O;have j:ar (k-1)<=ar m+log 2:=by by_contra o;push Not at o;exact jW (ax (ar m+log 2)) (_O :k-1< k) o
 have h:k-1+1=k:=_O;have b:k.Prime:=by by_contra y;have c:=aw (k-1);rw[h,gc y,i0]at c;linarith
 have d:m< k-1:=by by_contra i;push Not at i;have e:k-1=m:=_O;have c:=aw m;rw[<- e,h,iM b]at c;have z:(1:O)/(k:O)<=1/2:=(by have w:(2:O)<=(k:O):=_M b.two_le;exact dX _N w);rw[e]at c;linarith[a3]
 change m< k-1/\ar (k-1)-ar m<=log 2 /\log 2< ar (k-1+1)-ar m/\(k-1+1).Prime;rw[h];exact⟨d,by linarith,by linarith,b⟩
lemma aC:StrictMono az:=by
 refine strictMono_nat_of_lt_succ fun j=>?_
 have b:1<=az j:=by
  induction j with
  | zero=>simp[az]
  | succ k ih=>
   have:=(aB (az k) ih).1
   change 1<=ay (az k);omega
 exact (aB (az j) b).1
lemma aD (j:ℕ):1<=az j:=by
 have:=aC.monotone (g5 j)
 simpa[az] using this
lemma aE (j:ℕ):j+1<=az j:=by
 induction j with
 | zero=>simp[az]
 | succ k ih=>
  have b:az k< az (k+1):=aC (Nat.lt_succ_self k);omega
lemma aF (j:ℕ) (i:1<=j) :
 ∑p∈aA j,(1:O)/(p:O)=ar (az j)-ar (az (j-1)):=by
 have d:j≠0:=_O;unfold aA ar;rw[gc d];have c:dv (az (j-1))⊆dv (az j):=by intro p b;rw[e7]at b ⊢;exact⟨b.1.trans (aC.monotone _O),b.2⟩
 rw[<- iI c];congr 1;ext p;simp only[dB,fw,gj,e7];constructor
 ·rintro⟨⟨hgt,hle⟩,b⟩;exact⟨⟨hle,b⟩,fun h=>by omega⟩
 ·rintro⟨⟨hle,b⟩,hnot⟩;refine⟨⟨?_,hle⟩,b⟩;by_contra e;exact hnot ⟨by omega,b⟩
lemma aG (j:ℕ) (b:1<=j) :
 ∑p∈aA j,(1:O)/(p:O)<=log 2:=by
 rw[aF j b];obtain⟨k,rfl⟩:=jL b;simpa[az] using (aB (az k) (aD k)).2.1
lemma aH (j:ℕ) (d:1<=j) :
 log 2-1/((az j+1:ℕ):O)< ∑p∈aA j,(1:O)/(p:O):=by
 rw[aF j d];obtain⟨k,rfl⟩:=jL d;have c:=aB (az k) (aD k);have b:=aw (ay (az k));rw[iM c.2.2.2]at b;change log 2-1/((ay (az k)+1:ℕ):O) < ar (ay (az k))-ar (az k);linarith[c.2.2.1]
set_option maxHeartbeats 800000 in
lemma aI (j:ℕ) :
 (j:O)*log 2-10<=ar (az j) /\ar (az j)<=(j:O)*log 2:=by
 have b:∀n:ℕ,ar (az n)<=(n:O)*log 2:=by
  intro n;induction n with
  | zero=>simp[az,av]
  | succ k ih=>
   have R:=(aB (az k) (aD k)).2.1;change ar (ay (az k))<=((k+1:ℕ):O)*log 2;push_cast;linarith
 refine⟨?_,b j⟩
 have c:∀n:ℕ,(n:O)/3-2<=ar (az n):=by
  intro n;induction n with
  | zero=>simp[az,av]
  | succ k ih=>
   have o:=aH (k+1) _O;rw[aF (k+1) _O]at o;simp only[gn]at o;by_cases hk:5<=k
   ·have q:(6:O)<=((az (k+1)+1:ℕ):O):=by
     have:=aE (k+1)
     exact_mod_cast (_O :6<=az (k+1)+1)
    have P:(1:O)/((az (k+1)+1:ℕ):O)<=1/6:=dX _N q;have S:(1/3:O)<=log 2-1/6:=_l a3;push_cast;linarith
   ·have T:0<=ar (az (k+1)):=by
     unfold ar;exact ea fun _ _=>_P
    have U:(k:O)<=4:=_M (_O :k<=4);push_cast;linarith
 have d:∑i∈Icc 1 j,(1:O)/((az i+1:ℕ):O)<=10:=by
  have E:∑i∈Icc 1 j,(1:O)/((az i+1:ℕ):O) <=(∑i∈Icc (1:ℕ) 150,(1:O)/(i:O)) +∑i∈Ioc (150:ℕ) (max 150 j),(288:O)/((i:O)^2):=by
   have u:Icc 1 j⊆Icc (1:ℕ) 150∪Ioc 150 (max 150 j):=by
    intro i hi;rw[dT]at hi;rw[ff,dT,fw];by_cases m:i<=150
    ·exact Or.inl ⟨hi.1,m⟩
    ·exact Or.inr ⟨by omega,hi.2.trans (ep 150 j)⟩
   have v:∑i∈Icc 1 j,(1:O)/((az i+1:ℕ):O) <=(∑i∈Icc (1:ℕ) 150,(1:O)/((az i+1:ℕ):O)) +(∑i∈Ioc (150:ℕ) (max 150 j),(1:O)/((az i+1:ℕ):O)):=(by have w:Disjoint (Icc (1:ℕ) 150) (Ioc 150 (max 150 j)):=(by rw[eb];intro x M N;rw[dT]at M;rw[fw]at N;omega);rw[<- jr w];exact dC u fun _ _ _=>_P);refine v.trans (fd ?_ ?_)
   ·refine dG fun i hi=>?_
    rw[dT]at hi;have W:=aE i;exact dX (_M (_O :0< i)) (_M (_O :i<=az i+1))
   ·refine dG fun i hi=>?_
    rw[fw]at hi;have y:151<=i:=_O;have z:3<=az i:=(by have:=aE i;omega);have X:=ao (az i) z;have hr:=c i;change ar (az i)<=log (log (az i:O))+35 at X;have Z:(151:O)<=(i:O):=_M y;have J:(i:O)/12<=log (log (az i:O)):=_L;have A:exp ((i:O)/12)<=log (az i:O):=by have h:=me.mpr J;have e:0< log (az i:O):=et (_M (_O :1< az i));rwa[eX e]at h
    have l:(i:O)/12<=log (az i:O):=by
     have:=fB ((i:O)/12)
     linarith
    have B:((i:O)/12)^2/2<=(az i:O):=(by have F:exp ((i:O)/12)<=(az i:O):=(by have h:=me.mpr l;rwa[eX _P]at h);have K:((i:O)/12)^2/2<=exp ((i:O)/12):=(by have h:=kl (_P :0<=(i:O)/12) 3;simp[jt,Nat.factorial]at h;linarith);linarith);have Q:((i:O)^2)/288<=((az i+1:ℕ):O):=(by push_cast;linarith);rw[mb _P _P];nlinarith
  have G:∑i∈Icc (1:ℕ) 150,(1:O)/(i:O)<=7:=by
   have F:=a9 150;have C:log ((150:ℕ):O)<=6:=by
    have m:((150:ℕ):O)<=exp 6:=by
     have he:(2.7:O)<=exp 1:=_l lX;have h6:(2.7:O)^6<=exp 6:=by
      calc (2.7:O)^6<=(exp 1)^6:=m9 _N he 6
        _=exp 6:=by rw[<- gg];norm_num
     norm_num at h6 ⊢
     linarith
    have:=dM _N m
    rwa[iu]at this
   exact F.trans _L
  have H:∑i∈Ioc (150:ℕ) (max 150 j),(288:O)/((i:O)^2)<=2:=(by have F:∑i∈Ioc (150:ℕ) (max 150 j),(288:O)/((i:O)^2) =288*∑i∈Ioc (150:ℕ) (max 150 j),(1:O)/((i:O)^2):=(by rw[dP];exact dF rfl fun _ _=>_R);rw[F];have K:=ab 150 (max 150 j) _N;have K':∑i∈Ioc (150:ℕ) (max 150 j),(1:O)/((i:O)^2)<=1/(150:O):=(by simpa using K);linarith);linarith
 have D:ar (az j) =∑i∈Icc 1 j,∑p∈aA i,(1:O)/(p:O):=by
  clear d c b;induction j with
  | zero=>simp[az,av]
  | succ k ih=>
   rw[iK _O,<- ih,aF (k+1) _O];simp only[gn];ring
 rw[D];have o:∑i∈Icc 1 j,(log 2-1/((az i+1:ℕ):O)) <=∑i∈Icc 1 j,∑p∈aA i,(1:O)/(p:O):=dG fun i hi=>(aH i (dT.mp hi).1).le;rw[f2,ex,Nat.card_Icc,gn,e3]at o;linarith
lemma aJ (j:ℕ) (z:1<=j) :
 (2:O)^((j:ℤ)-100)<=log (az j:O) /\log (az j:O)<=(2:O)^((j:ℤ)+100):=by
 by_cases u:3<=az j
 ·have v:=an (az j) u;have w:=aI j;change |ar (az j)-log (log (az j:O))|<=35 at v;rw[ms]at v;have d:((j:ℤ)-100:O)*log 2<=log (log (az j:O)):=by
   have:(45:O)<=100*log 2:=_l a3
   push_cast;linarith
  have e:log (log (az j:O))<=((j:ℤ)+100:O)*log 2:=by
   have:(35:O)<=100*log 2:=_l a3
   push_cast;linarith
  have b:0< log (az j:O):=et (_M (_O :1< az j));constructor
  ·have c:=me.mpr d;rw[eX b]at c;have o:exp (((j:ℤ)-100:O)*log 2)=(2:O)^((j:ℤ)-100):=(by rw[e8,<- fQ (_N :(0:O)< 2),show ((j:ℤ)-100:O)=(((j:ℤ)-100:ℤ):O) by push_cast;ring,Real.rpow_intCast]);linarith
  ·have c:=me.mpr e;rw[eX b]at c;have o:exp (((j:ℤ)+100:O)*log 2)=(2:O)^((j:ℤ)+100):=(by rw[e8,<- fQ (_N :(0:O)< 2),show ((j:ℤ)+100:O)=(((j:ℤ)+100:ℤ):O) by push_cast;ring,Real.rpow_intCast]);linarith
 ·have y:=aE j;have q:j=1:=_O;subst q;have i:az 1=2:=_O;rw[i];have l:((2:ℕ):O)=2:=_N;rw[l];constructor
  ·have h:(2:O)^(((1:ℕ):ℤ)-100)<=(2:O)^(-1:ℤ):=zpow_le_zpow_right₀ _N _O;have m:(2:O)^(-1:ℤ)=1/2:=_N;exact (h.trans_eq m).trans a3.le
  ·have h:(1:O)<=(2:O)^(((1:ℕ):ℤ)+100):=one_le_zpow₀ _N _O;linarith[a4]
def aK (X z:ℕ):ℕ:=((Icc 1 X).filter fun b=>∀p ≤ z,p.Prime->¬ p∣b).card
lemma aL (X:ℕ) {z1 z2:ℕ} (h:z1<=z2) :
 aK X z2<=aK X z1:=by
 unfold aK;refine er fun b c=>?_
 simp only[dB]at c ⊢;exact⟨c.1,fun p d e=>c.2 p (d.trans h) e⟩
def aM (w:ℕ):Finset ℕ:=(Icc 1 w).filter Squarefree
def aN (w:ℕ):O:=∑m∈aM w,(1:O)/(Nat.totient m:O)
def aO (w m:ℕ):O:=
 if m∈aM w then (dz m:O)/((Nat.totient m:O)*aN w) else 0
def aP (w r:ℕ):O:=
 if r∈aM w then (r:O)*∑m∈(aM w).filter (r∣·),(dz (m/r):O)*aO w m
 else 0
lemma aQ {w:ℕ} (b:1<=w):1∈aM w:=by simp only[aM,dB,dT];exact⟨⟨eR,b⟩,lG⟩
lemma aR {w m k:ℕ} (e:k∈aM w) (d:m∣k):m∈aM w:=by simp only[aM,dB,dT]at e ⊢;have b:1<=m:=j3 d _O;have c:m<=w:=(el _O d).trans e.1.2;exact⟨⟨b,c⟩,e.2.squarefree_of_dvd d⟩
lemma aS {m:ℕ} (i:Squarefree m) :
 ∏p∈m.primeFactors,p=m:=by
 have b:m≠0:=i.ne_zero;conv_rhs=>rw[<- ew b,Finsupp.prod]
 refine f9 (by rw[ej]) fun p h=>?_
 have c:=dD h;have d:1<=m.factorization p:=kL c b (dS h);have e:m.factorization p<=1:=by by_contra l;have j:p^2∣m:=(c.pow_dvd_iff_le_factorization b).mpr (_O :2<=m.factorization p);exact c.ne_one (mn.mp (i p (by simpa[sq] using j)))
 simp[(_O :m.factorization p=1)]
lemma aT (S:Finset ℕ) (b:∀p∈S,p.Prime) :
 Nat.totient (∏p∈S,p)=∏p∈S,(p-1):=by
 induction S using eW with
 | empty=>simp
 | @insert q S hqS ih=>
  have e:=b q (ev q S);have b':∀p∈S,p.Prime:=fun p d=>b p (fa d);have c:Nat.Coprime q (∏p∈S,p):=fL fun p d=>(ft e (b' p d)).mpr (fun h=>hqS (h ▸ d));rw[fN hqS,fN hqS,lu c,Nat.totient_prime e,ih b']
lemma aU (m:ℕ) (c:Squarefree m) :
 Nat.totient m=∏p∈m.primeFactors,(p-1):=by
 conv_lhs=>rw[<- aS c]
 exact aT m.primeFactors fun p b=>dD b
set_option maxHeartbeats 800000 in
lemma aV (r:ℕ) (z:Squarefree r) :
 (r:O)/(Nat.totient r:O)=∑d∈r.divisors,(1:O)/(Nat.totient d:O):=by
 have o:r≠0:=z.ne_zero;have b:∏p∈r.primeFactors,p=r:=aS z;rw[aU r z];have q:(r:O)/((∏p∈r.primeFactors,(p-1):ℕ):O) =∏p∈r.primeFactors,(1+(1:O)/((p:O)-1)):=by
  calc (r:O)/((∏p∈r.primeFactors,(p-1):ℕ):O)
      = ((∏p∈r.primeFactors,p:ℕ):O)/((∏p∈r.primeFactors,(p-1):ℕ):O):=by rw[b]
    _=(∏p∈r.primeFactors,(p:O))/(∏p∈r.primeFactors,((p-1:ℕ):O)):=by push_cast;rfl
    _=∏p∈r.primeFactors,(p:O)/((p-1:ℕ):O):=(gM ..).symm
    _=∏p∈r.primeFactors,(1+(1:O)/((p:O)-1)):=by
        refine f9 rfl fun p i=>?_
        have u:=dD i;have A:(0:O)< (p:O)-1:=(by have B:(2:O)<=p:=_M u.two_le;linarith);rw[ei u.one_le,eF];field_simp [A.ne'];ring
 rw[q,Finset.prod_one_add];let f:Finset ℕ->ℕ:=fun S=>∏p∈S,p;have v:r.divisors=r.primeFactors.powerset.image f:=by
  ext d;simp only[fW,dW,eS,f];constructor
  ·rintro⟨hdvd,_⟩;exact⟨d.primeFactors,k9 hdvd o,aS (z.squarefree_of_dvd hdvd)⟩
  ·rintro⟨S,m,rfl⟩;refine⟨?_,o⟩;rw[<- b];exact iF S r.primeFactors (fun p=>p) m
 have w:Set.InjOn f (r.primeFactors.powerset:Set (Finset ℕ)):=by intro E c F e y;rw[eB,eS]at c e;have C:=go (fun p i=>dD (c i));have D:=go (fun p i=>dD (e i));dsimp only[f]at y;rw[<- C,<- D,y]
 rw[v,fr (fun E c F e h=>w c e h)];refine dF rfl fun S m=>?_
 rw[eS]at m;have j:Squarefree (f S):=z.squarefree_of_dvd (by
  rw[<- b];exact iF S r.primeFactors (fun p=>p) m)
 have l:(f S).primeFactors=S:=go (fun p i=>dD (m i));rw[aU (f S) j,l];push_cast;rw[gM,kb];congr 1;refine f9 rfl fun p i=>?_
 rw[ei (dD (m i)).one_le,eF]
set_option maxHeartbeats 800000 in
lemma aW (w:ℕ) (hw:1<=w) :
 log ((w+1:ℕ):O)<=aN w:=by
 let A:ℕ->Finset ℕ:=fun m=>(Icc 1 w).filter fun n=>n.primeFactors=m.primeFactors;have h4:∀m∈aM w,∑n∈A m,(1:O)/(n:O)<=(1:O)/(Nat.totient m:O):=by
  intro m hm;simp only[aM,dB]at hm;rw[aU m hm.2];have e:(1:O)/((∏p∈m.primeFactors,(p-1):ℕ):O) =∏p∈m.primeFactors,(1:O)/((p:O)-1):=by
   push_cast;rw[gM,kb];congr 1;refine f9 rfl fun p u=>?_
   rw[ei (dD u).one_le,eF]
  rw[e];have hg:∀(F:Finset ℕ),(∀p∈F,p.Prime) -> ∑n∈(Icc 1 w).filter (fun n=>n.primeFactors=F),(1:O)/(n:O) <=∏p∈F,(1:O)/((p:O)-1):=by
   intro F;induction F using eW with
   | empty=>
    intro _;have h5:(Icc 1 w).filter (fun n=>n.primeFactors=∅)={1}:=by
     ext n;simp only[dB,dT,eg];constructor
     ·rintro⟨⟨hC,_⟩,hpf⟩;by_contra hD;obtain⟨p,u,hx⟩:=jK hD;have Z:p∈n.primeFactors:=md.mpr ⟨u,hx,_O⟩;rw[hpf]at Z;simp at Z
     ·rintro rfl;exact⟨⟨eR,hw⟩,Nat.primeFactors_one⟩
    rw[h5];simp
   | @insert q F hqF ih=>
    intro z;have y:q.Prime:=z q (ev q F);have z':∀p∈F,p.Prime:=fun p u=>z p (fa u);rw[fN hqF];let d:=(Icc 1 w).filter fun n=>n.primeFactors=insert q F;let h6:=(Icc 1 w).filter fun n=>n.primeFactors=F;let i:ℕ->ℕ × ℕ:=fun n=>(n.factorization q,n/q^(n.factorization q));have h7:∀n∈d,i n∈Icc 1 w×ˢh6:=by
     intro n X;simp only[d,dB,dT]at X;have N:q∈n.primeFactors:=(by rw[X.2];exact ev q F);have P:1<=n.factorization q:=kL y _O (dS N);have c:q^(n.factorization q)∣n:=gd n q;have h8:n.factorization q<=w:=by have hE:n.factorization q< q^(n.factorization q):=Nat.lt_pow_self y.one_lt;have hy:q^(n.factorization q)<=n:=el _O c;omega
     have v:1<=n/q^(n.factorization q):=ia (el _O c) (iN y.pos _);have B:n/q^(n.factorization q)<=w:=(gs _ _).trans X.1.2;have C:(n/q^(n.factorization q)).primeFactors=F:=by
      have D:q^(n.factorization q)*(n/q^(n.factorization q))=n:=eC c;have h9:¬ q∣n/q^(n.factorization q):=Nat.not_dvd_ordCompl y _O;ext p;simp only[md];constructor
      ·rintro⟨Q,hpdvd,_⟩;have j:p∈n.primeFactors:=md.mpr ⟨Q,hpdvd.trans (Nat.div_dvd_of_dvd c),_O⟩;rw[X.2,ga]at j;rcases j with rfl | M
       ·exact absurd hpdvd h9
       ·exact M
      ·intro M;have Q:=z' p M;have hh:p≠q:=fun h=>hqF (h ▸ M);have j:p∈n.primeFactors:=(by rw[X.2];exact fa M);have l:p∣n:=dS j;rw[<- D]at l;have hj:Nat.Coprime p (q^(n.factorization q)):=((ft Q y).mpr hh).pow_right _;exact⟨Q,hj.dvd_of_dvd_mul_left l,_O⟩
     rw[ki];exact⟨dT.mpr ⟨P,h8⟩,dB.mpr ⟨dT.mpr ⟨v,B⟩,C⟩⟩
    have hk:Set.InjOn i (d:Set ℕ):=(by intro n1 hC n2 hF H;simp only[i,jb]at H;have h1:q^(n1.factorization q)*(n1/q^(n1.factorization q))=n1:=eC (gd n1 q);have h2:q^(n2.factorization q)*(n2/q^(n2.factorization q))=n2:=eC (gd n2 q);rw[<- h1,<- h2,H.2,H.1]);have hl:∀n∈d,(1:O)/(n:O)=((1:O)/((q:O)^(i n).1))*((1:O)/((i n).2:O)):=by
     intro n _;have D:(n:O)=((q:O)^(i n).1)*((i n).2:O):=by have ho:=(eC (gd n q)).symm;exact_mod_cast ho
     rw[D,one_div_mul_one_div]
    have hs:∑k∈Icc 1 w,(1:O)/((q:O)^k)<=(1:O)/((q:O)-1):=by
     have E:(2:O)<=q:=_M y.two_le;have hr:(q:O)⁻¹< 1:=mL _L;have G:0< 1-(q:O)⁻¹:=_L;have ht:∑k∈Icc 1 w,(1:O)/((q:O)^k) =(∑k∈range (w+1),((q:O)⁻¹)^k)-1:=by
      have h0:=lb (f:=fun k=>((q:O)⁻¹)^k) (gO w);rw[Finset.range_eq_Ico,h0];have hv:Icc 1 w=Ico 1 (w+1):=rfl;rw[hv];have R:∑k∈Ico 1 (w+1),(1:O)/((q:O)^k) =∑k∈Ico 1 (w+1),((q:O)⁻¹)^k:=dF rfl fun k _=>by rw[inv_pow,g9]
      rw[R];simp
     rw[ht,fO hr.ne];have h3:(q:O)⁻¹ - 1≠0:=_L;have H:(((q:O)⁻¹)^(w+1)-1)/((q:O)⁻¹ - 1)-1 =((q:O)⁻¹ - ((q:O)⁻¹)^(w+1))/(1-(q:O)⁻¹):=(by rw[div_sub_one h3,div_eq_div_iff h3 G.ne'];ring);rw[H];have S:(0:O)< q:=_L;have J:(0:O)< (q:O)-1:=_L;have h1:((q:O)⁻¹ - ((q:O)⁻¹)^(w+1))/(1-(q:O)⁻¹) <=(q:O)⁻¹/(1-(q:O)⁻¹):=dI (by have hz:(0:O)<=((q:O)⁻¹)^(w+1):=_P;linarith) G.le;have h2:(q:O)⁻¹/(1-(q:O)⁻¹)=(1:O)/((q:O)-1):=(by field_simp [S.ne',J.ne',G.ne']);linarith
    calc ∑n∈d,(1:O)/(n:O)
        = ∑n∈d,((1:O)/((q:O)^(i n).1))*((1:O)/((i n).2:O)):=dF rfl hl
      _=∑x∈d.image i,((1:O)/((q:O)^x.1))*((1:O)/(x.2:O)):=(fr (f:=fun x:ℕ × ℕ=>((1:O)/((q:O)^x.1))*((1:O)/(x.2:O)))
            (fun a ha b hb h=>hk ha hb h)).symm
      _<=∑x∈Icc 1 w×ˢh6,((1:O)/((q:O)^x.1))*((1:O)/(x.2:O)):=dC (mv.mpr h7) (fun _ _ _=>by positivity)
      _=(∑k∈Icc 1 w,(1:O)/((q:O)^k)) *(∑n∈h6,(1:O)/(n:O)):=by
          rw[lc,jn];refine dF rfl fun k _=>?_
          dsimp only;exact (dP ..).symm
      _<=((1:O)/((q:O)-1))*(∏p∈F,(1:O)/((p:O)-1)):=en hs (ih z') (ea fun _ _=>by positivity) (by
            have E:(2:O)<=q:=_M y.two_le;exact ed eO _L)
  exact hg m.primeFactors (fun p u=>dD u)
 have hc:Icc 1 w⊆(aM w).biUnion A:=by
  intro n X;rw[dT]at X;let r:=∏p∈n.primeFactors,p;have U:r∣n:=Nat.prod_primeFactors_dvd n;have W:1<=r:=by
   have:0< r:=jf fun p u=>(dD u).pos
   omega
  have hd:r<=w:=(el _O U).trans X.2;have K:r.primeFactors=n.primeFactors:=go (fun p u=>dD u);have he:Squarefree r:=by
   rw[Nat.squarefree_iff_prime_squarefree];intro q y E;have hf:q∈n.primeFactors:=by rw[<- K];exact md.mpr ⟨y,(kS q q).trans E,_O⟩
   have e:r=q*∏p∈n.primeFactors.erase q,p:=(gk _ _ hf).symm;rw[e]at E;have o:q∣∏p∈n.primeFactors.erase q,p:=(Nat.mul_dvd_mul_iff_left y.pos).mp E;rw[y.prime.dvd_finsetProd_iff]at o;obtain⟨p,u,hB⟩:=o;rw[gS]at u;exact u.1 ((eI y (dD u.2)).mp hB).symm
  rw[g4];exact⟨r,dB.mpr ⟨dT.mpr ⟨W,hd⟩,he⟩,dB.mpr ⟨dT.mpr X,K.symm⟩⟩
 calc log ((w+1:ℕ):O)
     <= ∑n∈Icc 1 w,(1:O)/(n:O):=aa w
   _<=∑n∈(aM w).biUnion A,(1:O)/(n:O):=dC hc fun _ _ _=>_P
   _<=∑m∈aM w,∑n∈A m,(1:O)/(n:O):=by
       have hA:∀(T:Finset ℕ),∑n∈T.biUnion A,(1:O)/(n:O) <=∑m∈T,∑n∈A m,(1:O)/(n:O):=by
         intro T;induction T using eW with
         | empty=>simp
         | @insert m T hmT ihT=>
           rw[iS,i3 hmT];have hu:=fb (s₁:=A m) (s₂:=T.biUnion A) (f:=fun n:ℕ=>(1:O)/(n:O));have hz:0<=∑n∈A m∩T.biUnion A,(1:O)/(n:O):=ea fun _ _=>_P;linarith
       exact hA (aM w)
   _<=∑m∈aM w,(1:O)/(Nat.totient m:O):=dG h4
lemma aX {w:ℕ} (b:1<=w):1<=aN w:=by
 calc (1:O)=(1:O)/(Nat.totient 1:O):=by simp
   _<=aN w:=fi (f:=fun m=>(1:O)/(Nat.totient m:O)) (fun _ _=>by positivity) (aQ b)
lemma aY {w m:ℕ} (b:m∈aM w) :
 ((dz m:O))^2=1:=by
 simp only[aM,dB]at b;rw[jM b.2];push_cast;rw[<- it,e8,it];simp
lemma aZ {w:ℕ} (h:1<=w):aP w 1=1:=by
 have d:1∈aM w:=aQ h;have b:0< aN w:=e9 i5 (aX h);simp only[aP,d,↓reduceIte,eF,gz,Nat.div_one];rw[Finset.filter_true_of_mem fun _ _=>one_dvd _]
 calc ∑m∈aM w,(dz m:O)*aO w m
     = ∑m∈aM w,(1:O)/((Nat.totient m:O)*aN w):=by
       refine dF rfl fun m e=>?_
       simp only[aO,e,↓reduceIte];have i:=aY e;have c:(Nat.totient m:O)≠0:=(by simp only[aM,dB,dT]at e;exact_mod_cast (mw.mpr _O).ne');field_simp [c,b.ne'];linarith
   _=(1/aN w)*aN w:=by dsimp only[aN];rw[dP];exact dF rfl fun _ _=>_R
   _=1:=by field_simp [b.ne']
set_option maxHeartbeats 800000 in
lemma b3 {w r:ℕ} (hw:1<=w) (hr:r∈aM w) :
 |aP w r|<=1:=by
 have c:0< aN w:=e9 i5 (aX hw);have o:=hr;simp only[aM,dB,dT]at o;have j:Squarefree r:=o.2;have e:(0:O)< (Nat.totient r:O):=by exact_mod_cast mw.mpr _O
 let K:=(aM (w/r)).filter (fun k=>Nat.Coprime k r);have P:(aM w).filter (r∣·)=K.image (fun k=>r*k):=by
  ext m;simp only[dB,dW,K,aM,dT];constructor
  ·rintro⟨⟨⟨hm1,hmw⟩,hmsq⟩,⟨k,rfl⟩⟩;refine⟨k,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,rfl⟩
   ·rcases eq_or_ne k 0 with rfl | hk0
    ·simp at hm1
    ·omega
   ·exact (dZ _O).mpr _L
   ·exact hmsq.squarefree_of_dvd (kS k r)
   ·exact (mq.mp hmsq).1.symm
  ·rintro⟨k,⟨⟨⟨h4,h3⟩,hksq⟩,hkcop⟩,rfl⟩;refine⟨⟨⟨by nlinarith,?_⟩,?_⟩,ir r k⟩
   ·have:=(dZ _O).mp h3;nlinarith
   ·exact mq.mpr ⟨hkcop.symm,j,hksq⟩
 have h0:Set.InjOn (fun k=>r*k) (K:Set ℕ):=by intro k1 _ k2 _ h;exact fR _O h
 have B:aP w r =((dz r:O)/aN w) *((r:O)/(Nat.totient r:O)) *(∑k∈K,(1:O)/(Nat.totient k:O)):=by
  simp only[aP,hr,↓reduceIte];rw[P,fr (fun a ha b hb h=>h0 ha hb h)];rw[dP,dP];refine dF rfl fun k q=>?_
  have q':=q;simp only[K,aM,dB,dT]at q';have C:r*k∈aM w:=by
   have:r*k∈K.image (fun k=>r*k):=iL _ q
   rw[<- P]at this;exact (dB.mp this).1
  simp only[aO,C,↓reduceIte,gb k (_O :0< r)];have i:Nat.Coprime r k:=q'.2.symm;have D:(dz (r*k):O) =(dz r:O)*(dz k:O):=(by exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime i);have v:(Nat.totient (r*k):O)=(Nat.totient r:O)*(Nat.totient k:O):=(by exact_mod_cast lu i);have Z:((dz k:O))^2=1:=by rw[jM q'.1.2];push_cast;rw[<- it,e8,it];simp
  have l:(Nat.totient k:O)≠0:=(by exact_mod_cast (mw.mpr _O).ne');rw[D,v];field_simp [e.ne',l,c.ne'];nlinarith
 have y:((r:O)/(Nat.totient r:O))*(∑k∈K,(1:O)/(Nat.totient k:O))<=aN w:=by
  rw[aV r j,jn];have R:∑d∈r.divisors,(1:O)/(Nat.totient d:O) *(∑k∈K,(1:O)/(Nat.totient k:O)) =∑p∈r.divisors×ˢK,(1:O)/(Nat.totient (p.1*p.2):O):=by
   rw[lc];refine dF rfl fun d hd=>?_
   rw[dP];refine dF rfl fun k q=>?_
   simp only[K,dB]at q;have E:Nat.Coprime d k:=q.2.symm.coprime_dvd_left (ef hd);rw[lu E,g3,one_div_mul_one_div]
  rw[R];let z:ℕ × ℕ->ℕ:=fun p=>p.1*p.2;have S:∀p∈r.divisors×ˢK,z p∈aM w:=by
   intro p hp;rw[ki]at hp;have F:p.1∣r:=ef hp.1;have h5:1<=p.1:=em hp.1;have h6:p.1<=r:=el _O F;have q:=hp.2;simp only[K,aM,dB,dT]at q;have E:Nat.Coprime p.1 p.2:=q.2.symm.coprime_dvd_left F;simp only[aM,dB,dT,z];refine⟨⟨by nlinarith,?_⟩,mq.mpr ⟨E,j.squarefree_of_dvd F,q.1.2⟩⟩
   have h3:r*p.2<=w:=(dZ _O).mp q.1.1.2 |> fun h=>_L;nlinarith
  have A:Set.InjOn z ((r.divisors×ˢK:Finset (ℕ × ℕ)):Set (ℕ × ℕ)):=by intro Q M W X N;rw[eB,ki]at M X;simp only[z]at N;have h1:=ef M.1;have h2:=ef X.1;have h4:Nat.Coprime Q.2 r:=(dB.mp M.2).2;have h7:Nat.Coprime W.2 r:=(dB.mp X.2).2;have T:Nat.gcd (Q.1*Q.2) r=Q.1:=(by rw[l4 Q.1 h4,lw h1]);have U:Nat.gcd (W.1*W.2) r=W.1:=(by rw[l4 W.1 h7,lw h2]);have u:Q.1=W.1:=(by rw[<- T,N,U]);have G:0< Q.1:=em M.1;have J:Q.2=W.2:=fR G (by rw[<- u]at N;exact N);exact iq u J
  calc ∑p∈r.divisors×ˢK,(1:O)/(Nat.totient (z p):O)
      = ∑m∈(r.divisors×ˢK).image z,(1:O)/(Nat.totient m:O):=(fr (f:=fun m=>(1:O)/(Nat.totient m:O))
          (fun a ha b hb h=>A ha hb h)).symm
    _<=∑m∈aM w,(1:O)/(Nat.totient m:O):=dC (mv.mpr S) (fun _ _ _=>by positivity)
 rw[B,lA,lA,abs_div,abs_of_pos c];have H : |(dz r:O)|=1:=by have h8:=aY hr;nlinarith[sq_abs (dz r:O),abs_nonneg (dz r:O)]
 rw[H,jE _P,jE (ea fun _ _=>by positivity),f0,g9,inv_mul_le_iff₀ c,fv]
 exact y
set_option maxHeartbeats 800000 in
lemma b4 {w m:ℕ} (Z:m∈aM w) :
 ∑r∈(aM w).filter (m∣·),aP w r/(r:O)=aO w m:=by
 let S:=aM w;have u:∑r∈S.filter (m∣·),aP w r/(r:O) =∑r∈S.filter (m∣·),∑k∈S.filter (r∣·),(dz (k/r):O)*aO w k:=by
  refine dF rfl fun r o=>?_
  rw[dB]at o;have v:(0:O)< r:=by simp only[S,aM,dB,dT]at o;exact_mod_cast (_O :0< r)
  simp only[aP,S,o.1,↓reduceIte];field_simp [v.ne']
 rw[u];have G:∑r∈S.filter (m∣·),∑k∈S.filter (r∣·),(dz (k/r):O)*aO w k =∑k∈S.filter (m∣·),(∑r∈k.divisors.filter (m∣·),(dz (k/r):O))*aO w k:=by
  trans ∑r∈S.filter (m∣·),∑k∈S.filter (m∣·),if r∣k then (dz (k/r):O)*aO w k else 0
  ·refine dF rfl fun r o=>?_
   rw[<- f8];congr 1;ext k;simp only[dB];rw[dB]at o;constructor
   ·rintro⟨h,hrk⟩;exact⟨⟨h,o.2.trans hrk⟩,hrk⟩
   ·rintro⟨⟨h,_⟩,hrk⟩;exact⟨h,hrk⟩
  ·rw[hH];refine dF rfl fun k h=>?_
   rw[<- f8,jn];congr 1;ext r;simp only[dB,fW];rw[dB]at h;have T:k≠0:=(by simp only[S,aM,dB,dT]at h;omega);constructor
   ·rintro⟨⟨_,hmr⟩,hrk⟩;exact⟨⟨hrk,T⟩,hmr⟩
   ·rintro⟨⟨hrk,_⟩,hmr⟩;exact⟨⟨aR h.1 hrk,hmr⟩,hrk⟩
 rw[G];have y:∀k∈S.filter (m∣·),(∑r∈k.divisors.filter (m∣·),(dz (k/r):O))*aO w k =if k=m then aO w m else 0:=by
  intro k h;rw[dB]at h;have e:1<=k:=(by simp only[S,aM,dB,dT]at h;omega);have d:1<=m:=(by simp only[aM,dB,dT]at Z;omega);have i:1<=k/m:=ia (el e h.2) d;have M:∑r∈k.divisors.filter (m∣·),(dz (k/r):O) =∑t∈(k/m).divisors,(dz t:O):=by
   refine Finset.sum_nbij (fun r=>k/r) ?_ ?_ ?_ ?_
   ·intro r o;simp only[dB,fW]at o ⊢;rcases o.2 with⟨c,rfl⟩;have N:c≠0:=(by rintro rfl;simp at o);have j:m*c∣k:=o.1.1;rcases j with⟨t,F⟩;refine⟨⟨c,?_⟩,_O⟩;have z:k/m=c*t:=(by rw[F,f0,gb _ d]);have A:k/(m*c)=t:=(by rw[F,gb _ (fP d _O)]);rw[z,A,e8]
   ·intro W D X Q R;simp only[eB,dB,fW]at D Q;have H:W*(k/W)=k:=eC D.1.1;have q:X*(k/X)=k:=eC Q.1.1;have B:0< k/W:=ia (el e D.1.1) (j3 D.1.1 e);dsimp only at R;rw[<- R]at q;exact ii B (H.trans q.symm)
   ·intro t F;rw[eB,fW]at F;rcases F.1 with⟨c,K⟩;have U:m*c∣k:=by
     refine⟨t,?_⟩
     have H:m*(k/m)=k:=eC h.2;rw[K]at H;linarith
    have C:0< c:=(by by_contra N;push Not at N;have:c=0:=_O;rw[this,hK]at K;omega);refine⟨m*c,?_,?_⟩
    ·simp only[eB,dB,fW];exact⟨⟨U,_O⟩,ir m c⟩
    ·have H:m*(k/m)=k:=eC h.2;rw[K]at H;have q:(m*c)*t=k:=_L;dsimp only;rw[<- q,gb _ (fP d C)]
   ·intro _ _;rfl
  rw[M];have J:(∑t∈(k/m).divisors,(dz t:O)) =if k/m=1 then 1 else 0:=by
   have hz:(∑t∈(k/m).divisors,dz t) =if k/m=1 then 1 else 0:=by
    have q:=fT (fun f=>f (k/m)) ArithmeticFunction.moebius_mul_coe_zeta;rw[ArithmeticFunction.mul_apply,ArithmeticFunction.one_apply,Nat.sum_divisorsAntidiagonal (f:=fun a b=>dz a*((ArithmeticFunction.zeta:ArithmeticFunction ℤ) b))]at q;rw[<- q];refine dF rfl fun t F=>?_
    have l:k/m / t≠0:=(by have P:=ef F;have:=ia (el i P) (em F);omega);simp[ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply,l]
   exact_mod_cast hz
  rw[J];have E:k/m=1↔k=m:=by
   constructor
   ·intro H;have q:=eC h.2;rw[H,fv]at q;exact q.symm
   ·rintro rfl;exact Nat.div_self d
  by_cases j:k=m
  ·subst j;simp[E.mpr rfl]
  ·simp[mt E.mp j,j]
 rw[dF rfl y,Finset.sum_ite_eq'];simp[S,Z]
set_option maxHeartbeats 800000 in
lemma b5 {w:ℕ} (D:1<=w) :
 ∑c∈aM w,∑b∈aM w,aP w c*aP w b/((Nat.lcm c b:ℕ):O) =1/aN w:=by
 let S:=aM w;have d:0< aN w:=e9 i5 (aX D);have e:∀c∈S,∀b∈S,(1:O)/((Nat.lcm c b:ℕ):O) =((1:O)/(c:O))*((1:O)/(b:O)) *∑m∈(Nat.gcd c b).divisors,(Nat.totient m:O):=by intro c l b u;have z:1<=c:=(by simp only[S,aM,dB,dT]at l;omega);have E:1<=b:=(by simp only[S,aM,dB,dT]at u;omega);have v:(∑m∈(Nat.gcd c b).divisors,(Nat.totient m:O))=(Nat.gcd c b:O):=(by exact_mod_cast Nat.sum_totient (Nat.gcd c b));rw[v];have C:(Nat.gcd c b:O)*(Nat.lcm c b:O)=(c:O)*(b:O):=(by exact_mod_cast Nat.gcd_mul_lcm c b);have i:(Nat.lcm c b:O)≠0:=(by exact_mod_cast (Nat.lcm_ne_zero _O _O));field_simp [i,(_P :(c:O)≠0),(_P :(b:O)≠0)];linarith
 have o:∑c∈S,∑b∈S,aP w c*aP w b/((Nat.lcm c b:ℕ):O) =∑m∈S,(Nat.totient m:O)*(∑r∈S.filter (m∣·),aP w r/(r:O))^2:=by
  trans ∑c∈S,∑b∈S,∑m∈S,if m∣c/\m∣b then (Nat.totient m:O)*(aP w c/(c:O))*(aP w b/(b:O))
   else 0
  ·refine dF rfl fun c l=>dF rfl fun b u=>?_
   rw[div_eq_mul_one_div,e c l b u,dP,dP];rw[<- f8];have q:S.filter (fun m=>m∣c/\m∣b)=(Nat.gcd c b).divisors:=by
    ext m;simp only[dB,fW,Nat.dvd_gcd_iff];have A:Nat.gcd c b≠0:=by simp only[S,aM,dB,dT]at l;exact (Nat.gcd_pos_of_pos_left b _O).ne'
    constructor
    ·rintro⟨_,h⟩;exact⟨h,A⟩
    ·rintro⟨h,_⟩;exact⟨aR l h.1,h⟩
   rw[q];exact dF rfl fun m _=>_R
  ·trans ∑c∈S,∑m∈S,∑b∈S,if m∣c/\m∣b then (Nat.totient m:O)*(aP w c/(c:O))*(aP w b/(b:O))
    else 0
   ·exact dF rfl fun c _=>hH
   ·rw[hH];refine dF rfl fun m _=>?_
    rw[sq,kJ,dP];rw[f8];refine dF rfl fun c _=>?_
    split_ifs with z
    ·rw[f8,dP];refine dF rfl fun b _=>?_
     simp only[z,dV];split_ifs <;> ring
    ·exact g0 fun b _=>by simp[z]
 rw[o]
 calc ∑m∈S,(Nat.totient m:O)*(∑r∈S.filter (m∣·),aP w r/(r:O))^2
     = ∑m∈S,(Nat.totient m:O)*(aO w m)^2:=dF rfl fun m y=>by rw[b4 y]
   _=∑m∈S,(1:O)/((Nat.totient m:O)*(aN w)^2):=by
       refine dF rfl fun m y=>?_
       simp only[aO,S,y,↓reduceIte];have B:=aY y;have j:(Nat.totient m:O)≠0:=(by simp only[S,aM,dB,dT]at y;exact_mod_cast (mw.mpr _O).ne');rw[ij,B,eP];field_simp [j,d.ne']
   _=(1/(aN w)^2)*aN w:=by dsimp only[aN,S];rw[dP];exact dF rfl fun _ _=>_R
   _=1/aN w:=by field_simp [d.ne']
set_option maxHeartbeats 800000 in
lemma b6 (X w:ℕ) (C:1<=w) :
 (aK X w:O)<=(X:O)/log ((w+1:ℕ):O)+(w:O)^2:=by
 let S:=aM w;have D:∀b∈(Icc 1 X).filter (fun b=>∀p ≤ w,p.Prime->¬ p∣b),(1:O)<=(∑r∈S.filter (·∣b),aP w r)^2:=by
  intro b P;simp only[dB,dT]at P;have u:S.filter (·∣b)={1}:=by
   ext r;simp only[S,aM,dB,dT,eg];constructor
   ·rintro⟨⟨⟨m,hrw⟩,_⟩,hrb⟩;by_contra N;obtain⟨p,T,K⟩:=jK N;exact P.2 p ((el _O K).trans hrw) T (K.trans hrb)
   ·rintro rfl;exact⟨⟨⟨eR,C⟩,lG⟩,one_dvd b⟩
  rw[u,jA,aZ C,jQ]
 have M:(aK X w:O) <=∑b∈Icc 1 X,(∑r∈S.filter (·∣b),aP w r)^2:=by
  unfold aK
  calc (((Icc 1 X).filter fun b=>∀p ≤ w,p.Prime->¬ p∣b).card:O)
      = ∑_b∈(Icc 1 X).filter (fun b=>∀p ≤ w,p.Prime->¬ p∣b),(1:O):=by simp
    _<=∑b∈(Icc 1 X).filter (fun b=>∀p ≤ w,p.Prime->¬ p∣b),(∑r∈S.filter (·∣b),aP w r)^2:=dG D
    _<=∑b∈Icc 1 X,(∑r∈S.filter (·∣b),aP w r)^2:=dC (fj _ _) fun _ _ _=>gR _
 have U:∑b∈Icc 1 X,(∑r∈S.filter (·∣b),aP w r)^2 =∑e∈S,∑c∈S,aP w e*aP w c*((X/Nat.lcm e c:ℕ):O):=by
  have E:∀b∈Icc 1 X,(∑r∈S.filter (·∣b),aP w r)^2 =∑e∈S,∑c∈S,if Nat.lcm e c∣b then aP w e*aP w c else 0:=by
   intro b _;rw[sq,kJ,f8];refine dF rfl fun e _=>?_
   split_ifs with M
   ·rw[f8];refine dF rfl fun c _=>?_
    simp only[Nat.lcm_dvd_iff,M,dV]
   ·symm;apply g0;intro c _;simp only[Nat.lcm_dvd_iff,M,false_and,↓reduceIte]
  rw[dF rfl E,hH];refine dF rfl fun e m=>?_
  rw[hH];refine dF rfl fun c q=>?_
  rw[<- f8,ex,e3,e8];congr 1;have d:0< Nat.lcm e c:=by simp only[S,aM,dB,dT]at m q;exact Nat.lcm_pos _O _O
  have v:((Icc 1 X).filter (Nat.lcm e c∣·)).card=X/Nat.lcm e c:=by
   have F:(Icc 1 X).filter (Nat.lcm e c∣·) =(Icc 1 (X/Nat.lcm e c)).image (fun k=>Nat.lcm e c*k):=by
    ext b;simp only[dB,dT,dW];constructor
    ·rintro⟨⟨hb1,hbX⟩,⟨k,rfl⟩⟩;refine⟨k,⟨?_,(dZ d).mpr _L⟩,rfl⟩;rcases eq_or_ne k 0 with rfl | hk0
     ·simp at hb1
     ·omega
    ·rintro⟨k,⟨hk1,hkX⟩,rfl⟩;have:=(dZ d).mp hkX;exact⟨⟨by nlinarith,_L⟩,ir _ _⟩
   rw[F,fs _ (fun a b h=>fR d h)];simp
  exact_mod_cast v
 have W:∑e∈S,∑c∈S,aP w e*aP w c*((X/Nat.lcm e c:ℕ):O) <=(X:O)/aN w+(w:O)^2:=by
  have y:∑e∈S,∑c∈S,aP w e*aP w c*((X/Nat.lcm e c:ℕ):O) -(X:O)*(∑e∈S,∑c∈S,aP w e*aP w c/((Nat.lcm e c:ℕ):O)) <=(w:O)^2:=by
   rw[dP];simp_rw [dP];rw[<- f2];have o:∑e∈S,(∑c∈S,aP w e*aP w c*((X/Nat.lcm e c:ℕ):O) -∑c∈S,(X:O)*(aP w e*aP w c/((Nat.lcm e c:ℕ):O))) <=∑_r1∈S,∑_r2∈S,(1:O):=by
    refine dG fun e m=>?_
    rw[<- f2];refine dG fun c q=>?_
    have z:=b3 C m;have A:=b3 C q;have d:(0:O)< (Nat.lcm e c:O):=(by simp only[S,aM,dB,dT]at m q;exact_mod_cast Nat.lcm_pos _O _O);have G : |((X/Nat.lcm e c:ℕ):O)-(X:O)/(Nat.lcm e c:O)|<=1:=by
     rw[ms];have Q:((X/Nat.lcm e c:ℕ):O)<=(X:O)/(Nat.lcm e c:O):=by rw[ma d];exact_mod_cast eD X (Nat.lcm e c)
     have R:(X:O)/(Nat.lcm e c:O)-1< ((X/Nat.lcm e c:ℕ):O):=by
      rw[sub_lt_iff_lt_add,mm d];have j:X< (X/Nat.lcm e c+1)*Nat.lcm e c:=by
       have:=iz (by exact_mod_cast d:0< Nat.lcm e c) (a:=X)
       linarith
      exact_mod_cast j
     constructor <;> linarith
    have H:aP w e*aP w c*((X/Nat.lcm e c:ℕ):O) -(X:O)*(aP w e*aP w c/(Nat.lcm e c:O)) =aP w e*aP w c*(((X/Nat.lcm e c:ℕ):O)-(X:O)/(Nat.lcm e c:O)):=_R;rw[H]
    calc aP w e*aP w c *
          (((X/Nat.lcm e c:ℕ):O)-(X:O)/(Nat.lcm e c:O))
        <= |aP w e*aP w c *(((X/Nat.lcm e c:ℕ):O)-(X:O)/(Nat.lcm e c:O))|:=le_abs_self _
      _=|aP w e| *|aP w c| *
          |((X/Nat.lcm e c:ℕ):O)-(X:O)/(Nat.lcm e c:O)|:=by
          rw[lA,lA]
      _<=1*1*1:=by refine en (en z A (abs_nonneg _) eO) G (abs_nonneg _) _N
      _=1:=by ring
   have l:(S.card:O)<=(w:O):=by have j:S.card<=w:=(by dsimp only[S,aM];simpa using er (fj Squarefree (Icc 1 w)));exact_mod_cast j
   calc _<=∑_r1∈S,∑_r2∈S,(1:O):=o
     _=(S.card:O)^2:=by simp[sq]
     _<=(w:O)^2:=m9 (dK _) l 2
  rw[b5 C]at y;have H:(X:O)*(1/aN w)=(X:O)/aN w:=_R;linarith
 have B:=aW w C;have i:0< log ((w+1:ℕ):O):=et (_M (_O :1< w+1));have J:(X:O)/aN w<=(X:O)/log ((w+1:ℕ):O):=dL (dK X) i B;linarith
set_option maxHeartbeats 800000 in
lemma b7 (X z:ℕ) (T:2<=z) (U:2*z<=X) :
 (aK X z:O)<=64*(X:O)/log (z:O):=by
 have c:0< log (z:O):=et (_M (_O :1< z));by_cases q:X< 64
 ·have G:(aK X z:O)<=(X:O):=by
   unfold aK;have C:((Icc 1 X).filter fun b=>∀p ≤ z,p.Prime->¬ p∣b).card<=X:=(by simpa using er (fj _ (Icc 1 X)));exact_mod_cast C
  have D:log (z:O)<=64:=(by have J:(z:O)<=64:=_M (_O :z<=64);have y:=eY (_P :(0:O)< (z:O));linarith);have K:(0:O)<=(X:O):=dK X;rw[ma c];nlinarith
 ·push Not at q
  let w:ℕ:=min z ⌊(X:O)^((1:O)/3)⌋₊;have d:(0:O)< X:=_P;have A:(4:O)<=(X:O)^((1:O)/3):=by
   have y:(4:O)^(3:O)<=(X:O):=by norm_num;exact_mod_cast q
   calc (4:O)=((4:O)^(3:O))^((1:O)/3):=by
         rw[<- gE _N];norm_num
     _<=(X:O)^((1:O)/3):=fx _P y _N
  have H:2<=w:=le_min T (g2 _L);have m:w<=z:=i7 _ _;have P:=b6 X w _O;have M:(aK X z:O)<=(aK X w:O):=mr.mpr (aL X m);have i:log (z:O)/3<=log ((w+1:ℕ):O):=by
   by_cases v:z<=⌊(X:O)^((1:O)/3)⌋₊
   ·have e:w=z:=li v;rw[e];have y:log (z:O)<=log ((z+1:ℕ):O):=dM _P (by push_cast;linarith);linarith
   ·push Not at v
    have e:w=⌊(X:O)^((1:O)/3)⌋₊:=jo v.le;rw[e];have y:(X:O)^((1:O)/3)< ((⌊(X:O)^((1:O)/3)⌋₊+1:ℕ):O):=(by push_cast;exact f6 _);have o:(z:O)<=(X:O):=_M (_O :z<=X);have Q:(z:O)^((1:O)/3)<=(X:O)^((1:O)/3):=fx _P o _N;have R:=dM _P (Q.trans y.le);rw[kR _P]at R;linarith
  have B:(w:O)^2<=(X:O)^((2:O)/3):=by
   have u:(w:O)<=(X:O)^((1:O)/3):=(mr.mpr (gw _ _)).trans (fC _P)
   calc (w:O)^2<=((X:O)^((1:O)/3))^2:=
         m9 (dK w) u 2
     _=(X:O)^((2:O)/3):=by rw[<- eK,<- gE d.le];norm_num
  have E:(X:O)^((2:O)/3)<=3*(X:O)/log (z:O):=by
   rw[ma c];have j:log (z:O)<=log (X:O):=dM _P (_M (_O :z<=X));have l:log (X:O)<=3*(X:O)^((1:O)/3):=by have h:=ig d.le (_N :(0:O)< 1/3);linarith
   calc (X:O)^((2:O)/3)*log (z:O)
       <= (X:O)^((2:O)/3)*(3*(X:O)^((1:O)/3)):=dA (j.trans l) _P
     _=3*((X:O)^((2:O)/3)*(X:O)^((1:O)/3)):=_R
     _=3*(X:O):=by rw[<- gF d];norm_num
  have F:(X:O)/log ((w+1:ℕ):O)<=3*(X:O)/log (z:O):=(by have y:=dL d.le (gN c (_N :(0:O)< 3)) i;have Q:(X:O)/(log (z:O)/3)=3*(X:O)/log (z:O):=_R;linarith);have N:6*(X:O)/log (z:O)<=64*(X:O)/log (z:O):=dI _L c.le;have S:3*(X:O)/log (z:O)+3*(X:O)/log (z:O) =6*(X:O)/log (z:O):=_R;linarith
def b8:ℕ:=max 2000000 ⌈exp 2000⌉₊
lemma b9:2000000<=b8:=eo _ _
lemma ba:(2000:O)<=log (b8:O):=by have b:exp 2000<=(b8:O):=(g6 _).trans (_M (ep 2000000 _));have c:=dM (ez 2000) b;rwa[iu]at c
def bb:ℕ:=∏p∈dv (b8-1),p
lemma bc:0< bb:=jf fun p b=>(dU b).pos
def bd (z:ℕ):Finset ℕ:=(Ico b8 z).filter Nat.Prime
def be (z:ℕ):O:=∏p∈bd z,(1-(1:O)/(p:O))
lemma bf (z:ℕ):0< be z:=by
 unfold be;refine jf fun p c=>?_
 have b:(2:O)<=p:=_M (dB.mp c).2.two_le;have:(1:O)/(p:O)<=1/2:=dX _N b;linarith
set_option maxHeartbeats 800000 in
lemma bg (z:ℕ) :
 be z=1 - ∑p∈bd z,(1:O)/(p:O)*be p:=by
 induction z with
 | zero=>
  have j:bd 0=∅:=(by simp[bd]);simp[be,j]
 | succ n ih=>
  by_cases c:b8<=n/\n.Prime
  ·have d:bd (n+1)=insert n (bd n):=by
    ext p;simp only[bd,dB,f3,ga];constructor
    ·rintro⟨⟨h1,h2⟩,hp⟩;by_cases i:p=n
     ·exact Or.inl i
     ·exact Or.inr ⟨⟨h1,_O⟩,hp⟩
    ·rintro (rfl | ⟨⟨h1,h2⟩,hp⟩)
     ·exact⟨⟨c.1,Nat.lt_succ_self p⟩,c.2⟩
     ·exact⟨⟨h1,_O⟩,hp⟩
   have b:n ∉ bd n:=(by simp[bd]);unfold be at ih ⊢;rw[d,fN b,i3 b];change (1-(1:O)/(n:O))*be n =1-((1:O)/(n:O)*be n+∑p∈bd n,(1:O)/(p:O)*be p);change be n=1 - ∑p∈bd n,(1:O)/(p:O)*be p at ih;linarith
  ·have e:bd (n+1)=bd n:=by
    ext p;simp only[bd,dB,f3];constructor
    ·rintro⟨⟨h1,h2⟩,hp⟩;have l:p≠n:=fun h=>c ⟨h ▸ h1,h ▸ hp⟩;exact⟨⟨h1,_O⟩,hp⟩
    ·rintro⟨⟨h1,h2⟩,hp⟩;exact⟨⟨h1,_O⟩,hp⟩
   unfold be at ih ⊢;rw[e];exact ih
def bh:ℕ->O->Finset ℕ->Prop
 | 0,_,S=>S=∅
 | n+1,D,S=>
  if h:S=∅ then True
  else
   let p:=S.max' (mf.mpr h)
   (p:O)^(201:ℕ)< D/\inBetaLower n (D/(p:O)) (S.erase p)
where
 inBetaLower:ℕ->O->Finset ℕ->Prop
 | 0,_,S=>S=∅
 | n+1,D,S=>
  if h:S=∅ then True
  else
   let p:=S.max' (mf.mpr h)
   bh n (D/(p:O)) (S.erase p)
def bi (D:O) (S:Finset ℕ):Prop:=bh S.card D S
def bj (D:O) (S:Finset ℕ):Prop:=bh.inBetaLower S.card D S
lemma bk (D:O):bi D ∅:=by simp[bi,bh]
lemma bl (D:O):bj D ∅:=by simp[bj,bh.inBetaLower]
lemma bm {D:O} {p:ℕ} {S:Finset ℕ} (c:∀q∈S,q< p) :
 bi D (insert p S)↔(p:O)^(201:ℕ)< D/\bj (D/(p:O)) S:=by
 have e:p ∉ S:=fun h=>kp p (c p h);have i:insert p S≠∅:=k4 p S;have d:(insert p S).card=S.card+1:=fE e;have b:(insert p S).max' (mf.mpr i)=p:=by
  apply i8
  ·rw[Finset.max'_le_iff];intro q l;rcases ga.mp l with rfl | hqS
   ·exact eR
   ·exact (c q hqS).le
  ·exact gK _ _ (ev p S)
 have j:(insert p S).erase p=S:=iQ e;unfold bi bj;rw[d,bh];simp only[i,↓reduceDIte,b,j]
lemma bn {D:O} {p:ℕ} {S:Finset ℕ} (c:∀q∈S,q< p) :
 bj D (insert p S)↔bi (D/(p:O)) S:=by
 have e:p ∉ S:=fun h=>kp p (c p h);have i:insert p S≠∅:=k4 p S;have d:(insert p S).card=S.card+1:=fE e;have b:(insert p S).max' (mf.mpr i)=p:=by
  apply i8
  ·rw[Finset.max'_le_iff];intro q l;rcases ga.mp l with rfl | hqS
   ·exact eR
   ·exact (c q hqS).le
  ·exact gK _ _ (ev p S)
 have j:(insert p S).erase p=S:=iQ e;unfold bi bj;rw[d,bh.inBetaLower];simp only[i,↓reduceDIte,b,j]
set_option maxHeartbeats 800000 in
lemma bo (T:Finset ℕ) :
 ∀D:O,(if T=∅ then (1:O) else 0) <=∑S∈T.powerset.filter (fun S=>bi D S),(-1:O)^S.card /\∑S∈T.powerset.filter (fun S=>bj D S),(-1:O)^S.card <=(if T=∅ then (1:O) else 0):=by
 induction d:T.card generalizing T with
 | zero=>
  intro D;have K:T=∅:=mA.mp d;subst K;simp[Finset.powerset_empty,Finset.filter_singleton,bk,bl]
 | succ c ih=>
  intro D;have B:T≠∅:=(by intro h;rw[h]at d;simp at d);let p:=T.max' (mf.mpr B);let T':=T.erase p;have m:p∈T:=kg T _;have m':p ∉ T':=io p T;have z:T=insert p T':=(gD m).symm;have d':T'.card=c:=(by rw[kV m,d];simp);have l':∀q∈T',q< p:=by intro q v;rw[gS]at v;exact ib (gK T q v.2) v.1
  have u:∀(P:Finset ℕ->Prop) [DecidablePred P],∑S∈T.powerset.filter P,(-1:O)^S.card =(∑S∈T'.powerset.filter P,(-1:O)^S.card) -(∑S∈T'.powerset.filter (fun S=>P (insert p S)),(-1:O)^S.card):=by
   intro P _;have C:T.powerset=T'.powerset∪T'.powerset.image (insert p):=(by rw[z,Finset.powerset_insert]);have A:Disjoint (T'.powerset.filter P) ((T'.powerset.image (insert p)).filter P):=by rw[eb];intro S w y;simp only[dB,eS,dW]at w y;rcases y.1 with⟨S',_,rfl⟩;exact m' (w.1 (ev p S'))
   rw[C,Finset.filter_union,jr A];have E:(T'.powerset.image (insert p)).filter P =(T'.powerset.filter (fun S=>P (insert p S))).image (insert p):=by
    ext S;simp only[dB,dW];constructor
    ·rintro⟨⟨S',j',rfl⟩,hP⟩;exact⟨S',⟨j',hP⟩,rfl⟩
    ·rintro⟨S',⟨j',hP⟩,rfl⟩;exact⟨⟨S',j',rfl⟩,hP⟩
   rw[E];have F:Set.InjOn (insert p) ((T'.powerset.filter (fun S=>P (insert p S)):Finset (Finset ℕ)):Set (Finset ℕ)):=by intro R w U y M;simp only[eB,dB,eS]at w y;have N:p ∉ R:=fun h=>m' (w.1 h);have Q:p ∉ U:=fun h=>m' (y.1 h);rw[<- iQ N,M,iQ Q]
   rw[fr (fun a W b X h=>F W X h)];have G:∑S∈T'.powerset.filter (fun S=>P (insert p S)),(-1:O)^(insert p S).card =- ∑S∈T'.powerset.filter (fun S=>P (insert p S)),(-1:O)^S.card:=by
    rw[<- iw];refine dF rfl fun S j=>?_
    simp only[dB,eS]at j;have H:p ∉ S:=fun h=>m' (j.1 h);rw[fE H,fc];ring
   rw[G];ring
  have o:=ih T' d' D;have J:=ih T' d' (D/(p:O));simp only[B,↓reduceIte];constructor
  ·rw[u (bi D)];have e:T'.powerset.filter (fun S=>bi D (insert p S)) =if (p:O)^(201:ℕ)< D then T'.powerset.filter (fun S=>bj (D/(p:O)) S) else ∅:=by
    split_ifs with hlt
    ·ext S;simp only[dB,eS];constructor
     ·rintro⟨j,hup⟩;have i:∀q∈S,q< p:=fun q v=>l' q (j v);exact⟨j,((bm i).mp hup).2⟩
     ·rintro⟨j,hlo⟩;have i:∀q∈S,q< p:=fun q v=>l' q (j v);exact⟨j,(bm i).mpr ⟨hlt,hlo⟩⟩
    ·ext S;simp only[dB,eS,fq,iC];rintro⟨j,hup⟩;have i:∀q∈S,q< p:=fun q v=>l' q (j v);exact hlt ((bm i).mp hup).1
   rw[e];split_ifs with hlt
   ·linarith[o.1,J.2]
   ·simp only[gG,kf];by_cases K':T'=∅
    ·rw[K']at o ⊢;simp only[↓reduceIte]at o;linarith[o.1]
    ·simp only[K',↓reduceIte]at o;linarith[o.1]
  ·rw[u (bj D)];have e:T'.powerset.filter (fun S=>bj D (insert p S)) =T'.powerset.filter (fun S=>bi (D/(p:O)) S):=by
    ext S;simp only[dB,eS];constructor
    ·rintro⟨j,hlo⟩;exact⟨j,(bn (fun q v=>l' q (j v))).mp hlo⟩
    ·rintro⟨j,hup⟩;exact⟨j,(bn (fun q v=>l' q (j v))).mpr hup⟩
   rw[e];linarith[o.2,J.1]
set_option maxHeartbeats 800000 in
lemma bp:∀(n:ℕ) (S:Finset ℕ) (D:O),S.card=n -> (∀p∈S,2<=p) -> (bi D S->1<=D->(∏p∈S,(p:O))<=D) /\(bj D S->(∀p∈S,(p:O)<=D)->1<=D->(∏p∈S,(p:O))<=D)
 | 0,S,D,c,_=>by
  have F:S=∅:=mA.mp c
  subst F
  simp
 | n+1,S,D,c,j=>by
  have B:S≠∅:=by intro h;rw[h]at c;simp at c
  let p:=S.max' (mf.mpr B);let S':=S.erase p;have i:p∈S:=kg S _;have i':p ∉ S':=io p S;have l:S=insert p S':=(gD i).symm;have c':S'.card=n:=(by rw[kV i,c];simp);have m':∀q∈S',q< p:=fun q z=>
   ib (gK S q (gS.mp z).2) (gS.mp z).1
  have G:(2:O)<=p:=_M (j p i);have b:(0:O)< p:=_L;have j':∀q∈S',2<=q:=fun q z=>j q (gS.mp z).2;have C:=bp n S' (D/(p:O)) c' j';constructor
  ·intro u _;rw[l]at u ⊢;have ⟨hlt,v⟩:=(bm m').mp u;have d:1<=D/(p:O):=by
    rw[js b];have w:(p:O)<=(p:O)^(201:ℕ):=mG _L _N;linarith
   have y:∀q∈S',(q:O)<=D/(p:O):=(by intro q z;rw[ma b];have H:(q:O)<=(p:O):=_M (m' q z).le;have J:(q:O)*(p:O)<=(p:O)^2:=_Q;have E:(p:O)^2<=(p:O)^(201:ℕ):=mg _L _N;linarith);have o:=C.2 v y d;rw[fN i'];have e:=dA o b.le;rw[mC _ b.ne']at e;exact e
  ·intro v A _;rw[l]at v ⊢;have u:=(bn m').mp v;have d:1<=D/(p:O):=(js b).mpr (A p i);have o:=C.1 u d;rw[fN i'];have e:=dA o b.le;rw[mC _ b.ne']at e;exact e
def bq (z:ℕ) (D:O):O:=by classical
 exact ∑S∈(bd z).powerset.filter (fun S=>bi D S),(-1:O)^S.card/(∏p∈S,(p:O))
def br (z:ℕ) (D:O):O:=by classical
 exact ∑S∈(bd z).powerset.filter (fun S=>bj D S),(-1:O)^S.card/(∏p∈S,(p:O))
def bs (z:ℕ) (D:O):O:=bq z D-be z
def bt (z:ℕ) (D:O):O:=be z-br z D
set_option maxHeartbeats 800000 in
lemma bu (z:ℕ) (D:O) :
 bq z D =1 - ∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*br p (D/(p:O)) /\
 br z D =1 - ∑p∈bd z,(1:O)/(p:O)*bq p (D/(p:O)):=by
 classical
 have i:∀(P:Finset ℕ->Prop) [DecidablePred P],P ∅ -> ∑S∈(bd z).powerset.filter P,(-1:O)^S.card/(∏q∈S,(q:O)) =1 - ∑p∈bd z,(1:O)/(p:O) *∑S'∈(bd p).powerset.filter (fun S'=>P (insert p S')),(-1:O)^S'.card/(∏q∈S',(q:O)):=by
  intro P _ X;have B:(∅ : Finset ℕ)∈(bd z).powerset.filter P:=(by simp[X]);rw[<- fJ _ _ B];simp only[card_empty,kQ,prod_empty,kO];have J:((bd z).powerset.filter P).erase ∅ =(bd z).biUnion fun p=>
    ((bd p).powerset.filter (fun S'=>P (insert p S'))).image (insert p):=by
   ext S;simp only[gS,dB,eS,g4,dW];constructor
   ·rintro⟨hSne,hSsub,hPS⟩;let p:=S.max' (mf.mpr hSne);have C:p∈S:=kg S _;refine⟨p,hSsub C,S.erase p,⟨?_,?_⟩,gD C⟩
    ·intro q d;rw[gS]at d;have E:=hSsub d.2;simp only[bd,dB,f3]at E ⊢;exact⟨⟨E.1.1,ib (gK S q d.2) d.1⟩,E.2⟩
    ·rwa[gD C]
   ·rintro⟨p,hpz,S',⟨h0sub,hPS'⟩,rfl⟩;refine⟨k4 p S',?_,hPS'⟩;intro q d;rcases ga.mp d with rfl | d'
    ·exact hpz
    ·have m:=h0sub d';simp only[bd,dB,f3]at hpz m ⊢;exact⟨⟨m.1.1,m.1.2.trans hpz.1.2⟩,m.2⟩
  have F:Set.PairwiseDisjoint (bd z:Set ℕ) (fun p=>
   ((bd p).powerset.filter (fun S'=>P (insert p S'))).image (insert p)):=by
   intro T _ U _ W;dsimp only[Function.onFun];rw[eb];intro S j l;simp only[dW,dB,eS]at j l;rcases j with⟨Q,⟨v,_⟩,rfl⟩;rcases l with⟨R,⟨w,_⟩,y⟩;have G:∀q∈Q,q< T:=fun q d=>
    (f3.mp (dB.mp (v d)).1).2
   have H:∀q∈R,q< U:=fun q d=>
    (f3.mp (dB.mp (w d)).1).2
   have o:T∈insert U R:=y ▸ ev T Q;have u:U∈insert T Q:=y.symm ▸ ev U R;rcases ga.mp o with h | h
   ·exact W h
   ·rcases ga.mp u with M | M
    ·exact W M.symm
    ·have:=H T h;have:=G U M;omega
  rw[J,kh F];have e:∀p∈bd z,∑S∈((bd p).powerset.filter (fun S'=>P (insert p S'))).image (insert p),(-1:O)^S.card/(∏q∈S,(q:O)) =-((1:O)/(p:O) *∑S'∈(bd p).powerset.filter (fun S'=>P (insert p S')),(-1:O)^S'.card/(∏q∈S',(q:O))):=by
   intro p _;have K:Set.InjOn (insert p) (((bd p).powerset.filter (fun S'=>P (insert p S')):Finset (Finset ℕ)):Set (Finset ℕ)):=by intro Q j R l y;simp only[eB,dB,eS]at j l;have Z:p ∉ Q:=fun h=>kp p (f3.mp (dB.mp (j.1 h)).1).2;have M:p ∉ R:=fun h=>kp p (f3.mp (dB.mp (l.1 h)).1).2;rw[<- iQ Z,y,iQ M]
   rw[fr (fun a ha b hb h=>K ha hb h),dP,<- iw];refine dF rfl fun S' hS'=>?_
   simp only[dB,eS]at hS';have A:p ∉ S':=fun h=>kp p (f3.mp (dB.mp (hS'.1 h)).1).2;rw[fE A,fN A,fc];ring
  rw[dF rfl e,iw];ring
 constructor
 ·unfold bq br;rw[i (bi D) (bk D)];congr 1;rw[f8];refine dF rfl fun p _=>?_
  split_ifs with hlt
  ·congr 1;refine dF ?_ (fun _ _=>rfl);ext S';simp only[dB,eS];constructor
   ·rintro⟨hsub,hup⟩;have c:∀q∈S',q< p:=fun q d=>
     (f3.mp (dB.mp (hsub d)).1).2
    exact⟨hsub,((bm c).mp hup).2⟩
   ·rintro⟨hsub,hlo⟩;have c:∀q∈S',q< p:=fun q d=>
     (f3.mp (dB.mp (hsub d)).1).2
    exact⟨hsub,(bm c).mpr ⟨hlt,hlo⟩⟩
  ·have N:(bd p).powerset.filter (fun S'=>bi D (insert p S'))=∅:=by
    ext S';simp only[dB,eS,fq,iC];rintro⟨hsub,hup⟩;have c:∀q∈S',q< p:=fun q d=>
     (f3.mp (dB.mp (hsub d)).1).2
    exact hlt ((bm c).mp hup).1
   rw[N,gG,hK]
 ·unfold br bq;rw[i (bj D) (bl D)];congr 1;refine dF rfl fun p _=>?_
  congr 1;refine dF ?_ (fun _ _=>rfl);ext S';simp only[dB,eS];constructor
  ·rintro⟨hsub,hlo⟩;have c:∀q∈S',q< p:=fun q d=>
    (f3.mp (dB.mp (hsub d)).1).2
   exact⟨hsub,(bn c).mp hlo⟩
  ·rintro⟨hsub,hup⟩;have c:∀q∈S',q< p:=fun q d=>
    (f3.mp (dB.mp (hsub d)).1).2
   exact⟨hsub,(bn c).mpr hup⟩
lemma bv (z:ℕ) (D:O) :
 bs z D =(∑p∈(bd z).filter (fun (p:ℕ)=>¬ (p:O)^(201:ℕ)< D),(1:O)/(p:O)*be p) +(∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*bt p (D/(p:O))) /\
 bt z D =∑p∈bd z,(1:O)/(p:O)*bs p (D/(p:O)):=by
 have d:=bu z D;have e:=bg z;constructor
 ·unfold bs bt;rw[d.1,e];have c:=(eh (bd z)
   (fun (p:ℕ)=>(p:O)^(201:ℕ)< D) (fun p=>(1:O)/(p:O)*be p)).symm
  have b:(∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*be p) -(∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*br p (D/(p:O))) =∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*(be p-br p (D/(p:O))):=(by rw[<- f2];exact dF rfl fun _ _=>_R);linarith
 ·unfold bt bs;rw[d.2,e];have b:(∑p∈bd z,(1:O)/(p:O)*bq p (D/(p:O))) -(∑p∈bd z,(1:O)/(p:O)*be p) =∑p∈bd z,(1:O)/(p:O)*(bq p (D/(p:O))-be p):=by
   rw[<- f2];exact dF rfl fun _ _=>_R
  linarith
set_option maxHeartbeats 800000 in
lemma bw {z:ℕ} {L:O} (hz:b8< z)
 (hL:2*log (z:O)<=L) :
 ∑p∈bd z,(1:O)/(p:O)*exp (-L/log (p:O)) <=(log (z:O)/L+1/50)*exp (-L/log (z:O)):=by
 let S:ℕ->O:=fun m=>∑p∈dv m,log (p:O)/(p:O);let g:O->O:=fun x=>exp (-L/log x)/log x;have b:0< log (z:O):=by
  have:(2000:O)<=log (b8:O):=ba
  have D:log (b8:O)<=log (z:O):=dM (by exact_mod_cast (by have:=b9;omega :0< b8)) (_M hz.le);linarith
 have e:0< L:=_L;have c:∀ {x y:O},(b8:O)<=x->x<=y->y<=(z:O)->g x<=g y:=by
  intro x y hx hd hy;have w:(0:O)< (b8:O):=(by have:=b9;positivity);have q:0< x:=w.trans_le hx;have X:0< y:=q.trans_le hd;have E:(2000:O)<=log x:=ba.trans (dM w hx);have hf:(2000:O)<=log y:=E.trans (dM q hd);have hA:log x<=log y:=dM q hd;have hg:log y<=log (z:O):=dM X hy;have G:0< g x:=gN (ez _) _L;have H:0< g y:=gN (ez _) _L;rw[<- kj G H];simp only[g];rw[gW (ez _).ne' _L,iu,gW (ez _).ne' _L,iu];have hl:log (log y)-log (log x) <=(log y-log x)/log x:=by rw[<- gW _L _L];have D:=eY (gN (_L :0< log y) (_L :0< log x));have h2:log y/log x-1=(log y-log x)/log x:=(by field_simp [(_L :log x≠0)]);linarith
  have hh:(log y-log x)/log x <=-L/log y-(-L/log x):=(by have ha : -L/log y-(-L/log x) =L*(log y-log x)/(log x*log y):=(by field_simp [(_L :log x≠0),(_L :log y≠0)];ring);rw[ha,mb _L _P];have D:log y<=L:=_L;have h2:0<=(log y-log x)*log x:=ek _L _L;nlinarith);linarith
 have l:∀m:ℕ,2<=m -> S m-S (m-1)=if m.Prime then log (m:O)/(m:O) else 0:=by
  intro m U;have hb:dv m=(if m.Prime then {m} else ∅)∪dv (m-1):=by
   ext p;simp only[e7,ff];split_ifs with hmp
   ·simp only[eg];constructor
    ·rintro⟨hple,hp⟩;by_cases hP:p=m;exact Or.inl hP;exact Or.inr ⟨by omega,hp⟩
    ·rintro (rfl | ⟨hple,hp⟩);exact⟨eR,hmp⟩;exact⟨by omega,hp⟩
   ·simp only[fq,false_or];constructor
    ·rintro⟨hple,hp⟩;exact⟨by have:p≠m:=fun h=>hmp (h ▸ hp);omega,hp⟩
    ·rintro⟨hple,hp⟩;exact⟨by omega,hp⟩
  have hc:Disjoint (if m.Prime then ({m}:Finset ℕ) else ∅) (dv (m-1)):=by
   split_ifs
   ·rw[j8,e7];intro h;omega
   ·exact jy _
  change (∑p∈dv m,log (p:O)/(p:O)) -(∑p∈dv (m-1),log (p:O)/(p:O))=_;rw[hb,jr hc,add_sub_cancel_right];split_ifs <;> simp
 have i:∑p∈bd z,(1:O)/(p:O)*exp (-L/log (p:O)) =∑m∈Icc b8 (z-1),(S m-S (m-1))*g (m:O):=by
  have D:∑m∈Icc b8 (z-1),(S m-S (m-1))*g (m:O) =∑m∈(Icc b8 (z-1)).filter Nat.Prime,(1:O)/(m:O)*exp (-L/log (m:O)):=by
   rw[f8];refine dF rfl fun m U=>?_
   rw[dT]at U;have hn:2<=m:=(by have:=b9;omega);rw[l m hn];split_ifs with hmp
   ·have J:log (m:O)≠0:=(et (_M hmp.one_lt)).ne';simp only[g];field_simp [J]
   ·simp
  rw[D];congr 1;ext p;simp only[bd,dB,f3,dT];exact⟨fun ⟨⟨D,h2⟩,hp⟩=>⟨⟨D,_O⟩,hp⟩,fun ⟨⟨D,h2⟩,hp⟩=>⟨⟨D,_O⟩,hp⟩⟩
 rw[i,ad S (fun m=>g (m:O)) b8 (z-1) (by have:=b9;omega) _O];have Z : (S (z-1)-log ((z-1:ℕ):O))*g ((z-1:ℕ):O) -(S (b8-1)-log ((b8-1:ℕ):O))*g (b8:O) +∑m∈Ico b8 (z-1),(S m-log (m:O))*(g (m:O)-g ((m+1:ℕ):O)) <=36*g (z:O):=by
  have u:∀m:ℕ,b8<=m->m<=z->0<=g (m:O):=(by intro m hN _;have hE:(2000:O)<=log (m:O):=ba.trans (dM (by have:=b9;positivity) (_M hN));exact ed (ez _).le _L);have K:g ((z-1:ℕ):O)<=g (z:O):=c (_M (_O :b8<=z-1)) (_M (_O :z-1<=z)) eR;have M:g (b8:O)<=g (z:O):=c eR (_M hz.le) eR;have ho:(S (z-1)-log ((z-1:ℕ):O))*g ((z-1:ℕ):O)<=9*g (z:O):=(by have hR:=(ms.mp (al (z-1) (by have:=b9;omega))).2;have hq:=u (z-1) _O _O;nlinarith);have hr : -(S (b8-1)-log ((b8-1:ℕ):O))*g (b8:O)<=9*g (z:O):=(by have hR:=(ms.mp (al (b8-1) (by have:=b9;omega))).1;have hq:=u b8 eR hz.le;nlinarith);have hQ:∑m∈Ico b8 (z-1),(S m-log (m:O))*(g (m:O)-g ((m+1:ℕ):O))<=18*g (z:O):=by
   calc ∑m∈Ico b8 (z-1),
           (S m-log (m:O))*(g (m:O)-g ((m+1:ℕ):O))
       <= ∑m∈Ico b8 (z-1),9*(g ((m+1:ℕ):O)-g (m:O)):=by
         refine dG fun m U=>?_
         rw[f3]at U;have hU:g (m:O)<=g ((m+1:ℕ):O):=c (_M U.1) (by push_cast;linarith) (_M (_O :m+1<=z));have hR:=(ms.mp (al m (by have:=b9;omega))).1;nlinarith
     _=9*(g ((z-1:ℕ):O)-g (b8:O)):=by
         rw[<- dP];congr 1;have N:b8<=z-1:=_O;generalize z-1=B at N;clear ho hr K M hz b hL e c l i u;induction B,N using fe with
         | base=>simp
         | succ k hk ih=>
           rw[iJ hk,ih];ring
     _<=18*g (z:O):=by have hq:=u b8 eR hz.le;linarith
  linarith
 have hF :
  log ((z-1:ℕ):O)*g ((z-1:ℕ):O) -
  log ((b8-1:ℕ):O)*g (b8:O) +
  ∑m∈Ico b8 (z-1),log (m:O)*(g (m:O)-g ((m+1:ℕ):O)) <=
  (log (z:O)/L)*exp (-L/log (z:O))+g (z:O):=by
  rw[<- ad (fun m=>log (m:O)) (fun m=>g (m:O))
   b8 (z-1) (by have:=b9;omega) _O]
  have P:∀m∈Icc b8 (z-1),(log (m:O)-log ((m-1:ℕ):O))*g (m:O) <=(log (z:O)/L) *(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O))) +(4/((m:O)^2))*g (z:O):=by
   intro m U;rw[dT]at U;have hB:2000000<=m:=gf b9 U.1;have d:(0:O)< m:=_M (_O :0< m);have Q:(0:O)< ((m-1:ℕ):O):=_M (_O :0< m-1);have F:((m-1:ℕ):O)=(m:O)-1:=(by rw[ei (_O :1<=m),eF]);have o:0< log (m:O):=et (_M (_O :1< m));have j:0< log ((m+1:ℕ):O):=et (_M (_O :1< m+1));have h8:log (m:O)<=log (z:O):=dM d (_M (_O :m<=z));have hC:log (m:O)-log ((m-1:ℕ):O)<=1/((m:O)-1):=by rw[<- gW d.ne' Q.ne',F];have h:=eY (gN d (_L :(0:O)< (m:O)-1));have ha:(m:O)/((m:O)-1)-1=1/((m:O)-1):=(by field_simp [(_L :(m:O)-1≠0)];ring);linarith
   have hD:1/((m:O)+1)<=log ((m+1:ℕ):O)-log (m:O):=(by rw[<- gW _P d.ne'];have h:=fl (gN (_P :(0:O)< ((m+1:ℕ):O)) d);rw[inv_div]at h;have ha:1-(m:O)/((m+1:ℕ):O)=1/((m:O)+1):=(by push_cast;field_simp [(_L :(m:O)+1≠0)];ring);linarith);have hS:1/((m:O)-1)-1/((m:O)+1)<=4/((m:O)^2):=(by have D:1/((m:O)-1)-1/((m:O)+1)=2/(((m:O)-1)*((m:O)+1)):=(by field_simp [(_L :(m:O)-1≠0),(_L :(m:O)+1≠0)];ring);rw[D,mb (by nlinarith) _P];have hn:(2:O)<=m:=_M (_O :2<=m);nlinarith);have h0:0<=g (m:O):=ed (ez _).le o.le;have h5:g (m:O)<=g (z:O):=c (_M U.1) (_M (_O :m<=z)) eR;have v:log ((m+1:ℕ):O)<=log (z:O):=dM _P (_M (_O :m+1<=z));have C : (log ((m+1:ℕ):O)-log (m:O))*g (m:O) <=(log (z:O)/L) *(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O))):=by
    let A:=-L/log (m:O);let B:=-L/log ((m+1:ℕ):O);have hI:B-A =L*(log ((m+1:ℕ):O)-log (m:O)) /(log (m:O)*log ((m+1:ℕ):O)):=(by simp only[A,B];field_simp [o.ne',j.ne'];ring);have D:exp A*(B-A)<=exp B-exp A:=(by have he:=fB (B-A);have R:=dA he (ez A).le;rw[<- gX]at R;have:A+(B-A)=B:=_R;rw[this]at R;linarith);have h2:(L/log (z:O))*((log ((m+1:ℕ):O)-log (m:O))*g (m:O)) <=exp A*(B-A):=by
     rw[hI];simp only[g,A];have W:0<=log ((m+1:ℕ):O)-log (m:O):=by
      have:=dM d (by push_cast;linarith :(m:O)<=((m+1:ℕ):O))
      linarith
     have hs:(L/log (z:O)) *((log ((m+1:ℕ):O)-log (m:O))*(exp (-L/log (m:O))/log (m:O))) =(L*(log ((m+1:ℕ):O)-log (m:O))*exp (-L/log (m:O))/log (m:O)) /log (z:O):=_R;have ht:exp (-L/log (m:O)) *(L*(log ((m+1:ℕ):O)-log (m:O)) /(log (m:O)*log ((m+1:ℕ):O))) =(L*(log ((m+1:ℕ):O)-log (m:O))*exp (-L/log (m:O))/log (m:O)) /log ((m+1:ℕ):O):=_R;rw[hs,ht];exact dL _P j v
    have h3:=h2.trans D;have R:=dA h3 (ed b.le e.le);have hu:(log (z:O)/L)*((L/log (z:O)) *((log ((m+1:ℕ):O)-log (m:O))*g (m:O))) =(log ((m+1:ℕ):O)-log (m:O))*g (m:O):=(by field_simp [e.ne',b.ne']);linarith
   calc (log (m:O)-log ((m-1:ℕ):O))*g (m:O)
       <= ((log ((m+1:ℕ):O)-log (m:O))+4/((m:O)^2))*g (m:O):=dE _L h0
     _=(log ((m+1:ℕ):O)-log (m:O))*g (m:O)+(4/((m:O)^2))*g (m:O):=_R
     _<=(log (z:O)/L) *(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O))) +(4/((m:O)^2))*g (z:O):=fd C (dA h5 _P)
  calc ∑m∈Icc b8 (z-1),(log (m:O)-log ((m-1:ℕ):O))*g (m:O)
      <= ∑m∈Icc b8 (z-1),((log (z:O)/L) *(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O))) +(4/((m:O)^2))*g (z:O)):=dG P
    _=(log (z:O)/L) *(∑m∈Icc b8 (z-1),(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O)))) +(∑m∈Icc b8 (z-1),4/((m:O)^2))*g (z:O):=by rw[fD,<- dP,<- jn]
    _<=(log (z:O)/L)*exp (-L/log (z:O))+g (z:O):=by
        have hv:∑m∈Icc b8 (z-1),(exp (-L/log ((m+1:ℕ):O))-exp (-L/log (m:O))) =exp (-L/log (z:O))-exp (-L/log (b8:O)):=by
          have N:b8<=z-1:=_O;have h9:z=(z-1)+1:=_O;conv_rhs=>rw[h9]
          generalize z-1=B at N
          clear Z P hz b hL e c l i h9;induction B,N using fe with
          | base=>simp[Finset.Icc_self]
          | succ k hk ih=>
            rw[iK _O,ih];ring
        rw[hv];have T:exp (-L/log (z:O))-exp (-L/log (b8:O)) <=exp (-L/log (z:O)):=_l (ez (-L/log (b8:O)))
        have h6:∑m∈Icc b8 (z-1),(4:O)/((m:O)^2)<=1:=by
          have hw:Icc b8 (z-1)⊆Ioc (b8-1) (z-1):=by intro m U;rw[dT]at U;rw[fw];have:=b9;omega
          calc ∑m∈Icc b8 (z-1),(4:O)/((m:O)^2)
              <= ∑m∈Ioc (b8-1) (z-1),(4:O)/((m:O)^2):=dC hw fun _ _ _=>_P
            _=4*∑m∈Ioc (b8-1) (z-1),(1:O)/((m:O)^2):=by rw[dP];exact dF rfl fun _ _=>_R
            _<=4*(1/((b8-1:ℕ):O)):=dA (ab (b8-1) (z-1) (by have:=b9;omega)) _N
            _<=1:=by have h4:(4:O)<=((b8-1:ℕ):O):=(by have:=b9;exact_mod_cast (_O :4<=b8-1));rw[iE,iy _L];exact h4
        have h7:0<=g (z:O):=ed (ez _).le b.le;have D:=dA T (ed b.le e.le);have h2:=dE h6 h7;linarith
 have hM:S (z-1)*g ((z-1:ℕ):O)-S (b8-1)*g (b8:O) +∑m∈Ico b8 (z-1),S m*(g (m:O)-g ((m+1:ℕ):O)) =(log ((z-1:ℕ):O)*g ((z-1:ℕ):O) -log ((b8-1:ℕ):O)*g (b8:O) +∑m∈Ico b8 (z-1),log (m:O)*(g (m:O)-g ((m+1:ℕ):O))) +((S (z-1)-log ((z-1:ℕ):O))*g ((z-1:ℕ):O) -(S (b8-1)-log ((b8-1:ℕ):O))*g (b8:O) +∑m∈Ico b8 (z-1),(S m-log (m:O))*(g (m:O)-g ((m+1:ℕ):O))):=by have hT:(∑m∈Ico b8 (z-1),log (m:O)*(g (m:O)-g ((m+1:ℕ):O))) +(∑m∈Ico b8 (z-1),(S m-log (m:O))*(g (m:O)-g ((m+1:ℕ):O))) =∑m∈Ico b8 (z-1),S m*(g (m:O)-g ((m+1:ℕ):O)):=(by rw[<- fD];exact dF rfl fun _ _=>_R);linarith
 have hj:(2000:O)<=log (z:O):=ba.trans (dM (by have:=b9;positivity) (_M hz.le));have hV:37*g (z:O)<=(1/50:O)*exp (-L/log (z:O)):=by simp only[g];rw[gl,mc b];have:(0:O)< exp (-L/log (z:O)):=ez _;nlinarith
 linarith
set_option maxHeartbeats 800000 in
lemma bx :
 ∃A:O,0< A/\∀(z:ℕ) (D:O),b8<=z -> (4*(z:O)<=D -> bs z D<=A*exp (-log D/log (z:O))/log D) /\((z:O)^(200:ℕ)<=D -> bt z D<=A*exp (-log D/log (z:O))/log D):=by
 let i:=∏p∈dv (b8-1),(1-(1:O)/(p:O));have h4:0< i:=by
  refine jf fun p d=>?_
  have hv:(2:O)<=p:=_M (dU d).two_le;have:(1:O)/(p:O)<=1/2:=dX _N hv;linarith
 let U:O:=2*exp 36/i;have h5:0< U:=_P;have hm:∀w:ℕ,b8<=w->be w<=U/log (w:O):=by
  intro w hw;have Hm:3<=w:=(by have:=b9;omega);have hn:∏p∈dv (w-1),(1-(1:O)/(p:O))=i*be w:=by
   have hx:Disjoint (dv (b8-1)) (bd w):=(by rw[eb];intro p Hk hv;rw[e7]at Hk;simp only[bd,dB,f3]at hv;have:=b9;omega);have ho:dv (b8-1)∪bd w=dv (w-1):=by
    ext p;simp only[ff,e7,bd,dB,f3];have:=b9;constructor
    ·rintro (⟨q,d⟩ | ⟨⟨q,h2⟩,d⟩) <;> exact⟨by omega,d⟩
    ·rintro⟨q,d⟩;by_cases hS:p< b8
     ·exact Or.inl ⟨by omega,d⟩
     ·exact Or.inr ⟨⟨by omega,_O⟩,d⟩
   rw[<- ho,kD hx];rfl
  have hy:3<=w-1:=(by have:=b9;omega);have H9:=(aq (w-1) hy).2;rw[hn]at H9;have hA:log (w:O)/2<=log ((w-1:ℕ):O):=(by have q:(w:O)<=((w-1:ℕ):O)^2:=(by have Hn:2<=w:=(by have:=b9;omega);have hB:((w-1:ℕ):O)=(w:O)-1:=(by rw[ei _O,eF]);rw[hB];have hZ:(4:O)<=(w:O):=(by exact_mod_cast (by have:=b9;omega :4<=w));nlinarith);have h2:=dM _P q;rw[fm]at h2;push_cast at h2;linarith);have hU:0< log (w:O):=et (_M (_O :1< w));have q:i*be w<=2*exp 36/log (w:O):=(by have h6:=dL (ez 36).le _L hA;have H0:exp 36/(log (w:O)/2)=2*exp 36/log (w:O):=_R;linarith);have h3:U/log (w:O)=(2*exp 36/log (w:O))/i:=(by simp only[U];ring);rw[h3,ma h4,e8];exact q
 let A:O:=2*U*201*exp 201;refine⟨A,by positivity,?_⟩
 intro z;induction z using Nat.strong_induction_on with
 | h z ih=>
  intro D hz;have H7:2000000<=z:=gf b9 hz;have hV:(2000:O)<=log (z:O):=ba.trans (dM (by have:=b9;positivity) (_M hz));have P:0< log (z:O):=_L;by_cases hT:z=b8
  ·subst hT;have y:bd b8=∅:=(by simp[bd]);have u:=bv b8 D;rw[y]at u;simp only[Finset.filter_empty,gG,i0]at u;rw[u.1,u.2];constructor
   ·intro hD;have hC:0< log D:=et (by
     have:(4:O)<=(b8:O):=by have:=b9;exact_mod_cast (_O :4<=b8)
     linarith)
    positivity
   ·intro hD;have hC:0< log D:=et (by
     have q:(2:O)<=(b8:O):=(by have:=b9;exact_mod_cast (_O :2<=b8));have h2:(2:O)<=(b8:O)^(200:ℕ):=mG _L _N |> gf q;linarith)
    positivity
  ·have Ha:b8< z:=(by omega);have u:=bv z D;have B:∀(w:ℕ),b8<=w->w<=z -> (∀p∈bd w,(log D/2<=log (D/(p:O))) /\(0< log (D/(p:O)))) -> (w=b8 ∨ 200*log (w:O)<=log D) -> ∀(E:ℕ->O->O),(∀p∈bd w,E p (D/(p:O))<=A*exp (-log (D/(p:O))/log (p:O))/log (D/(p:O))) -> 0< log D -> ∑p∈bd w,(1:O)/(p:O)*E p (D/(p:O)) <=(A/2)*exp (-log D/log (w:O))/log D:=by
    intro w hw Hs j o E hE b;by_cases hl:w=b8
    ·subst hl;have y:bd b8=∅:=(by simp[bd]);rw[y,gG];have:0< log (b8:O):=_l ba;positivity
    ·have h7:b8< w:=(by omega);have h8:200*log (w:O)<=log D:=(by rcases o with h | h;exact absurd h hl;exact h);have hW:(2000:O)<=log (w:O):=ba.trans (dM (by have:=b9;positivity) (_M hw));have v:0< log (w:O):=_L;have q:∑p∈bd w,(1:O)/(p:O)*E p (D/(p:O)) <=(2*A*exp 1/log D) *∑p∈bd w,(1:O)/(p:O)*exp (-log D/log (p:O)):=by
      rw[dP];refine dG fun p d=>?_
      have G:=d;simp only[bd,dB,f3]at G;have c:(0:O)< (p:O):=_M G.2.pos;have Q:0< log (p:O):=et (_M G.2.one_lt);have h9:=j p d;have H1:D≠0:=(by intro h0;rw[h0,log_zero]at b;exact kp 0 b);have W:log (D/(p:O))=log D-log (p:O):=gW H1 c.ne';have ha:exp (-log (D/(p:O))/log (p:O)) =exp 1*exp (-log D/log (p:O)):=(by rw[W,<- gX];congr 1;field_simp [Q.ne'];ring);have hb:1/log (D/(p:O))<=2/log D:=(by rw[mb h9.2 b];linarith[h9.1]);have hc:=hE p d;rw[ha]at hc;have hq:E p (D/(p:O)) <=(2*A*exp 1/log D)*exp (-log D/log (p:O)):=by
       calc E p (D/(p:O))
           <= A*(exp 1*exp (-log D/log (p:O)))/log (D/(p:O)):=hc
         _=A*(exp 1*exp (-log D/log (p:O)))*(1/log (D/(p:O))):=_R
         _<=A*(exp 1*exp (-log D/log (p:O)))*(2/log D):=dA hb _P
         _=(2*A*exp 1/log D)*exp (-log D/log (p:O)):=_R
      calc (1:O)/(p:O)*E p (D/(p:O))
          <= (1:O)/(p:O) *((2*A*exp 1/log D)*exp (-log D/log (p:O))):=dA hq _P
        _=(2*A*exp 1/log D) *((1:O)/(p:O)*exp (-log D/log (p:O))):=_R
     have H2:=bw (L:=log D) h7 _L;have hF:log (w:O)/log D+1/50<=1/40:=(by have h6:log (w:O)/log D<=1/200:=(by rw[mb b _N];linarith);linarith);have Hb:exp 1< 3:=_l gT;have Hc:2*exp 1*(1/40:O)<=1/2:=_L
     calc ∑p∈bd w,(1:O)/(p:O)*E p (D/(p:O))
         <= (2*A*exp 1/log D) *((log (w:O)/log D+1/50)*exp (-log D/log (w:O))):=q.trans (dA H2 _P)
       _<=(2*A*exp 1/log D) *((1/40:O)*exp (-log D/log (w:O))):=by refine dA (dE hF (ez _).le) _P
       _=(2*exp 1*(1/40:O))*(A*exp (-log D/log (w:O))/log D):=_R
       _<=(1/2:O)*(A*exp (-log D/log (w:O))/log D):=dE Hc _P
       _=(A/2)*exp (-log D/log (w:O))/log D:=_R
   constructor
   ·
    intro hD;have l:0< D:=by
     have:(4:O)<=4*(z:O):=_M (_O :4<=4*z)
     linarith
    have hX:log (z:O)<=log D:=dM _P _L;have b:0< log D:=_L;rw[u.1];let r:O:=D^((1:O)/201);let w:ℕ:=max b8 (min z ⌈r⌉₊);have hd:b8<=w:=eo _ _;have m:w<=z:=kC hz (i7 _ _);have R:(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D)⊆bd w:=by
     intro p d;simp only[bd,dB,f3]at d ⊢;refine⟨⟨d.1.1.1,?_⟩,d.1.2⟩;have H3:(p:O)< r:=by
      have q:(p:O)^(201:O)< D:=by simpa using d.2
      calc (p:O)=((p:O)^(201:O))^((1:O)/201):=by
            rw[<- gE _P];norm_num
        _< D^((1:O)/201):=Real.rpow_lt_rpow _P q _N
     have H:p< ⌈r⌉₊:=(by by_contra H6;push Not at H6;have:r<=(p:O):=(g6 r).trans (_M H6);linarith);have S:p< min z ⌈r⌉₊:=lt_min d.1.1.2 H;exact e9 S (ep _ _)
    have Hd:∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*bt p (D/(p:O)) <=(A/2)*exp (-log D/log (z:O))/log D:=by
     let E2:ℕ->O->O:=fun p t=>if (p:O)^(201:ℕ)< D then bt p t else 0;have hI:∑p∈(bd z).filter (fun (p:ℕ)=>(p:O)^(201:ℕ)< D),(1:O)/(p:O)*bt p (D/(p:O)) =∑p∈bd w,(1:O)/(p:O)*E2 p (D/(p:O)):=by
      rw[<- Finset.sum_subset R]
      ·refine dF rfl fun p d=>?_
       simp only[E2,(dB.mp d).2,↓reduceIte]
      ·intro p hu hR;have H4:¬ (p:O)^(201:ℕ)< D:=by
        intro hS;apply hR;simp only[bd,dB,f3]at hu ⊢;exact⟨⟨⟨hu.1.1,e9 hu.1.2 m⟩,hu.2⟩,hS⟩
       simp[E2,H4]
     rw[hI];have o:w=b8 ∨ 200*log (w:O)<=log D:=by
      by_cases q:w=b8
      ·exact Or.inl q
      ·right
       have h7:b8< w:=_O;have J:w<=⌈r⌉₊:=by
        have:w=min z ⌈r⌉₊:=jU _O
        rw[this];exact gw _ _
       have hL:(w:O)<=r+1:=(by have He:(w:O)<=(⌈r⌉₊ : O):=_M J;have Hf:=jm (_P :0<=r);linarith);have hM:(1000000:O)<=r:=by
        have:(2000000:O)<=(w:O):=by have:=b9;exact_mod_cast (_O :2000000<=w)
        linarith
       have H5:log (r+1)<=log r+1/1000000:=(by have He:log (r+1)-log r=log ((r+1)/r):=(gW _L _L).symm;have Hf:=eY (gN (_L :0< r+1) (_L :0< r));have Ho:(r+1)/r-1=1/r:=(by field_simp [(_L :r≠0)];ring);have Hp:1/r<=1/1000000:=dX _N hM;linarith);have H8:log r=log D/201:=(by simp only[r,kR l];ring);have hY:log (w:O)<=log (r+1):=dM (by have:=b9;positivity) hL;linarith
     have j:∀p∈bd w,log D/2<=log (D/(p:O))/\0< log (D/(p:O)):=by
      intro p d;simp only[bd,dB,f3]at d;have c:(0:O)< p:=_M d.2.pos;rw[gW l.ne' c.ne'];rcases o with hweq | h8
      ·exfalso;rw[hweq]at d;omega
      ·have X:log (p:O)<=log (w:O):=dM c (_M d.1.2.le);constructor <;> linarith
     have Hg:∀p∈bd w,E2 p (D/(p:O)) <=A*exp (-log (D/(p:O))/log (p:O))/log (D/(p:O)):=by
      intro p d;simp only[E2];split_ifs with hS
      ·simp only[bd,dB,f3]at d;have K:p< z:=e9 d.1.2 m;have c:(0:O)< p:=_M d.2.pos;have h9:(p:O)^(200:ℕ)<=D/(p:O):=by
        rw[ma c];have H0:(p:O)^(200:ℕ)*(p:O)=(p:O)^(201:ℕ):=_R;linarith
       exact (ih p K (D/(p:O)) d.1.1).2 h9
      ·have h9:=(j p d).2;positivity
     have he:=B w hd m j o E2 Hg b;have v:0< log (w:O):=(by have hZ:(b8:O)<=(w:O):=_M hd;have:=ba.trans (dM (by have:=b9;positivity) hZ);linarith);have M:log (w:O)<=log (z:O):=dM (by have:=b9;positivity) (_M m);have T:exp (-log D/log (w:O)) <=exp (-log D/log (z:O)):=by
      apply me.mpr
      rw[ly,ly,neg_le_neg_iff];exact dL b.le v M
     exact he.trans (dI
      (dA T _P) b.le)
    have Hh:∑p∈(bd z).filter (fun (p:ℕ)=>¬ (p:O)^(201:ℕ)< D),(1:O)/(p:O)*be p <=(A/2)*exp (-log D/log (z:O))/log D:=by
     by_cases y:((bd z).filter (fun (p:ℕ)=>¬ (p:O)^(201:ℕ)< D))=∅
     ·rw[y,gG];positivity
     ·
      let F:=(bd z).filter (fun (p:ℕ)=>¬ (p:O)^(201:ℕ)< D);let N:=F.min' (mf.mpr y);have hf:N∈F:=Finset.min'_mem F _;have e:=hf;simp only[F,bd,dB,f3]at e;have Z:D<=(N:O)^(201:ℕ):=not_lt.mp e.2;have C:N< z:=e.1.1.2;have hg:log D/201<=log (N:O):=(by have q:=dM l Z;rw[fm]at q;push_cast at q;linarith);have Hi:log D/log (z:O)<=201:=(by have q:log (N:O)<=log (z:O):=dM (_M e.1.2.pos) (_M C.le);rw[mc P];linarith);have hr:F⊆bd z \ bd N:=(by intro p d;have Hl:N<=p:=Finset.min'_le F p d;simp only[F,bd,dB,gj,f3]at d ⊢;exact⟨d.1,fun h=>by omega⟩);have hh:bd N⊆bd z:=(by intro p d;simp only[bd,dB,f3]at d ⊢;exact⟨⟨d.1.1,d.1.2.trans C⟩,d.2⟩);have hj:∑p∈bd z \ bd N,(1:O)/(p:O)*be p =be N-be z:=(by rw[iI hh];have q:=bg z;have h2:=bg N;linarith);have hs:∑p∈F,(1:O)/(p:O)*be p<=be N:=by
       calc ∑p∈F,(1:O)/(p:O)*be p
           <= ∑p∈bd z \ bd N,(1:O)/(p:O)*be p:=dC hr fun _ _ _=>
               ek _P (bf _).le
         _=be N-be z:=hj
         _<=be N:=by linarith[bf z]
      have ht:=hm N e.1.1.1;have h6:U/log (N:O)<=201*U/log D:=(by have q:=dL h5.le (gN b (_N :(0:O)< 201)) hg;have H0:U/(log D/201)=201*U/log D:=_R;linarith);have hk:(1:O)<=exp 201*exp (-log D/log (z:O)):=by
       rw[<- gX];have:0<=201+-log D/log (z:O):=by rw[ly];linarith
       exact Real.one_le_exp this
      have hN:A/2=201*U*exp 201:=by simp only[A];ring
      calc ∑p∈F,(1:O)/(p:O)*be p
          <= 201*U/log D:=hs.trans (ht.trans h6)
        _=(201*U/log D)*1:=(fv _).symm
        _<=(201*U/log D)*(exp 201*exp (-log D/log (z:O))):=dA hk _P
        _=(A/2)*exp (-log D/log (z:O))/log D:=by rw[hN];ring
    have hP:(A/2)*exp (-log D/log (z:O))/log D +(A/2)*exp (-log D/log (z:O))/log D =A*exp (-log D/log (z:O))/log D:=_R;linarith
   ·
    intro hD;have l:0< D:=by
     have:(0:O)< (z:O)^(200:ℕ):=_P
     linarith
    have h8:200*log (z:O)<=log D:=(by have q:=dM _P hD;rw[fm]at q;exact q);have b:0< log D:=_L;rw[u.2];have j:∀p∈bd z,log D/2<=log (D/(p:O))/\0< log (D/(p:O)):=(by intro p d;simp only[bd,dB,f3]at d;have c:(0:O)< p:=_M d.2.pos;rw[gW l.ne' c.ne'];have X:log (p:O)<=log (z:O):=dM c (_M d.1.2.le);constructor <;> linarith);have hQ:∀p∈bd z,bs p (D/(p:O)) <=A*exp (-log (D/(p:O))/log (p:O))/log (D/(p:O)):=by
     intro p d;simp only[bd,dB,f3]at d;have c:(0:O)< p:=_M d.2.pos;have Hj:4*(p:O)<=D/(p:O):=by
      rw[ma c];have K:(p:O)<=(z:O):=_M d.1.2.le;have Hq:(4:O)<=(z:O):=_M (_O :4<=z);have q:4*(p:O)*(p:O)<=(z:O)^(3:ℕ):=by
       calc 4*(p:O)*(p:O)<=(z:O)*(z:O)*(z:O):=by nlinarith
         _=(z:O)^(3:ℕ):=_R
      have h2:(z:O)^(3:ℕ)<=(z:O)^(200:ℕ):=mg _L _N;linarith
     exact (ih p d.1.2 (D/(p:O)) d.1.1).1 Hj
    have he:=B z hz eR j (Or.inr h8) bs hQ b;have Hr:0<=(A/2)*exp (-log D/log (z:O))/log D:=_P;have hP:(A/2)*exp (-log D/log (z:O))/log D +(A/2)*exp (-log D/log (z:O))/log D =A*exp (-log D/log (z:O))/log D:=_R;linarith
set_option maxHeartbeats 800000 in
lemma bz :
 ∃v:O,0< v/\∀X z:ℕ,2<=z->4*z<=X -> v*(X:O)/log (z:O)<=(aK X z:O):=by
 obtain⟨A,HK,H6⟩:=bx;let j:ℕ:=max 200 (⌈2*A*exp 38⌉₊+10);have hP:200<=j:=eo _ _;have hA:A*exp (-(j:O))<=(j:O)/(2*exp 38):=by have l:2*A*exp 38<=(j:O):=(by have hc:=g6 (2*A*exp 38);have : ⌈2*A*exp 38⌉₊<=j:=gf (Nat.le_add_right _ 10) (ep _ _);have hR:(⌈2*A*exp 38⌉₊ : O)<=(j:O):=_M this;linarith);have h2:(1:O)<=exp (j:O):=Real.one_le_exp (dK j);rw[lz,mul_inv_le_iff₀ (ez _)];have h3:A<=(j:O)/(2*exp 38):=(by rw[ma _P];linarith);have h4:(j:O)/(2*exp 38)*1<=(j:O)/(2*exp 38)*exp (j:O):=dA h2 _P;linarith
 let m:ℕ:=2*j+⌈log (16*(bb:O)*exp 38)/log 2⌉₊+10;let c1:O:=log 2/(4*(bb:O));let c2:O:=1/(80*(m:O));let c3:O:=1/(8*(bb:O)*exp 38);let v:O:=min c1 (min c2 c3);have hQ:0< v:=by have v1:(0:O)< (bb:O):=_M bc;have hB:0< log 2:=_l a3;have v2:(0:O)< (m:O):=_M (_O :0< m);have HL:0< c1:=_P;have HM:0< c2:=_P;have HN:0< c3:=_P;exact lt_min HL (lt_min HM HN)
 refine⟨v,hQ,?_⟩
 intro X z hz HV;have o:0< log (z:O):=et (_M (_O :1< z));have H:log 2<=log (z:O):=dM _N (_M hz);have hC:(0:O)< (bb:O):=_M bc;by_cases hy:z< b8
 ·
  have Z:(range ((X-1)/bb+1)).image (fun k=>k*bb+1) ⊆ (Icc 1 X).filter (fun b=>∀p ≤ z,p.Prime->¬ p∣b):=by
   intro b hb;simp only[dW,dN]at hb;rcases hb with⟨k,hk,rfl⟩;simp only[dB,dT];have Ha:k<=(X-1)/bb:=_O;have Hs:k*bb<=X-1:=(eE bb Ha).trans (eD (X-1) bb);refine⟨⟨by omega,_O⟩,?_⟩
   intro p Ho w U;have G:p∈dv (b8-1):=e7.mpr ⟨by omega,w⟩
   have u:p∣bb:=ji id G;have hl:p∣1:=(Nat.dvd_add_right (dvd_mul_of_dvd_right u k)).mp U;exact w.not_dvd_one hl
  have hD:Function.Injective (fun k=>k*bb+1):=(by intro k1 k2 h;exact ii bc (Nat.add_right_cancel h));have hm:((X-1)/bb+1:ℕ)<=aK X z:=(by unfold aK;have l:=er Z;rw[fs _ hD,fy]at l;exact l);have hn:(X:O)/(4*(bb:O))<=((X-1)/bb+1:ℕ):=(by have Ht:X<=((X-1)/bb+1)*bb:=(by have l:=iz bc (a:=X-1);have h2:((X-1)/bb+1)*bb=(X-1)/bb*bb+bb:=_R;omega);have hR:(X:O)<=(((X-1)/bb+1:ℕ):O)*(bb:O):=_M Ht;rw[mc _P];nlinarith);have J:v<=c1:=i7 _ _;have hU:c1*(X:O)/log (z:O)<=(X:O)/(4*(bb:O)):=by simp only[c1];have h5:log 2/(4*(bb:O))*(X:O)/log (z:O) =(log 2/log (z:O))*((X:O)/(4*(bb:O))):=_R;rw[h5];have hE:log 2/log (z:O)<=1:=(iy o).mpr H;have HO:0<=(X:O)/(4*(bb:O)):=_P;nlinarith
  calc v*(X:O)/log (z:O)
      <= c1*(X:O)/log (z:O):=dI (dE J (dK X)) o.le
    _<=(X:O)/(4*(bb:O)):=hU
    _<=(((X-1)/bb+1:ℕ):O):=hn
    _<=(aK X z:O):=mr.mpr hm
 ·push Not at hy
  by_cases W:(X:O)< (z:O)^m
  ·
   have hV:(2000000:O)<=(X:O)/2:=by
    have:=b9
    have:(4000000:O)<=(X:O):=_M (_O :4000000<=X)
    linarith
   have h6:=ag ((X:O)/2) hV;have Hu:2*((X:O)/2)=(X:O):=_R;rw[Hu,jz]at h6;have Z:(Ioc ⌊(X:O)/2⌋₊ X).filter Nat.Prime ⊆ (Icc 1 X).filter (fun b=>∀p ≤ z,p.Prime->¬ p∣b):=by
    intro q hq;simp only[dB,fw,dT]at hq ⊢;refine⟨⟨hq.2.one_le,hq.1.2⟩,?_⟩;intro p Ho w HW;have Hb:p=q:=(eI w hq.2).mp HW;have HP:(X:O)/2< (q:O):=by have l : ⌊(X:O)/2⌋₊+1<=q:=hq.1.1;have h2:=f6 ((X:O)/2);have h3:((⌊(X:O)/2⌋₊ : O)+1)<=(q:O):=_M l;linarith
    have HX:4*(z:O)<=(X:O):=_M HV;have Hv:(p:O)<=(z:O):=_M Ho;rw[Hb]at Hv;linarith
   have C:(((Ioc ⌊(X:O)/2⌋₊ X).filter Nat.Prime).card:O)<=(aK X z:O):=mr.mpr (er Z);have Hp:log (X:O)<=(m:O)*log (z:O):=(by have hW:(0:O)< (X:O):=(by have:=b9;exact_mod_cast (_O :0< X));have l:=dM hW W.le;rwa[fm]at l);have Hc:0< log (X:O):=et (by have:=b9;exact_mod_cast (_O :1< X));have J:v<=c2:=(gw _ _).trans (i7 _ _)
   calc v*(X:O)/log (z:O)
       <= c2*(X:O)/log (z:O):=dI (dE J (dK X)) o.le
     _=((X:O)/2)/(40*((m:O)*log (z:O))):=by simp only[c2];ring
     _<=((X:O)/2)/(40*log (X:O)):=dL _P _P _L
     _<=((X:O)/2)/(20*log (X:O)):=dL _P _P _L
     _<=(((Ioc ⌊(X:O)/2⌋₊ X).filter Nat.Prime).card:O):=h6
     _<=(aK X z:O):=C
  ·
   push Not at W
   classical
   let e:ℕ:=z+1;let D:O:=(e:O)^j;have hX:b8<=e:=_O;have E:0< log (e:O):=et (by have:=b9;exact_mod_cast (_O :1< e));have ho:(e:O)^(200:ℕ)<=D:=mg (by have:=b9;exact_mod_cast (_O :1<=e)) hP;have H7:=(H6 e D hX).2 ho;have hr:log D=(j:O)*log (e:O):=fm _ _;have h7:bt e D<=1/(2*exp 38*log (e:O)):=(by rw[hr]at H7;have hE : -((j:O)*log (e:O))/log (e:O)=-(j:O):=(by field_simp [E.ne']);rw[hE]at H7;have l:A*exp (-(j:O))/((j:O)*log (e:O)) <=((j:O)/(2*exp 38))/((j:O)*log (e:O)):=dI hA _P;have h2:((j:O)/(2*exp 38))/((j:O)*log (e:O)) =1/(2*exp 38*log (e:O)):=(by field_simp [(_P :(j:O)≠0),(ez 38).ne',E.ne']);linarith);have HJ:1/(exp 38*log (e:O))<=be e:=by
    have Z:bd e⊆dv z:=(by intro p w;simp only[bd,dB,f3,e7]at w ⊢;exact⟨by omega,w.2⟩);have hs:∏p∈dv z,(1-(1:O)/(p:O))<=be e:=by
     unfold be;rw[<- Finset.prod_sdiff Z];have HY:∏p∈dv z \ bd e,(1-(1:O)/(p:O))<=1:=by
      refine Finset.prod_le_one (fun p w=>?_) (fun p w=>?_)
      ·have HQ:(2:O)<=p:=by
        exact_mod_cast (dU (gj.mp w).1).two_le
       have:(1:O)/(p:O)<=1/2:=dX _N HQ
       linarith
      ·have:(0:O)<=1/(p:O):=by positivity
       linarith
     have HO:0<=∏p∈bd e,(1-(1:O)/(p:O)):=(bf e).le;nlinarith
    have HR:=(aq z (by have:=b9;omega)).1;have K:log (z:O)<=log (e:O):=dM _P (_M (_O :z<=e));have Hw:1/(exp 38*log (e:O))<=1/(exp 38*log (z:O)):=dX _P (dA K (ez 38).le);exact Hw.trans (HR.trans hs)
   have hF:1/(2*exp 38*log (e:O))<=br e D:=(by unfold bt at h7;have h2:1/(exp 38*log (e:O))=2*(1/(2*exp 38*log (e:O))):=_R;linarith);let B:Finset ℕ:=(Icc 1 X).filter (fun b=>b % bb=1 % bb);let i:=(bd e).powerset.filter (fun S=>bj D S);have hY:B.filter (fun b=>∀p∈bd e,¬ p∣b) ⊆ (Icc 1 X).filter (fun b=>∀p ≤ z,p.Prime->¬ p∣b):=by
    intro b hb;simp only[B,dB,dT]at hb ⊢;refine⟨hb.1.1,fun p Ho w U=>?_⟩;by_cases v5:p< b8
    ·have u:p∣bb:=ji id (e7.mpr ⟨by omega,w⟩)
     have hh:b % p=1 % p:=(by have l:=fT (· % p) hb.1.2;rwa[gP b u,gP 1 u]at l);have h0:b % p=0:=Nat.mod_eq_zero_of_dvd U;rw[h0,gi w.one_lt]at hh;omega
    ·exact hb.2 p (dB.mpr ⟨f3.mpr ⟨by omega,_O⟩,w⟩) U
   have H8 :
    ∑S∈i,(-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) <=(aK X z:O):=by
    have Hd:∑S∈i,(-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) =∑b∈B,∑S∈((bd e).filter (·∣b)).powerset.filter (fun S=>bj D S),(-1:O)^S.card:=by
     have l:∀S∈i,(-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) =∑b∈B,if (∏p∈S,p)∣b then (-1:O)^S.card else 0:=(by intro S _;rw[<- f8,ex,e3,e8]);rw[dF rfl l,hH];refine dF rfl fun b _=>?_
     rw[<- f8];refine dF ?_ (fun _ _=>rfl);ext S;simp only[i,dB,eS];constructor
     ·rintro⟨⟨hSsub,hlo⟩,hdvd⟩;refine⟨fun p hg=>dB.mpr ⟨hSsub hg,(ji id hg).trans hdvd⟩,hlo⟩
     ·rintro⟨hSsub,hlo⟩;refine⟨⟨fun p hg=>(dB.mp (hSsub hg)).1,hlo⟩,?_⟩;have hd:∀(T:Finset ℕ),(∀p∈T,p.Prime/\p∣b)->(∏p∈T,p)∣b:=by
       intro T;induction T using eW with
       | empty=>intro _;simp
       | @insert q T hqT ihT=>
        intro hT;have hq:=hT q (ev q T);have hT':∀p∈T,p.Prime/\p∣b:=fun p w=>hT p (fa w);have Hx:Nat.Coprime q (∏p∈T,p):=fL fun p w=>(ft hq.1 (hT' p w).1).mpr (fun h=>hqT (h ▸ w));rw[fN hqT];exact Hx.mul_dvd_of_dvd_of_dvd hq.2 (ihT hT')
      exact hd S fun p hg=>
       ⟨(dB.mp (dB.mp (hSsub hg)).1).2,(dB.mp (hSsub hg)).2⟩
    rw[Hd];have ht:∑b∈B,∑S∈((bd e).filter (·∣b)).powerset.filter (fun S=>bj D S),(-1:O)^S.card <=∑b∈B,if (bd e).filter (·∣b)=∅ then (1:O) else 0:=dG fun b _=>(bo ((bd e).filter (·∣b)) D).2;refine ht.trans ?_
    rw[<- f8,ex,e3,fv];have hu:B.filter (fun b=>(bd e).filter (·∣b)=∅) =B.filter (fun b=>∀p∈bd e,¬ p∣b):=(by ext b;simp[jl]);rw[hu];exact mr.mpr (er hY)
   have Q:∀S∈i,
    |((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) -((X:O)/(bb:O))/(∏p∈S,(p:O))|<=2:=by
    intro S hS;simp only[i,dB,eS]at hS;let d:=∏p∈S,p;have hZ:0< d:=jf fun p w=>(dB.mp (hS.1 w)).2.pos;have hj:Nat.Coprime d bb:=by
     refine Nat.Coprime.prod_left fun p w=>?_
     refine fL fun q hq=>?_
     have G:=hS.1 w;simp only[bd,dB,f3]at G;rw[e7]at hq;have:=b9;exact (ft G.2 hq.2).mpr _O
    let c:=Nat.chineseRemainder hj 0 1;let N:=c.1 % (bb*d);have y:0< bb*d:=fP bc hZ;have R:N< bb*d:=dY _ y;have H9:∀b:ℕ,(b % bb=1 % bb/\d∣b)↔b % (bb*d)=N:=by
     intro b;have P:N % d=0:=by rw[gP _ (kS d bb)];exact c.2.1
     have F:N % bb=1 % bb:=(by rw[gP _ (ir bb d)];exact c.2.2);constructor
     ·rintro⟨hbP,hbd⟩;have He:b ≡ N [MOD d]:=(by change b % d=N % d;rw[Nat.mod_eq_zero_of_dvd hbd,P]);have Hf:b ≡ N [MOD bb]:=(by change b % bb=N % bb;rw[hbP,F]);have he:b ≡ N [MOD d*bb]:=(Nat.modEq_and_modEq_iff_modEq_mul hj).mp ⟨He,Hf⟩;rw[e8]at he;change b % (bb*d)=N % (bb*d) at he;rwa[gi R]at he
     ·intro hh;constructor
      ·have l:=fT (· % bb) hh;rw[gP _ (ir bb d)]at l;exact l.trans F
      ·apply Nat.dvd_of_mod_eq_zero
       have l:=fT (· % d) hh;rw[gP _ (kS d bb)]at l;exact l.trans P
    let M:=bb*d;have H0:B.filter (fun b=>d∣b)=(Icc 1 X).filter (fun b=>b % M=N):=(by ext b;simp only[B,dB];exact⟨fun ⟨⟨l,h2⟩,h3⟩=>⟨l,(H9 b).mp ⟨h2,h3⟩⟩,fun ⟨l,h2⟩=>let ⟨ha,hb⟩:=(H9 b).mpr h2;⟨⟨l,ha⟩,hb⟩⟩);rw[H0];have HS:((Icc 1 X).filter (fun b=>b % M=N)).card<=X/M+1:=by
     have H1:(Icc 1 X).filter (fun b=>b % M=N) ⊆ (range (X/M+1)).image (fun k=>k*M+N):=by
      intro b hb;simp only[dB,dT,dW,dN]at hb ⊢;refine⟨b/M,?_,?_⟩
      ·have:b/M<=X/M:=Nat.div_le_div_right hb.1.2
       omega
      ·have:=gu b M
       rw[hb.2]at this;linarith
     exact (er H1).trans (ja.trans (by simp))
    have HT:X/M<=((Icc 1 X).filter (fun b=>b % M=N)).card+1:=by
     have H2:(Ico 1 (X/M)).image (fun k=>k*M+N) ⊆ (Icc 1 X).filter (fun b=>b % M=N):=by
      intro b hb;simp only[dW,f3]at hb;rcases hb with⟨k,⟨HU,HG⟩,rfl⟩;simp only[dB,dT];have Hy:k*M+N<=X:=by have l:(k+1)*M<=X:=(eE M HG).trans (eD X M);have h2:(k+1)*M=k*M+M:=_R;have h3:N< M:=R;omega
      have Hz:1<=k*M+N:=(by have l:1*1<=k*M:=eH HU y;omega);refine⟨⟨Hz,Hy⟩,?_⟩;rw[Nat.mul_add_mod_self_right,gi R]
     have H3:Function.Injective (fun k=>k*M+N):=(by intro k1 k2 h;exact ii y (Nat.add_right_cancel h));have hc:=er H2;rw[fs _ H3,kT]at hc;omega
    have h9:(0:O)< (M:O):=_M y;have HA:((X/M:ℕ):O)<=(X:O)/(M:O):=(by rw[ma h9];exact_mod_cast eD X M);have HB:(X:O)/(M:O)-1< ((X/M:ℕ):O):=by
     rw[sub_lt_iff_lt_add,mm h9];have l:X< (X/M+1)*M:=by have v3:X< X/M*M+M:=iz y (a:=X);have v4:(X/M+1)*M=X/M*M+M:=_R;omega
     exact_mod_cast l
    have hI:((X:O)/(bb:O))/(∏p∈S,(p:O))=(X:O)/(M:O):=(by have hL:(d:O)=∏p∈S,(p:O):=(by simp[d]);have hM:(M:O)=(bb:O)*(d:O):=(by simp[M]);rw[hM,<- hL,div_div]);rw[hI,ms];have HZ:(((Icc 1 X).filter (fun b=>b % M=N)).card:O)<=((X/M:ℕ):O)+1:=(by exact_mod_cast HS);have v0:((X/M:ℕ):O)<=(((Icc 1 X).filter (fun b=>b % M=N)).card:O)+1:=(by exact_mod_cast HT);constructor <;> linarith
   have Hg:(i.card:O)<=D:=by
    have Hh:∀S∈i,(∏p∈S,p)∈Icc 1 ⌊D⌋₊:=by
     intro S hS;simp only[i,dB,eS]at hS;rw[dT];have HC:1<=∏p∈S,p:=(by have:=jf fun p w=>(dB.mp (hS.1 w)).2.pos;omega);have HD:(∏p∈S,(p:O))<=D:=by
      refine (bp S.card S D rfl (fun p w=>(dB.mp (hS.1 w)).2.two_le)).2 hS.2 ?_ ?_
      ·intro p w;have hv:(p:O)<=(e:O):=(by exact_mod_cast (f3.mp (dB.mp (hS.1 w)).1).2.le);have hw:(e:O)<=D:=mG (by have:=b9;exact_mod_cast (_O :1<=e)) _O;exact hv.trans hw
      ·exact mo (by have:=b9;exact_mod_cast (_O :1<=e))
     refine⟨HC,g2 ?_⟩
     rw[fu];exact HD
    have hD:Set.InjOn (fun S:Finset ℕ=>∏p∈S,p) (i:Set (Finset ℕ)):=(by intro S1 HH S2 HI h5;simp only[eB,i,dB,eS]at HH HI;have l:=go (fun p w=>(dB.mp (HH.1 w)).2);have h2:=go (fun p w=>(dB.mp (HI.1 w)).2);dsimp only at h5;rw[<- l,<- h2,h5]);have C:i.card<=⌊D⌋₊:=by
     calc i.card=(i.image fun S=>∏p∈S,p).card:=
           (gA hD).symm
       _<=(Icc 1 ⌊D⌋₊).card:=er (mv.mpr Hh)
       _=⌊D⌋₊:=by simp
    exact (mr.mpr C).trans (fC _P)
   have Hq:((X:O)/(bb:O))*br e D -∑S∈i,(-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) <=2*D:=by
    have Hi:((X:O)/(bb:O))*br e D =∑S∈i,(-1:O)^S.card*(((X:O)/(bb:O))/(∏p∈S,(p:O))):=(by unfold br;rw[dP];refine dF rfl fun S _=>_R);rw[Hi,<- f2]
    calc ∑S∈i,((-1:O)^S.card*(((X:O)/(bb:O))/(∏p∈S,(p:O))) -
          (-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O))
        <= ∑_S∈i,(2:O):=by
          refine dG fun S hS=>?_
          have l:(-1:O)^S.card*(((X:O)/(bb:O))/(∏p∈S,(p:O))) -(-1:O)^S.card*((B.filter (fun b=>(∏p∈S,p)∣b)).card:O) <=
              |(-1:O)^S.card*(((X:O)/(bb:O))/(∏p∈S,(p:O)) -((B.filter (fun b=>(∏p∈S,p)∣b)).card:O))|:=by
            have:=le_abs_self ((-1:O)^S.card*(((X:O)/(bb:O))/(∏p∈S,(p:O)) -((B.filter (fun b=>(∏p∈S,p)∣b)).card:O)))
            linarith
          rw[lA,abs_pow,abs_neg,abs_one,jQ,gz,abs_sub_comm]at l;exact l.trans (Q S hS)
      _=2*(i.card:O):=by rw[ex,e3];ring
      _<=2*D:=by linarith
   have HE:2*D<=((X:O)/(bb:O))*(1/(4*exp 38*log (e:O))):=by
    have Hj:D<=(2:O)^j*(z:O)^j:=(by simp only[D];rw[<- eP];refine m9 _P ?_ j;exact_mod_cast (_O :e<=2*z));have K:log (e:O)<=(z:O):=(by have l:=eY (_P :(0:O)< (e:O));have h2:(e:O)=(z:O)+1:=_M (rfl :e=z+1);linarith);let k0:ℕ:=⌈log (16*(bb:O)*exp 38)/log 2⌉₊;have H4:16*(bb:O)*exp 38<=(2:O)^k0:=(by have hB:0< log 2:=_l a3;have l:log (16*(bb:O)*exp 38)/log 2<=(k0:O):=g6 _;have h2:=(mc hB).mp l;have h3:=me.mpr h2;rw[eX _P]at h3;have h5:exp ((k0:O)*log 2)=(2:O)^k0:=(by rw[e8,<- fQ (_N :(0:O)< 2),eK]);linarith);have HF:(2:O)<=(z:O):=_M hz;have Hk:(2:O)^(j+k0)<=(z:O)^(j+k0):=m9 _N HF (j+k0);have hx:2*D*(4*(bb:O)*exp 38*log (e:O))<=(z:O)^m:=by
     calc 2*D*(4*(bb:O)*exp 38*log (e:O))
         <= 2*((2:O)^j*(z:O)^j)*(4*(bb:O)*exp 38*(z:O)):=by refine en (dA Hj _N) (dA K _P) _P _P
       _=(8*(bb:O)*exp 38)*(2:O)^j*(z:O)^(j+1):=by rw[fc];ring
       _<=(2:O)^k0*(2:O)^j*(z:O)^(j+1):=by have h8:8*(bb:O)*exp 38<=(2:O)^k0:=(by nlinarith[H4,ez 38,hC]);refine dE (dE h8 _P) _P
       _=(2:O)^(j+k0)*(z:O)^(j+1):=by rw[ee];ring
       _<=(z:O)^(j+k0)*(z:O)^(j+1):=dE Hk _P
       _=(z:O)^(2*j+k0+1):=by rw[<- ee];congr 1;omega
       _<=(z:O)^m:=mg _L (by dsimp[m,k0];omega)
    have hN:2*D*(4*(bb:O)*exp 38*log (e:O))<=(X:O):=hx.trans W;have h5:((X:O)/(bb:O))*(1/(4*exp 38*log (e:O))) =(X:O)/(4*(bb:O)*exp 38*log (e:O)):=_R;rw[h5,ma _P];exact hN
   have Hl:log (e:O)<=2*log (z:O):=(by have H5:(e:O)<=(z:O)^2:=(by have HF:(2:O)<=(z:O):=_M hz;have Hm:(e:O)=(z:O)+1:=_M (rfl :e=z+1);rw[Hm];nlinarith);have l:=dM _P H5;rwa[fm]at l);have J:v<=c3:=(gw _ _).trans (gw _ _);have Hr:c3*(X:O)/log (z:O) <=((X:O)/(bb:O))*(1/(4*exp 38*log (e:O))):=(by simp only[c3];have l:1/(8*(bb:O)*exp 38)*(X:O)/log (z:O) =((X:O)/(bb:O))*(1/(4*exp 38*(2*log (z:O)))):=_R;rw[l];refine dA ?_ _P;exact dX _P (by nlinarith[ez 38]));have hf:(0:O)<=(X:O)/(bb:O):=_P;have Hn:((X:O)/(bb:O))*(1/(4*exp 38*log (e:O))) <=((X:O)/(bb:O))*br e D-2*D:=by have Hs:=dA hF hf;have h5:((X:O)/(bb:O))*(1/(2*exp 38*log (e:O))) =2*(((X:O)/(bb:O))*(1/(4*exp 38*log (e:O)))):=_R;linarith
   calc v*(X:O)/log (z:O)
       <= c3*(X:O)/log (z:O):=dI (dE J (dK X)) o.le
     _<=(aK X z:O):=_L
def LL (a:ℕ):Set O:=⋃ d∈a.divisors,Set.Ico (log (d:O)-log 2) (log (d:O))
def bA:List O->O
 | []=>0
 | [_]=>log 2
 | x :: y :: rest=>min (log 2) (y-x)+bA (y :: rest)
def bB (a:ℕ):List O:=(a.divisors.sort (·<=·)).map fun (d:ℕ)=>log (d:O)
def L (a:ℕ):O:=bA (bB a)
def W (a:ℕ):ℕ:=((a.divisors×ˢa.divisors).filter fun p=>
  |log (p.1:O)-log (p.2:O)|<=log 2).card
lemma bC:∀xs:List O,xs.Pairwise (·<=·)->0<=bA xs
 | [],_=>eR
 | [_],_=>by simp only[bA];linarith[a3]
 | x :: y :: rest,h=>by
  simp only[bA]
  have c:x<=y:=fS h (fZ ..)
  have b:(y :: rest).Pairwise (·<=·):=(ml.mp h).2
  have d:0<=min (log 2) (y-x):=le_min (_l a3) _L
  linarith[bC (y :: rest) b]
lemma bD:∀xs:List O,bA xs<=(xs.length:O)*log 2
 | []=>by simp[bA]
 | [_]=>by simp[bA]
 | x :: y :: rest=>by
  simp only[bA,l9,jX,eF]
  have b:=bD (y :: rest)
  simp only[l9,jX,eF]at b
  linarith[i7 (log 2) (y-x)]
lemma bE:∀(xs:List O) (h:xs≠[]),bA xs<=log 2+(xs.getLast h-xs.head h)
 | [],h=>absurd rfl h
 | [x],_=>by simp[bA]
 | x :: y :: rest,_=>by
  simp only[bA]
  have c:=bE (y :: rest) (jN y rest)
  have b:(x :: y :: rest).getLast (jN x (y :: rest)) =(y :: rest).getLast (jN y rest):=List.getLast_cons (jN y rest)
  simp only[List.head_cons]at c ⊢
  rw[b]
  linarith[gw (log 2) (y-x)]
lemma bF:∀xs:List O,MeasurableSet (⋃ z∈xs,Set.Ico (z-log 2) z)
 | []=>by simp
 | z :: rest=>by
  have b:(⋃ w∈(z :: rest),Set.Ico (w-log 2) w) =Set.Ico (z-log 2) z∪⋃ w∈rest,Set.Ico (w-log 2) w:=by ext t;simp[eQ]
  rw[b];exact iU.union (bF rest)
set_option maxHeartbeats 800000 in
lemma bG:∀xs:List O,xs.Pairwise (·<=·) -> volume (⋃ x∈xs,Set.Ico (x-log 2) x)=ENNReal.ofReal (bA xs)
 | [],_=>by simp[bA]
 | [x],_=>by
  simp only[List.mem_singleton,lR,bA,ix]
  congr 1;ring
 | x :: y :: rest,h=>by
  have u:x<=y:=fS h (fZ ..)
  have d:(y :: rest).Pairwise (·<=·):=(ml.mp h).2
  have q:∀z∈y :: rest,y<=z:=by
   intro z m;rcases kB.mp m with rfl | hzr
   ·exact eR
   ·exact fS d hzr
  let U:Set O:=⋃ z∈(y :: rest),Set.Ico (z-log 2) z;have j:(⋃ z∈(x :: y :: rest),Set.Ico (z-log 2) z) =Set.Ico (x-log 2) (min x (y-log 2))∪U:=by
   ext t;simp only[eQ,kB,kA,fF,U];constructor
   ·rintro⟨z,rfl | m,c,b⟩
    ·by_cases o:t< y-log 2
     ·exact Or.inl ⟨c,lt_min b o⟩
     ·push Not at o
      exact Or.inr ⟨y,Or.inl rfl,o,e9 b u⟩
    ·exact Or.inr ⟨z,m,c,b⟩
   ·rintro (⟨c,b⟩ | ⟨z,m,c,b⟩)
    ·exact⟨x,Or.inl rfl,c,e9 b (i7 _ _)⟩
    ·exact⟨z,Or.inr m,c,b⟩
  have l:Disjoint (Set.Ico (x-log 2) (min x (y-log 2))) U:=(by rw[kX];intro t c b;simp only[fF]at c;simp only[eQ,fF,U]at b;rcases b with⟨z,m,w,_⟩;have A:y<=z:=q z m;have v:t< y-log 2:=e9 c.2 (gw _ _);linarith);have i:MeasurableSet U:=bF (y :: rest);rw[j,lB l i,ix,bG (y :: rest) d];have e:min x (y-log 2)-(x-log 2)=min (log 2) (y-x):=by
   rcases le_total x (y-log 2) with hle | hle
   ·rw[li hle,li _L];ring
   ·rw[jo hle,jo _L];ring
  rw[e,<- ENNReal.ofReal_add (le_min (_l a3) _L)
   (bC (y :: rest) d)]
  rfl
lemma bH (a:ℕ):(bB a).Pairwise (·<=·):=by unfold bB;have e:(a.divisors.sort (·<=·)).Pairwise (·<=·):=lW _ _;rw[List.pairwise_map];refine List.Pairwise.imp_of_mem ?_ e;intro h i b c d;rw[iO]at b c;exact dM (_M (em b)) (_M d)
lemma bI (a:ℕ) :
 LL a=⋃ x∈bB a,Set.Ico (x-log 2) x:=by
 ext t;simp only[LL,bB,eQ,mB,iO];constructor
 ·rintro⟨d,hd,ht⟩;exact⟨log (d:O),⟨d,hd,rfl⟩,ht⟩
 ·rintro⟨_,⟨d,hd,rfl⟩,ht⟩;exact⟨d,hd,ht⟩
lemma bJ (a:ℕ):volume (LL a)=ENNReal.ofReal (L a):=by rw[bI,L];exact bG _ (bH a)
lemma bK (a:ℕ):0<=L a:=bC _ (bH a)
lemma bL:L 1=log 2:=by unfold L bB;rw[Nat.divisors_one,Finset.sort_singleton];simp[bA]
lemma bM (a:ℕ):L a<=(a.divisors.card:O)*log 2:=by have h:=bD (bB a);simp only[bB,List.length_map,lk]at h;exact h
lemma bO (a:ℕ) (u:1<=a):L a<=log 2+log (a:O):=by
 let i:=bB a;have b:i≠[]:=by
  intro h;have q:(1:ℕ)∈a.divisors:=Nat.one_mem_divisors.mpr _O;have e:log (1:O)∈i:=mB.mpr ⟨1,(iO (·<=·)).mpr q,by simp⟩
  rw[h]at e;simp at e
 have l:=bE i b;have m:0<=i.head b:=by obtain⟨d,j,c⟩:=mB.mp (List.head_mem b);rw[iO]at j;rw[<- c];exact f1 (_M (em j))
 have o:i.getLast b<=log (a:O):=by obtain⟨d,j,c⟩:=mB.mp (List.getLast_mem b);rw[iO]at j;rw[<- c];exact dM (_M (em j)) (_M (el _O (ef j)))
 change bA i<=log 2+log (a:O);linarith
lemma bP {a b:ℕ} (E:Nat.Coprime a b) :
 L (a*b)<=(b.divisors.card:O)*L a:=by
 by_cases B:a=0
 ·subst B;simp[L,bB,bA]
 by_cases C:b=0
 ·subst C;simp[L,bB,bA]
 have w:LL (a*b)⊆⋃ e∈b.divisors,(fun u=>u+(-log (e:O))) ⁻¹' LL a:=by
  intro u G;simp only[LL,eQ,fF]at G;rcases G with⟨d,F,J,K⟩;have y:d∣a*b:=ef F;have c:0< d:=em F;let z:=Nat.gcd d a;let A:=Nat.gcd d b;have q:d=z*A:=by have H:Nat.gcd d (a*b)=d:=lw y;rw[<- H];exact Nat.Coprime.gcd_mul d E
  have h:z∈a.divisors:=fW.mpr ⟨kY d a,B⟩;have i:A∈b.divisors:=fW.mpr ⟨kY d b,C⟩;have j:(0:O)< z:=(by exact_mod_cast j3 (l8 d a) c);have l:(0:O)< A:=(by exact_mod_cast j3 (l8 d b) c);have D:log (d:O)=log (z:O)+log (A:O):=(by rw[q,g3,log_mul j.ne' l.ne']);simp only[eQ,eL,LL,fF];exact⟨A,i,z,h,by linarith,_L⟩
 have m:volume (LL (a*b)) <=∑e∈b.divisors,volume ((fun u=>u+(-log (e:O))) ⁻¹' LL a):=(f4 w).trans (g1 _ _);have o:∀e∈b.divisors,volume ((fun u=>u+(-log (e:O))) ⁻¹' LL a) =volume (LL a):=fun e _=>
  kd volume (-log (e:O)) (LL a)
 rw[dF rfl o,ex,e3,bJ,bJ]at m;have v:(b.divisors.card:ENNReal)*ENNReal.ofReal (L a) =ENNReal.ofReal ((b.divisors.card:O)*L a):=by rw[jx (dK _),ENNReal.ofReal_natCast]
 rw[v]at m;exact (ENNReal.ofReal_le_ofReal_iff (ek (dK _) (bK a))).mp m
lemma bQ {p a:ℕ} (c:p.Prime) (d:¬ p∣a) :
 L (p*a)<=2*L a:=by
 have b:Nat.Coprime a p:=(c.coprime_iff_not_dvd.mpr d).symm;rw[e8];have h:=bP b;rw[c.divisors,la c.ne_one.symm]at h;simpa using h
lemma bR (ps:List ℕ) (D:∀p∈ps,p.Prime) (B:ps.Pairwise (·< ·))
 (g:ℕ) (_hg:g<=ps.length) :
 L ps.prod<=(2:O)^(ps.length-g)*(log ((ps.take g).prod:O)+log 2):=by
 have c:ps=ps.take g ++ ps.drop g:=(List.take_append_drop g ps).symm;have u:ps.prod=(ps.take g).prod*(ps.drop g).prod:=by conv_lhs=>rw[c];rw[List.prod_append]
 have y:Nat.Coprime (ps.take g).prod (ps.drop g).prod:=by
  refine Nat.coprime_list_prod_left_iff.mpr fun p m=>
   mD.mpr fun q A=>?_
  have E:=D p (kn m);have l:=D q (List.mem_of_mem_drop A);have b:=B;rw[c,List.pairwise_append]at b;exact (ft E l).mpr (b.2.2 p m q A).ne
 have F:=bP y;have e:1<=(ps.take g).prod:=Nat.succ_le_of_lt (List.prod_pos fun p m=>(D p (kn m)).pos);have G:=bO (ps.take g).prod e;have h:((ps.drop g).prod.divisors.card:O)<=(2:O)^(ps.length-g):=by
  have i:(ps.drop g).Pairwise (·< ·):=(by have b:=B;rw[c,List.pairwise_append]at b;exact b.2.1);have v:∀(qs:List ℕ),(∀q∈qs,q.Prime)->qs.Pairwise (·< ·) -> qs.prod.divisors.card=2^qs.length:=by
   intro qs;induction qs with
   | nil=>intro _ _;simp
   | cons q rest ih=>
    intro l o;have z:=l q (fZ ..);have d:=fun r C=>l r (gy q C);have j:=(ml.mp o).2;have w:Nat.Coprime q rest.prod:=mD.mpr fun r C=>
      (ft z (d r C)).mpr (fS o C).ne
    rw[List.prod_cons,w.card_divisors_mul,z.divisors,la z.ne_one.symm,ih d j,l9,fp]
  rw[v (ps.drop g) (fun q z=>D q (List.mem_of_mem_drop z)) i,List.length_drop];norm_cast
 rw[u];exact F.trans (en h _L (bK _) _P)
set_option maxHeartbeats 800000 in
lemma bS (a:ℕ) :
 ((a.divisors.card:O)*log 2)^2<=L a*((W a:O)*log 2):=by
 let f:O->O:=fun u=>
  ∑d∈a.divisors,(Set.Ico (log (d:O)-log 2) (log (d:O))).indicator (fun _=>(1:O)) u
 have j:∀d∈a.divisors,Integrable ((Set.Ico (log (d:O)-log 2) (log (d:O))).indicator (fun _=>(1:O))):=by intro d _;have v:volume (Set.Ico (log (d:O)-log 2) (log (d:O)))≠⊤:=(by simp[ix]);exact (jH iU).mpr (ju v)
 have B : ∫ u,f u=(a.divisors.card:O)*log 2:=by
  change ∫ u,∑d∈a.divisors,(Set.Ico (log (d:O)-log 2) (log (d:O))).indicator (fun _=>(1:O)) u=_;rw[iZ _ j];have F:∀d∈a.divisors,∫ u,(Set.Ico (log (d:O)-log 2) (log (d:O))).indicator (fun _=>(1:O)) u =log 2:=by intro d _;rw[iY iU,iT,Measure.real,ix];have M:log (d:O)-(log (d:O)-log 2)=log 2:=_R;rw[M,eZ (_l a3)];simp
  rw[dF rfl F,ex,e3]
 have G:∀u,f u=((LL a).indicator (fun _=>(1:O)) u)*f u:=by
  intro u;by_cases K:u∈LL a
  ·simp[Set.indicator_of_mem K]
  ·simp only[m5 K,kP];apply g0;intro d hd;have N:u ∉ Set.Ico (log (d:O)-log 2) (log (d:O)):=fun U=>K (k6 hd U);simp[m5 N]
 have c:MeasurableSet (LL a):=MeasurableSet.biUnion a.divisors.countable_toSet fun _ _=>iU;have C:volume (LL a)≠⊤:=by rw[bJ];exact ec
 have o:Integrable ((LL a).indicator (fun _=>(1:O))):=(jH c).mpr (ju C);have e:Integrable f:=iB _ j;have l:(fun u=>f u^2)=fun u=>
  ∑p∈a.divisors×ˢa.divisors,((Set.Ico (log (p.1:O)-log 2) (log (p.1:O))) ∩
    (Set.Ico (log (p.2:O)-log 2) (log (p.2:O)))).indicator (fun _=>(1:O)) u:=by
  ext u;dsimp only[f];rw[sq,kJ,<- sum_product'];refine dF rfl fun p _=>?_
  by_cases Z:u∈Set.Ico (log (p.1:O)-log 2) (log (p.1:O)) <;>
   by_cases h2:u∈Set.Ico (log (p.2:O)-log 2) (log (p.2:O)) <;>
   simp[Z,h2]
 have b:∀p∈a.divisors×ˢa.divisors,Integrable ((Set.Ico (log (p.1:O)-log 2) (log (p.1:O)) ∩
   Set.Ico (log (p.2:O)-log 2) (log (p.2:O))).indicator (fun _=>(1:O))):=by
  intro p _;have v:volume
   (Set.Ico (log (p.1:O)-log 2) (log (p.1:O)) ∩
    Set.Ico (log (p.2:O)-log 2) (log (p.2:O)))≠⊤:=
   fz (by simp[ix]) (f4 Set.inter_subset_left)
  exact (jH (iU.inter iU)).mpr (ju v)
 have i:Integrable (fun u=>f u^2):=by rw[l];exact iB _ b
 have P:(∫ u,f u)^2<=(∫ u,(LL a).indicator (fun _=>(1:O)) u)*(∫ u,f u^2):=by
  have w:∀t:O,0<=t^2*(∫ u,(LL a).indicator (fun _=>(1:O)) u) -2*t*(∫ u,f u)+(∫ u,f u^2):=by
   intro t;have H:0<=∫ u,(t*(LL a).indicator (fun _=>(1:O)) u-f u)^2:=ll fun u=>gR _;have Q:(fun u=>(t*(LL a).indicator (fun _=>(1:O)) u-f u)^2) =fun u=>(t^2*(LL a).indicator (fun _=>(1:O)) u-2*t*f u)+f u^2:=by
    ext u;have Z:((LL a).indicator (fun _=>(1:O)) u)^2=(LL a).indicator (fun _=>(1:O)) u:=(by by_cases K:u∈LL a <;> simp[K]);have h2:(LL a).indicator (fun _=>(1:O)) u*f u=f u:=(G u).symm
    calc (t*(LL a).indicator (fun _=>(1:O)) u-f u)^2
        = t^2*((LL a).indicator (fun _=>(1:O)) u)^2 -2*t*((LL a).indicator (fun _=>(1:O)) u*f u)+f u^2:=_R
      _=(t^2*(LL a).indicator (fun _=>(1:O)) u-2*t*f u)+f u^2:=by rw[Z,h2]
   rw[Q]at H;have y:Integrable (fun u=>t^2*(LL a).indicator (fun _=>(1:O)) u):=o.const_mul (t^2);have z:Integrable (fun u=>2*t*f u):=e.const_mul (2*t);have D:Integrable (fun u=>t^2*(LL a).indicator (fun _=>(1:O)) u-2*t*f u):=y.sub z;rw[MeasureTheory.integral_add D i,MeasureTheory.integral_sub y z,kF,kF]at H;exact H
  by_cases hA : ∫ u,(LL a).indicator (fun _=>(1:O)) u=0
  ·by_contra E;push Not at E;rw[hA,kP]at E;have R : ∫ u,f u≠0:=fun hB=>by rw[hB]at E;norm_num at E
   have X:=w (((∫ u,f u^2)+1)/(2*∫ u,f u));rw[hA,hK,zero_sub]at X;have J:2*(((∫ u,f u^2)+1)/(2*∫ u,f u))*∫ u,f u=(∫ u,f u^2)+1:=(by field_simp [R]);rw[J]at X;linarith
  ·have m:0< ∫ u,(LL a).indicator (fun _=>(1:O)) u:=ib (ll fun u=>by
     by_cases K:u∈LL a <;> simp[K]) (Ne.symm hA)
   have X:=w ((∫ u,f u)/(∫ u,(LL a).indicator (fun _=>(1:O)) u));have J:((∫ u,f u)/(∫ u,(LL a).indicator (fun _=>(1:O)) u))^2 *(∫ u,(LL a).indicator (fun _=>(1:O)) u) -2*((∫ u,f u)/(∫ u,(LL a).indicator (fun _=>(1:O)) u))*(∫ u,f u) +(∫ u,f u^2) =(∫ u,f u^2)-(∫ u,f u)^2/(∫ u,(LL a).indicator (fun _=>(1:O)) u):=(by field_simp [m.ne'];ring);rw[J]at X;rw[<- div_le_iff₀' m];linarith
 have q : ∫ u,(LL a).indicator (fun _=>(1:O)) u=L a:=by rw[iY c,iT,Measure.real,bJ,eZ (bK a)];simp
 have h : ∫ u,f u^2<=(W a:O)*log 2:=by
  rw[l,iZ _ b]
  calc ∑p∈a.divisors×ˢa.divisors,
          ∫ u,(Set.Ico (log (p.1:O)-log 2) (log (p.1:O)) ∩
            Set.Ico (log (p.2:O)-log 2) (log (p.2:O))).indicator (fun _=>(1:O)) u
      <= ∑p∈a.divisors×ˢa.divisors,if |log (p.1:O)-log (p.2:O)|<=log 2 then log 2 else 0:=by
        refine dG fun p _=>?_
        split_ifs with hclose
        · rw[iY (iU.inter iU),iT,lf,fv,Measure.real]
          have h0:=f4 (μ:=volume)
            (Set.inter_subset_left (s:=Set.Ico (log (p.1:O)-log 2) (log (p.1:O)))
              (t:=Set.Ico (log (p.2:O)-log 2) (log (p.2:O))))
          have A:volume (Set.Ico (log (p.1:O)-log 2) (log (p.1:O))) =ENNReal.ofReal (log 2):=(by rw[ix];congr 1;ring);have S:=fM (by rw[A];exact ec) h0;rwa[A,eZ (_l a3)]at S
        · have T:Set.Ico (log (p.1:O)-log 2) (log (p.1:O)) ∩
              Set.Ico (log (p.2:O)-log 2) (log (p.2:O))=∅:=by
            ext u;simp only[kW,fF,iG,iC];rintro⟨⟨h1a,h1b⟩,⟨h2a,h2b⟩⟩;exact hclose (ms.mpr ⟨by linarith,_L⟩)
          rw[T];simp
    _=(W a:O)*log 2:=by rw[<- f8,ex,e3];rfl
 rw[B,q]at P;exact P.trans (dA h (bK a))
set_option maxHeartbeats 800000 in
lemma bT (A:Finset ℕ) (u:∀a∈A,1<=a) :
 (log 2)*(∑a∈A,(a.divisors.card:O)/(a:O))^2 <=(∑a∈A,L a/(a:O))*(∑a∈A,(W a:O)/(a:O)):=by
 have j:=Finset.sum_mul_sq_le_sq_mul_sq A (fun a=>sqrt (L a/(a:O))) (fun a=>sqrt ((W a:O)/(a:O)));have m:(∑a∈A,sqrt (L a/(a:O))^2)=∑a∈A,L a/(a:O):=dF rfl fun a _=>kN (ed (bK a) (dK _));have o:(∑a∈A,sqrt ((W a:O)/(a:O))^2)=∑a∈A,(W a:O)/(a:O):=dF rfl fun _ _=>kN _P;rw[m,o]at j;have h:∀a∈A,sqrt (log 2)*((a.divisors.card:O)/(a:O)) <=sqrt (L a/(a:O))*sqrt ((W a:O)/(a:O)):=by
  intro a q;have c:(0:O)< a:=_M (u a q);have b:0< log 2:=_l a3;rw[<- sqrt_mul (ed (bK a) c.le)];rw[Real.le_sqrt _P (ek (ed (bK a) c.le) _P)];have l:log 2*((a.divisors.card:O)/(a:O))^2 <=L a/(a:O)*((W a:O)/(a:O)):=by
   have i:log 2*(log 2*((a.divisors.card:O)/(a:O))^2) <=log 2*(L a/(a:O)*((W a:O)/(a:O))):=by
    calc log 2*(log 2*((a.divisors.card:O)/(a:O))^2)
        = ((a.divisors.card:O)*log 2)^2/(a:O)^2:=_R
      _<=(L a*((W a:O)*log 2))/(a:O)^2:=dI (bS a) _P
      _=log 2*(L a/(a:O)*((W a:O)/(a:O))):=_R
   exact k8 i b
  calc (sqrt (log 2)*((a.divisors.card:O)/(a:O)))^2
      = log 2*((a.divisors.card:O)/(a:O))^2:=by rw[eP,kN b.le]
    _<=L a/(a:O)*((W a:O)/(a:O)):=l
 have e:sqrt (log 2)*∑a∈A,(a.divisors.card:O)/(a:O) <=∑a∈A,sqrt (L a/(a:O))*sqrt ((W a:O)/(a:O)):=by rw[dP];exact dG h
 have d:=m9 (ek (ld _) (ea fun _ _=>by positivity)) e 2
 rw[eP,kN (_l a3)]at d;exact d.trans j
def bU (u v:O):List O->List (O × O)
 | []=>[(u,v)]
 | y :: rest=>
  if y-log 2<=v then bU u y rest
  else (u,v) :: bU (y-log 2) y rest
def bV:List O->List (O × O)
 | []=>[]
 | x :: rest=>bU (x-log 2) x rest
set_option maxHeartbeats 800000 in
lemma bW (u v:O) (w:log 2<=v-u) :
 ∀(xs:List O),xs.Pairwise (·<=·)->(∀y∈xs,v<=y) -> (∀j∈bU u v xs,log 2<=j.2-j.1/\u<=j.1) /\(bU u v xs).Pairwise (fun a b=>a.2< b.1) /\(⋃ j∈bU u v xs,Set.Ico j.1 j.2) =Set.Ico u v∪⋃ y∈xs,Set.Ico (y-log 2) y /\((bU u v xs).map fun j=>j.2-j.1).sum =(v-u - log 2)+bA (v :: xs):=by
 intro xs;induction xs generalizing u v with
 | nil=>
  intro _ _;simp only[bU,List.mem_singleton,forall_eq,List.pairwise_singleton,lR,List.not_mem_nil,Set.iUnion_false,Set.iUnion_empty,Set.union_empty,je,List.map_nil,jd,List.sum_nil,i0,bA];exact⟨⟨w,eR⟩,trivial,trivial,_R⟩
 | cons y rest ih=>
  intro o C;have B:v<=y:=C y (fZ ..);have e:rest.Pairwise (·<=·):=(ml.mp o).2;have i:∀z∈rest,y<=z:=fun z l=>fS o l;simp only[bU];split_ifs with hmerge
  ·have c:=ih u y _L e i;refine⟨c.1,c.2.1,?_,?_⟩
   ·rw[c.2.2.1];ext t;simp only[kA,eQ,kB,fF];constructor
    ·rintro (⟨ht1,ht2⟩ | ⟨z,l,htz⟩)
     ·by_cases q:t< v
      ·exact Or.inl ⟨ht1,q⟩
      ·push Not at q
       exact Or.inr ⟨y,Or.inl rfl,by linarith,ht2⟩
     ·exact Or.inr ⟨z,Or.inr l,htz⟩
    ·rintro (⟨ht1,ht2⟩ | ⟨z,rfl | l,ht1,ht2⟩)
     ·exact Or.inl ⟨ht1,e9 ht2 B⟩
     ·exact Or.inl ⟨by linarith,ht2⟩
     ·exact Or.inr ⟨z,l,ht1,ht2⟩
   ·rw[c.2.2.2];simp only[bA];rw[jo (_L :y-v<=log 2)];ring
  ·push Not at hmerge
   have c:=ih (y-log 2) y (by ring_nf;exact eR) e i;refine⟨?_,?_,?_,?_⟩
   ·intro j d;rcases kB.mp d with rfl | d'
    ·exact⟨w,eR⟩
    ·exact⟨(c.1 j d').1,by linarith[(c.1 j d').2]⟩
   ·rw[ml];exact⟨fun j d=>by linarith[(c.1 j d).2],c.2.1⟩
   ·ext t;have A:=Set.ext_iff.mp c.2.2.1 t;simp only[eQ,kB,kA]at A ⊢;constructor
    ·rintro⟨j,rfl | d,m⟩
     ·exact Or.inl m
     ·rcases A.mp ⟨j,d,m⟩ with h | ⟨z,l,htz⟩
      ·exact Or.inr ⟨y,Or.inl rfl,h⟩
      ·exact Or.inr ⟨z,Or.inr l,htz⟩
    ·rintro (m | ⟨z,rfl | l,htz⟩)
     ·exact⟨(u,v),Or.inl rfl,m⟩
     ·rcases A.mpr (Or.inl htz) with⟨j,d,m⟩;exact⟨j,Or.inr d,m⟩
     ·rcases A.mpr (Or.inr ⟨z,l,htz⟩) with⟨j,d,m⟩;exact⟨j,Or.inr d,m⟩
   ·simp only[je,jd,bA];rw[c.2.2.2,li (_L :log 2<=y-v)];ring
set_option maxHeartbeats 800000 in
lemma bX (a:ℕ) :
 let ivs:=bV (bB a)
 (∀c∈ivs,log 2<=c.2-c.1) /\
 ivs.Pairwise (fun x y=>x.2< y.1) /\
 (⋃ c∈ivs,Set.Ico c.1 c.2)=LL a /\
 (ivs.map fun c=>c.2-c.1).sum=L a:=by
 intro ivs;have d:=bH a;have e:=bI a;cases hxs:bB a with
 | nil=>
  refine⟨by simp[ivs,hxs,bV],by simp[ivs,hxs,bV],?_,by simp[ivs,L,hxs,bV,bA]⟩
  rw[e,hxs];simp[ivs,hxs,bV]
 | cons x rest=>
  rw[hxs]at d;have b:=bW (x-log 2) x (by ring_nf;exact eR) rest (ml.mp d).2 (fun z h=>fS d h);refine⟨fun c i=>?_,?_,?_,?_⟩
  ·simp only[ivs,hxs,bV]at i;exact (b.1 c i).1
  ·simp only[ivs,hxs,bV];exact b.2.1
  ·simp only[ivs,hxs,bV];rw[b.2.2.1,e,hxs];ext t;simp only[eQ,kB,kA];constructor
   ·rintro (ht | ⟨z,h,htz⟩)
    ·exact⟨x,Or.inl rfl,ht⟩
    ·exact⟨z,Or.inr h,htz⟩
   ·rintro⟨z,rfl | h,htz⟩
    ·exact Or.inl htz
    ·exact Or.inr ⟨z,h,htz⟩
  ·simp only[ivs,bV,L,hxs];rw[b.2.2.2];ring
lemma bY (Y u:O) (r:ℕ) :
 2*(Y*exp (-(u+((r+1:ℕ):O)*log 2))) =Y*exp (-(u+(r:O)*log 2)):=by
 have b : -(u+((r+1:ℕ):O)*log 2)=-(u+(r:O)*log 2)-log 2:=by push_cast;ring
 rw[b,exp_sub,eX (_N :(0:O)< 2)];ring
lemma bZ {α : Type*} [DecidableEq α] {s t:Finset α} {f : α->O}
 (c:∀x,0<=f x):∑x∈s∪t,f x<=∑x∈s,f x+∑x∈t,f x:=by
 have h:=fb (s₁:=s) (s₂:=t) (f:=f);have b:0<=∑x∈s∩t,f x:=ea fun x _=>c x;linarith
lemma c0 {α β : Type*} [DecidableEq β] {s:Finset α}
 {t : α->Finset β} {f : β->O} (b:∀x,0<=f x) :
 ∑x∈s.biUnion t,f x<=∑i∈s,∑x∈t i,f x:=by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | insert a s ha ih=>
  rw[iS,i3 ha];exact (bZ b).trans (fd eR ih)
set_option maxHeartbeats 800000 in
lemma c4 {y:O} {a:ℕ} (ha:1<=a) (hy:(4000000:O)^8<=y)
 (hP:(a:O)^8<=y) :
 L a/(40*log 2*log (2*y)) <=∑p∈(Icc 1 ⌊2*y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (y/(p:O))∈LL a),(1:O)/(p:O):=by
 have h:0< y:=_P;have d:0< log 2:=_l a3;have hg:0< log (2*y):=et _L;have i:=bX a;set ivs:=bV (bB a);have B:∀b∈ivs,-log 2<=b.1/\b.2<=log (a:O):=by
  intro b K;have hh:=i.1 b K;have l:Set.Ico b.1 b.2⊆LL a:=fun x hx=>by
   rw[<- i.2.2.1];exact k6 K hx
  have h1:b.1∈LL a:=l ⟨eR,_L⟩;simp only[LL,eQ,fF]at h1;rcases h1 with⟨d1,hF,hS,_⟩;have hB : -log 2<=b.1:=(by linarith[f1 (by exact_mod_cast em hF:(1:O)<=d1)]);have hC:b.2<=log (a:O):=(by by_contra hM;push Not at hM;let hQ:=max b.1 ((b.2+log (a:O))/2);have w:=l ⟨eo _ _,max_lt _L _L⟩;simp only[LL,eQ,fF]at w;rcases w with⟨d2,hz,_,hI⟩;have h4:log (d2:O)<=log (a:O):=dM (_M (em hz)) (_M (el _O (ef hz)));linarith[ep b.1 (log (a:O)),hI,h4]);exact⟨hB,hC⟩
 let c:O × O->Finset ℕ:=fun b=>
  (Icc 1 ⌊2*y⌋₊).filter fun (p:ℕ)=>p.Prime/\log (y/(p:O))∈Set.Ico b.1 b.2
 have U:∀b∈ivs,(b.2-b.1)/(40*log 2*log (2*y))<=∑p∈c b,(1:O)/(p:O):=by
  intro b K;have hh:=i.1 b K;have hk:=B b K;let m:ℕ:=⌊(b.2-b.1)/log 2⌋₊;have h5:1<=m:=g2 (by push_cast;rw[js d];exact hh);have z:(b.2-b.1)/(2*log 2)<=(m:O):=by have C:=f6 ((b.2-b.1)/log 2);have hR:(1:O)<=(m:O):=_M h5;have:(b.2-b.1)/log 2<=2*(m:O):=_L;rw[mc _P];rw[mc d]at this;linarith
  let o:ℕ->O:=fun r=>y*exp (-(b.1+((r+1:ℕ):O)*log 2));let Qr:ℕ->Finset ℕ:=fun r=>(Ioc ⌊o r⌋₊ ⌊2*o r⌋₊).filter Nat.Prime;have W:∀r∈range m,Qr r⊆c b:=by
   intro r hr p T;rw[dN]at hr;simp only[Qr,dB,fw]at T;have h6:b.1+((r+1:ℕ):O)*log 2<=b.2:=by have D:(m:O)<=(b.2-b.1)/log 2:=fC (ed _L d.le);have:=(ma d).mp ((by exact_mod_cast hr:((r+1:ℕ):O)<=m).trans D);linarith
   have ho:0< o r:=_P;have N:o r< (p:O):=(by have h2:=f6 (o r);have h3:((⌊o r⌋₊ : O)+1)<=(p:O):=_M T.1.1;linarith);have e:(p:O)<=2*o r:=(by exact_mod_cast T.1.2:(p:O)<=(⌊2*o r⌋₊ : O)).trans (fC _P);have A:2*o r=y*exp (-(b.1+(r:O)*log 2)):=bY y b.1 r;have P:p<=⌊2*y⌋₊:=by
    apply g2
    rw[A]at e;have X:exp (-(b.1+(r:O)*log 2))<=2:=by
     have:(0:O)<=(r:O)*log 2:=_P
     calc exp (-(b.1+(r:O)*log 2))<=exp (log 2):=
           me.mpr (_l hk.1)
       _=2:=eX _N
    nlinarith
   simp only[c,dB,dT,fF];refine⟨⟨T.2.one_le,P⟩,T.2,?_,?_⟩
   ·rw[A]at e;have h1:exp (b.1+(r:O)*log 2)<=y/(p:O):=by
     rw[ma (_M T.2.pos)];have M:=dE e (ez (b.1+(r:O)*log 2)).le;rw[f0,<- gX,neg_add_cancel,lE,fv]at M;linarith
    have h2:=dM (ez _) h1;rw[iu]at h2;have:(0:O)<=(r:O)*log 2:=_P;linarith
   ·have h1:y/(p:O)< exp (b.1+((r+1:ℕ):O)*log 2):=by
     rw[mm (_M T.2.pos)];have M:=mul_lt_mul_of_pos_right N (ez (b.1+((r+1:ℕ):O)*log 2));simp only[o]at M;rw[f0,<- gX,neg_add_cancel,lE,fv]at M;linarith
    have h2:=jS (gN h (_M T.2.pos)) h1;rw[iu]at h2;linarith
  have Q:Set.PairwiseDisjoint (range m:Set ℕ) Qr:=by
   have u:∀r1 r2,r1< r2->Disjoint (Qr r1) (Qr r2):=by
    intro r1 r2 C;rw[eb];intro p hb hc;simp only[Qr,dB,fw]at hb hc;have h7:2*o r2<=o r1:=by
     rw[bY y b.1 r2];refine dA (me.mpr ?_) h.le;have:((r1+1:ℕ):O)<=(r2:O):=_M C;nlinarith
    have hl : ⌊2*o r2⌋₊<=⌊o r1⌋₊:=Nat.floor_mono h7;omega
   intro r1 _ r2 _ hL;dsimp only[Function.onFun];rcases gI hL with C | C
   ·exact u r1 r2 C
   ·exact (u r2 r1 C).symm
  have E:∀r∈range m,2000000<=o r/\2*o r<=2*y:=by
   intro r hr;rw[dN]at hr;have h6:b.1+((r+1:ℕ):O)*log 2<=log (a:O):=by have D:(m:O)<=(b.2-b.1)/log 2:=fC (ed _L d.le);have:=(ma d).mp ((by exact_mod_cast hr:((r+1:ℕ):O)<=m).trans D);linarith[hk.2]
   have j:(0:O)< a:=_M ha;have F:y/(a:O)<=o r:=by
    simp only[o];have hq:(a:O)⁻¹<=exp (-(b.1+((r+1:ℕ):O)*log 2)):=by have h1:exp (-log (a:O))=(a:O)⁻¹:=(by rw[lz,eX j]);rw[<- h1];exact me.mpr _L
    rw[ic];exact dA hq h.le
   have h8:(2000000:O)<=y/(a:O):=by
    rw[ma j];have hm:(a:O)<=y^((1:O)/8):=by
     calc (a:O)=((a:O)^(8:O))^((1:O)/8):=by
           rw[<- gE j.le];norm_num
       _<=y^((1:O)/8):=fx _P (by simpa using hP) _N
    have hs:(2000000:O)<=y^((7:O)/8):=by
     have h1:(2000000:O)^(8:O)<=y^(7:O):=by
      have ht:(2000000:O)^8<=y:=gf (by gcongr;norm_num) hy;have hD:(1:O)<=y:=gf _N hy;have hE:y<=y^(7:O):=by
       calc y=y^(1:O):=(rpow_one y).symm
         _<=y^(7:O):=eT hD _N
      exact (by simpa using ht:(2000000:O)^(8:O)<=y).trans hE
     calc (2000000:O)=((2000000:O)^(8:O))^((1:O)/8):=by
           rw[<- gE _N];norm_num
       _<=(y^(7:O))^((1:O)/8):=fx _P h1 _N
       _=y^((7:O)/8):=by rw[<- gE h.le];norm_num
    calc (2000000:O)*(a:O)<=y^((7:O)/8)*y^((1:O)/8):=
          en hs hm j.le _P
      _=y:=by rw[<- gF h];norm_num
   have Z:2*o r<=2*y:=by
    rw[bY y b.1 r];have X:exp (-(b.1+(r:O)*log 2))<=2:=by
     have:(0:O)<=(r:O)*log 2:=_P
     calc exp (-(b.1+(r:O)*log 2))<=exp (log 2):=
           me.mpr (_l hk.1)
       _=2:=eX _N
    nlinarith
   exact⟨h8.trans F,Z⟩
  calc (b.2-b.1)/(40*log 2*log (2*y))
      <= (m:O)*(1/(20*log (2*y))):=by rw[iE,mb _P _P];rw[mc _P]at z;nlinarith
    _=∑_r∈range m,(1:O)/(20*log (2*y)):=by rw[ex,fy,e3]
    _<=∑r∈range m,∑p∈Qr r,(1:O)/(p:O):=by
        refine dG fun r hr=>?_
        have hu:=E r hr;have hv:log (2*o r)<=log (2*y):=dM _L hu.2;have hw:1/(20*log (2*y))<=1/(20*log (2*o r)):=dX (by have:=et (_L :1< 2*o r);positivity) _L;exact hw.trans (af (o r) hu.1)
    _=∑p∈(range m).biUnion Qr,(1:O)/(p:O):=(kh Q).symm
    _<=∑p∈c b,(1:O)/(p:O):=dC (Finset.biUnion_subset.mpr W) fun _ _ _=>_P
 have G:ivs.Pairwise (fun he hf=>Disjoint (c he) (c hf)):=by
  refine List.Pairwise.imp (fun {he hf} C=>?_) i.2.1
  rw[eb];intro p hb hc;simp only[c,dB,fF]at hb hc;linarith[hb.2.2.2,hc.2.2.1]
 have H:∀(ls:List (O × O)),ls.Pairwise (fun he hf=>Disjoint (c he) (c hf)) -> (∀b∈ls,c b⊆(Icc 1 ⌊2*y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (y/(p:O))∈LL a)) -> (ls.map fun b=>∑p∈c b,(1:O)/(p:O)).sum <=∑p∈(Icc 1 ⌊2*y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (y/(p:O))∈LL a),(1:O)/(p:O):=by
  intro ls q l;have v:(ls.map fun b=>∑p∈c b,(1:O)/(p:O)).sum =∑p∈ls.foldr (fun b hn=>c b∪hn) ∅,(1:O)/(p:O):=by
   induction ls with
   | nil=>simp
   | cons b rest ih=>
    rw[ml]at q;simp only[je,jd,jk];rw[ih q.2 (fun jv h0=>l jv (gy _ h0))];have hd:Disjoint (c b) (rest.foldr (fun jv hn=>c jv∪hn) ∅):=by
     have hj:=q.1;clear ih l q;induction rest with
     | nil=>simp
     | cons jv rest2 ih2=>
      simp only[jk];rw[Finset.disjoint_union_right];exact⟨hj jv (fZ ..),ih2 fun kv hN=>hj kv (gy _ hN)⟩
    rw[jr hd]
  rw[v];refine dC ?_ (fun (p:ℕ) _ _=>by positivity)
  clear v;induction ls with
  | nil=>simp
  | cons b rest ih=>
   simp only[jk,Finset.union_subset_iff];exact⟨l b (fZ ..),ih (ml.mp q).2 fun jv h0=>l jv (gy _ h0)⟩
 have J:∀b∈ivs,c b⊆(Icc 1 ⌊2*y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (y/(p:O))∈LL a):=by intro b K p T;simp only[c,dB]at T ⊢;exact⟨T.1,T.2.1,by rw[<- i.2.2.1];exact k6 K T.2.2⟩
 have h9:L a/(40*log 2*log (2*y)) <=(ivs.map fun b=>∑p∈c b,(1:O)/(p:O)).sum:=by
  rw[<- i.2.2.2];have R:∀(ls:List (O × O)),(ls.map fun b=>b.2-b.1).sum/(40*log 2*log (2*y)) =(ls.map fun b=>(b.2-b.1)/(40*log 2*log (2*y))).sum:=(by intro ls;induction ls with | nil=>simp | cons _ _ ih=>simp[add_div,ih]);rw[R];have S:∀(ls:List (O × O)),(∀b∈ls,(b.2-b.1)/(40*log 2*log (2*y))<=∑p∈c b,(1:O)/(p:O)) -> (ls.map fun b=>(b.2-b.1)/(40*log 2*log (2*y))).sum <=(ls.map fun b=>∑p∈c b,(1:O)/(p:O)).sum:=by
   intro ls hA;induction ls with
   | nil=>simp
   | cons b rest ih=>
    simp only[je,jd];exact fd (hA b (fZ ..)) (ih fun jv h0=>hA jv (gy _ h0))
  exact S ivs U
 exact h9.trans (H ivs G J)
set_option maxHeartbeats 800000 in
lemma c5 {Y V:O} {a:ℕ} (hY:0< Y) (hV:4<=V) :
 ∑p∈(Icc ⌈V⌉₊ ⌊2*Y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (Y/(p:O))∈LL a),(1:O)/(p:O) <=(24/log 2)*L a/log V:=by
 have c:0< log 2:=_l a3;have u:0< log V:=et _L;have h:=bX a;set v:=bV (bB a);let d:O × O->Finset ℕ:=fun b=>
  (Icc ⌈V⌉₊ ⌊2*Y⌋₊).filter fun (p:ℕ)=>p.Prime/\log (Y/(p:O))∈Set.Ico b.1 b.2
 have i:∀b∈v,∑p∈d b,(1:O)/(p:O)<=(24/log 2)*(b.2-b.1)/log V:=by
  intro b G;have U:=h.1 b G;let m:ℕ:=⌈(b.2-b.1)/log 2⌉₊;have M:(m:O)<=2*(b.2-b.1)/log 2:=by have h6:(m:O)< (b.2-b.1)/log 2+1:=jm (ed _L c.le);have J:1<=(b.2-b.1)/log 2:=(js c).mpr U;have h2:(b.2-b.1)/log 2+1<=2*(b.2-b.1)/log 2:=(by rw[mul_div_assoc];linarith);linarith
  let W:ℕ->O:=fun r=>Y*exp (-(b.1+((r+1:ℕ):O)*log 2));let X:ℕ->O:=fun r=>max V (W r);let Z:ℕ->Finset ℕ:=fun r=>(Icc ⌈X r⌉₊ ⌊2*X r⌋₊).filter Nat.Prime;have h0:d b⊆(range m).biUnion Z:=by
   intro p C;simp only[d,dB,dT,fF]at C;have e:(0:O)< p:=_M C.2.1.pos;have D:V<=(p:O):=(g6 V).trans (_M C.1.1);let r:ℕ:=⌊(log (Y/(p:O))-b.1)/log 2⌋₊;have N:r< m:=by have J:(r:O)<=(log (Y/(p:O))-b.1)/log 2:=fC (ed (_l C.2.2.1) c.le);have h2:(log (Y/(p:O))-b.1)/log 2< (b.2-b.1)/log 2:=div_lt_div_of_pos_right (_l C.2.2.2) c;exact_mod_cast (J.trans_lt (h2.trans_le (g6 _)))
   rw[g4];refine⟨r,dN.mpr N,?_⟩;simp only[Z,dB,dT];have P:b.1+(r:O)*log 2<=log (Y/(p:O)):=by have J:(r:O)<=(log (Y/(p:O))-b.1)/log 2:=fC (ed (_l C.2.2.1) c.le);have:=(ma c).mp J;linarith
   have Q:log (Y/(p:O))< b.1+((r+1:ℕ):O)*log 2:=(by have h2:(log (Y/(p:O))-b.1)/log 2< ((r+1:ℕ):O):=(by push_cast;exact f6 _);have:=(mm c).mp h2;linarith);have y:W r<=(p:O):=(by have j:=me.mpr Q.le;rw[eX (gN hY e)]at j;have J:=(mc e).mp j;have l:=dE J (ez (-(b.1+((r+1:ℕ):O)*log 2))).le;rw[lH,<- gX,lJ,lE,gz]at l;exact l);have R:(p:O)<=2*W r:=(by rw[bY Y b.1 r];have j:=me.mpr P;rw[eX (gN hY e)]at j;have J:=(ma e).mp j;have l:=dE J (ez (-(b.1+(r:O)*log 2))).le;rw[lH,<- gX,lJ,lE,gz]at l;exact l);refine⟨⟨my.mpr (kC D y),?_⟩,C.2.1⟩;apply g2;linarith[ep V (W r)]
  calc ∑p∈d b,(1:O)/(p:O)
      <= ∑p∈(range m).biUnion Z,(1:O)/(p:O):=dC h0 fun _ _ _=>_P
    _<=∑r∈range m,∑p∈Z r,(1:O)/(p:O):=c0 fun _=>_P
    _<=∑_r∈range m,12/log V:=by
        refine dG fun r _=>?_
        have H:4<=X r:=hV.trans (eo _ _);have h7:=ai (X r) 2 H _N;have E:=dM _L (eo V (W r));have F:=dL (_N :(0:O)<=12) u E;exact (_L :∑p∈Z r,(1:O)/(p:O)<=12/log (X r)).trans F
    _=(m:O)*(12/log V):=by rw[ex,fy,e3]
    _<=(2*(b.2-b.1)/log 2)*(12/log V):=dE M _P
    _=(24/log 2)*(b.2-b.1)/log V:=by ring
 have z:(Icc ⌈V⌉₊ ⌊2*Y⌋₊).filter (fun (p:ℕ)=>p.Prime/\log (Y/(p:O))∈LL a) ⊆
  v.foldr (fun b T=>d b∪T) ∅:=by
  intro p C;simp only[dB]at C;have K:log (Y/(p:O))∈⋃ b∈v,Set.Ico b.1 b.2:=(by rw[h.2.2.1];exact C.2.2);simp only[eQ]at K;rcases K with⟨b,G,h3⟩;have S:p∈d b:=(by simp only[d,dB];exact⟨C.1,C.2.1,h3⟩);clear h i;generalize v=q at G ⊢;induction q with
  | nil=>simp at G
  | cons jv rest ih=>
   simp only[jk,ff];rcases kB.mp G with rfl | hrest
   ·exact Or.inl S
   ·exact Or.inr (ih hrest)
 have w:∀q:List (O × O),∑p∈q.foldr (fun b T=>d b∪T) ∅,(1:O)/(p:O) <=(q.map fun b=>∑p∈d b,(1:O)/(p:O)).sum:=by
  intro q;induction q with
  | nil=>simp
  | cons b rest ih=>
   simp only[jk,je,jd];exact (bZ fun (p:ℕ)=>by positivity).trans (fd eR ih)
 have o:(v.map fun b=>∑p∈d b,(1:O)/(p:O)).sum <=(24/log 2)*L a/log V:=by
  rw[<- h.2.2.2];have A:∀q:List (O × O),(24/log 2)*(q.map fun b=>b.2-b.1).sum/log V =(q.map fun b=>(24/log 2)*(b.2-b.1)/log V).sum:=(by intro q;induction q with | nil=>simp | cons _ _ ih=>simp[mul_add,add_div,ih]);rw[A];have B:∀q:List (O × O),(∀b∈q,∑p∈d b,(1:O)/(p:O)<=(24/log 2)*(b.2-b.1)/log V) -> (q.map fun b=>∑p∈d b,(1:O)/(p:O)).sum <=(q.map fun b=>(24/log 2)*(b.2-b.1)/log V).sum:=by
   intro q h4;induction q with
   | nil=>simp
   | cons b rest ih=>
    simp only[je,jd];exact fd (h4 b (fZ ..)) (ih fun jv h5=>h4 jv (gy _ h5))
  exact B v i
 exact (dC z fun (p:ℕ) _ _=>by positivity).trans ((w v).trans o)
def c6 (x j:ℕ):Finset ℕ:=(Icc 1 x).filter fun n=>j∈n.divisors.image (Nat.log 2)
lemma c7 {x j n:ℕ} :
 n∈c6 x j↔1<=n/\n<=x/\∃d∈n.divisors,2^j<=d/\d< 2^(j+1):=by
 simp only[c6,dB,dT,dW];constructor
 ·rintro⟨⟨h1,hx⟩,d,hd,hlog⟩;have c:d≠0:=(em hd).ne';have b:=(Nat.log_eq_iff (Or.inr ⟨by norm_num,c⟩)).mp hlog
  exact⟨h1,hx,d,hd,b.1,b.2⟩
 ·rintro⟨h1,hx,d,hd,hlo,hhi⟩;have c:d≠0:=(em hd).ne';refine⟨⟨h1,hx⟩,d,hd,?_⟩;exact (Nat.log_eq_iff (Or.inr ⟨by norm_num,c⟩)).mpr ⟨hlo,hhi⟩
set_option maxHeartbeats 800000 in
lemma c8 {X j:ℕ} (hj:1000<=j)
 (w:2^(7*j/8-2)<=X) (J:X< 2^(j+3)) :
 let B:=(Icc 1 X).filter fun b=>
  ∃q1 q2:ℕ,q1.Prime/\q2.Prime /\2^(j/4)< q1/\q1<=2^(3*j/8) /\2^(3*j/8)< q2/\q2< 2^(7*j/8-2)/\b=q1*q2
 (X:O)/(64000*log ((2^(j+1):ℕ):O))<=(B.card:O):=by
 classical
 intro B;have l:0< log ((2^(j+1):ℕ):O):=et (_M (show 1< 2^(j+1) from kH _O));let R:=Ico (j/4) (3*j/8);let D (r:ℕ):=(Ioc (2^r) (2^(r+1))).filter Nat.Prime;let M (q1:ℕ):=(Ioc (X/(2*q1)) (X/q1)).filter Nat.Prime;let d:=R.biUnion fun r=>(D r).biUnion fun q1=>(M q1).image fun q2=>(q1,q2);have u:∀p∈d,p.1*p.2∈B:=by
  intro ⟨q1,q2⟩ hp;simp only[d,g4,dW,jb]at hp;rcases hp with⟨r,K,q1',c,q2',i,rfl,rfl⟩;simp only[R,f3]at K;simp only[D,dB,fw]at c;simp only[M,dB,fw]at i;have y:2^(j/4)< q1':=gJ (dH _N K.1) c.1.1;have m:q1'<=2^(3*j/8):=c.1.2.trans (dH _N _O);have N:2^(3*j/8)< q2':=by
   have q:2^(3*j/8)<=X/(2*q1'):=by
    rw[dZ _O]
    calc 2^(3*j/8)*(2*q1')
        <= 2^(3*j/8)*(2*2^(3*j/8)):=dR _ (dR _ m)
      _=2^(3*j/8+3*j/8+1):=by rw[ee,ee];ring
      _<=2^(7*j/8-2):=dH _N _O
      _<=X:=w
   exact gJ q i.1.1
  have P:q2'< 2^(7*j/8-2):=by
   have q:X/q1'< 2^(7*j/8-2):=by
    rw[Nat.div_lt_iff_lt_mul _O]
    calc X< 2^(j+3):=J
      _<=2^((7*j/8-2)+j/4):=dH _N _O
      _=2^(7*j/8-2)*2^(j/4):=ee _ _ _
      _<=2^(7*j/8-2)*q1':=dR _ y.le
   exact gJ i.1.2 q
  have z:q1'*q2'<=X:=by
   calc q1'*q2'<=q1'*(X/q1'):=dR _ i.1.2
     _<=X:=lL X q1'
  simp only[B,dB,dT];exact⟨⟨fP c.2.pos i.2.pos,z⟩,q1',q2',c.2,i.2,y,m,N,P,rfl⟩
 have h5:Set.InjOn (fun p:ℕ × ℕ=>p.1*p.2) (d:Set (ℕ × ℕ)):=by
  intro ⟨a1,b1⟩ E ⟨a2,b2⟩ h2 heq;have hm:=u _ E;have ho:=u _ h2;simp only[eB,d,g4,dW,jb]at E h2;rcases E with⟨r1,hg,a1,c,b1,i,rfl,rfl⟩;rcases h2 with⟨r2,hh,a2,c',b2,i',rfl,rfl⟩;simp only[R,f3]at hg hh;simp only[D,dB,fw]at c c';simp only[M,dB,fw]at i i';have hc:a1< b2:=by
   have hq:a1<=2^(3*j/8):=c.1.2.trans (dH _N _O);have ht:2^(3*j/8)< b2:=by
    have q:2^(3*j/8)<=X/(2*a2):=by
     rw[dZ _O];have he:a2<=2^(3*j/8):=c'.1.2.trans (dH _N _O)
     calc 2^(3*j/8)*(2*a2)<=2^(3*j/8)*(2*2^(3*j/8)):=
           dR _ (dR _ he)
       _=2^(3*j/8+3*j/8+1):=by rw[ee,ee];ring
       _<=2^(7*j/8-2):=dH _N _O
       _<=X:=w
    exact gJ q i'.1.1
   omega
  have h6:a1∣a2*b2:=⟨b1,_L⟩;rcases c.2.dvd_mul.mp h6 with h | h
  ·have ha:a1=a2:=(eI c.2 c'.2).mp h;subst ha;exact iq rfl (fR c.2.pos heq)
  ·have ha:a1=b2:=(eI c.2 i'.2).mp h;omega
 have A:(d.card:O)<=(B.card:O):=by
  have o:d.card<=B.card:=by
   rw[<- gA h5];exact er fun n hn=>by
    rcases dW.mp hn with⟨p,hp,rfl⟩;exact u p hp
  exact_mod_cast o
 have Q:Set.PairwiseDisjoint (R:Set ℕ) (fun r=>(D r).biUnion fun q1=>(M q1).image fun q2=>(q1,q2)):=by
  intro r1 _ r2 _ hk;dsimp only[Function.onFun];rw[eb];intro ⟨q1,q2⟩ E h2;simp only[g4,dW,jb]at E h2;rcases E with⟨_,c,_,_,rfl,rfl⟩;rcases h2 with⟨_,i,_,_,hb,_⟩;subst hb;simp only[D,dB,fw]at c i;rcases gI hk with hlt | hgt
  ·have:2^(r1+1)<=2^r2:=dH _N _O;omega
  ·have:2^(r2+1)<=2^r1:=dH _N _O;omega
 have C:(d.card:O)=∑r∈R,∑q1∈D r,((M q1).card:O):=by
  have o:d.card=∑r∈R,∑q1∈D r,(M q1).card:=by
   rw[jV Q];refine dF rfl fun r _=>?_
   rw[jV]
   ·refine dF rfl fun q1 _=>fs _ (fun a b h=>(gv h).2)
   ·intro a _ b _ hl;dsimp only[Function.onFun];rw[eb];intro p E h2;simp only[dW]at E h2;rcases E with⟨_,_,rfl⟩;rcases h2 with⟨_,_,h⟩;exact hl (gv h).1.symm
  exact_mod_cast o
 have S:∀r∈R,∀q1∈D r,(X:O)/(40*(q1:O)*log ((2^(j+1):ℕ):O))<=((M q1).card:O):=by
  intro r K q1 c;simp only[R,f3]at K;simp only[D,dB,fw]at c;have e:(0:O)< (q1:O):=_M c.2.pos;let U:O:=(X:O)/(2*(q1:O));have m:q1<=2^(3*j/8):=c.1.2.trans (dH _N _O);have v:2000000<=U:=by
   dsimp only[U];rw[ma _P];have E:2000000*(2*q1)<=X:=by
    have hf:2000000*2<=2^22:=_N
    calc 2000000*(2*q1)=(2000000*2)*q1:=by ring
      _<=2^22*2^(3*j/8):=eH hf m
      _=2^(22+3*j/8):=(ee _ _ _).symm
      _<=2^(7*j/8-2):=dH _N _O
      _<=X:=w
   exact_mod_cast E
  have h7:=ag U v;have F : ⌊U⌋₊=X/(2*q1):=(by dsimp only[U];rw[show (2:O)*(q1:O)=((2*q1:ℕ):O) by push_cast;ring,Nat.floor_div_eq_div]);have G : ⌊2*U⌋₊=X/q1:=by
   have:2*U=(X:O)/(q1:O):=by dsimp only[U];field_simp [e.ne']
   rw[this,Nat.floor_div_eq_div]
  rw[F,G]at h7;have T:2*U<=((2^(j+1):ℕ):O):=by
   have:2*U=(X:O)/(q1:O):=by dsimp only[U];field_simp [e.ne']
   rw[this,mc e];have o:X<=2^(j+1)*q1:=by
    have W:4<=q1:=by
     have:2^2<=2^r:=dH _N _O
     omega
    calc X<=2^(j+3):=J.le
      _=2^(j+1)*4:=by rw[show j+3=(j+1)+2 by omega,ee];norm_num
      _<=2^(j+1)*q1:=dR _ W
   exact_mod_cast o
  have H:log (2*U)<=log ((2^(j+1):ℕ):O):=dM _L T;have h0:0< log (2*U):=et _L
  calc (X:O)/(40*(q1:O)*log ((2^(j+1):ℕ):O))
      = U/(20*log ((2^(j+1):ℕ):O)):=by dsimp only[U];field_simp [e.ne',l.ne'];ring
    _<=U/(20*log (2*U)):=dL _L _P _L
    _<=((M q1).card:O):=h7
 have Z:∀r∈R,1/(20*log ((2^(j+1):ℕ):O))<=∑q1∈D r,(1:O)/(q1:O):=by
  intro r K;simp only[R,f3]at K;have v:(2000000:O)<=((2^r:ℕ):O):=by
   have:2000000<=2^r:=(_N :2000000<=2^21).trans (dH _N _O)
   exact_mod_cast this
  have hs:=af ((2^r:ℕ):O) v;have F : ⌊((2^r:ℕ):O)⌋₊=2^r:=jz _;have G : ⌊2*((2^r:ℕ):O)⌋₊=2^(r+1):=(by rw[show (2:O)*((2^r:ℕ):O)=((2^(r+1):ℕ):O) by rw[fp];push_cast;ring,jz]);rw[F,G]at hs;have H:log (2*((2^r:ℕ):O))<=log ((2^(j+1):ℕ):O):=by
   apply dM _P
   rw[show (2:O)*((2^r:ℕ):O)=((2^(r+1):ℕ):O) by rw[fp];push_cast;ring]
   exact_mod_cast dH _N _O
  have h3:0< log (2*((2^r:ℕ):O)):=et _L;exact (dL eO _P _L).trans hs
 have h8:(j:O)/10<=(R.card:O):=by have o:j<=10*R.card:=(by simp only[R,kT];omega);have hR:(j:O)<=10*(R.card:O):=_M o;linarith
 have h9:log ((2^(j+1):ℕ):O)<=(j:O)+1:=by rw[gx,g7,fm];have E:=a4;push_cast;nlinarith
 have h4:(1:O)/80<=(R.card:O)/log ((2^(j+1):ℕ):O):=by rw[mb _N l];have hd:(1000:O)<=(j:O):=_M hj;linarith
 calc (X:O)/(64000*log ((2^(j+1):ℕ):O))
     = ((X:O)/(40*log ((2^(j+1):ℕ):O)))*((1/20)*(1/80)):=_R
   _<=((X:O)/(40*log ((2^(j+1):ℕ):O))) *((R.card:O)/(20*log ((2^(j+1):ℕ):O))):=by
       gcongr
       calc (1:O)/20*(1/80)=(1/20)*(1/80):=rfl
         _<=(1/20)*((R.card:O)/log ((2^(j+1):ℕ):O)):=by gcongr
         _=_:=by ring
   _=∑_r∈R,((X:O)/(40*log ((2^(j+1):ℕ):O))) *(1/(20*log ((2^(j+1):ℕ):O))):=by rw[ex,e3];ring
   _<=∑r∈R,((X:O)/(40*log ((2^(j+1):ℕ):O))) *∑q1∈D r,(1:O)/(q1:O):=by refine dG fun r K=>dA (Z r K) _P
   _<=∑r∈R,∑q1∈D r,((M q1).card:O):=by
       refine dG fun r K=>?_
       rw[dP];refine dG fun q1 c=>?_
       exact (_R :_=(X:O)/(40*(q1:O)*log ((2^(j+1):ℕ):O))).trans_le (S r K q1 c)
   _=(d.card:O):=C.symm
   _<=(B.card:O):=A
set_option maxHeartbeats 800000 in
lemma c9 :
 ∃c_HL:O,0< c_HL/\∀(x j:ℕ),1000<=j->2*j<=Nat.log 2 x -> ∀(A:Finset ℕ),(∀a∈A,1<=a/\(a:O)^8<=((2^j:ℕ):O)) -> c_HL*((x:O)/(log ((2^(j+1):ℕ):O))^2) *(∑a∈A,L a/(a:O))<=((c6 x j).card:O):=by
 classical
 obtain⟨h5,hX,hw⟩:=bz;let cB:O:=min (h5/2) (1/128000);refine⟨cB/(40*log 2),by positivity,?_⟩
 intro x j hj H8 A hA;set y:ℕ:=2^j;have Hc:0< y:=gr j;have H:y^2<=x:=by
  have Hk:2^(2*j)<=x:=(dH _N H8).trans (gB 2 (by
    intro h0;subst h0;simp at H8;omega))
  have Hr:y^2=2^(2*j):=(by dsimp only[y];rw[sq,<- ee,two_mul]);omega
 have h7:(4000000:O)^8<=(y:O):=by
  have C:4000000^8<=2^j:=by
   calc 4000000^8<=(2^22)^8:=fA _N 8
     _=2^176:=by norm_num
     _<=2^j:=dH _N _O
  exact_mod_cast C
 have hE:0< log ((2^(j+1):ℕ):O):=et (_M (show 1< 2^(j+1) from kH _O));have h9:2*(y:O)=((2^(j+1):ℕ):O):=by dsimp only[y];rw[fp];push_cast;ring
 let v (a:ℕ):Finset ℕ:=(Icc 1 (2*y)).filter fun p=>p.Prime/\log ((y:O)/(p:O))∈LL a;let i (a p:ℕ):Finset ℕ:=
  let X:=x/(a*p);if 8*y<=X then (Icc 1 X).filter fun b=>∀q ≤ 2*y,q.Prime->¬ q∣b
  else (Icc 1 X).filter fun b=>
    ∃q1 q2:ℕ,q1.Prime/\q2.Prime /\2^(j/4)< q1/\q1<=2^(3*j/8) /\2^(3*j/8)< q2/\q2< 2^(7*j/8-2)/\b=q1*q2
 let T:=A.biUnion fun a=>(v a).biUnion fun p=>(i a p).image fun b=>(a,p,b);have l:∀a∈A,a<=2^(j/8+1):=by intro a u;have h8:a^8<=2^j:=_M (hA a u).2;by_contra Hb;push Not at Hb;have J:(2^(j/8+1))^8<=a^8:=fA Hb.le 8;rw[<- it]at J;have h3:2^j< 2^((j/8+1)*8):=Nat.pow_lt_pow_right _N _O;omega
 have e:∀a∈A,∀p∈v a,2^(7*j/8-2)< p/\p<=2*y/\∃d∈a.divisors,y<=d*p/\d*p< 2*y:=by
  intro a u p Q;simp only[v,dB,dT]at Q;rcases Q with⟨⟨hY,H7⟩,m,hv⟩;simp only[LL,eQ,fF]at hv;rcases hv with⟨d,Z,hZ,H0⟩;have hc:0< d:=em Z;have W:d<=a:=el (hA a u).1 (ef Z);have E:(0:O)< (p:O):=_M m.pos;have D:(0:O)< (d:O):=_M hc;have he:(y:O)< (d:O)*(p:O):=by have w:=mF.mpr H0;rw[eX _P,eX D]at w;exact (mm E).mp w
  have hf:(d:O)*(p:O)<=2*(y:O):=(by have w:=me.mpr hZ;rw[exp_sub,eX D,eX _N,eX _P]at w;rw[mb _N E]at w;linarith);have hg:y< d*p:=_M he;have hh:d*p<=2*y:=_M hf;have hL:2^(7*j/8-2)< p:=(by have hM:=l a u;by_contra K;push Not at K;have:d*p<=2^(j/8+1)*2^(7*j/8-2):=eH (W.trans hM) K;rw[<- ee]at this;have:2^((j/8+1)+(7*j/8-2))<=2^j:=dH _N _O;omega);have hl:d*p≠2*y:=by
   intro Ho;have Hl:p∣2^(j+1):=by
    rw[show 2^(j+1)=2*y by dsimp only[y];rw[fp]]
    exact⟨d,_L⟩
   have hN:p=2:=(eI m Nat.prime_two).mp (m.dvd_of_dvd_pow Hl);have:2< 2^(7*j/8-2):=e9 (_N :2< 2^2) (dH _N _O);omega
  exact⟨hL,H7,d,Z,hg.le,ib hh hl⟩
 have hP:∀t∈T,t.1*t.2.1*t.2.2∈c6 x j:=by
  intro ⟨a,p,b⟩ ht;simp only[T,g4,dW,jb]at ht;rcases ht with⟨a',u,p',Q,b',R,rfl,rfl,rfl⟩;obtain⟨_,_,d,Z,hZ,H0⟩:=e a' u p' Q;have F:1<=b'/\b'<=x/(a'*p'):=(by dsimp only[i]at R;split_ifs at R <;> exact dT.mp (dB.mp R).1);have hQ:a'*p'*b'<=x:=(dR _ F.2).trans (lL x (a'*p'));have hF:1<=a'*p'*b':=fP (fP (hA a' u).1 (dB.mp Q).2.1.pos) F.1;rw[c7];refine⟨hF,hQ,d*p',?_,hZ,by rw[fp];exact H0⟩
  rw[fW];refine⟨?_,Nat.ne_of_gt hF⟩;obtain⟨k,hk⟩:=ef Z;exact⟨k*b',by rw[hk];ring⟩
 have H4:Set.InjOn (fun t:ℕ × ℕ × ℕ=>t.1*t.2.1*t.2.2) (T:Set (ℕ × ℕ × ℕ)):=by
  intro ⟨a1,S,b1⟩ w ⟨U,p2,b2⟩ J Ho;simp only[eB,T,g4,dW,jb]at w J;rcases w with⟨a1,hx,S,hY,b1,Hn,rfl,rfl,rfl⟩;rcases J with⟨U,hy,p2,hN,b2,h6,rfl,rfl,rfl⟩;have c:=(dB.mp hY).2.1;have hm:=(dB.mp hN).2.1;obtain⟨Hf,hz,_⟩:=e a1 hx S hY;obtain⟨Hg,Hh,_⟩:=e U hy p2 hN;have Hd:=l a1 hx;have He:=l U hy;have z:¬ S∣b2:=by
   dsimp only[i]at h6;split_ifs at h6 with hbig
   ·exact (dB.mp h6).2 S hz c
   ·rcases (dB.mp h6).2 with⟨q1,q2,H1,H2,_,Hi,_,Hj,rfl⟩;intro Z;rcases c.dvd_mul.mp Z with h | h
    ·have:=(eI c H1).mp h
     have:2^(3*j/8)<=2^(7*j/8-2):=dH _N _O
     omega
    ·have:=(eI c H2).mp h;omega
  have B:¬ S∣U:=(by intro Z;have K:=el (hA U hy).1 Z;have:2^(j/8+1)<=2^(7*j/8-2):=dH _N _O;omega);have hR:S=p2:=by
   have Z:S∣U*p2*b2:=⟨a1*b1,_L⟩;rcases c.dvd_mul.mp Z with h12 | R
   ·rcases c.dvd_mul.mp h12 with u | Q
    ·exact absurd u B
    ·exact (eI c hm).mp Q
   ·exact absurd R z
  subst hR;have ho:a1*b1=U*b2:=by have w:S*(a1*b1)=S*(U*b2):=_L;exact fR c.pos w
  have hI:∀a' b',a'∈A -> (∀q:ℕ,q.Prime->q∣b'->2^(j/4)< q)->Nat.Coprime a' b':=by
   intro a' b' u' R';refine Nat.coprime_of_dvd fun q hq Hp hD=>?_
   have w:=(el (hA a' u').1 Hp).trans (l a' u');have J:=R' q hq hD;have h3:2^(j/8+1)<=2^(j/4):=dH _N _O;omega
  have G:∀a' p' b',b'∈i a' p'->∀q:ℕ,q.Prime->q∣b'->2^(j/4)< q:=by
   intro a' p' b' R' q hq hD;dsimp only[i]at R';split_ifs at R'
   ·by_contra K;push Not at K;have H5:q<=2*y:=K.trans (by
     calc 2^(j/4)<=2^j:=dH _N _O
       _<=2*2^j:=by omega)
    exact (dB.mp R').2 q H5 hq hD
   ·rcases (dB.mp R').2 with⟨q1,q2,H1,H2,hB,_,hC,_,rfl⟩;rcases hq.dvd_mul.mp hD with h | h
    ·rw[(eI hq H1).mp h];exact hB
    ·rw[(eI hq H2).mp h];exact gJ (dH _N _O) hC
  have hS:a1=U:=Nat.dvd_antisymm ((hI a1 b2 hx (G U S b2 h6)).dvd_of_dvd_mul_right ⟨b1,_L⟩) ((hI U b1 hy (G a1 S b1 Hn)).dvd_of_dvd_mul_right ⟨b2,_L⟩);subst hS;have hT:b1=b2:=fR (hA a1 hx).1 ho;exact iq rfl (iq rfl hT)
 have M:(T.card:O)<=((c6 x j).card:O):=by
  have C:T.card<=(c6 x j).card:=by
   rw[<- gA H4];exact er fun n hn=>by
    rcases dW.mp hn with⟨t,ht,rfl⟩;exact hP t ht
  exact_mod_cast C
 have h4:(T.card:O)=∑a∈A,∑p∈v a,((i a p).card:O):=by
  have C:T.card=∑a∈A,∑p∈v a,(i a p).card:=by
   rw[jV]
   ·refine dF rfl fun a _=>?_
    rw[jV]
    ·refine dF rfl fun p _=>
      fs _ (fun b1 b2 h=>(gv (gv h).2).2)
    ·intro S _ p2 _ H9;dsimp only[Function.onFun];rw[eb];intro t w J;simp only[dW]at w J;rcases w with⟨_,_,rfl⟩;rcases J with⟨_,_,h⟩;exact H9 (gv (gv h).2).1.symm
   ·intro a1 _ U _ Ha;dsimp only[Function.onFun];rw[eb];intro t w J;simp only[g4,dW]at w J;rcases w with⟨_,_,_,_,rfl⟩;rcases J with⟨_,_,_,_,h⟩;exact Ha (gv h).1.symm
  exact_mod_cast C
 have hU:∀a∈A,∀p∈v a,cB*((x:O)/((a:O)*(p:O)))/log ((2^(j+1):ℕ):O)<=((i a p).card:O):=by
  intro a u p Q;set X:=x/(a*p);have hu:0< a:=(hA a u).1;have m:=(dB.mp Q).2.1;obtain⟨_,H3,_⟩:=e a u p Q;have o:0< a*p:=fP hu m.pos;have hV:2^(7*j/8-2)<=X:=by
   rw[dZ o]
   calc 2^(7*j/8-2)*(a*p)
       <= 2^(7*j/8-2)*(2^(j/8+1)*(2*2^j)):=dR _ (eH (l a u) H3)
     _=2^(7*j/8-2+(j/8+1)+j+1):=by rw[ee,ee,ee];ring
     _<=2^(2*j):=dH _N _O
     _=y^2:=by dsimp only[y];rw[sq,<- ee,two_mul]
     _<=x:=H
  have H6:(x:O)/((a:O)*(p:O))<=2*(X:O):=(by have w:x< (X+1)*(a*p):=(by have Hq:x % (a*p)< a*p:=dY x o;have Hs:a*p*X+x % (a*p)=x:=gu x (a*p);nlinarith);have J:X+1<=2*X:=(by have:1<=2^(7*j/8-2):=fY;omega);have h3:x<=2*X*(a*p):=w.le.trans (eE _ J);have N:(0:O)< (a:O)*(p:O):=_M o;rw[mc N];have Ht:(x:O)<=2*(X:O)*((a:O)*(p:O)):=_M h3;linarith);dsimp only[i];split_ifs with hbig
  ·have hr:=hw X (2*y) (by have:=fY (n:=j);omega) _O;have P:((2*y:ℕ):O)=((2^(j+1):ℕ):O):=(by dsimp only[y];rw[fp]);rw[P]at hr
   calc cB*((x:O)/((a:O)*(p:O)))/log ((2^(j+1):ℕ):O)
       <= (h5/2)*(2*(X:O))/log ((2^(j+1):ℕ):O):=by gcongr;exact i7 _ _
     _=h5*(X:O)/log ((2^(j+1):ℕ):O):=_R
     _<=(aK X (2*y):O):=hr
  ·push Not at hbig
   have hW:X< 2^(j+3):=by
    calc X< 8*2^j:=hbig
      _=2^(j+3):=by rw[ee];ring
   have hs:=c8 hj hV hW
   calc cB*((x:O)/((a:O)*(p:O)))/log ((2^(j+1):ℕ):O)
       <= (1/128000)*(2*(X:O))/log ((2^(j+1):ℕ):O):=by gcongr;exact gw _ _
     _=(X:O)/(64000*log ((2^(j+1):ℕ):O)):=_R
     _<=_:=hs
 calc (cB/(40*log 2))*((x:O)/(log ((2^(j+1):ℕ):O))^2) *
         (∑a∈A,L a/(a:O))
     = ∑a∈A,(cB*(x:O)/log ((2^(j+1):ℕ):O))*(1/(a:O)) *(L a/(40*log 2*log (2*(y:O)))):=by rw[dP];refine dF rfl fun a _=>by rw[h9];ring
   _<=∑a∈A,(cB*(x:O)/log ((2^(j+1):ℕ):O))*(1/(a:O)) *∑p∈v a,(1:O)/(p:O):=by
       refine dG fun a u=>dA ?_ _P
       have hv:=c4 (hA a u).1 h7 (hA a u).2;have Hm : ⌊2*(y:O)⌋₊=2*y:=(by rw[show (2:O)*(y:O)=((2*y:ℕ):O) by push_cast;ring,jz]);simpa only[v,Hm] using hv
   _<=∑a∈A,∑p∈v a,((i a p).card:O):=by
       refine dG fun a u=>?_
       rw[dP];refine dG fun p Q=>?_
       exact (_R :_=cB*((x:O)/((a:O)*(p:O)))/log ((2^(j+1):ℕ):O)).trans_le (hU a u p Q)
   _=(T.card:O):=h4.symm
   _<=((c6 x j).card:O):=M
def ca (M k:ℕ) (b:Fin k->ℕ):Finset ℕ:=(Fintype.piFinset fun i:Fin k=>(aA (M+i)).powersetCard (b i)).image
  fun S=>∏i:Fin k,∏p∈S i,p
lemma cb {i j:ℕ} (h:i≠j):Disjoint (aA i) (aA j):=by
 rw[eb];intro p hi d;unfold aA at hi d;by_cases b:i=0
 ·simp[b]at hi
 by_cases c:j=0
 ·simp[c]at d
 rw[gc b,dB,fw]at hi;rw[gc c,dB,fw]at d;rcases gI h with hlt | hgt
 ·have:=aC.monotone (_O :i<=j-1);omega
 ·have:=aC.monotone (_O :j<=i-1);omega
lemma cc {i p:ℕ} (b:p∈aA i):p.Prime:=by
 unfold aA at b;split_ifs at b
 ·simp at b
 ·exact (dB.mp b).2
lemma cd (S:Finset ℕ) (h:∀p∈S,p.Prime) :
 (∏p∈S,p).primeFactors=S:=by
 induction S using eW with
 | empty=>simp
 | @insert q S hq ih=>
  have c:q.Prime:=h q (ev q S);have d:∀p∈S,p.Prime:=fun p e=>h p (fa e);have b:∏p∈S,p≠0:=mi.mpr fun p e=>(d p e).ne_zero;rw[fN hq,jh c.ne_zero b,c.primeFactors,ih d];ext x;simp
lemma ce (M k:ℕ) (b:Fin k->ℕ) :
 Set.InjOn (fun S:(i:Fin k)->Finset ℕ=>∏i:Fin k,∏p∈S i,p) (Fintype.piFinset fun i:Fin k=>(aA (M+i)).powersetCard (b i):Set _):=by
 intro z v A w y;simp only[eB,e5,fU]at v w;have m:∀S:(i:Fin k)->Finset ℕ,(∀i,S i⊆aA (M+i)) -> (∏i:Fin k,∏p∈S i,p).primeFactors=univ.biUnion S:=by
  intro S l;have e:Set.PairwiseDisjoint ((univ:Finset (Fin k)):Set (Fin k)) S:=fun i _ j _ o=>
   (cb (_O :M+i.1≠M+j.1)).mono (l i) (l j)
  rw[<- kw e];exact cd _ fun p q=>by
   rcases g4.mp q with⟨i,_,h⟩;exact cc (l i h)
 have c:=fT Nat.primeFactors y;rw[m z (fun i=>(v i).1),m A (fun i=>(w i).1)]at c;funext i;ext p;have d:∀S:(j:Fin k)->Finset ℕ,(∀j,S j⊆aA (M+j)) -> (p∈univ.biUnion S/\p∈aA (M+i)↔p∈S i):=by
  intro S l;constructor
  ·rintro⟨hbi,h⟩;rcases g4.mp hbi with⟨j,_,u⟩;by_cases o:j=i
   ·rwa[<- o]
   ·exfalso;exact eb.mp (cb (_O :M+j.1≠M+i.1)) (l j u) h
  ·intro q;exact⟨g4.mpr ⟨i,dJ i,q⟩,(l i) q⟩
 rw[<- d z (fun j=>(v j).1),<- d A (fun j=>(w j).1),c]
lemma cf (M k:ℕ) {b1 b2:Fin k->ℕ} (A:b1≠b2) :
 Disjoint (ca M k b1) (ca M k b2):=by
 rw[eb];intro a o q;simp only[ca,dW,e5,fU]at o q;rcases o with⟨w,e,rfl⟩;rcases q with⟨y,h,z⟩;have d:∀S:(i:Fin k)->Finset ℕ,(∀i,S i⊆aA (M+i)) -> ∀i:Fin k,((∏j:Fin k,∏p∈S j,p).primeFactors∩aA (M+i))=S i:=by
  intro S l i;have b:Set.PairwiseDisjoint ((univ:Finset (Fin k)):Set (Fin k)) S:=fun B _ C _ m=>
   (cb (_O :M+B.1≠M+C.1)).mono (l B) (l C)
  rw[<- kw b,cd _ fun p u=>by
   rcases g4.mp u with⟨j,_,c⟩;exact cc (l j c)]
  ext p;simp only[Finset.mem_inter,g4,dJ,dV];constructor
  ·rintro⟨⟨j,c⟩,hpi⟩;by_cases m:j=i
   ·rwa[<- m]
   ·exfalso;exact eb.mp (cb (_O :M+j.1≠M+i.1)) (l j c) hpi
  ·intro u;exact⟨⟨i,u⟩,l i u⟩
 apply A;funext i
 have o:=d w (fun j=>(e j).1) i;have q:=d y (fun j=>(h j).1) i;have v:((∏j:Fin k,∏p∈w j,p).primeFactors∩aA (M+i)) =((∏j:Fin k,∏p∈y j,p).primeFactors∩aA (M+i)):=by rw[z]
 have:w i=y i:=o.symm.trans (v.trans q)
 rw[<- (e i).2,<- (h i).2,this]
set_option maxHeartbeats 800000 in
lemma cg {M k:ℕ} {b:Fin k->ℕ} {a:ℕ} (J:a∈ca M k b) :
 1<=a/\Squarefree a/\a.primeFactors.card=∑i:Fin k,b i /\
 a.divisors.card=2^(∑i:Fin k,b i) /\
 log (a:O)<=∑i:Fin k,(b i:O)*log (az (M+i):O):=by
 simp only[ca,dW,e5,fU]at J;rcases J with⟨S,y,rfl⟩;have u:Set.PairwiseDisjoint ((univ:Finset (Fin k)):Set (Fin k)) S:=fun G _ H _ K=>
  (cb (_O :M+G.1≠M+H.1)).mono (y G).1 (y H).1
 have o:(∏i:Fin k,∏p∈S i,p)=∏p∈univ.biUnion S,p:=(kw u).symm;have c:∀p∈univ.biUnion S,p.Prime:=fun p l=>by
  rcases g4.mp l with⟨i,_,F⟩;exact cc ((y i).1 F)
 have z:1<=∏p∈univ.biUnion S,p:=Finset.one_le_prod' fun p l=>(c p l).one_le;have A:Squarefree (∏p∈univ.biUnion S,p):=by
  have v:∀T:Finset ℕ,(∀p∈T,p.Prime)->Squarefree (∏p∈T,p):=by
   intro T;induction T using eW with
   | empty=>intro _;simp
   | @insert q T hq ih=>
    intro E;have d:=E q (ev q T);have h:∀p∈T,p.Prime:=fun p l=>E p (fa l);rw[fN hq,mq];refine⟨fL fun p l=>?_,d.squarefree,ih h⟩;exact (ft d (h p l)).mpr (fun B=>hq (B ▸ l))
  exact v _ c
 have C:(∏p∈univ.biUnion S,p).primeFactors=univ.biUnion S:=cd _ c;have e:(∏p∈univ.biUnion S,p).primeFactors.card=∑i:Fin k,b i:=by rw[C,jV u];exact dF rfl fun i _=>(y i).2
 have j:(∏p∈univ.biUnion S,p).divisors.card=2^(∑i:Fin k,b i):=by
  rw[<- e];have v:∀T:Finset ℕ,(∀p∈T,p.Prime)->(∏p∈T,p).divisors.card=2^T.card:=by
   intro T;induction T using eW with
   | empty=>intro _;simp
   | @insert q T hq ih=>
    intro E;have d:=E q (ev q T);have h:∀p∈T,p.Prime:=fun p l=>E p (fa l);have D:Nat.Coprime q (∏p∈T,p):=fL fun p l=>
     (ft d (h p l)).mpr (fun B=>hq (B ▸ l))
    rw[fN hq,D.card_divisors_mul,d.divisors,la d.ne_one.symm,ih h,fE hq,fp]
  rw[C];exact v _ c
 have w:log ((∏i:Fin k,∏p∈S i,p:ℕ):O) <=∑i:Fin k,(b i:O)*log (az (M+i):O):=by
  rw[fu,iP (fun i _=>by
   exact_mod_cast mi.mpr fun p l=>(cc ((y i).1 l)).ne_zero)]
  refine dG fun i _=>?_
  rw[fu,iP (fun p l=>by exact_mod_cast (cc ((y i).1 l)).ne_zero)]
  calc ∑p∈S i,log (p:O)
      <= ∑_p∈S i,log (az (M+i):O):=by
        refine dG fun p l=>dM (_M (cc ((y i).1 l)).pos) ?_
        have m:=(y i).1 l;unfold aA at m;split_ifs at m
        · simp at m
        · exact_mod_cast (fw.mp (dB.mp m).1).2
    _=(b i:O)*log (az (M+i):O):=by rw[ex,(y i).2,e3]
 rw[<- o]at z A e j;exact⟨z,A,e,j,w⟩
set_option maxHeartbeats 800000 in
lemma ch (D:Finset ℕ) (L:O) (A:0< L)
 (C:∀p∈D,L<=(p:O)) :
 ∀r:ℕ,0<=(∑p∈D,(1:O)/(p:O))-(r:O)/L -> ((∑p∈D,(1:O)/(p:O))-(r:O)/L)^r/(r.factorial:O) <=∑T∈D.powersetCard r,(1:O)/((∏p∈T,p:ℕ):O):=by
 intro r;induction r with
 | zero=>intro _;simp
 | succ r ih=>
  intro y;have b:0<=(∑p∈D,(1:O)/(p:O))-(r:O)/L:=by
   have:(r:O)/L<=((r+1:ℕ):O)/L:=dI (by push_cast;linarith) A.le
   linarith
  have m:((r+1:ℕ):O)*∑U∈D.powersetCard (r+1),(1:O)/((∏p∈U,p:ℕ):O) =∑T∈D.powersetCard r,((1:O)/((∏p∈T,p:ℕ):O)) *∑p∈D \ T,(1:O)/(p:O):=by
   have h:((r+1:ℕ):O)*∑U∈D.powersetCard (r+1),(1:O)/((∏p∈U,p:ℕ):O) =∑U∈D.powersetCard (r+1),∑_p∈U,(1:O)/((∏q∈U,q:ℕ):O):=by
    rw[dP];refine dF rfl fun U v=>?_
    rw[ex,(fU.mp v).2,e3]
   rw[h];simp_rw [dP];rw[gY,gY];refine fh (fun x _=>⟨x.1.erase x.2,x.2⟩) ?_ ?_ ?_ ?_
   ·intro ⟨U,p⟩ hx;simp only[fg,fU,gj]at hx ⊢;refine⟨⟨(Finset.erase_subset p U).trans hx.1.1,by rw[kV hx.2,hx.1.2];omega⟩,hx.1.1 hx.2,io p U⟩
   ·intro ⟨U1,p1⟩ h1 ⟨U2,p2⟩ h2 heq;simp only[fG,iD]at heq;rcases heq with⟨v,rfl⟩;simp only[fg]at h1 h2;have:insert p1 (U1.erase p1)=insert p1 (U2.erase p1):=fT (insert p1) v;rw[gD h1.2,gD h2.2]at this;subst this;rfl
   ·intro ⟨T,p⟩ hx;simp only[fg,fU,gj]at hx;refine⟨⟨insert p T,p⟩,?_,?_⟩
    ·simp only[fg,fU,ga,true_or,and_true];exact⟨Finset.insert_subset hx.2.1 hx.1.1,by rw[fE hx.2.2,hx.1.2]⟩
    ·simp only[fG,iD,and_true];exact iQ hx.2.2
   ·intro ⟨U,p⟩ hx;simp only[fg]at hx;have d:∏q∈U,q=p*∏q∈U.erase p,q:=(gk U _ hx.2).symm;rw[d,g3];ring
  have i:∀T∈D.powersetCard r,(∑p∈D,(1:O)/(p:O))-(r:O)/L<=∑p∈D \ T,(1:O)/(p:O):=by
   intro T z;rcases fU.mp z with⟨j,w⟩;have l:∑p∈D \ T,(1:O)/(p:O)+∑p∈T,(1:O)/(p:O) =∑p∈D,(1:O)/(p:O):=sum_sdiff j;have o:∑p∈T,(1:O)/(p:O)<=(r:O)/L:=by
    calc ∑p∈T,(1:O)/(p:O)<=∑_p∈T,(1:O)/L:=
          dG fun p B=>dX A (C p (j B))
      _=(r:O)/L:=by rw[ex,w,e3];ring
   linarith
  have e:((∑p∈D,(1:O)/(p:O))-((r+1:ℕ):O)/L)^(r+1)/((r+1).factorial:O) <=((∑p∈D,(1:O)/(p:O))-(r:O)/L)^r/(r.factorial:O) *(((∑p∈D,(1:O)/(p:O))-(r:O)/L)/((r+1:ℕ):O)):=by
   rw[e6,g3,fc];have u:(∑p∈D,(1:O)/(p:O))-((r+1:ℕ):O)/L <=(∑p∈D,(1:O)/(p:O))-(r:O)/L:=by
    have:(r:O)/L<=((r+1:ℕ):O)/L:=dI (by push_cast;linarith) A.le
    linarith
   have c:=m9 y u (r+1);rw[fc]at c
   calc _=(((∑p∈D,(1:O)/(p:O))-((r+1:ℕ):O)/L)^r *
           ((∑p∈D,(1:O)/(p:O))-((r+1:ℕ):O)/L)) /
         (((r+1:ℕ):O)*(r.factorial:O)):=rfl
     _<=(((∑p∈D,(1:O)/(p:O))-(r:O)/L)^r *((∑p∈D,(1:O)/(p:O))-(r:O)/L)) /(((r+1:ℕ):O)*(r.factorial:O)):=dI c _P
     _=_:=by ring
  refine e.trans ?_
  rw[gl,mc (_P :(0:O)< ((r+1:ℕ):O)),e8 _ ((r+1:ℕ):O),m]
  calc ((∑p∈D,(1:O)/(p:O))-(r:O)/L)^r/(r.factorial:O) *
          ((∑p∈D,(1:O)/(p:O))-(r:O)/L)
      <= (∑T∈D.powersetCard r,(1:O)/((∏p∈T,p:ℕ):O)) *((∑p∈D,(1:O)/(p:O))-(r:O)/L):=dE (ih b) b
    _=∑T∈D.powersetCard r,((1:O)/((∏p∈T,p:ℕ):O)) *((∑p∈D,(1:O)/(p:O))-(r:O)/L):=jn ..
    _<=_:=dG fun T z=>dA (i T z) _P
set_option maxHeartbeats 800000 in
lemma ci {k:ℕ} (b:Fin k->ℕ)
 (j:∑i:Fin k,b i=k) (hb:∀i:Fin k,b i<=200*(200+i.1)) :
 (2*log 2)^k/(2*∏i:Fin k,((b i).factorial:O)) <=∑a∈ca 200 k b,(a.divisors.card:O)/(a:O):=by
 have e:0< log 2:=_l a3;have w:∑a∈ca 200 k b,(a.divisors.card:O)/(a:O) =(2:O)^k*∏i:Fin k,∑T∈(aA (200+i.1)).powersetCard (b i),(1:O)/((∏p∈T,p:ℕ):O):=by
  have K:∑a∈ca 200 k b,(a.divisors.card:O)/(a:O) =(2:O)^k*∑a∈ca 200 k b,(1:O)/(a:O):=by
   rw[dP];refine dF rfl fun a ha=>?_
   have hd:=(cg ha).2.2.2.1;rw[j]at hd;rw[hd];push_cast;ring
  rw[K];congr 1;unfold ca;rw[fr (fun S1 B S2 J Q=>ce 200 k b B J Q)];have l:(∏i:Fin k,∑T∈(aA (200+i.1)).powersetCard (b i),(1:O)/((∏p∈T,p:ℕ):O)) =∑S∈Fintype.piFinset (fun i:Fin k=>(aA (200+i.1)).powersetCard (b i)),∏i:Fin k,(1:O)/((∏p∈S i,p:ℕ):O):=j9 ..;rw[l];refine dF rfl fun S _=>?_
  rw[fu,g9,<- gL];exact f9 rfl fun i _=>(g9 _).symm
 rw[w];have z:∀i:Fin k,(log 2)^(b i)/((b i).factorial:O)*exp (-(1/(2:O)^(i.1+10))) <=∑T∈(aA (200+i.1)).powersetCard (b i),(1:O)/((∏p∈T,p:ℕ):O):=by
  intro i;let c:O:=(az (200+i.1-1):O);have d:0< c:=(by dsimp only[c];exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (aD (200+i.1-1)));have E:∀p∈aA (200+i.1),c<=(p:O):=by intro p hp;unfold aA at hp;rw[gc _O]at hp;dsimp only[c];exact_mod_cast (fw.mp (dB.mp hp).1).1.le
  have o:(2:O)^(99+i.1)<=log c:=(by have h:=(aJ (200+i.1-1) _O).1;have M:(((200+i.1-1:ℕ):ℤ)-100)=((99+i.1:ℕ):ℤ):=_O;rw[M,fo]at h;exact h);have H':4*(((b i:O)+1)^2)*(2:O)^(i.1+10)<=c:=by
   have F:(log c)^3/6<=c:=by
    have j:=kl (show 0<=log c by linarith[show (0:O)< (2:O)^(99+i.1) by positivity]) 4
    simp[jt,Nat.factorial]at j;rw[eX d]at j;have G:0<=log c:=_l (show (0:O)< (2:O)^(99+i.1) by positivity)
    nlinarith[gR (log c)]
   have B:4*(((b i:O)+1)^2)*(2:O)^(i.1+10)<=((2:O)^(99+i.1))^3/6:=by
    have h7:(b i:O)+1<=200*(200+(i.1:O))+1:=by
     have:(b i:O)<=(200*(200+i.1):ℕ):=_M (hb i)
     push_cast at this;linarith
    have h8:(200*(200+(i.1:O))+1)<=(2:O)^(20+i.1):=by
     have N:200*(200+i.1)+1<=2^(20+i.1):=by
      induction i.1 with
      | zero=>norm_num
      | succ n ih=>
       calc 200*(200+(n+1))+1<=2*(200*(200+n)+1):=by omega
         _<=2*2^(20+n):=dR 2 ih
         _=2^(20+(n+1)):=by rw[show 20+(n+1)=(20+n)+1 by omega,fp]
     exact_mod_cast N
    calc 4*(((b i:O)+1)^2)*(2:O)^(i.1+10)
        <= 4*((2:O)^(20+i.1))^2*(2:O)^(i.1+10):=by gcongr;linarith
      _=4*(2:O)^(50+3*i.1):=by rw[<- it,f0,<- ee];congr 2;ring
      _<=(2:O)^(297+3*i.1)/6:=by
          rw[ma _N]
          calc 4*(2:O)^(50+3*i.1)*6=24*(2:O)^(50+3*i.1):=by ring
            _<=(2:O)^247*(2:O)^(50+3*i.1):=by gcongr;norm_num
            _=(2:O)^(297+3*i.1):=by rw[<- ee];congr 1;ring
      _=((2:O)^(99+i.1))^3/6:=by rw[<- it];congr 2;ring
   exact B.trans ((dI (m9 _P o 3) _N).trans F)
  have m:log 2-((b i:O)+1)/c <=(∑p∈aA (200+i.1),(1:O)/(p:O))-(b i:O)/c:=by
   have h9:=aH (200+i.1) _O;have q:c<=((az (200+i.1)+1:ℕ):O):=by
    have:az (200+i.1-1)<=az (200+i.1)+1:=(aC.monotone _O).trans (Nat.le_succ _)
    dsimp only[c];exact_mod_cast this
   have P:1/((az (200+i.1)+1:ℕ):O)<=1/c:=dX d q;have Q:((b i:O)+1)/c=(b i:O)/c+1/c:=_R;linarith
  have A:((b i:O)+1)/c<=log 2/4:=by
   rw[mc d];have B:(1:O)<=((b i:O)+1):=_l (dK (α:=O) (b i));have J:(8:O)<=(2:O)^(i.1+10):=by
    have:8<=2^(i.1+10):=(_N :8<=2^3).trans (dH _N _O)
    exact_mod_cast this
   nlinarith[a3]
  have G:0<=(∑p∈aA (200+i.1),(1:O)/(p:O))-(b i:O)/c:=_L;have Z:=ch (aA (200+i.1)) c d E (b i) G;refine (?_:(log 2)^(b i)/((b i).factorial:O)*exp (-(1/(2:O)^(i.1+10)))<=_).trans Z;rw[gm];refine dI ?_ _P;have u:log 2*exp (-(((b i:O)+1)*4/c))<=log 2-((b i:O)+1)/c:=by
   let δ:=((b i:O)+1)/(log 2*c);have hδ_le : δ<=1/4:=(by dsimp only[δ];rw[mc _P];linarith[(mc d).mp A]);have B:exp (-2*δ)<=1 - δ:=(by have h:=fB (2*δ);have v:exp (-2*δ)=(exp (2*δ))⁻¹:=(by rw[<- lz];congr 1;ring);rw[v,inv_le_comm₀ (ez _) _L];have P:(1 - δ)⁻¹<=1+2*δ:=(by rw[inv_le_iff_one_le_mul₀' _L];nlinarith[show 0<=δ by dsimp only[δ];positivity]);linarith);have J : -(((b i:O)+1)*4/c)<=-2*δ:=(by dsimp only[δ];have R : -(2*(((b i:O)+1)/(log 2*c)))=-2*(((b i:O)+1)/(log 2*c)):=_R;rw[<- R,neg_le_neg_iff];have:2*(((b i:O)+1)/(log 2*c))=(((b i:O)+1)/c)*(2/log 2):=_R;rw[this];have hc:2/log 2<=4:=(by rw[mc e];linarith[a3]);have h0:0<=((b i:O)+1)/c:=_P;have h6:((b i:O)+1)*4/c=((b i:O)+1)/c*4:=_R;nlinarith);have h3:=(me.mpr J).trans B;have h4:=dA h3 e.le;have h5:log 2*(1 - δ)=log 2-((b i:O)+1)/c:=(by dsimp only[δ];field_simp [e.ne',d.ne']);linarith
  have C:=m9 _P (u.trans m) (b i);rw[eP,<- gg]at C;refine gf ?_ C;refine dA (me.mpr ?_) _P;have D:(b i:O)*(((b i:O)+1)*4/c)<=1/(2:O)^(i.1+10):=(by rw[gl,mb d _P];have B:(b i:O)<=(b i:O)+1:=_L;nlinarith);linarith
 have y:=im (s:=univ) (fun i _=>by positivity) (fun i _=>z i)
 rw[prod_mul_distrib,gM,kq,j,<- exp_sum]at y;have U:(1:O)/2<=exp (∑i:Fin k,-(1/(2:O)^(i.1+10))):=by
  have W:∑i:Fin k,(1:O)/(2:O)^(i.1+10)<=1/2:=by
   calc ∑i:Fin k,(1:O)/(2:O)^(i.1+10)
       = (1/1024:O)*∑i:Fin k,((1:O)/2)^i.1:=by rw[dP];refine dF rfl fun i _=>by rw[ee,i6];norm_num
     _=(1/1024:O)*∑r∈range k,((1:O)/2)^r:=by congr 1;exact fh (fun i _=>i.1) (fun i _=>dN.mpr i.2) (fun _ _ _ _ h=>dQ h) (fun r hr=>⟨⟨r,dN.mp hr⟩,dJ _,rfl⟩) (fun _ _=>rfl)
     _<=(1/1024:O)*2:=by rw[fO (_N :((1:O)/2)≠1) k];have G:0<=((1:O)/2)^k:=_P;have:(((1:O)/2)^k-1)/((1:O)/2-1)=2*(1-((1:O)/2)^k):=_R;rw[this];nlinarith
     _<=1/2:=by norm_num
  have D : -(1/2:O)<=∑i:Fin k,-(1/(2:O)^(i.1+10)):=(by rw[iw];linarith);have B:=fB (1/2:O);have J:(1:O)/2<=exp (-(1/2:O)):=by
   rw[lz,le_inv_comm₀ _N (ez _)];have:exp (1/2:O)<=2:=by have he:(exp (1/2:O))^2=exp 1:=(by rw[<- gg];norm_num);have hf:exp 1<=3:=_l gT;nlinarith[ez (1/2:O)]
   linarith
  exact J.trans (me.mpr D)
 have X:=dA y (_P :(0:O)<=(2:O)^k)
 calc (2*log 2)^k/(2*∏i:Fin k,((b i).factorial:O))
     = (2:O)^k*((log 2)^k/(∏i:Fin k,((b i).factorial:O))*(1/2)):=by rw[eP];ring
   _<=(2:O)^k*((log 2)^k/(∏i:Fin k,((b i).factorial:O)) *exp (∑i:Fin k,-(1/(2:O)^(i.1+10)))):=by gcongr
   _<=_:=X
def cj {k:ℕ} (b:Fin k->ℕ):O:=∑h:Fin k,(2:O)^(((∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),b i:ℕ):ℤ)-(h.1:ℤ)-1)
set_option maxHeartbeats 800000 in
lemma ck {k:ℕ} (hk:1<=k) (b:Fin k->ℕ) (Hj:∑i:Fin k,b i=k) :
 ∑a∈ca 200 k b,(W a:O)/(a:O) <=(2^108*(2*log 2)^k/∏i:Fin k,((b i).factorial:O))*cj b:=by
 classical
 let l (h:ℕ):ℕ:=∑i∈univ.filter (fun i:Fin k=>i.1< h),b i;have hj:l 0=0:=by simp[l]
 have G:l k=k:=by
  have:univ.filter (fun i:Fin k=>i.1< k)=univ:=by ext i;simp[i.2]
  simp[l,this,Hj]
 have M:∀h:Fin k,l (h.1+1)=l h.1+b h:=by intro h;have hs:univ.filter (fun i:Fin k=>i.1< h.1+1) =insert h (univ.filter (fun i:Fin k=>i.1< h.1)):=(by ext i;simp only[dB,dJ,dV,ga,Fin.ext_iff];omega);simp only[l,hs];rw[i3 (by simp)];ring
 have u:Monotone l:=by
  intro a b HT;exact Finset.sum_le_sum_of_subset (fun i hi=>dB.mpr
   ⟨dJ i,e9 (dB.mp hi).2 HT⟩)
 have ht:∀r:Fin k,∃h:ℕ,h< k/\l h<=r.1/\r.1< l (h+1):=by
  intro r;have H5:∃m:ℕ,r.1< l m:=⟨k,by rw[G];exact r.2⟩
  let m0:=Nat.find H5;have H6:r.1< l m0:=jF H5;have hR:1<=m0:=(by by_contra h0;push Not at h0;have:m0=0:=_O;rw[this,hj]at H6;omega);have HI:m0<=k:=Nat.find_min' H5 (by rw[G];exact r.2);have Hk:l (m0-1)<=r.1:=(by by_contra hE;push Not at hE;exact jW H5 (_O :m0-1< m0) hE);exact⟨m0-1,by omega,Hk,by rwa[eN hR]⟩
 let E:Fin k->Fin k:=fun r=>⟨(ht r).choose,(ht r).choose_spec.1⟩;have y:∀r:Fin k,l (E r).1<=r.1/\r.1< l ((E r).1+1):=fun r=>(ht r).choose_spec.2;let P:=Fintype.piFinset fun r:Fin k=>aA (200+(E r).1);have Hz:∀a∈ca 200 k b,(∏i:Fin k,((b i).factorial:O))*((W a:O)/(a:O)) <=∑p∈P.filter (fun p=>∏r:Fin k,p r=a),(((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
     |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:O) /
    ((∏r:Fin k,p r:ℕ):O):=by
  intro a ha;have H7:=ha;simp only[ca,dW,e5,fU]at ha;rcases ha with⟨S,hS,rfl⟩;let w:=P.filter fun p=>Function.Injective p/\∀r:Fin k,p r∈S (E r);have h5:w⊆P.filter (fun p=>∏r:Fin k,p r=∏i:Fin k,∏q∈S i,q):=by
   intro p X;simp only[w,dB]at X ⊢;refine⟨X.1,?_⟩;have hT:∏r:Fin k,p r=∏h:Fin k,∏r∈univ.filter (fun r:Fin k=>E r=h),p r:=(lP (fun _ _=>dJ _) _).symm;rw[hT];refine f9 rfl fun h _=>?_
   have hv:(univ.filter (fun r:Fin k=>E r=h)).card=b h:=by
    have N:univ.filter (fun r:Fin k=>E r=h) =univ.filter (fun r:Fin k=>l h.1<=r.1/\r.1< l (h.1+1)):=by
     ext r;simp only[dB,dJ,dV];constructor
     ·intro he;rw[<- he];exact y r
     ·rintro⟨h1,h2⟩;by_contra T;rcases gI (jP T) with hE | hgt
      ·have:=(y r).2;have:=u (_O :(E r).1+1<=h.1);omega
      ·have:=(y r).1;have:=u (_O :h.1+1<=(E r).1);omega
    rw[N];have hU:(univ.filter (fun r:Fin k=>l h.1<=r.1/\r.1< l (h.1+1))).card =(Ico (l h.1) (l (h.1+1))).card:=hO (fun r _=>r.1) (fun r D=>by simp at D ⊢;exact D) (fun _ _ _ _ h=>dQ h)
      (fun m hm=>⟨⟨m,e9 (f3.mp hm).2 ((u h.2).trans_eq G)⟩,by simp[f3.mp hm],rfl⟩)
    rw[hU,kT,M h];omega
   have B:(univ.filter (fun r:Fin k=>E r=h)).image p=S h:=by
    apply m3
    ·intro q hq;rcases dW.mp hq with⟨r,D,rfl⟩;rw[<- (dB.mp D).2];exact X.2.2 r
    ·rw[fs _ X.2.1,hv,(hS h).2]
   rw[<- B,jR (fun _ _ _ _ h=>X.2.1 h)]
  have Hl:∀p∈w,W (∏i:Fin k,∏q∈S i,q) =((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
     |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:=by
   intro p X;have h8:=(dB.mp (h5 X)).2;have J:=(dB.mp X).2.1;have z:∀r:Fin k,(p r).Prime:=fun r=>cc ((hS (E r)).1 ((dB.mp X).2.2 r));have h6:∀Y:Finset (Fin k),(∏r∈Y,p r)∈(∏r:Fin k,p r).divisors:=by
    intro Y;rw[fW];refine⟨?_,mi.mpr fun r _=>(z r).ne_zero⟩;exact⟨∏r∈univ \ Y,p r,by
     rw[<- kD (Finset.disjoint_sdiff),Finset.union_sdiff_of_subset (Finset.subset_univ Y)]⟩
   have h7:Function.Injective (fun Y:Finset (Fin k)=>∏r∈Y,p r):=by
    intro Y1 Y2 hY;dsimp only at hY;have HA:(∏r∈Y1,p r).primeFactors=Y1.image p:=by
     have B:∏r∈Y1,p r=∏q∈Y1.image p,q:=(jR (f:=fun x:ℕ=>x) (g:=p) (fun _ _ _ _ h=>J h)).symm;rw[B];exact cd _ fun q hq=>by
      rcases dW.mp hq with⟨r,_,rfl⟩;exact z r
    have HB:(∏r∈Y2,p r).primeFactors=Y2.image p:=by
     have B:∏r∈Y2,p r=∏q∈Y2.image p,q:=(jR (f:=fun x:ℕ=>x) (g:=p) (fun _ _ _ _ h=>J h)).symm;rw[B];exact cd _ fun q hq=>by
      rcases dW.mp hq with⟨r,_,rfl⟩;exact z r
    have Hh:Y1.image p=Y2.image p:=(by rw[<- HA,<- HB,hY]);ext r;constructor <;> intro D
    ·have hm:=iL p D;rw[Hh,dW]at hm;rcases hm with⟨r',D',A⟩;rwa[<- J A]
    ·have hm:=iL p D;rw[<- Hh,dW]at hm;rcases hm with⟨r',D',A⟩;rwa[<- J A]
   have Q:∀d∈(∏r:Fin k,p r).divisors,∃Y:Finset (Fin k),∏r∈Y,p r=d:=by
    intro d hd;have hF:0< d:=em hd;have hw:Squarefree (∏r:Fin k,p r):=(by rw[h8];exact (cg H7).2.1);have H8:Squarefree d:=hw.squarefree_of_dvd (ef hd);have Hm:d=∏q∈d.primeFactors,q:=by
     conv_lhs=>rw[<- ew hF.ne',Finsupp.prod]
     rw[ej];refine f9 rfl fun q hq=>?_
     have K:=dD hq;have h1:d.factorization q=1:=by
      have HU:d.factorization q<=1:=by
       by_contra h2;push Not at h2;have HK:q*q∣d:=by
        have:=gd d q
        exact (show q*q∣q^d.factorization q by
         rw[<- sq];exact jj q h2).trans this
       exact K.ne_one (mn.mp (H8 q HK))
      have HV:1<=d.factorization q:=(by rw[md]at hq;exact (K.dvd_iff_one_le_factorization hF.ne').mp hq.2.1);omega
     rw[h1,pow_one]
    refine⟨univ.filter (fun r:Fin k=>p r∈d.primeFactors),?_⟩
    have hy:∏r∈univ.filter (fun r:Fin k=>p r∈d.primeFactors),p r =∏q∈(univ.filter (fun r:Fin k=>p r∈d.primeFactors)).image p,q:=(jR (f:=fun x:ℕ=>x) (g:=p) (fun _ _ _ _ h=>J h)).symm;rw[hy];conv_rhs=>rw[Hm]
    congr 1;ext q;simp only[dW,dB,dJ,dV];constructor
    ·rintro⟨r,D,rfl⟩;exact D
    ·intro hq;have h9:q∣∏r:Fin k,p r:=(dS hq).trans (ef hd);have hL:q∈(∏r:Fin k,p r).primeFactors:=md.mpr ⟨dD hq,h9,mi.mpr fun r _=>(z r).ne_zero⟩;have hV:(∏r:Fin k,p r).primeFactors=univ.image p:=by
      have h1:∏r:Fin k,p r=∏q∈univ.image p,q:=(jR (f:=fun x:ℕ=>x) (g:=p) (fun _ _ _ _ h=>J h)).symm;rw[h1];exact cd _ fun q' hq'=>by
       rcases dW.mp hq' with⟨r,_,rfl⟩;exact z r
     rw[hV,dW]at hL;rcases hL with⟨r,_,rfl⟩;exact⟨r,hq,rfl⟩
   rw[<- h8];unfold W;symm;refine hO (fun YZ _=>(∏r∈YZ.1,p r,∏r∈YZ.2,p r)) ?_ ?_ ?_
   ·intro ⟨Y,Z⟩ h3;simp only[dB,dJ,dV,ki]at h3 ⊢;refine⟨⟨h6 Y,h6 Z⟩,?_⟩;rw[fu,fu,iP (fun r _=>by exact_mod_cast (z r).ne_zero),iP (fun r _=>by exact_mod_cast (z r).ne_zero)]
    exact h3
   ·intro ⟨Y1,Z1⟩ _ ⟨Y2,Z2⟩ _ A;exact iq (h7 (gv A).1) (h7 (gv A).2)
   ·intro ⟨d1,d2⟩ hd;simp only[dB,ki]at hd;obtain⟨Y,rfl⟩:=Q d1 hd.1.1;obtain⟨Z,rfl⟩:=Q d2 hd.1.2;refine⟨⟨Y,Z⟩,?_,rfl⟩;simp only[dB,dJ,dV];have h:=hd.2;rwa[fu,fu,iP (fun r _=>by exact_mod_cast (z r).ne_zero),iP (fun r _=>by exact_mod_cast (z r).ne_zero)]at h
  have hl:w.card=∏i:Fin k,(b i).factorial:=by
   let F (h:Fin k):=univ.filter (fun r:Fin k=>E r=h);have R:∀h:Fin k,(F h).card=b h:=by
    intro h;have N:F h=univ.filter (fun r:Fin k=>l h.1<=r.1/\r.1< l (h.1+1)):=by
     ext r;simp only[F,dB,dJ,dV];constructor
     ·intro he;rw[<- he];exact y r
     ·rintro⟨h1,h2⟩;by_contra T;rcases gI (jP T) with hE | hgt
      ·have:=(y r).2;have:=u (_O :(E r).1+1<=h.1);omega
      ·have:=(y r).1;have:=u (_O :h.1+1<=(E r).1);omega
    rw[N];have hU:(univ.filter (fun r:Fin k=>l h.1<=r.1/\r.1< l (h.1+1))).card =(Ico (l h.1) (l (h.1+1))).card:=hO (fun r _=>r.1) (fun r D=>by simp at D ⊢;exact D) (fun _ _ _ _ h=>dQ h)
      (fun m hm=>⟨⟨m,e9 (f3.mp hm).2 ((u h.2).trans_eq G)⟩,by simp[f3.mp hm],rfl⟩)
    rw[hU,kT,M h];omega
   let hf:=(h:Fin k)->(F h ≃ S h);have hN:Fintype.card hf=∏h:Fin k,(b h).factorial:=by
    rw[Fintype.card_pi];refine f9 rfl fun h _=>?_
    have HL:Fintype.card (F h)=Fintype.card (S h):=(by simp only[jO,R h,(hS h).2]);rw[Fintype.card_equiv (Fintype.equivOfCardEq HL),jO,R h]
   rw[<- hN];symm;refine hO (fun (e:hf) _=>fun r:Fin k=>(e (E r) ⟨r,dB.mpr ⟨dJ r,rfl⟩⟩).1) ?_ ?_ ?_
   ·intro e _;simp only[w,P,dB,e5];refine⟨fun r=>(hS (E r)).1 (e (E r) ⟨r,dB.mpr ⟨dJ r,rfl⟩⟩).2,?_,fun r=>(e (E r) ⟨r,dB.mpr ⟨dJ r,rfl⟩⟩).2⟩;intro r1 r2 D;dsimp only at D;have Hn:E r1=E r2:=by by_contra T;have HM:=(hS (E r1)).1 (e (E r1) ⟨r1,dB.mpr ⟨dJ r1,rfl⟩⟩).2;have HC:=(hS (E r2)).1 (e (E r2) ⟨r2,dB.mpr ⟨dJ r2,rfl⟩⟩).2;rw[<- D]at HC;exact eb.mp (cb (_O :200+(E r1).1≠200+(E r2).1)) HM HC
    let h:=E r1;have H9:E r1=h:=rfl;have hM:E r2=h:=Hn.symm;have HD:(e h ⟨r1,dB.mpr ⟨dJ r1,H9⟩⟩).1 =(e h ⟨r2,dB.mpr ⟨dJ r2,hM⟩⟩).1:=(by have Ho:∀(h':Fin k) (hh:E r2=h'),(e (E r2) ⟨r2,dB.mpr ⟨dJ r2,rfl⟩⟩).1 =(e h' ⟨r2,dB.mpr ⟨dJ r2,hh⟩⟩).1:=(by intro h' hh;subst hh;rfl);rw[<- Ho h hM];exact D);exact fT Subtype.val ((e h).injective (i9 HD))
   ·intro e1 _ e2 _ A;funext h;apply Equiv.ext;intro ⟨r,D⟩;have HN:E r=h:=(dB.mp D).2;subst HN;exact i9 (gH A r)
   ·intro p X;simp only[w,dB]at X;let e:hf:=fun h=>Equiv.ofBijective (fun r:F h=>⟨p r.1,Eq.mp (congrArg (fun x=>p r.1∈S x) (dB.mp r.2).2) (X.2.2 r.1)⟩)
     ((ke _).mpr ⟨fun r1 r2 D=>
      i9 (X.2.1 (fT Subtype.val D)),by simp[jO,R h,(hS h).2]⟩)
    refine⟨e,dJ _,?_⟩
    funext r;rfl
  calc (∏i:Fin k,((b i).factorial:O))*((W (∏i:Fin k,∏q∈S i,q):O)/((∏i:Fin k,∏q∈S i,q:ℕ):O))
      = ∑_p∈w,(W (∏i:Fin k,∏q∈S i,q):O)/((∏i:Fin k,∏q∈S i,q:ℕ):O):=by rw[ex,hl,e3];conv_rhs=>rw[fu]
    _=∑p∈w,(((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
            |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:O) /
          ((∏r:Fin k,p r:ℕ):O):=by
        refine dF rfl fun p X=>?_
        rw[Hl p X,(dB.mp (h5 X)).2]
    _<=_:=dC h5 fun _ _ _=>_P
 have hP:(∏i:Fin k,((b i).factorial:O))*∑a∈ca 200 k b,(W a:O)/(a:O) <=∑YZ:Finset (Fin k) × Finset (Fin k),∑p∈P.filter (fun p=>|∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2),(1:O)/((∏r:Fin k,p r:ℕ):O):=by
  rw[dP]
  calc _<=∑a∈ca 200 k b,∑p∈P.filter (fun p=>∏r:Fin k,p r=a),
            (((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
              |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:O) /
            ((∏r:Fin k,p r:ℕ):O):=dG Hz
    _=∑p∈(ca 200 k b).biUnion (fun a=>P.filter (fun p=>∏r:Fin k,p r=a)),(((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
              |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:O) /
            ((∏r:Fin k,p r:ℕ):O):=by
          rw[kh];intro a1 _ a2 _ T;dsimp only[Function.onFun];rw[eb];intro p h1 h2;exact T ((dB.mp h1).2.symm.trans (dB.mp h2).2)
    _<=∑p∈P,(((univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
              |∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2).card:O) /
            ((∏r:Fin k,p r:ℕ):O):=
          dC (Finset.biUnion_subset.mpr fun _ _=>fj _ _) (fun _ _ _=>by positivity)
    _=_:=by
          simp_rw [Finset.card_eq_sum_ones,jp,eF,kM,g9]
          simp_rw [f8]
          rw[hH]
 have hz:∀YZ:Finset (Fin k) × Finset (Fin k),YZ.1=YZ.2 -> ∑p∈P.filter (fun p=>|∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2),(1:O)/((∏r:Fin k,p r:ℕ):O)<=(log 2)^k:=by
  intro ⟨Y,Z⟩ h3
  calc _<=∑p∈P,(1:O)/((∏r:Fin k,p r:ℕ):O):=
        dC (fj _ _) (fun _ _ _=>by positivity)
    _=∏r:Fin k,∑q∈aA (200+(E r).1),(1:O)/(q:O):=by
        rw[j9];refine dF rfl fun p _=>?_
        rw[fu,g9,<- gL];exact f9 rfl fun r _=>(g9 _).symm
    _<=∏_r:Fin k,log 2:=im (fun _ _=>ea fun _ _=>by positivity) (fun r _=>aG (200+(E r).1) _O)
    _=(log 2)^k:=by simp
 have hA:∀YZ:Finset (Fin k) × Finset (Fin k),∀I:Fin k,(I∈YZ.1/\I ∉ YZ.2 ∨ I ∉ YZ.1/\I∈YZ.2) -> ∑p∈P.filter (fun p=>|∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2),(1:O)/((∏r:Fin k,p r:ℕ):O) <=(2^106/(2:O)^(200+(E I).1))*(log 2)^(k-1):=by
  intro ⟨Y,Z⟩ I hI;let hn:=Fintype.piFinset fun r:{r:Fin k // r≠I}=>aA (200+(E r.1).1);let v (p':(r:{r:Fin k // r≠I})->ℕ) (q:ℕ):Fin k->ℕ:=fun r=>if h:r=I then q else p' ⟨r,h⟩;have Ha:∑p∈P.filter (fun p=>|∑r∈Y,log (p r:O) - ∑r∈Z,log (p r:O)|<=log 2),(1:O)/((∏r:Fin k,p r:ℕ):O) =∑p'∈hn,((1:O)/((∏r:{r:Fin k // r≠I},p' r:ℕ):O)) *∑q∈(aA (200+(E I).1)).filter (fun q=>
     |∑r∈Y,log (v p' q r:O) - ∑r∈Z,log (v p' q r:O)|<=log 2),
     (1:O)/(q:O):=by
   simp_rw [dP]
   rw[gY];refine fh (fun p _=>⟨fun r=>p r.1,p I⟩) ?_ ?_ ?_ ?_
   ·intro p X;simp only[dB,P,e5,fg,hn]at X ⊢;have HO:v (fun r=>p r.1) (p I)=p:=(by funext r;dsimp only[v];split_ifs with h;exact h ▸ rfl;rfl);exact⟨fun r=>X.1 r.1,X.1 I,by rw[HO];exact X.2⟩
   ·intro p1 _ p2 _ A;simp only[fG,iD]at A;funext r;by_cases D:r=I
    ·rw[D,A.2]
    ·exact gH A.1 ⟨r,D⟩
   ·intro ⟨p',q⟩ hx;simp only[fg,hn,e5,dB]at hx;refine⟨v p' q,?_,?_⟩
    ·simp only[dB,P,e5];refine⟨fun r=>by dsimp only[v];split_ifs with h;rw[h];exact hx.2.1;exact hx.1 ⟨r,h⟩,hx.2.2⟩
    ·simp only[fG,iD];refine⟨by funext r;dsimp only[v];rw[eA r.2],by dsimp only[v];rw[eG rfl]⟩
   ·intro p _;have h8:∏r:Fin k,p r=p I*∏r:{r:Fin k // r≠I},p r.1:=by
     rw[<- gk univ p (dJ I)];congr 1;exact hJ (fun r D=>⟨r,(gS.mp D).1⟩) (fun _ _=>dJ _) (fun _ _ _ _ h=>fT Subtype.val h) (fun r _=>⟨r.1,gS.mpr ⟨r.2,dJ _⟩,rfl⟩) (fun _ _=>rfl)
    rw[h8,g3];ring
  rw[Ha];have Hp:∀p'∈hn,∑q∈(aA (200+(E I).1)).filter (fun q=>
    |∑r∈Y,log (v p' q r:O) - ∑r∈Z,log (v p' q r:O)|<=log 2),
    (1:O)/(q:O)<=2^106/(2:O)^(200+(E I).1):=by
   intro p' _;let c:O:=
    if I∈Y then (∑r∈Z,log (v p' 1 r:O))-(∑r∈Y.erase I,log (v p' 1 r:O))
    else (∑r∈Y,log (v p' 1 r:O))-(∑r∈Z.erase I,log (v p' 1 r:O))
   let U:O:=max (exp (c-log 2)) (az (200+(E I).1-1):O);have Hb:4<=U:=(by have Hq:4<=az (200+(E I).1-1):=(_O :4<=200+(E I).1-1+1).trans (aE _);exact (by exact_mod_cast Hq:(4:O)<=_).trans (ep _ _));have Hc:(aA (200+(E I).1)).filter (fun q=>
    |∑r∈Y,log (v p' q r:O) - ∑r∈Z,log (v p' q r:O)|<=log 2) ⊆
    (Icc ⌈U⌉₊ ⌊4*U⌋₊).filter Nat.Prime:=by
    intro q hq;simp only[dB,dT]at hq ⊢;have K:=cc hq.1;have Hd:az (200+(E I).1-1)< q:=by have h1:=hq.1;unfold aA at h1;rw[gc _O]at h1;exact (fw.mp (dB.mp h1).1).1
    have hW : |log (q:O)-c|<=log 2:=by
     have C:∀S:Finset (Fin k),I ∉ S -> ∑r∈S,log (v p' q r:O)=∑r∈S,log (v p' 1 r:O):=by
      intro S hS;refine dF rfl fun r D=>?_
      have T:r≠I:=fun h=>hS (h ▸ D);simp only[v,eA T]
     rcases hI with⟨H4,Hw⟩ | ⟨H4,Hw⟩
     ·have hc:c=(∑r∈Z,log (v p' 1 r:O))-(∑r∈Y.erase I,log (v p' 1 r:O)):=iM H4;have hY:∑r∈Y,log (v p' q r:O)=log (q:O)+∑r∈Y.erase I,log (v p' 1 r:O):=(by rw[<- fJ Y _ H4,C _ (io I Y)];simp[v]);have hZ:=C Z Hw;have h2:=hq.2;rw[hY,hZ]at h2;rw[hc];convert h2 using 2;ring
     ·have hc:c=(∑r∈Y,log (v p' 1 r:O))-(∑r∈Z.erase I,log (v p' 1 r:O)):=gc H4;have hZ:∑r∈Z,log (v p' q r:O)=log (q:O)+∑r∈Z.erase I,log (v p' 1 r:O):=(by rw[<- fJ Z _ Hw,C _ (io I Z)];simp[v]);have hY:=C Y H4;have h2:=hq.2;rw[hY,hZ]at h2;rw[hc,<- abs_neg];convert h2 using 2;ring
    have hX:exp (c-log 2)<=(q:O):=by
     have:=(ms.mp hW).1
     have:=me.mpr (_L :c-log 2<=log (q:O))
     rwa[eX (_M K.pos)]at this
    have H0:(q:O)<=4*exp (c-log 2):=by
     have:=(ms.mp hW).2
     have:=me.mpr (_L :log (q:O)<=c+log 2)
     rw[eX (_M K.pos)]at this;have h4:4*exp (c-log 2)=exp (c+log 2):=(by rw[show c+log 2=log 4+(c-log 2) by rw[a5];ring,gX,eX _N]);linarith
    refine⟨⟨my.mpr (kC hX (_M Hd.le)),g2 (H0.trans (dA (eo _ _) _N))⟩,K⟩
   have HE:=ai U 4 Hb _N;have Hr:(2:O)^(((200+(E I).1-1:ℕ):ℤ)-100)<=log U:=(aJ (200+(E I).1-1) _O).1.trans (dM (_M (aD _)) (ep _ _))
   calc _<=∑q∈(Icc ⌈U⌉₊ ⌊4*U⌋₊).filter Nat.Prime,(1:O)/(q:O):=
         dC Hc (fun _ _ _=>by positivity)
     _<=6*4/log U:=HE
     _=24/log U:=by norm_num
     _<=24/(2:O)^(((200+(E I).1-1:ℕ):ℤ)-100):=dL _N _P Hr
     _<=2^106/(2:O)^(200+(E I).1):=by
         have A:(2:O)^(((200+(E I).1-1:ℕ):ℤ)-100) =(2:O)^(200+(E I).1)/(2:O)^101:=(by rw[show (((200+(E I).1-1:ℕ):ℤ)-100)=((200+(E I).1:ℕ):ℤ)-101 by omega,mE (_N :(2:O)≠0),fo,show (101:ℤ)=(101:ℕ) by rfl,fo]);rw[A,div_div_eq_mul_div];refine dI ?_ _P
         norm_num
  calc _<=∑p'∈hn,((1:O)/((∏r:{r:Fin k // r≠I},p' r:ℕ):O)) *
            (2^106/(2:O)^(200+(E I).1)):=
        dG fun p' X'=>dA (Hp p' X') _P
    _=(2^106/(2:O)^(200+(E I).1)) *∏r:{r:Fin k // r≠I},∑q∈aA (200+(E r.1).1),(1:O)/(q:O):=by
        rw[<- jn,e8,j9];congr 1;refine dF rfl fun p' _=>?_
        rw[fu,g9,<- gL];exact f9 rfl fun r _=>(g9 _).symm
    _<=(2^106/(2:O)^(200+(E I).1))*(log 2)^(k-1):=by
        refine dA ?_ _P
        calc ∏r:{r:Fin k // r≠I},∑q∈aA (200+(E r.1).1),(1:O)/(q:O)
            <= ∏_r:{r:Fin k // r≠I},log 2:=im (fun _ _=>ea fun _ _=>by positivity) (fun r _=>aG (200+(E r.1).1) _O)
          _=(log 2)^(Fintype.card {r:Fin k // r≠I}):=by simp
          _=(log 2)^(k-1):=by rw[Fintype.card_subtype_compl,fH,Fintype.card_unique]
 let H:=(univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>YZ.1=YZ.2;let o (I:Fin k):=(univ:Finset (Finset (Fin k) × Finset (Fin k))).filter fun YZ=>
  (I∈YZ.1/\I ∉ YZ.2 ∨ I ∉ YZ.1/\I∈YZ.2)/\∀r:Fin k,I.1< r.1->(r∈YZ.1↔r∈YZ.2)
 have Hs:(univ:Finset (Finset (Fin k) × Finset (Fin k)))⊆H∪univ.biUnion o:=by
  intro ⟨Y,Z⟩ _;by_cases h3:Y=Z
  ·exact e0 _ (dB.mpr ⟨dJ _,h3⟩)
  ·apply eu;rw[g4]
   let diff:=univ.filter fun r:Fin k=>¬ (r∈Y↔r∈Z);have T:diff.Nonempty:=by
    by_contra Hi;rw[mI]at Hi;apply h3;ext r;have:=fq r;rw[<- Hi,dB]at this;push Not at this;exact this (dJ r)
   let I:=diff.max' T;have He:I∈diff:=kg diff T;refine⟨I,dJ I,dB.mpr ⟨dJ _,?_,?_⟩⟩
   ·have h:=(dB.mp He).2;by_cases h1:I∈Y <;> by_cases h2:I∈Z <;> simp_all
   ·intro r D;by_contra Hx;have H1:=gK diff r (dB.mpr ⟨dJ r,Hx⟩);exact absurd D (not_lt_of_ge H1)
 have ho:H.card=2^k:=by
  have:H.card=(univ:Finset (Finset (Fin k))).card:=hO (fun YZ _=>YZ.1) (fun _ _=>dJ _) (fun a ha b hb h=>iq h ((dB.mp ha).2.symm.trans (h.trans (dB.mp hb).2))) (fun Y _=>⟨(Y,Y),dB.mpr ⟨dJ _,rfl⟩,rfl⟩)
  rw[this,j5,ku,fH]
 have hg:∀I:Fin k,(o I).card<=2^(k+I.1):=by
  intro I;let Ht:=Finset (Fin k) × Finset {r:Fin k // r.1< I.1};have H2:Fintype.card Ht=2^(k+I.1):=by
   have hB:Fintype.card {r:Fin k // r.1< I.1}=I.1:=by
    conv_rhs=>rw[<- fH I.1,<- j5]
    rw[<- j5];refine hO (fun (r:{r:Fin k // r.1< I.1}) _=>(⟨r.1.1,r.2⟩:Fin I.1)) (fun _ _=>dJ _) (fun _ _ _ _ h=>i9 (dQ (es h))) (fun j _=>⟨⟨⟨j.1,by have:=j.2;have:=I.2;omega⟩,j.2⟩,dJ _,rfl⟩)
   rw[Fintype.card_prod,ku,ku,fH,hB,ee]
  rw[<- H2];let f:Finset (Fin k) × Finset (Fin k)->Ht:=fun YZ=>
   (YZ.1,univ.filter fun r:{r:Fin k // r.1< I.1}=>r.1∈YZ.2)
  have HF:Set.InjOn f (o I:Set _):=by
   intro ⟨Y1,Z1⟩ h1 ⟨Y2,Z2⟩ h2 A;simp only[eB,o,dB]at h1 h2;have hY:Y1=Y2:=(gv A).1;subst hY;refine iq rfl (Finset.ext fun r=>?_);rcases jC r.1 I.1 with hE | heqI | hgt
   ·have:=Finset.ext_iff.mp (gv A).2 ⟨r,hE⟩
    simpa using this
   ·have HP:r=I:=dQ heqI;subst HP;rcases h1.2.1 with⟨hY,HR⟩ | ⟨hY,HR⟩ <;> rcases h2.2.1 with⟨hY',HS⟩ | ⟨hY',HS⟩ <;> tauto
   ·rw[<- h1.2.2 r hgt,<- h2.2.2 r hgt]
  calc (o I).card=((o I).image f).card:=(gA HF).symm
    _<=univ.card:=card_le_univ _
    _=Fintype.card Ht:=j5
 have Hf:∑I:Fin k,(2:O)^I.1/(2:O)^(E I).1<=2*cj b:=by
  have hT:∑I:Fin k,(2:O)^I.1/(2:O)^(E I).1 =∑h:Fin k,∑I∈univ.filter (fun I:Fin k=>E I=h),(2:O)^I.1/(2:O)^h.1:=(by rw[<- jG (t:=(univ:Finset (Fin k))) (fun _ _=>dJ _) _];refine dF rfl fun h _=>dF rfl fun I hI=>by rw[(dB.mp hI).2]);unfold cj;rw[hT,dP];refine dG fun h _=>?_
  have hC:∑I∈univ.filter (fun I:Fin k=>E I=h),(2:O)^I.1<=(2:O)^(l (h.1+1)):=by
   have h5:(univ.filter (fun I:Fin k=>E I=h)).image Fin.val⊆range (l (h.1+1)):=by intro m hm;rcases dW.mp hm with⟨I,hI,rfl⟩;rw[dN,<- (dB.mp hI).2];exact (y I).2
   calc _=∑m∈(univ.filter (fun I:Fin k=>E I=h)).image Fin.val,(2:O)^m:=
         (fr (f:=fun m=>(2:O)^m) (fun _ _ _ _ A=>dQ A)).symm
     _<=∑m∈range (l (h.1+1)),(2:O)^m:=dC h5 fun _ _ _=>_P
     _=(2:O)^(l (h.1+1))-1:=by rw[fO (_N :(2:O)≠1) (l (h.1+1))];ring
     _<=(2:O)^(l (h.1+1)):=_L
  have hQ:l (h.1+1)=∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),b i:=(by dsimp only[l];congr 1;ext i;simp only[dB,dJ,dV];omega);rw[<- kM]
  calc _<=(2:O)^(l (h.1+1))/(2:O)^h.1:=dI hC _P
    _=2*(2:O)^(((∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),b i:ℕ):ℤ)-(h.1:ℤ)-1):=by rw[hQ,mE _N,mE _N,fo,fo,zpow_one];ring
 have HJ:(1:O)<=cj b:=by
  unfold cj;have Hu:(⟨k-1,_O⟩:Fin k)∈(univ:Finset (Fin k)):=dJ _;have H1:=fi (f:=fun h:Fin k=>(2:O)^(((∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),b i:ℕ):ℤ)-(h.1:ℤ)-1)) (fun _ _=>zpow_nonneg (_N :(0:O)<=2) _) Hu;have hs:univ.filter (fun i:Fin k=>i.1<=k-1)=univ:=(by ext i;simp;have:=i.2;omega);dsimp only at H1;rw[hs,Hj,show (k:ℤ)-((k-1:ℕ):ℤ)-1=0 by omega,zpow_zero]at H1
  exact H1
 have HG:(∏i:Fin k,((b i).factorial:O))*∑a∈ca 200 k b,(W a:O)/(a:O) <=(2*log 2)^k*(1+2^107*cj b/(2^200*log 2)):=by
  refine hP.trans ?_
  let g (YZ:Finset (Fin k) × Finset (Fin k)):O:=∑p∈P.filter (fun p=>|∑r∈YZ.1,log (p r:O) - ∑r∈YZ.2,log (p r:O)|<=log 2),(1:O)/((∏r:Fin k,p r:ℕ):O);have h1:∑YZ:Finset (Fin k) × Finset (Fin k),g YZ <=∑YZ∈H,g YZ+∑I:Fin k,∑YZ∈o I,g YZ:=by
   have hu:=fb (s₁:=H) (s₂:=univ.biUnion o) (f:=g);have HW:∑YZ∈univ.biUnion o,g YZ<=∑I:Fin k,∑YZ∈o I,g YZ:=by
    have HH:∀S:Finset (Fin k),∑YZ∈S.biUnion o,g YZ<=∑I∈S,∑YZ∈o I,g YZ:=by
     intro S;induction S using eW with
     | empty=>simp
     | @insert a S ha ih=>
      rw[iS,i3 ha];have hu':=fb (s₁:=o a) (s₂:=S.biUnion o) (f:=g);have HQ':0<=∑YZ∈o a∩S.biUnion o,g YZ:=ea fun _ _=>ea fun _ _=>_P;linarith
    exact HH univ
   have HQ:0<=∑YZ∈H∩univ.biUnion o,g YZ:=ea fun _ _=>ea fun _ _=>_P;have h5:=dC Hs (f:=g) (fun _ _ _=>ea fun _ _=>by positivity)
   linarith
  have Hy:∑YZ∈H,g YZ<=(2*log 2)^k:=by
   calc ∑YZ∈H,g YZ<=∑_YZ∈H,(log 2)^k:=
         dG fun YZ h3=>hz YZ (dB.mp h3).2
     _=(2:O)^k*(log 2)^k:=by rw[ex,ho,e3];push_cast;ring
     _=(2*log 2)^k:=(eP 2 _ k).symm
  have Hv:∑I:Fin k,∑YZ∈o I,g YZ <=(2*log 2)^k*(2^107*cj b/(2^200*log 2)):=by
   have hD:0< log 2:=_l a3;have Hg:(log 2)^k=(log 2)^(k-1)*log 2:=by rw[<- fc,eN hk]
   calc ∑I:Fin k,∑YZ∈o I,g YZ
       <= ∑I:Fin k,((o I).card:O)*((2^106/(2:O)^(200+(E I).1))*(log 2)^(k-1)):=by
         refine dG fun I _=>?_
         calc ∑YZ∈o I,g YZ<=∑_YZ∈o I,(2^106/(2:O)^(200+(E I).1))*(log 2)^(k-1):=
               dG fun YZ h3=>hA YZ I (dB.mp h3).2.1
           _=_:=by rw[ex,e3]
     _<=∑I:Fin k,((2:O)^(k+I.1))*((2^106/(2:O)^(200+(E I).1))*(log 2)^(k-1)):=by refine dG fun I _=>dE (_M (hg I)) _P
     _=((2*log 2)^k*2^106/(2^200*log 2)) *∑I:Fin k,(2:O)^I.1/(2:O)^(E I).1:=by
         rw[dP];refine dF rfl fun I _=>?_
         rw[eP,Hg,ee,ee];field_simp [hD.ne']
     _<=((2*log 2)^k*2^106/(2^200*log 2))*(2*cj b):=dA Hf _P
     _=_:=by ring
  linarith
 have H3:1+2^107*cj b/(2^200*log 2)<=2^108*cj b:=by
  have h1:2^107*cj b/(2^200*log 2)<=cj b:=by
   rw[mc (by linarith[a3]:0< (2:O)^200*log 2)];have:(2:O)^107<=(2:O)^200*log 2:=by have hE:=a3;norm_num at *;nlinarith
   nlinarith
  linarith
 rw[gm,ma _P];rw[e8]
 calc _<=(2*log 2)^k*(1+2^107*cj b/(2^200*log 2)):=HG
   _<=(2*log 2)^k*(2^108*cj b):=dA H3 _P
   _=_:=by ring
set_option maxHeartbeats 800000 in
lemma cl {r:ℕ} (K:1<=r) (x:ℕ->O) (l:∀i,0< x i)
 (z:∀i,x (i+r)=x i) :
 let X:=∏i∈range r,x i
 1/max 1 X<=∑j∈range r,(∑h∈range r,∏i∈range (h+1),x (j+i))⁻¹ /\
 ∑j∈range r,(∑h∈range r,∏i∈range (h+1),x (j+i))⁻¹<=1/min 1 X:=by
 intro X;let y (m:ℕ):O:=∏i∈range m,x i;have c:∀m,0< y m:=fun m=>jf fun i _=>l i;have u:∀m,y (m+r)=X*y m:=by
  intro m;induction m with
  | zero=>simp[y,X]
  | succ m ih=>
   rw[show m+1+r=(m+r)+1 by omega]
   simp only[y,prod_range_succ]at ih ⊢;rw[z m,ih];ring
 have e:0< ∑i∈range r,y i:=sum_pos (fun i _=>c i) ⟨0,dN.mpr K⟩;have D:∀j∈range r,(∑h∈range r,∏i∈range (h+1),x (j+i))⁻¹ =y j/(X*∑i∈range (j+1),y i+∑i∈Ico (j+1) r,y i):=by
  intro j C;rw[dN]at C;have E:∀h:ℕ,∏i∈range (h+1),x (j+i)=y (j+h+1)/y j:=by
   intro h;rw[eq_div_iff (c j).ne',e8];have:y (j+(h+1))=y j*∏i∈range (h+1),x (j+i):=by
    induction h+1 with
    | zero=>simp[y]
    | succ m ih=>
     rw[show j+(m+1)=(j+m)+1 by omega]
     simp only[y,prod_range_succ]at ih ⊢;rw[ih,f0]
   simpa[add_assoc] using this.symm
  have o:∑h∈range r,y (j+h+1) =X*∑i∈range (j+1),y i+∑i∈Ico (j+1) r,y i:=by
   have G:∑h∈range r,y (j+h+1)=∑m∈Ico (j+1) (j+1+r),y m:=by
    refine fh (fun h _=>j+h+1) (fun h J=>by rw[dN]at J;rw[f3];omega)
     (fun _ _ _ _ h=>by omega) (fun m F=>⟨m-(j+1),by rw[f3]at F;rw[dN];omega,by rw[f3]at F;omega⟩) (fun _ _=>rfl)
   rw[G,<- lN y (_O :j+1<=r) (_O :r<=j+1+r)];rw[ip];congr 1;have H:∑m∈Ico r (j+1+r),y m=∑i∈range (j+1),y (i+r):=fh (fun m _=>m-r) (fun m F=>by rw[f3]at F;rw[dN];omega) (fun M G N H h=>by rw[f3]at G H;omega) (fun i hi=>⟨i+r,by rw[dN]at hi;rw[f3];omega,_O⟩) (fun m F=>by rw[f3]at F;rw[eN F.1])
   rw[H,dP];exact dF rfl fun i _=>u i
  simp_rw [E]
  rw[<- kM,o,inv_div]
 have b:∀j∈range r,min 1 X*∑i∈range r,y i <=X*∑i∈range (j+1),y i+∑i∈Ico (j+1) r,y i /\X*∑i∈range (j+1),y i+∑i∈Ico (j+1) r,y i <=max 1 X*∑i∈range r,y i:=by
  intro j C;rw[dN]at C;have v:∑i∈range r,y i=∑i∈range (j+1),y i+∑i∈Ico (j+1) r,y i:=(by rw[<- Nat.Ico_zero_eq_range,<- Nat.Ico_zero_eq_range,lN y (g5 _) _O]);have A:0<=∑i∈range (j+1),y i:=ea fun i _=>(c i).le;have B:0<=∑i∈Ico (j+1) r,y i:=ea fun i _=>(c i).le;rw[v,mul_add,mul_add];exact⟨fd (dE (gw 1 X) A) ((dE (i7 1 X) B).trans_eq (gz _)),fd (dE (ep 1 X) A)
    ((gz _).symm.trans_le (dE (eo 1 X) B))⟩
 have w:0< X:=jf fun i _=>l i;have d:0< min 1 X:=lt_min i5 w;have q:0< max 1 X:=e9 i5 (eo 1 X);rw[dF rfl D];constructor
 · calc 1/max 1 X=(∑j∈range r,y j)/(max 1 X*∑i∈range r,y i):=by
           field_simp [q.ne',e.ne']
     _=∑j∈range r,y j/(max 1 X*∑i∈range r,y i):=kM ..
     _<=_:=dG fun j C=>dL (c j).le (e9 (ko d e) (b j C).1) (b j C).2
 · calc _<=∑j∈range r,y j/(min 1 X*∑i∈range r,y i):=
         dG fun j C=>dL (c j).le (ko d e) (b j C).1
     _=(∑j∈range r,y j)/(min 1 X*∑i∈range r,y i):=(kM ..).symm
     _=1/min 1 X:=by field_simp [d.ne',e.ne']
set_option maxHeartbeats 800000 in
lemma cm {m:ℕ} (w:Fin m->O) (n:ℕ) :
 ∑b∈(Fintype.piFinset fun _:Fin m=>range (n+1)).filter (fun b=>∑i:Fin m,b i=n),∏i:Fin m,w i^(b i)/((b i).factorial:O)=(∑i:Fin m,w i)^n/(n.factorial:O):=by
 induction m generalizing n with
 | zero=>
  cases n with
  | zero=>simp
  | succ n=>
   have l:((Fintype.piFinset fun _:Fin 0=>range (n+2)).filter
    (fun b=>∑i:Fin 0,b i=n+1))=∅:=by
    ext b;simp
   rw[l];simp[lC (j7 n)]
 | succ m ih=>
  rw[kc,add_pow,kM];have c:∑b∈(Fintype.piFinset fun _:Fin (m+1)=>range (n+1)).filter (fun b=>∑i,b i=n),∏i:Fin (m+1),w i^(b i)/((b i).factorial:O) =∑r∈range (n+1),(w (Fin.last m)^r/(r.factorial:O)) *∑b'∈(Fintype.piFinset fun _:Fin m=>range (n-r+1)).filter (fun b'=>∑i,b' i=n-r),∏i:Fin m,w i.castSucc^(b' i)/((b' i).factorial:O):=by
   simp_rw [dP]
   rw[gY];refine fh (fun b _=>⟨b (Fin.last m),fun i=>b i.castSucc⟩) ?_ ?_ ?_ ?_
   ·intro b A;simp only[dB,e5,dN,fg]at A ⊢;rw[kc]at A;refine⟨by omega,fun i=>?_,_O⟩
    have C:b i.castSucc<=∑j:Fin m,b j.castSucc:=fi (f:=fun j:Fin m=>b j.castSucc) (fun _ _=>g5 _) (dJ i);omega
   ·intro F _ G _ e;simp only[fG,iD]at e;funext i;refine Fin.lastCases e.1 (fun j=>gH e.2 j) i
   ·intro ⟨r,b'⟩ hx;simp only[fg,dN,dB,e5]at hx;refine⟨Fin.snoc b' r,?_,?_⟩
    ·simp only[dB,e5,dN];refine⟨fun i=>Fin.lastCases (by simp[hx.1]) (fun j=>by simp;have:=hx.2.1 j;omega) i,?_⟩
     rw[kc];simp[hx.2.2];omega
    ·simp only[fG,iD,Fin.snoc_last,dV];funext j;simp
   ·intro b _;rw[Fin.prod_univ_castSucc];ring
  rw[c];have o:∑r∈range (n+1),(w (Fin.last m)^r/(r.factorial:O)) *((∑i:Fin m,w i.castSucc)^(n-r)/((n-r).factorial:O)) =∑r∈range (n+1),((∑i:Fin m,w i.castSucc)^r*w (Fin.last m)^(n-r)*(dw n r:O))/(n.factorial:O):=by
   refine fh (fun r _=>n-r) (fun r z=>by rw[dN]at z ⊢;omega) (fun H D J E h=>by rw[dN]at D E;omega) (fun s B=>⟨n-s,by rw[dN]at B ⊢;omega,by rw[dN]at B;omega⟩) (fun r z=>?_)
   rw[dN]at z;have y:(dw n (n-r):O)*((n-r).factorial:O)*(r.factorial:O)=(n.factorial:O):=by have d:=f7 (_O :n-r<=n);rw[show n-(n-r)=r by omega]at d;exact_mod_cast d
   rw[show n-(n-r)=r by omega]
   have q:((n-r).factorial:O)≠0:=_P;have u:(r.factorial:O)≠0:=_P;have v:(n.factorial:O)≠0:=_P;field_simp [q,u,v];linear_combination -(w (Fin.last m)^r*(∑i:Fin m,w i.castSucc)^(n-r))*y
  rw[<- o];refine dF rfl fun r _=>by rw[ih (fun i=>w i.castSucc) (n-r)]
lemma cn {m a s:ℕ} (e:0< m) (h:a< m) :
 ((a+s) % m+(m-s % m)) % m=a:=by
 have c:=gu s m;have d:=dY s e;have b:m*(s/m+1)=m*(s/m)+m:=_R;rw[Nat.mod_add_mod,show a+s+(m-s % m)=a+m*(s/m+1) by omega,lT,gi h]
lemma cn' {m a s:ℕ} (e:0< m) (h:a< m) :
 ((a+(m-s % m)) % m+s) % m=a:=by
 have c:=gu s m;have d:=dY s e;have b:m*(s/m+1)=m*(s/m)+m:=_R;rw[Nat.mod_add_mod,show a+(m-s % m)+s=a+m*(s/m+1) by omega,lT,gi h]
lemma cp {α : Type*} (S:Finset α) (g : α->ℤ) :
 ∏i∈S,(2:O)^(g i)=(2:O)^(∑i∈S,g i):=by
 classical
 induction S using eW with
 | empty=>simp
 | @insert a S ha ih=>rw[fN ha,i3 ha,ih,zpow_add₀ _N]
set_option maxHeartbeats 800000 in
lemma cq {k:ℕ} (hk:1000<=k) :
 let B:=(Fintype.piFinset fun _:Fin k=>range (k+1)).filter fun b=>∑i:Fin k,b i=k
 let M:=B.filter fun b=>∀i:Fin k,b i<=200*(200+i.1)/\b i<=200*(k-i.1)
 (k:O)^(k-1)/(2*(k.factorial:O)) <=∑b∈M,1/((∏i:Fin k,((b i).factorial:O))*cj b):=by
 intro B M;let N (s:ℕ) (b:Fin k->ℕ):Fin k->ℕ:=fun i=>b ⟨(i.1+s) % k,dY _ _O⟩;have R:∀s b,N (k-s % k) (N s b)=b:=by intro s b;funext i;dsimp only[N];congr 1;apply dQ;dsimp only;exact cn' _O i.2
 have R':∀s b,N s (N (k-s % k) b)=b:=by intro s b;funext i;dsimp only[N];congr 1;apply dQ;dsimp only;exact cn _O i.2
 have hl:∀s,∀b∈B,N s b∈B:=by
  intro s b z;simp only[B,dB,e5,dN]at z ⊢;refine⟨fun i=>z.1 _,?_⟩;trans ∑i:Fin k,b i
  ·refine fh (fun i _=>⟨(i.1+s) % k,dY _ _O⟩) (fun _ _=>dJ _)
    (fun i1 _ i2 _ h=>by
     have hv:(i1.1+s) % k=(i2.1+s) % k:=es h;have E:=fT (fun t=>(t+(k-s % k)) % k) hv;rw[cn _O i1.2,cn _O i2.2]at E;exact dQ E)
    (fun j _=>⟨⟨(j.1+(k-s % k)) % k,dY _ _O⟩,dJ _,dQ (by dsimp only;exact cn' _O j.2)⟩)
    (fun _ _=>rfl)
  ·exact z.2
 have hI:∀s b,∏i:Fin k,((N s b i).factorial:O)=∏i:Fin k,((b i).factorial:O):=by
  intro s b;refine hJ (fun i _=>⟨(i.1+s) % k,dY _ _O⟩) (fun _ _=>dJ _)
   (fun i1 _ i2 _ h=>by
    have hv:(i1.1+s) % k=(i2.1+s) % k:=es h;have E:=fT (fun t=>(t+(k-s % k)) % k) hv;rw[cn _O i1.2,cn _O i2.2]at E;exact dQ E)
   (fun j _=>⟨⟨(j.1+(k-s % k)) % k,dY _ _O⟩,dJ _,dQ (by dsimp only;exact cn' _O j.2)⟩)
   (fun _ _=>rfl)
 have v8:∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj b) =(k:O)^(k-1)/(k.factorial:O):=by
  have HG:(k:O)*∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj b) =∑b∈B,(1/∏i:Fin k,((b i).factorial:O)) *∑s∈range k,(cj (N s b))⁻¹:=by
   have U:∀s∈range k,∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj b) =∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj (N s b)):=by intro s _;symm;refine fh (fun b _=>N s b) (fun b z=>hl s b z) (fun b1 _ b2 _ h=>by rw[<- R s b1,<- R s b2,h]) (fun b z=>⟨N (k-s % k) b,hl _ b z,R' s b⟩) (fun b _=>by rw[hI])
   calc (k:O)*∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj b)
       = ∑s∈range k,∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj (N s b)):=by rw[<- dF rfl U,ex,fy,e3]
     _=∑b∈B,∑s∈range k,1/((∏i:Fin k,((b i).factorial:O))*cj (N s b)):=hH
     _=_:=dF rfl fun b _=>by rw[dP];refine dF rfl fun s _=>_R
  have HH:∀b∈B,∑s∈range k,(cj (N s b))⁻¹=1:=by
   intro b z;let x (i:ℕ):O:=(2:O)^((b ⟨i % k,dY _ _O⟩:ℤ)-1);have Hl:∀i,0< x i:=fun _=>_P;have Hm:∀i,x (i+k)=x i:=fun i=>by
    dsimp only[x];have hy:(⟨(i+k) % k,dY _ _O⟩:Fin k)=⟨i % k,dY _ _O⟩:=dQ (kZ i k);rw[hy]
   have hX:∏i∈range k,x i=1:=by
    rw[cp];have hW:∑i∈range k,((b ⟨i % k,dY _ _O⟩:ℤ)-1)=0:=by
     rw[f2,ex,fy,e3,fv];have T:∑i∈range k,(b ⟨i % k,dY _ _O⟩:ℤ)=(∑i:Fin k,b i:ℕ):=by rw[jp];exact fh (fun i hi=>⟨i,dN.mp hi⟩) (fun _ _=>dJ _) (fun _ _ _ _ h=>es h) (fun i _=>⟨i.1,dN.mpr i.2,rfl⟩) (fun i hi=>by congr 2;apply dQ;exact gi (dN.mp hi))
     rw[T,(dB.mp z).2];omega
    rw[hW,zpow_zero]
   have hg:=cl (_O :1<=k) x Hl Hm;dsimp only at hg;rw[hX,max_self,min_self,kO]at hg;have Hy:∀s∈range k,cj (N s b) =∑h∈range k,∏i∈range (h+1),x (s+i):=by
    intro s _;unfold cj;refine fh (fun h _=>h.1) (fun h _=>dN.mpr h.2) (fun _ _ _ _ h=>dQ h) (fun h hh=>⟨⟨h,dN.mp hh⟩,dJ _,rfl⟩) (fun h _=>?_);rw[cp];congr 1;rw[f2,ex,fy,e3,fv];have hT:∑i∈range (h.1+1),(b ⟨(s+i) % k,dY _ _O⟩:ℤ) =(∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),N s b i:ℕ):=by rw[jp];exact fh (fun i hi=>⟨i,by rw[dN]at hi;omega⟩) (fun i hi=>by rw[dN]at hi;simp only[dB,dJ,dV];exact mx.mp hi) (fun _ _ _ _ h=>es h) (fun i hi=>⟨i.1,by simp only[dB,dJ,dV]at hi;rw[dN];omega,rfl⟩) (fun i _=>by dsimp only[N];congr 2;apply dQ;dsimp only;rw[ip])
    rw[hT];omega
   rw[dF rfl fun s hs=>by rw[Hy s hs]]
   exact i8 hg.2 hg.1
  have hU:∑b∈B,(1:O)/∏i:Fin k,((b i).factorial:O)=(k:O)^k/(k.factorial:O):=by
   have W:=cm (fun _:Fin k=>(1:O)) k;simp only[jQ,ex,j5,fH,e3,fv]at W;rw[<- W];refine dF rfl fun b _=>?_
   rw[g9,<- gL];exact f9 rfl fun i _=>(g9 _).symm
  have E:(k:O)*∑b∈B,1/((∏i:Fin k,((b i).factorial:O))*cj b)=(k:O)^k/(k.factorial:O):=(by rw[HG,dF rfl fun b z=>by rw[HH b z,fv],hU]);have Hz:(k:O)≠0:=_P;rw[<- mul_right_inj' Hz,E,gl,<- fp,eN (_O :1<=k)]
 let l (j:Fin k):=B.filter fun b=>200*(200+j.1)< b j;let o (j:Fin k):=B.filter fun b=>200*(k-j.1)< b j;have HI:B \ M⊆univ.biUnion l∪univ.biUnion o:=by
  intro b z;simp only[M,gj,dB,not_and,not_forall]at z;rcases z.2 z.1 with⟨j,hj⟩;by_cases E:200*(200+j.1)< b j
  ·exact e0 _ (g4.mpr ⟨j,dJ j,dB.mpr ⟨z.1,E⟩⟩)
  ·exact eu _ (g4.mpr ⟨j,dJ j,dB.mpr ⟨z.1,_O⟩⟩)
 have Hn:∀j:Fin k,∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=((k:O)^(k-1)/(k.factorial:O))*(2/((200*(200+j.1)).factorial:O)):=by
  intro j;by_cases Hw:k<=200*(200+j.1)
  ·have hY:l j=∅:=by
    ext b;simp only[l,B,dB,fq,iC];rintro⟨⟨_,hsum⟩,he⟩;have:b j<=k:=(fi (fun _ _=>g5 _) (dJ j)).trans_eq hsum;omega
   rw[hY,gG];positivity
  ·push Not at Hw
   let r:ℕ:=k-1 - j.1;have HV:k/2<=r:=_O;have e:1<=r:=_O;let q (s:ℕ) (b:Fin k->ℕ):Fin k->ℕ:=fun i=>
    if h:j.1< i.1 then b ⟨j.1+1+((i.1-(j.1+1)+s) % r),by
     have:=dY (i.1-(j.1+1)+s) e;omega⟩
    else b i
   have h0:∀s,∀b∈l j,q s b∈l j:=by
    intro s b z;simp only[l,B,dB,e5,dN]at z ⊢;refine⟨⟨fun i=>by dsimp only[q];split_ifs;exact z.1.1 _;exact z.1.1 i,?_⟩,?_⟩
    ·trans ∑i:Fin k,b i
     ·rw[<- eh univ (fun i:Fin k=>j.1< i.1),<- eh univ (fun i:Fin k=>j.1< i.1)];congr 1
      ·refine fh (fun i hi=>⟨j.1+1+((i.1-(j.1+1)+s) % r),by
        have:=dY (i.1-(j.1+1)+s) e;omega⟩)
        (fun i hi=>by simp only[dB,dJ,dV];omega)
        (fun i1 E i2 T h=>by
         simp only[dB,dJ,dV]at E T;have hv:(i1.1-(j.1+1)+s) % r=(i2.1-(j.1+1)+s) % r:=(by have:=es h;omega);have h3:=fT (fun t=>(t+(r-s % r)) % r) hv;rw[cn e (_O :i1.1-(j.1+1)< r),cn e (_O :i2.1-(j.1+1)< r)]at h3;exact dQ _O)
        (fun i hi=>by
         simp only[dB,dJ,dV]at hi;refine⟨⟨j.1+1+((i.1-(j.1+1)+(r-s % r)) % r),by
          have:=dY (i.1-(j.1+1)+(r-s % r)) e;omega⟩,
          by simp only[dB,dJ,dV];omega,?_⟩
         apply dQ;dsimp only
         rw[show j.1+1+(i.1-(j.1+1)+(r-s % r)) % r-(j.1+1)=(i.1-(j.1+1)+(r-s % r)) % r by omega,cn' e (_O :i.1-(j.1+1)< r)];omega)
        (fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[q];rw[eG hi])
      ·exact dF rfl fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[q];rw[eA hi]
     ·exact z.1.2
    ·dsimp only[q];rw[eA (gU _)];exact z.2
   have hz:∀s b,∏i:Fin k,((q s b i).factorial:O)=∏i:Fin k,((b i).factorial:O):=by
    intro s b;rw[<- ey univ (fun i:Fin k=>j.1< i.1),<- ey univ (fun i:Fin k=>j.1< i.1)];congr 1
    ·refine hJ (fun i hi=>⟨j.1+1+((i.1-(j.1+1)+s) % r),by
      have:=dY (i.1-(j.1+1)+s) e;omega⟩)
      (fun i hi=>by simp only[dB,dJ,dV];omega)
      (fun i1 E i2 T h=>by
       simp only[dB,dJ,dV]at E T;have hv:(i1.1-(j.1+1)+s) % r=(i2.1-(j.1+1)+s) % r:=(by have:=es h;omega);have h3:=fT (fun t=>(t+(r-s % r)) % r) hv;rw[cn e (_O :i1.1-(j.1+1)< r),cn e (_O :i2.1-(j.1+1)< r)]at h3;exact dQ _O)
      (fun i hi=>by
       simp only[dB,dJ,dV]at hi;refine⟨⟨j.1+1+((i.1-(j.1+1)+(r-s % r)) % r),by
        have:=dY (i.1-(j.1+1)+(r-s % r)) e;omega⟩,
        by simp only[dB,dJ,dV];omega,?_⟩
       apply dQ;dsimp only
       rw[show j.1+1+(i.1-(j.1+1)+(r-s % r)) % r-(j.1+1)=(i.1-(j.1+1)+(r-s % r)) % r by omega,cn' e (_O :i.1-(j.1+1)< r)];omega)
      (fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[q];rw[eG hi])
    ·exact f9 rfl fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[q];rw[eA hi]
   have hZ:∀b∈l j,∑s∈range r,(cj (q s b))⁻¹<=1:=by
    intro b z;let C:ℤ:=((∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),b i:ℕ):ℤ)-(j.1:ℤ)-1;have HS:0<=C:=by have E:b j<=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),b i:=fi (fun _ _=>g5 _) (by simp);have T:200*(200+j.1)< b j:=(dB.mp z).2;dsimp only[C];omega
    let x (i:ℕ):O:=(2:O)^((b ⟨j.1+1+i % r,by have:=dY i e;omega⟩:ℤ)-1)
    have h4:∏i∈range r,x i=(2:O)^(-C):=by
     rw[cp];congr 1;rw[f2,ex,fy,e3,fv];have HJ:∑i∈range r,(b ⟨j.1+1+i % r,by have:=dY i e;omega⟩:ℤ) =(∑i∈univ.filter (fun i:Fin k=>j.1< i.1),b i:ℕ):=by rw[jp];exact fh (fun i hi=>⟨j.1+1+i,by rw[dN]at hi;omega⟩) (fun i hi=>by simp only[dB,dJ,dV];omega) (fun _ _ _ _ h=>by have:=es h;omega) (fun i hi=>by simp only[dB,dJ,dV]at hi;exact⟨i.1-(j.1+1),dN.mpr _O,dQ (by dsimp only;omega)⟩) (fun i hi=>by rw[dN]at hi;congr 2;apply dQ;dsimp only;rw[gi hi])
     have hA:=(dB.mp (dB.mp z).1).2;rw[<- eh univ (fun i:Fin k=>i.1<=j.1)]at hA;have H0:univ.filter (fun i:Fin k=>¬ i.1<=j.1)=univ.filter (fun i:Fin k=>j.1< i.1):=(by ext i;simp);rw[H0]at hA;rw[HJ];dsimp only[C,r];omega
    have hp:∏i∈range r,x i<=1:=(by rw[h4];exact mJ _N _O);have hg:=(cl e x (fun _=>by positivity) (fun i=>by
     dsimp only[x];have hy:(⟨j.1+1+(i+r) % r,by have:=dY (i+r) e;omega⟩:Fin k) =⟨j.1+1+i % r,by have:=dY i e;omega⟩:=dQ (by dsimp only;rw[kZ])
     rw[hy])).2
    rw[jo hp,h4,g9,<- zpow_neg,neg_neg]at hg;have hL:∀s∈range r,(2:O)^C*∑h∈range r,∏i∈range (h+1),x (s+i)<=cj (q s b):=by
     intro s _;unfold cj;rw[dP]
     calc _=∑h∈univ.filter (fun h:Fin k=>j.1< h.1),
             (2:O)^(((∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),q s b i:ℕ):ℤ)-(h.1:ℤ)-1):=by
           refine fh (fun h hh=>⟨j.1+1+h,by rw[dN]at hh;omega⟩) (fun h hh=>by simp only[dB,dJ,dV];omega) (fun _ _ _ _ h=>by have:=es h;omega) (fun h hh=>by simp only[dB,dJ,dV]at hh;exact⟨h.1-(j.1+1),dN.mpr _O,dQ (by dsimp only;omega)⟩) (fun h hh=>?_)
           rw[dN]at hh;rw[cp,<- zpow_add₀ _N];congr 1;rw[f2,ex,fy,e3,fv];rw[<- eh _ (fun i:Fin k=>i.1<=j.1)];have HW:∑i∈(univ.filter (fun i:Fin k=>i.1<=j.1+1+h)).filter (fun i:Fin k=>i.1<=j.1),q s b i=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),b i:=(by have HX:(univ.filter (fun i:Fin k=>i.1<=j.1+1+h)).filter (fun i:Fin k=>i.1<=j.1) =univ.filter (fun i:Fin k=>i.1<=j.1):=(by ext i;simp;omega);rw[HX];exact dF rfl fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[q];rw[eA _O]);have HY:∑i∈(univ.filter (fun i:Fin k=>i.1<=j.1+1+h)).filter (fun i:Fin k=>¬ i.1<=j.1),q s b i=∑t∈range (h+1),b ⟨j.1+1+(s+t) % r,by have:=dY (s+t) e;omega⟩:=(by symm;refine fh (fun t ht=>⟨j.1+1+t,by rw[dN]at ht;omega⟩) (fun t ht=>by rw[dN]at ht;simp only[dB,dJ,dV];omega) (fun _ _ _ _ h=>by have:=es h;omega) (fun i hi=>by simp only[dB,dJ,dV]at hi;exact⟨i.1-(j.1+1),dN.mpr _O,dQ (by dsimp only;omega)⟩) (fun t _=>by dsimp only[q];rw[eG _O];congr 2;rw[show j.1+1+t-(j.1+1)=t by omega,ip t s]));rw[HW,HY];dsimp only[C];push_cast;omega
       _<=_:=dC (fj _ _) fun _ _ _=>_P
    calc ∑s∈range r,(cj (q s b))⁻¹
        <= ∑s∈range r,((2:O)^C*∑h∈range r,∏i∈range (h+1),x (s+i))⁻¹:=by
          refine dG fun s hs=>inv_anti₀ ?_ (hL s hs)
          have v9:0< ∑h∈range r,∏i∈range (h+1),x (s+i):=e9 _P (fi (fun _ _=>by positivity) (dN.mpr e))
          positivity
      _=((2:O)^C)⁻¹*∑s∈range r,(∑h∈range r,∏i∈range (h+1),x (s+i))⁻¹:=by rw[dP];exact dF rfl fun s _=>mul_inv _ _
      _<=((2:O)^C)⁻¹*(2:O)^C:=dA hg _P
      _=1:=inv_mul_cancel₀ _P
   have H1:(r:O)*∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=∑b∈l j,1/∏i:Fin k,((b i).factorial:O):=by
    have U:∀s∈range r,∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b) =∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj (q s b)):=by
     intro s _;symm;refine fh (fun b _=>q s b) (fun b z=>h0 s b z)
      (fun b1 _ b2 _ h=>by
       funext i;by_cases hi:j.1< i.1
       ·have:=gH h ⟨j.1+1+((i.1-(j.1+1)+(r-s % r)) % r),by
         have:=dY (i.1-(j.1+1)+(r-s % r)) e;omega⟩
        dsimp only[q]at this;rw[eG _O,eG _O]at this;have H2:(⟨j.1+1+(j.1+1+(i.1-(j.1+1)+(r-s % r)) % r-(j.1+1)+s) % r,by have:=dY (j.1+1+(i.1-(j.1+1)+(r-s % r)) % r-(j.1+1)+s) e;omega⟩:Fin k)=i:=by
         apply dQ;dsimp only
         rw[show j.1+1+(i.1-(j.1+1)+(r-s % r)) % r-(j.1+1)=(i.1-(j.1+1)+(r-s % r)) % r by omega,cn' e (_O :i.1-(j.1+1)< r)];omega
        rw[H2]at this;exact this
       ·have:=gH h i;dsimp only[q]at this;rwa[eA hi,eA hi]at this)
      (fun b z=>⟨q (r-s % r) b,h0 _ b z,by
       funext i;dsimp only[q];by_cases hi:j.1< i.1
       ·rw[eG hi,eG _O];congr 1;apply dQ;dsimp only;rw[show j.1+1+(i.1-(j.1+1)+s) % r-(j.1+1)=(i.1-(j.1+1)+s) % r by omega,cn e (_O :i.1-(j.1+1)< r)];omega
       ·rw[eA hi,eA hi]⟩)
      (fun b _=>by rw[hz])
    calc (r:O)*∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b)
        = ∑s∈range r,∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj (q s b)):=by rw[<- dF rfl U,ex,fy,e3]
      _=∑b∈l j,(1/∏i:Fin k,((b i).factorial:O))*∑s∈range r,(cj (q s b))⁻¹:=by
          rw[hH];refine dF rfl fun b _=>by
            rw[dP];refine dF rfl fun s _=>_R
      _<=_:=dG fun b z=>by
          calc _<=(1/∏i:Fin k,((b i).factorial:O))*1:=dA (hZ b z) _P
            _=_:=fv _
   have h5:∑b∈l j,(1:O)/∏i:Fin k,((b i).factorial:O) =∑m∈Icc (200*(200+j.1)+1) k,(1/(m.factorial:O)) *(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O)):=by
    have hM:∀m∈Icc (200*(200+j.1)+1) k,(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O)) =∑b'∈(Fintype.piFinset fun _:Fin (k-1)=>range (k-m+1)).filter (fun b'=>∑i,b' i=k-m),∏i:Fin (k-1),(1:O)/((b' i).factorial:O):=(by intro m _;have W:=cm (fun _:Fin (k-1)=>(1:O)) (k-m);simp only[jQ,ex,j5,fH,e3,fv]at W;exact W.symm);conv_rhs=>rw[dF rfl fun m W=>by rw[hM m W]]
    simp_rw [dP]
    rw[gY];let H:Fin (k-1)->Fin k:=fun i=>if h:i.1< j.1 then ⟨i.1,_O⟩ else ⟨i.1+1,_O⟩;have D:Function.Injective H:=by
     intro a b Z;dsimp only[H]at Z;split_ifs at Z with E T
     ·exact dQ (es Z)
     ·exfalso;have:=es Z;omega
     ·exfalso;have:=es Z;omega
     ·exact dQ (by have:=es Z;omega)
    have J:∀i:Fin (k-1),H i≠j:=(by intro i;dsimp only[H];split_ifs <;> intro h <;> have:=es h <;> omega);have y:∀i∈univ.erase j,∃t,∃(_:t∈(univ:Finset (Fin (k-1)))),H t=i:=by
     intro i hi;have HA:i.1≠j.1:=fun h=>(gS.mp hi).1 (dQ h);by_cases he:i.1< j.1
     ·exact⟨⟨i.1,_O⟩,dJ _,by dsimp only[H];rw[eG he]⟩
     ·exact⟨⟨i.1-1,_O⟩,dJ _,by dsimp only[H];rw[eA _O];exact dQ (by dsimp only;omega)⟩
    refine fh (fun b _=>⟨b j,fun i=>b (H i)⟩) ?_ ?_ ?_ ?_
    ·intro b z;simp only[l,B,dB,e5,dN,fg,dT]at z ⊢;have P:∑i:Fin (k-1),b (H i)+b j=k:=by
      trans ∑i:Fin k,b i
      ·rw[<- fJ univ b (dJ j),ip];congr 1;exact fh (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun _ _=>rfl)
      ·exact z.1.2
     refine⟨⟨by omega,_O⟩,fun i=>?_,_O⟩
     have:b (H i)<=∑t:Fin (k-1),b (H t):=fi (f:=fun t:Fin (k-1)=>b (H t)) (fun _ _=>g5 _) (dJ i)
     omega
    ·intro b1 _ b2 _ hf;simp only[fG,iD]at hf;funext i;by_cases hi:i=j
     ·rw[hi,hf.1]
     ·have HA:i.1≠j.1:=fun h=>hi (dQ h);by_cases he:i.1< j.1
      ·have:=gH hf.2 ⟨i.1,_O⟩;dsimp only[H]at this;rwa[eG he]at this
      ·have:=gH hf.2 ⟨i.1-1,_O⟩;dsimp only[H]at this
       rw[eA _O]at this;simpa[show (⟨i.1-1+1,_O⟩:Fin k)=i from dQ (by dsimp only;omega)] using this
    ·intro ⟨m,b'⟩ hx;simp only[fg,dT,dB,e5,dN]at hx;let b:Fin k->ℕ:=fun i=>if E:i.1< j.1 then b' ⟨i.1,_O⟩
      else if T:i.1=j.1 then m else b' ⟨i.1-1,_O⟩
     have h6:∀i:Fin (k-1),b (H i)=b' i:=by
      intro i;dsimp only[b,H];by_cases hi:i.1< j.1
      ·rw[eG hi,eG hi]
      ·rw[eA hi,eA (by dsimp only;omega),eA (by dsimp only;omega)];congr 1
     have h7:b j=m:=(by dsimp only[b];rw[eA (gU _),eG rfl]);refine⟨b,?_,?_⟩
     ·simp only[l,B,dB,e5,dN];refine⟨⟨fun i=>by
       dsimp only[b];split_ifs
       ·have:=hx.2.1 ⟨i.1,_O⟩;omega
       ·omega
       ·have:=hx.2.1 ⟨i.1-1,_O⟩;omega,?_⟩,
       by rw[h7];omega⟩
      rw[<- fJ univ b (dJ j),h7];have P:∑i∈univ.erase j,b i=∑i:Fin (k-1),b' i:=(by symm;refine fh (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun i _=>(h6 i).symm));rw[P,hx.2.2];omega
     ·simp only[fG,iD,h7,dV];funext i;exact h6 i
    ·intro b _;dsimp only;rw[<- gk univ (fun i=>((b i).factorial:O)) (dJ j)];have hV:∏i∈univ.erase j,((b i).factorial:O)=∏i:Fin (k-1),((b (H i)).factorial:O):=(by symm;refine hJ (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun _ _=>rfl));rw[hV,g9,mul_inv,<- gL];simp_rw [<- g9]
   have ho:∀m∈Icc (200*(200+j.1)+1) k,(1/(m.factorial:O))*(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O)) <=((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O)) *(1/(2:O)^(m-(200*(200+j.1)+1))):=by
    intro m W;rw[dT]at W;have H3:((k:O)^(k-m)/((k-m).factorial:O))<=(k:O)^k/(k.factorial:O):=by
     rw[mb _P _P];have h8:∀d:ℕ,d<=k->k.factorial<=k^d*(k-d).factorial:=by
      intro d;induction d with
      | zero=>intro _;simp
      | succ d ih=>
       intro hd;have K:k-d=(k-(d+1))+1:=_O;have hB:(k-d).factorial=(k-d)*(k-(d+1)).factorial:=by conv_lhs=>rw[K,e6,<- K]
       calc k.factorial<=k^d*(k-d).factorial:=ih _O
         _=k^d*((k-d)*(k-(d+1)).factorial):=by rw[hB]
         _<=k^d*(k*(k-(d+1)).factorial):=dR _ (eE _ (i4 k d))
         _=k^(d+1)*(k-(d+1)).factorial:=by rw[fc];ring
     have E:(k.factorial:O)<=(k:O)^m*((k-m).factorial:O):=_M (h8 m W.2);have H4:(k:O)^(k-m)*(k:O)^m=(k:O)^k:=by rw[<- ee,eN W.2]
     calc (k:O)^(k-m)*(k.factorial:O)
         <= (k:O)^(k-m)*((k:O)^m*((k-m).factorial:O)):=dA E _P
       _=(k:O)^k*((k-m).factorial:O):=by rw[<- f0,H4]
    have Ho:((200*(200+j.1)).factorial:O)*(2:O)^(m-(200*(200+j.1)+1))<=(m.factorial:O):=by
     have Q:(200*(200+j.1)).factorial*2^(m-(200*(200+j.1)+1))<=m.factorial:=by
      set A:=200*(200+j.1);have hd:A+1<=m:=W.1;have X:∀d:ℕ,A.factorial*2^d<=(A+1+d).factorial:=by
       intro d;induction d with
       | zero=>
        simp only[kQ,fv,i0];exact Nat.factorial_le _O
       | succ d ih=>
        rw[fc,<- f0,show A+1+(d+1)=(A+1+d)+1 by omega,e6,e8 (A+1+d+1)]
        exact eH ih _O
      simpa[show A+1+(m-(A+1))=m by omega] using X (m-(A+1))
     exact_mod_cast Q
    have H5:(((k-1:ℕ):O)^(k-m))<=(k:O)^(k-m):=m9 (dK _) (_M (i4 k 1)) _
    calc (1/(m.factorial:O))*(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O))
        <= (1/(((200*(200+j.1)).factorial:O)*(2:O)^(m-(200*(200+j.1)+1)))) *((k:O)^k/(k.factorial:O)):=en (dX _P Ho) ((dI H5 _P).trans H3) _P _P
      _=_:=by ring
   have hC:∑m∈Icc (200*(200+j.1)+1) k,(1:O)/(2:O)^(m-(200*(200+j.1)+1))<=2:=by
    set A:=200*(200+j.1)+1;have K:(Icc A k).image (fun m=>m-A)⊆range (k+1):=(by intro d hd;rcases dW.mp hd with⟨m,W,rfl⟩;rw[dT]at W;rw[dN];omega);have hD:Set.InjOn (fun m=>m-A) (Icc A k:Set ℕ):=by intro m1 E m2 T h;simp only[eB,dT]at E T;dsimp only at h;omega
    calc _=∑d∈(Icc A k).image (fun m=>m-A),((1:O)/2)^d:=by
          rw[fr (fun a ha b z h=>hD ha z h)];exact dF rfl fun m _=>(i6 _ _).symm
      _<=∑d∈range (k+1),((1:O)/2)^d:=dC K fun _ _ _=>_P
      _=(((1:O)/2)^(k+1)-1)/((1:O)/2-1):=fO (_N :((1:O)/2)≠1) (k+1)
      _<=2:=by have H6:0<=((1:O)/2)^(k+1):=_P;have:(((1:O)/2)^(k+1)-1)/((1:O)/2-1)=2*(1-((1:O)/2)^(k+1)):=_R;rw[this];linarith
   have H7:(k:O)/2<=(r:O):=by
    have:k<=2*r+1:=_O
    have Q:k<=2*r:=_O;have hR:(k:O)<=2*(r:O):=_M Q;linarith
   have hE:∑b∈l j,(1:O)/∏i:Fin k,((b i).factorial:O) <=((k:O)^k/(k.factorial:O))*(2/((200*(200+j.1)).factorial:O)):=by
    rw[h5]
    calc _<=∑m∈Icc (200*(200+j.1)+1) k,
            (((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O))) *(1/(2:O)^(m-(200*(200+j.1)+1))):=dG ho
      _=(((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O))) *∑m∈Icc (200*(200+j.1)+1) k,(1:O)/(2:O)^(m-(200*(200+j.1)+1)):=(dP ..).symm
      _<=(((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O)))*2:=dA hC _P
      _=_:=by ring
   have va:2*(200*(200+j.1)).factorial<=(200*(200+j.1)+1).factorial:=(by rw[e6];exact eE _ _O);have hN:∀m∈Icc (200*(200+j.1)+1) k,(1/(m.factorial:O))*(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O)) <=((k:O)^k/(k.factorial:O))*(1/(2*((200*(200+j.1)).factorial:O))) *(1/(2:O)^(m-(200*(200+j.1)+1))):=by
    intro m W;have E:=ho m W;rw[dT]at W;have H8:2*((200*(200+j.1)).factorial:O)*(2:O)^(m-(200*(200+j.1)+1))<=(m.factorial:O):=by
     have Q:2*(200*(200+j.1)).factorial*2^(m-(200*(200+j.1)+1))<=m.factorial:=by
      set A:=200*(200+j.1);have X:∀d:ℕ,2*A.factorial*2^d<=(A+1+d).factorial:=by
       intro d;induction d with
       | zero=>
        simp only[kQ,fv,i0,e6];exact eE _ _O
       | succ d ih=>
        rw[fc,<- f0,show A+1+(d+1)=(A+1+d)+1 by omega,e6,e8 (A+1+d+1)]
        exact eH ih _O
      simpa[show A+1+(m-(A+1))=m by omega] using X (m-(A+1))
     exact_mod_cast Q
    have H3:((k:O)^(k-m)/((k-m).factorial:O))<=(k:O)^k/(k.factorial:O):=by
     rw[mb _P _P];have h8:∀d:ℕ,d<=k->k.factorial<=k^d*(k-d).factorial:=by
      intro d;induction d with
      | zero=>intro _;simp
      | succ d ih=>
       intro hd;have K:k-d=(k-(d+1))+1:=_O;have hB:(k-d).factorial=(k-d)*(k-(d+1)).factorial:=by conv_lhs=>rw[K,e6,<- K]
       calc k.factorial<=k^d*(k-d).factorial:=ih _O
         _=k^d*((k-d)*(k-(d+1)).factorial):=by rw[hB]
         _<=k^d*(k*(k-(d+1)).factorial):=dR _ (eE _ (i4 k d))
         _=k^(d+1)*(k-(d+1)).factorial:=by rw[fc];ring
     have E':(k.factorial:O)<=(k:O)^m*((k-m).factorial:O):=_M (h8 m W.2);have H4:(k:O)^(k-m)*(k:O)^m=(k:O)^k:=by rw[<- ee,eN W.2]
     calc (k:O)^(k-m)*(k.factorial:O)
         <= (k:O)^(k-m)*((k:O)^m*((k-m).factorial:O)):=dA E' _P
       _=(k:O)^k*((k-m).factorial:O):=by rw[<- f0,H4]
    have H5:(((k-1:ℕ):O)^(k-m))<=(k:O)^(k-m):=m9 (dK _) (_M (i4 k 1)) _
    calc (1/(m.factorial:O))*(((k-1:ℕ):O)^(k-m)/((k-m).factorial:O))
        <= (1/(2*((200*(200+j.1)).factorial:O)*(2:O)^(m-(200*(200+j.1)+1)))) *((k:O)^k/(k.factorial:O)):=en (dX _P H8) ((dI H5 _P).trans H3) _P _P
      _=_:=by ring
   have hE':∑b∈l j,(1:O)/∏i:Fin k,((b i).factorial:O) <=((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O)):=by
    rw[h5]
    calc _<=∑m∈Icc (200*(200+j.1)+1) k,
            (((k:O)^k/(k.factorial:O))*(1/(2*((200*(200+j.1)).factorial:O)))) *(1/(2:O)^(m-(200*(200+j.1)+1))):=dG hN
      _=(((k:O)^k/(k.factorial:O))*(1/(2*((200*(200+j.1)).factorial:O)))) *∑m∈Icc (200*(200+j.1)+1) k,(1:O)/(2:O)^(m-(200*(200+j.1)+1)):=(dP ..).symm
      _<=(((k:O)^k/(k.factorial:O))*(1/(2*((200*(200+j.1)).factorial:O))))*2:=dA hC _P
      _=_:=by ring
   have H9:(0:O)< (r:O):=_M e;have hq:(k:O)^k=(k:O)*(k:O)^(k-1):=by rw[<- fp,eN (_O :1<=k)]
   calc ∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b)
       <= (∑b∈l j,(1:O)/∏i:Fin k,((b i).factorial:O))/(r:O):=by rw[ma H9,e8];exact H1
     _<=(((k:O)^k/(k.factorial:O))*(1/((200*(200+j.1)).factorial:O)))/((k:O)/2):=mj _P hE' _P H7
     _=((k:O)^(k-1)/(k.factorial:O))*(2/((200*(200+j.1)).factorial:O)):=by rw[hq];field_simp [(_P :(k:O)≠0)]
 have Hp:∀j:Fin k,∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=((k:O)^(k-1)/(k.factorial:O))*(1/(2:O)^(k-j.1+10)):=by
  intro j;let s:=k-j.1;by_cases Hx:k<=200*s
  ·have hY:o j=∅:=by
    ext b;simp only[o,B,dB,fq,iC];rintro⟨⟨_,hsum⟩,he⟩;have:b j<=k:=(fi (fun _ _=>g5 _) (dJ j)).trans_eq hsum;omega
   rw[hY,gG];positivity
  ·push Not at Hx
   have c:1<=j.1:=_O;have Ha:(k:O)/2<=(j.1:O):=by
    have:k<=2*j.1:=_O
    have hR:(k:O)<=2*(j.1:O):=_M this;linarith
   let v (t:ℕ) (b:Fin k->ℕ):Fin k->ℕ:=fun i=>
    if h:i.1< j.1 then b ⟨(i.1+t) % j.1,by have:=dY (i.1+t) c;omega⟩
    else b i
   have h9:∀t,∀b∈o j,v t b∈o j:=by
    intro t b z;simp only[o,B,dB,e5,dN]at z ⊢;refine⟨⟨fun i=>by dsimp only[v];split_ifs;exact z.1.1 _;exact z.1.1 i,?_⟩,?_⟩
    ·trans ∑i:Fin k,b i
     ·rw[<- eh univ (fun i:Fin k=>i.1< j.1),<- eh univ (fun i:Fin k=>i.1< j.1)];congr 1
      ·refine fh (fun i hi=>⟨(i.1+t) % j.1,by have:=dY (i.1+t) c;have:=j.2;omega⟩) (fun i hi=>by simp only[dB,dJ,dV];exact dY _ c)
        (fun i1 E i2 T h=>by
         simp only[dB,dJ,dV]at E T;have hv:(i1.1+t) % j.1=(i2.1+t) % j.1:=es h;have h3:=fT (fun u=>(u+(j.1-t % j.1)) % j.1) hv;rw[cn c E,cn c T]at h3;exact dQ h3)
        (fun i hi=>by
         simp only[dB,dJ,dV]at hi;refine⟨⟨(i.1+(j.1-t % j.1)) % j.1,by have:=dY (i.1+(j.1-t % j.1)) c;have:=j.2;omega⟩,by simp only[dB,dJ,dV];exact dY _ c,dQ (by dsimp only;exact cn' c hi)⟩)
        (fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[v];rw[eG hi])
      ·exact dF rfl fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[v];rw[eA hi]
     ·exact z.1.2
    ·dsimp only[v];rw[eA (gU _)];exact z.2
   have hF:∀t b,∏i:Fin k,((v t b i).factorial:O)=∏i:Fin k,((b i).factorial:O):=by
    intro t b;rw[<- ey univ (fun i:Fin k=>i.1< j.1),<- ey univ (fun i:Fin k=>i.1< j.1)];congr 1
    ·refine hJ (fun i hi=>⟨(i.1+t) % j.1,by have:=dY (i.1+t) c;have:=j.2;omega⟩) (fun i hi=>by simp only[dB,dJ,dV];exact dY _ c)
      (fun i1 E i2 T h=>by
       simp only[dB,dJ,dV]at E T;have hv:(i1.1+t) % j.1=(i2.1+t) % j.1:=es h;have h3:=fT (fun u=>(u+(j.1-t % j.1)) % j.1) hv;rw[cn c E,cn c T]at h3;exact dQ h3)
      (fun i hi=>by
       simp only[dB,dJ,dV]at hi;refine⟨⟨(i.1+(j.1-t % j.1)) % j.1,by have:=dY (i.1+(j.1-t % j.1)) c;have:=j.2;omega⟩,by simp only[dB,dJ,dV];exact dY _ c,dQ (by dsimp only;exact cn' c hi)⟩)
      (fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[v];rw[eG hi])
    ·exact f9 rfl fun i hi=>by simp only[dB,dJ,dV]at hi;dsimp only[v];rw[eA hi]
   have Hb:∀b∈o j,∑t∈range j.1,(cj (v t b))⁻¹ <=(2:O)^(((∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i:ℕ):ℤ)-(s:ℤ)):=by
    intro b z;let x (i:ℕ):O:=(2:O)^((b ⟨i % j.1,by have:=dY i c;omega⟩:ℤ)-1)
    let hw:ℤ:=((∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i:ℕ):ℤ)-(s:ℤ);have HZ:0<=hw:=(by have E:b j<=∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i:=fi (fun _ _=>g5 _) (by simp);have T:200*s< b j:=(dB.mp z).2;dsimp only[hw];omega);have h4:∏i∈range j.1,x i=(2:O)^(-hw):=by
     rw[cp];congr 1;rw[f2,ex,fy,e3,fv];have v0:∑i∈range j.1,(b ⟨i % j.1,by have:=dY i c;omega⟩:ℤ) =(∑i∈univ.filter (fun i:Fin k=>i.1< j.1),b i:ℕ):=by rw[jp];exact fh (fun i hi=>⟨i,by rw[dN]at hi;omega⟩) (fun i hi=>by rw[dN]at hi;simp only[dB,dJ,dV];exact hi) (fun _ _ _ _ h=>es h) (fun i hi=>by simp only[dB,dJ,dV]at hi;exact⟨i.1,dN.mpr hi,rfl⟩) (fun i hi=>by rw[dN]at hi;congr 2;apply dQ;dsimp only;exact gi hi)
     have hA:=(dB.mp (dB.mp z).1).2;rw[<- eh univ (fun i:Fin k=>i.1< j.1)]at hA;have H0:univ.filter (fun i:Fin k=>¬ i.1< j.1)=univ.filter (fun i:Fin k=>j.1<=i.1):=(by ext i;simp[Nat.not_lt]);rw[H0]at hA;rw[v0];dsimp only[hw,s];omega
    have hp:∏i∈range j.1,x i<=1:=(by rw[h4];exact mJ _N _O);have hg:=(cl c x (fun _=>by positivity) (fun i=>by
     dsimp only[x];have hy:(⟨(i+j.1) % j.1,by have:=dY (i+j.1) c;have:=j.2;omega⟩:Fin k) =⟨i % j.1,by have:=dY i c;have:=j.2;omega⟩:=dQ (kZ i j.1)
     rw[hy])).2
    rw[jo hp,h4,g9,<- zpow_neg,neg_neg]at hg;have hL:∀t∈range j.1,∑h∈range j.1,∏i∈range (h+1),x (t+i)<=cj (v t b):=by
     intro t _;unfold cj
     calc _=∑h∈univ.filter (fun h:Fin k=>h.1< j.1),
             (2:O)^(((∑i∈univ.filter (fun i:Fin k=>i.1<=h.1),v t b i:ℕ):ℤ)-(h.1:ℤ)-1):=by
           refine fh (fun h hh=>⟨h,by rw[dN]at hh;omega⟩) (fun h hh=>by rw[dN]at hh;simp only[dB,dJ,dV];exact hh) (fun _ _ _ _ h=>es h) (fun h hh=>by simp only[dB,dJ,dV]at hh;exact⟨h.1,dN.mpr hh,rfl⟩) (fun h hh=>?_)
           rw[dN]at hh;rw[cp];congr 1;rw[f2,ex,fy,e3,fv]
           have v1:∑i∈range (h+1),(b ⟨(t+i) % j.1,by have:=dY (t+i) c;have:=j.2;omega⟩:ℤ) =(∑i∈univ.filter (fun i:Fin k=>i.1<=h),v t b i:ℕ):=by
             rw[jp]
             exact fh (fun i hi=>⟨i,by rw[dN]at hi;omega⟩) (fun i hi=>by rw[dN]at hi;simp only[dB,dJ,dV];omega) (fun _ _ _ _ h=>es h) (fun i hi=>by simp only[dB,dJ,dV]at hi;exact⟨i.1,dN.mpr _O,rfl⟩)
               (fun i hi=>by
                 rw[dN]at hi;dsimp only[v];rw[eG _O];congr 2;apply dQ;dsimp only;rw[ip])
           dsimp only;rw[v1];omega
       _<=_:=dC (fj _ _) fun _ _ _=>_P
    refine (dG fun t ht=>inv_anti₀ ?_ (hL t ht)).trans hg
    exact e9 _P (fi (fun _ _=>by positivity) (dN.mpr c))
   have Hc:(j.1:O)*∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=(2:O)^(-(s:ℤ))*∑b∈o j,(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i)/∏i:Fin k,((b i).factorial:O):=by
    have U:∀t∈range j.1,∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b) =∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj (v t b)):=by
     intro t _;symm;refine fh (fun b _=>v t b) (fun b z=>h9 t b z)
      (fun b1 _ b2 _ h=>by
       funext i;by_cases hi:i.1< j.1
       ·have:=gH h ⟨(i.1+(j.1-t % j.1)) % j.1,by have:=dY (i.1+(j.1-t % j.1)) c;have:=j.2;omega⟩
        dsimp only[v]at this;rw[eG (dY _ c),eG (dY _ c)]at this;have H2:(⟨((i.1+(j.1-t % j.1)) % j.1+t) % j.1,by have:=dY ((i.1+(j.1-t % j.1)) % j.1+t) c;have:=j.2;omega⟩:Fin k)=i:=dQ (by dsimp only;exact cn' c hi)
        rw[H2]at this;exact this
       ·have:=gH h i;dsimp only[v]at this;rwa[eA hi,eA hi]at this)
      (fun b z=>⟨v (j.1-t % j.1) b,h9 _ b z,by
       funext i;dsimp only[v];by_cases hi:i.1< j.1
       ·rw[eG hi,eG (dY _ c)];congr 1;exact dQ (by dsimp only;exact cn c hi)
       ·rw[eA hi,eA hi]⟩)
      (fun b _=>by rw[hF])
    calc (j.1:O)*∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b)
        = ∑t∈range j.1,∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj (v t b)):=by rw[<- dF rfl U,ex,fy,e3]
      _=∑b∈o j,(1/∏i:Fin k,((b i).factorial:O))*∑t∈range j.1,(cj (v t b))⁻¹:=by
          rw[hH];refine dF rfl fun b _=>by
            rw[dP];refine dF rfl fun t _=>_R
      _<=∑b∈o j,(1/∏i:Fin k,((b i).factorial:O)) *(2:O)^(((∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i:ℕ):ℤ)-(s:ℤ)):=dG fun b z=>dA (Hb b z) _P
      _=_:=by
          rw[dP];refine dF rfl fun b _=>?_
          rw[mE _N,fo,zpow_neg,fo];ring
   have hP:∑b∈o j,(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i)/∏i:Fin k,((b i).factorial:O) =∑m∈Icc (200*s+1) k,((2:O)^m/(m.factorial:O)) *(((k+s-2:ℕ):O)^(k-m)/((k-m).factorial:O)):=by
    let w:Fin k->O:=fun i=>if j.1<=i.1 then 2 else 1;let H:Fin (k-1)->Fin k:=fun i=>if h:i.1< j.1 then ⟨i.1,_O⟩ else ⟨i.1+1,_O⟩;have D:Function.Injective H:=by
     intro a b Z;dsimp only[H]at Z;split_ifs at Z with E T
     ·exact dQ (es Z)
     ·exfalso;have:=es Z;omega
     ·exfalso;have:=es Z;omega
     ·exact dQ (by have:=es Z;omega)
    have J:∀i:Fin (k-1),H i≠j:=(by intro i;dsimp only[H];split_ifs <;> intro h <;> have:=es h <;> omega);have y:∀i∈univ.erase j,∃t,∃(_:t∈(univ:Finset (Fin (k-1)))),H t=i:=by
     intro i hi;have HA:i.1≠j.1:=fun h=>(gS.mp hi).1 (dQ h);by_cases he:i.1< j.1
     ·exact⟨⟨i.1,_O⟩,dJ _,by dsimp only[H];rw[eG he]⟩
     ·exact⟨⟨i.1-1,_O⟩,dJ _,by dsimp only[H];rw[eA _O];exact dQ (by dsimp only;omega)⟩
    have Hq:∑i:Fin (k-1),w (H i)=((k+s-2:ℕ):O):=by
     have E:∑i:Fin (k-1),w (H i)+w j=∑i:Fin k,w i:=(by rw[<- fJ univ w (dJ j),ip];congr 1;exact fh (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun _ _=>rfl));have T:∑i:Fin k,w i=(k:O)+(s:O):=by
      rw[<- eh univ (fun i:Fin k=>j.1<=i.1)];have v2:∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),w i=2*(s:O):=by
       have hc:(univ.filter (fun i:Fin k=>j.1<=i.1)).card=s:=by
        conv_rhs=>rw[<- fy s]
        exact hO (fun (i:Fin k) _=>i.1-j.1) (fun i hi=>by simp only[dB,dJ,dV]at hi;rw[dN];omega) (fun i1 E i2 T h=>by simp only[dB,dJ,dV]at E T;exact dQ _O) (fun t ht=>⟨⟨j.1+t,by rw[dN]at ht;omega⟩,by simp only[dB,dJ,dV];omega,by dsimp only;omega⟩)
       have Hd:∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),w i =∑_i∈univ.filter (fun i:Fin k=>j.1<=i.1),(2:O):=dF rfl fun i hi=>by dsimp only[w];rw[iM (dB.mp hi).2]
       rw[Hd,ex,hc,e3];ring
      have he:∑i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),w i=(j.1:O):=by
       have hc:(univ.filter (fun i:Fin k=>¬ j.1<=i.1)).card=j.1:=by
        conv_rhs=>rw[<- fy j.1]
        exact hO (fun (i:Fin k) _=>i.1) (fun i hi=>by simp only[dB,dJ,dV]at hi;rw[dN];omega) (fun _ _ _ _ h=>dQ h) (fun t ht=>⟨⟨t,by rw[dN]at ht;omega⟩,by rw[dN]at ht;simp only[dB,dJ,dV];omega,rfl⟩)
       have Hd:∑i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),w i =∑_i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),(1:O):=dF rfl fun i hi=>by dsimp only[w];rw[gc (dB.mp hi).2]
       rw[Hd,ex,hc,e3];ring
      rw[v2,he];have:j.1+s=k:=_O;have hR:(j.1:O)+(s:O)=(k:O):=_M this;linarith
     have HK:w j=2:=(by dsimp only[w];rw[iM eR]);have vb:((k+s-2:ℕ):O)=(k:O)+(s:O)-2:=(by rw[ei _O,jX];norm_num);linarith
    have hM:∀m∈Icc (200*s+1) k,(((k+s-2:ℕ):O)^(k-m)/((k-m).factorial:O)) =∑b'∈(Fintype.piFinset fun _:Fin (k-1)=>range (k-m+1)).filter (fun b'=>∑i,b' i=k-m),∏i:Fin (k-1),w (H i)^(b' i)/((b' i).factorial:O):=(by intro m _;rw[<- Hq,cm]);conv_rhs=>rw[dF rfl fun m W=>by rw[hM m W]]
    simp_rw [dP];rw[gY]
    refine fh (fun b _=>⟨b j,fun i=>b (H i)⟩) ?_ ?_ ?_ ?_
    ·intro b z;simp only[o,B,dB,e5,dN,fg,dT]at z ⊢;have P:∑i:Fin (k-1),b (H i)+b j=k:=by
      trans ∑i:Fin k,b i
      ·rw[<- fJ univ b (dJ j),ip];congr 1;exact fh (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun _ _=>rfl)
      ·exact z.1.2
     refine⟨⟨by omega,_O⟩,fun i=>?_,_O⟩
     have:b (H i)<=∑t:Fin (k-1),b (H t):=fi (f:=fun t:Fin (k-1)=>b (H t)) (fun _ _=>g5 _) (dJ i)
     omega
    ·intro b1 _ b2 _ hf;simp only[fG,iD]at hf;funext i;by_cases hi:i=j
     ·rw[hi,hf.1]
     ·have HA:i.1≠j.1:=fun h=>hi (dQ h);by_cases he:i.1< j.1
      ·have:=gH hf.2 ⟨i.1,_O⟩;dsimp only[H]at this;rwa[eG he]at this
      ·have:=gH hf.2 ⟨i.1-1,_O⟩;dsimp only[H]at this
       rw[eA _O]at this;simpa[show (⟨i.1-1+1,_O⟩:Fin k)=i from dQ (by dsimp only;omega)] using this
    ·intro ⟨m,b'⟩ hx;simp only[fg,dT,dB,e5,dN]at hx;let b:Fin k->ℕ:=fun i=>if E:i.1< j.1 then b' ⟨i.1,_O⟩
      else if T:i.1=j.1 then m else b' ⟨i.1-1,_O⟩
     have h6:∀i:Fin (k-1),b (H i)=b' i:=by
      intro i;dsimp only[b,H];by_cases hi:i.1< j.1
      ·rw[eG hi,eG hi]
      ·rw[eA hi,eA (by dsimp only;omega),eA (by dsimp only;omega)];congr 1
     have h7:b j=m:=(by dsimp only[b];rw[eA (gU _),eG rfl]);refine⟨b,?_,?_⟩
     ·simp only[o,B,dB,e5,dN];refine⟨⟨fun i=>by
       dsimp only[b];split_ifs
       ·have:=hx.2.1 ⟨i.1,_O⟩;omega
       ·omega
       ·have:=hx.2.1 ⟨i.1-1,_O⟩;omega,?_⟩,
       by rw[h7];omega⟩
      rw[<- fJ univ b (dJ j),h7];have P:∑i∈univ.erase j,b i=∑i:Fin (k-1),b' i:=(by symm;refine fh (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun i _=>(h6 i).symm));rw[P,hx.2.2];omega
     ·simp only[fG,iD,h7,dV];funext i;exact h6 i
    ·intro b _;have Hr:(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i)=∏i:Fin k,w i^(b i):=by
      rw[<- ey univ (fun i:Fin k=>j.1<=i.1)];have E:∏i∈univ.filter (fun i:Fin k=>j.1<=i.1),w i^(b i) =(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i):=by
       have HL:∏i∈univ.filter (fun i:Fin k=>j.1<=i.1),w i^(b i) =∏i∈univ.filter (fun i:Fin k=>j.1<=i.1),(2:O)^(b i):=f9 rfl fun i hi=>by dsimp only[w];rw[iM (dB.mp hi).2]
       rw[HL,kq]
      have T:∏i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),w i^(b i)=1:=by
       have HM:∏i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),w i^(b i) =∏_i∈univ.filter (fun i:Fin k=>¬ j.1<=i.1),(1:O):=f9 rfl fun i hi=>by dsimp only[w];rw[gc (dB.mp hi).2,jQ]
       rw[HM,kb]
      rw[E,T,fv]
     rw[Hr,<- gM,<- gk univ _ (dJ j)];have HK:w j=2:=(by dsimp only[w];rw[iM eR]);rw[HK];congr 1;symm;refine hJ (fun i _=>H i) (fun i _=>gS.mpr ⟨J i,dJ _⟩) (fun _ _ _ _ h=>D h) y (fun _ _=>rfl)
   have He:((k+s:O))^k<=exp (s:O)*(k:O)^k:=by
    have E:(1+(s:O)/(k:O))^k<=exp (s:O):=by
     calc (1+(s:O)/(k:O))^k<=(exp ((s:O)/(k:O)))^k:=
           m9 _P (_l (fB ((s:O)/(k:O)))) k
       _=exp ((k:O)*((s:O)/(k:O))):=(gg _ _).symm
       _=exp (s:O):=by congr 1;field_simp [(_P :(k:O)≠0)]
    have hf:(k:O)+(s:O)=(k:O)*(1+(s:O)/(k:O)):=(by field_simp [(_P :(k:O)≠0)]);rw[hf,eP];nlinarith[fK (_P :(0:O)<=(k:O)) k]
   have Hs:∀m∈Icc (200*s+1) k,((2:O)^m/(m.factorial:O))*(((k+s-2:ℕ):O)^(k-m)/((k-m).factorial:O)) <=(exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O))*(1/(2:O)^(m-(200*s+1))):=by
    intro m W;rw[dT]at W;have H3:(((k+s-2:ℕ):O)^(k-m)/((k-m).factorial:O)) <=((k:O)+(s:O))^k/(k.factorial:O):=by
     have HB:((k+s-2:ℕ):O)<=(k:O)+(s:O):=by
      have:k+s-2<=k+s:=i4 _ _
      exact_mod_cast this
     have HC:=m9 (dK _) HB (k-m);refine (dI HC _P).trans ?_
     rw[mb _P _P];have h8:∀d:ℕ,d<=k->k.factorial<=k^d*(k-d).factorial:=by
      intro d;induction d with
      | zero=>intro _;simp
      | succ d ih=>
       intro hd;have K:k-d=(k-(d+1))+1:=_O;have hB:(k-d).factorial=(k-d)*(k-(d+1)).factorial:=by conv_lhs=>rw[K,e6,<- K]
       calc k.factorial<=k^d*(k-d).factorial:=ih _O
         _=k^d*((k-d)*(k-(d+1)).factorial):=by rw[hB]
         _<=k^d*(k*(k-(d+1)).factorial):=dR _ (eE _ (i4 k d))
         _=k^(d+1)*(k-(d+1)).factorial:=by rw[fc];ring
     have E:(k.factorial:O)<=((k:O)+(s:O))^m*((k-m).factorial:O):=(by have E':(k.factorial:O)<=(k:O)^m*((k-m).factorial:O):=_M (h8 m W.2);exact E'.trans (dE (m9 (dK _) _L m) _P));have HD:((k:O)+(s:O))^(k-m)*((k:O)+(s:O))^m=((k:O)+(s:O))^k:=by rw[<- ee,eN W.2]
     calc ((k:O)+(s:O))^(k-m)*(k.factorial:O)
         <= ((k:O)+(s:O))^(k-m)*(((k:O)+(s:O))^m*((k-m).factorial:O)):=dA E _P
       _=((k:O)+(s:O))^k*((k-m).factorial:O):=by rw[<- f0,HD]
    have Ht:(2:O)^m/(m.factorial:O) <=((2:O)^(200*s+1)/((200*s+1).factorial:O))*(1/(2:O)^(m-(200*s+1))):=by
     set A:=200*s+1;have Hf:(A.factorial:O)*(4:O)^(m-A)<=(m.factorial:O):=by
      have Q:A.factorial*4^(m-A)<=m.factorial:=by
       have X:∀d:ℕ,A.factorial*4^d<=(A+d).factorial:=by
        intro d;induction d with
        | zero=>simp
        | succ d ih=>
         rw[fc,<- f0];conv_rhs=>rw[show A+(d+1)=(A+d)+1 by omega,e6,e8]
         exact eH ih _O
       simpa[iW W.1] using X (m-A)
      exact_mod_cast Q
     have v3:(2:O)^m=(2:O)^A*(2:O)^(m-A):=(by rw[<- ee,iW W.1]);have v4:(4:O)^(m-A)=(2:O)^(m-A)*(2:O)^(m-A):=(by rw[<- eP];norm_num);rw[v3]
     calc (2:O)^A*(2:O)^(m-A)/(m.factorial:O)
         <= (2:O)^A*(2:O)^(m-A)/((A.factorial:O)*(4:O)^(m-A)):=dL _P _P Hf
       _=_:=by rw[v4];field_simp [(_P :(A.factorial:O)≠0),(_P :(2:O)^(m-A)≠0)]
    calc ((2:O)^m/(m.factorial:O))*(((k+s-2:ℕ):O)^(k-m)/((k-m).factorial:O))
        <= (((2:O)^(200*s+1)/((200*s+1).factorial:O))*(1/(2:O)^(m-(200*s+1)))) *(exp (s:O)*(k:O)^k/(k.factorial:O)):=en Ht (H3.trans (dI He _P)) _P _P
      _=_:=by ring
   have Hu:∑m∈Icc (200*s+1) k,(1:O)/(2:O)^(m-(200*s+1))<=2:=by
    set A:=200*s+1;have K:(Icc A k).image (fun m=>m-A)⊆range (k+1):=(by intro d hd;rcases dW.mp hd with⟨m,W,rfl⟩;rw[dT]at W;rw[dN];omega);have hD:Set.InjOn (fun m=>m-A) (Icc A k:Set ℕ):=by intro m1 E m2 T h;simp only[eB,dT]at E T;dsimp only at h;omega
    calc _=∑d∈(Icc A k).image (fun m=>m-A),((1:O)/2)^d:=by
          rw[fr (fun a ha b z h=>hD ha z h)];exact dF rfl fun m _=>(i6 _ _).symm
      _<=∑d∈range (k+1),((1:O)/2)^d:=dC K fun _ _ _=>_P
      _=(((1:O)/2)^(k+1)-1)/((1:O)/2-1):=fO (_N :((1:O)/2)≠1) (k+1)
      _<=2:=by have H6:0<=((1:O)/2)^(k+1):=_P;have:(((1:O)/2)^(k+1)-1)/((1:O)/2-1)=2*(1-((1:O)/2)^(k+1)):=_R;rw[this];linarith
   have HN:4*(2:O)^(-(s:ℤ))*exp (s:O)*((2:O)^(200*s+1)/((200*s+1).factorial:O)) <=1/(2:O)^(s+10):=by
    have HO:(2:O)^(201*s+20)*(3:O)^s<=((200*s+1).factorial:O):=by
     have Q:2^(201*s+20)*3^s<=(200*s+1).factorial:=by
      have v5:1<=s:=_O;have X:∀n:ℕ,1<=n->2^(201*n+20)*3^n<=(200*n+1).factorial:=by
       intro n hn;induction n,hn using fe with
       | base=>
        have v6:∀m:ℕ,16^m<=(16+m).factorial:=by
         intro m;induction m with
         | zero=>exact iV 16
         | succ m ih=>
          rw[fc];conv_rhs=>rw[show 16+(m+1)=(16+m)+1 by omega,e6,e8]
          exact eH ih _O
        have E:=v6 185;have T:2^221*3<=16^185:=by
         calc 2^221*3<=2^221*2^2:=dR _ _N
           _=2^223:=by rw[<- ee]
           _<=2^(4*185):=dH _N _O
           _=(2^4)^185:=it 2 4 185
           _=16^185:=by norm_num
        exact T.trans E
       | succ n hn ih=>
        have U:∀d:ℕ,(200*n+1).factorial*16^d<=(200*n+1+d).factorial:=by
         intro d;induction d with
         | zero=>simp
         | succ d ihd=>
          rw[fc,<- f0];conv_rhs=>rw[show 200*n+1+(d+1)=(200*n+1+d)+1 by omega,e6,e8]
          exact eH ihd _O
        have T:2^201*3<=16^200:=by
         calc 2^201*3<=2^201*2^2:=dR _ _N
           _=2^203:=by rw[<- ee]
           _<=2^(4*200):=dH _N _O
           _=(2^4)^200:=it 2 4 200
           _=16^200:=by norm_num
        calc 2^(201*(n+1)+20)*3^(n+1)
            = (2^(201*n+20)*3^n)*(2^201*3):=by rw[show 201*(n+1)+20=(201*n+20)+201 by omega,ee,fc];ring
          _<=(200*n+1).factorial*16^200:=eH ih T
          _<=(200*n+1+200).factorial:=U 200
          _=(200*(n+1)+1).factorial:=by congr 1
      exact X s v5
     exact_mod_cast Q
    have HT:exp (s:O)<=(3:O)^s:=by
     calc exp (s:O)=exp ((s:ℕ)*(1:O)):=by ring_nf
       _=(exp 1)^s:=gg 1 s
       _<=(3:O)^s:=m9 (ez 1).le (_l gT) s
    rw[zpow_neg,fo,ic,ic];have Hv:0< ((200*s+1).factorial:O):=_P;have HP:4*((2:O)^s)⁻¹*exp (s:O)*((2:O)^(200*s+1)*((200*s+1).factorial:O)⁻¹) =(4*((2:O)^s)⁻¹*(exp (s:O)*(2:O)^(200*s+1)))*((200*s+1).factorial:O)⁻¹:=_R;rw[HP,mul_inv_le_iff₀ Hv];have HQ:0< (2:O)^s:=_P
    calc 4*((2:O)^s)⁻¹*(exp (s:O)*(2:O)^(200*s+1))
        <= 4*1*((3:O)^s*(2:O)^(200*s+1)):=by have v7:((2:O)^s)⁻¹<=1:=inv_le_one_of_one_le₀ (mo (_N :(1:O)<=2));gcongr
      _=(2:O)^(200*s+3)*(3:O)^s:=by rw[ee];norm_num;ring
      _<=1*((2:O)^(s+10))⁻¹*((2:O)^(201*s+20)*(3:O)^s):=by
          rw[gz,inv_mul_eq_div,ma _P]
          calc (2:O)^(200*s+3)*(3:O)^s*(2:O)^(s+10)
              = (2:O)^(201*s+13)*(3:O)^s:=by rw[lH,<- ee];congr 2;omega
            _<=(2:O)^(201*s+20)*(3:O)^s:=dE (mg _N _O) _P
      _<=1*((2:O)^(s+10))⁻¹*((200*s+1).factorial:O):=by gcongr
   have Hg:∑b∈o j,(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i)/∏i:Fin k,((b i).factorial:O) <=2*(exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O)):=by
    rw[hP]
    calc _<=∑m∈Icc (200*s+1) k,
            ((exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O))) *
            (1/(2:O)^(m-(200*s+1))):=dG Hs
      _=((exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O))) *∑m∈Icc (200*s+1) k,(1:O)/(2:O)^(m-(200*s+1)):=(dP ..).symm
      _<=((exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O)))*2:=dA Hu _P
      _=_:=by ring
   have Hh:(0:O)< (j.1:O):=_M c;have hq:(k:O)^k=(k:O)*(k:O)^(k-1):=by rw[<- fp,eN (_O :1<=k)]
   calc ∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b)
       <= ((2:O)^(-(s:ℤ))*∑b∈o j,(2:O)^(∑i∈univ.filter (fun i:Fin k=>j.1<=i.1),b i)/∏i:Fin k,((b i).factorial:O)) /(j.1:O):=by rw[ma Hh,e8];exact Hc
     _<=((2:O)^(-(s:ℤ))*(2*(exp (s:O)*(k:O)^k/(k.factorial:O)) *((2:O)^(200*s+1)/((200*s+1).factorial:O))))/((k:O)/2):=mj _P (dA Hg _P) _P Ha
     _=((k:O)^(k-1)/(k.factorial:O)) *(4*(2:O)^(-(s:ℤ))*exp (s:O)*((2:O)^(200*s+1)/((200*s+1).factorial:O))):=by rw[hq];field_simp [(_P :(k:O)≠0)];ring
     _<=((k:O)^(k-1)/(k.factorial:O))*(1/(2:O)^(s+10)):=dA HN _P
 have Hi:∑j:Fin k,∑b∈l j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=((k:O)^(k-1)/(k.factorial:O))/4:=by
  have Hj:∀j:Fin k,2/((200*(200+j.1)).factorial:O)<=1/(8*(2:O)^j.1):=by
   intro j;rw[mb _P _P];have Q:16*2^j.1<=(200*(200+j.1)).factorial:=by
    have E:16*2^j.1=2^(j.1+4):=(by rw[ee];norm_num;ring);have T:∀d:ℕ,2^d<=(d+4).factorial:=by
     intro d;induction d with
     | zero=>norm_num
     | succ d ih=>
      rw[fc,show d+1+4=(d+4)+1 by omega,e6,e8 (d+4+1)]
      exact eH ih _O
    calc 16*2^j.1=2^(j.1+4):=E
      _<=(j.1+8).factorial:=T (j.1+4)
      _<=(200*(200+j.1)).factorial:=Nat.factorial_le _O
   have hR:16*(2:O)^j.1<=((200*(200+j.1)).factorial:O):=_M Q;linarith
  calc _<=∑j:Fin k,((k:O)^(k-1)/(k.factorial:O))*(1/(8*(2:O)^j.1)):=
        dG fun j _=>(Hn j).trans (dA (Hj j) _P)
    _=((k:O)^(k-1)/(k.factorial:O))*((1/8:O)*∑j:Fin k,((1:O)/2)^j.1):=by rw[dP,dP];refine dF rfl fun j _=>by rw[i6];ring
    _<=((k:O)^(k-1)/(k.factorial:O))*((1/8:O)*2):=by
        refine dA (dA ?_ _N) _P
        have HR:∑j:Fin k,((1:O)/2)^j.1=∑r∈range k,((1:O)/2)^r:=fh (fun j _=>j.1) (fun j _=>dN.mpr j.2) (fun _ _ _ _ h=>dQ h) (fun r hr=>⟨⟨r,dN.mp hr⟩,dJ _,rfl⟩) (fun _ _=>rfl);rw[HR,fO (_N :((1:O)/2)≠1) k];have H6:0<=((1:O)/2)^k:=_P;have:(((1:O)/2)^k-1)/((1:O)/2-1)=2*(1-((1:O)/2)^k):=_R;rw[this];linarith
    _=((k:O)^(k-1)/(k.factorial:O))/4:=_R
 have Hk:∑j:Fin k,∑b∈o j,1/((∏i:Fin k,((b i).factorial:O))*cj b) <=((k:O)^(k-1)/(k.factorial:O))/4:=by
  calc _<=∑j:Fin k,((k:O)^(k-1)/(k.factorial:O))*(1/(2:O)^(k-j.1+10)):=
        dG fun j _=>Hp j
    _=((k:O)^(k-1)/(k.factorial:O))*((1/1024:O)*∑j:Fin k,((1:O)/2)^(k-j.1)):=by
        rw[dP,dP];refine dF rfl fun j _=>by
          rw[ee,i6];norm_num
    _<=((k:O)^(k-1)/(k.factorial:O))*((1/1024:O)*2):=by
        refine dA (dA ?_ _N) _P
        have K:(univ:Finset (Fin k)).image (fun j:Fin k=>k-j.1)⊆range (k+1):=(by intro d hd;rcases dW.mp hd with⟨j,_,rfl⟩;rw[dN];omega);have hD:Set.InjOn (fun j:Fin k=>k-j.1) ((univ:Finset (Fin k)):Set (Fin k)):=by intro j1 _ j2 _ h;dsimp only at h;exact dQ (by have:=j1.2;have:=j2.2;omega)
        calc ∑j:Fin k,((1:O)/2)^(k-j.1)
            = ∑d∈(univ:Finset (Fin k)).image (fun j:Fin k=>k-j.1),((1:O)/2)^d:=(fr (fun a ha b z h=>hD ha z h)).symm
          _<=∑d∈range (k+1),((1:O)/2)^d:=dC K fun _ _ _=>_P
          _=(((1:O)/2)^(k+1)-1)/((1:O)/2-1):=fO (_N :((1:O)/2)≠1) (k+1)
          _<=2:=by have H6:0<=((1:O)/2)^(k+1):=_P;have:(((1:O)/2)^(k+1)-1)/((1:O)/2-1)=2*(1-((1:O)/2)^(k+1)):=_R;rw[this];linarith
    _<=((k:O)^(k-1)/(k.factorial:O))/4:=by
        have:(0:O)<=(k:O)^(k-1)/(k.factorial:O):=_P
        linarith
 let F (b:Fin k->ℕ):O:=1/((∏i:Fin k,((b i).factorial:O))*cj b);have hQ:∀b,0<=F b:=fun b=>by
  dsimp only[F];have:0<=cj b:=ea fun _ _=>_P;positivity
 have HU:∑b∈B \ M,F b+∑b∈M,F b=∑b∈B,F b:=sum_sdiff (fj _ _);have hS:∀(G:Fin k->Finset (Fin k->ℕ)),∑b∈univ.biUnion G,F b<=∑j:Fin k,∑b∈G j,F b:=by
  intro G;have X:∀S:Finset (Fin k),∑b∈S.biUnion G,F b<=∑j∈S,∑b∈G j,F b:=by
   intro S;induction S using eW with
   | empty=>simp
   | @insert a S ha ih=>
    rw[iS,i3 ha];have hu:=fb (s₁:=G a) (s₂:=S.biUnion G) (f:=F);have H6:0<=∑b∈G a∩S.biUnion G,F b:=ea fun b _=>hQ b;linarith
  exact X univ
 have HE:∑b∈B \ M,F b<=((k:O)^(k-1)/(k.factorial:O))/2:=by have hu:=fb (s₁:=univ.biUnion l) (s₂:=univ.biUnion o) (f:=F);have H6:0<=∑b∈univ.biUnion l∩univ.biUnion o,F b:=ea fun b _=>hQ b;have E:=dC HI (fun b _ _=>hQ b);have T:=hS l;have h3:=hS o;linarith
 have HF:(k:O)^(k-1)/(k.factorial:O)/2=(k:O)^(k-1)/(2*(k.factorial:O)):=_R;linarith
set_option maxHeartbeats 800000 in
theorem ford_lower_bound :
 let α : O:=1-(1+log (log 2))/log 2
 let w (j:ℕ):=((j:O)+1)^(-α)/(log ((j:O)+2))^((3:O)/2)
 ∃c:O,0< c/\∀ᶠ x:ℕ in atTop,∀j ≤ Nat.log 2 x/2,c*((x:O)*w j)<=((c6 x j).card:O):=by
 intro α w;obtain⟨u,l,H3⟩:=c9;obtain⟨J0,E,hc⟩:∃J0:ℕ,(∀j,J0<=j->1600<=Nat.log 2 j)/\1000<=J0:=⟨2^1600,fun j hj=>(Nat.le_log_iff_pow_le _N (by have:=fY (n:=1600);omega)).mpr hj,(_N :1000<=2^10).trans (dH _N _O)⟩;have e:0< log 2:=_l a3;let v:O:=(u*log 2/(4*2^108*2*exp 1*20)) *((1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2));let o:O:=(1/(2:O)^(J0+1))*(log 2)^((3:O)/2);refine⟨min v o,lt_min _P _P,?_⟩;filter_upwards [lO (2^(J0+2))] with x hx j hj;have hQ:2*j<=Nat.log 2 x:=_O;by_cases hr:J0<=j
 ·
  obtain⟨k,h0⟩:∃k:ℕ,k=Nat.log 2 j-500:=⟨_,rfl⟩;have he:1600<=Nat.log 2 j:=E j hr;have hs:1000<=k:=_O;have Q:k+500=Nat.log 2 j:=_O;have z:2^(k+500)<=j:=(by rw[Q];exact gB 2 _O);have K:j+1<=2^(k+502):=by have M:j< 2^(Nat.log 2 j+1):=jJ _N j;exact M.trans_le (dH _N _O)
  let B:=(Fintype.piFinset fun _:Fin k=>range (k+1)).filter fun b=>∑i:Fin k,b i=k;let y:=B.filter fun b=>∀i:Fin k,b i<=200*(200+i.1)/\b i<=200*(k-i.1);let A:=y.biUnion fun b=>ca 200 k b;have h5:∀a∈A,1<=a/\(a:O)^8<=((2^j:ℕ):O):=by
   clear hj hQ H3 he h0 Q E;intro a ha;rcases g4.mp ha with⟨b,hb,Hq⟩;have H:=cg Hq;refine⟨H.1,?_⟩;have ht:(0:O)< (a:O):=_M H.1;rw[<- kj (iN ht 8) _P,fm,gx,fm];simp only[g7];have U:log (a:O)<=(2:O)^(k+315):=by
    refine H.2.2.2.2.trans ?_
    have hf:∀i:Fin k,log (az (200+i.1):O)<=(2:O)^(300+i.1):=(by intro i;have h:=(aJ (200+i.1) _O).2;have:(((200+i.1:ℕ):ℤ)+100)=((300+i.1:ℕ):ℤ):=_O;rwa[this,fo]at h);have hu:∀i:Fin k,(b i:O)<=200*((k-i.1:ℕ):O):=by intro i;exact_mod_cast ((dB.mp hb).2 i).2
    calc ∑i:Fin k,(b i:O)*log (az (200+i.1):O)
        <= ∑i:Fin k,(200*((k-i.1:ℕ):O))*(2:O)^(300+i.1):=dG fun i _=>en (hu i) (hf i) (f1 (_M (aD _))) (ek _N (dK _))
      _=200*(2:O)^(300+k)*∑i:Fin k,((k-i.1:ℕ):O)/(2:O)^(k-i.1):=by
          rw[dP];refine dF rfl fun i _=>?_
          have H4:(2:O)^(300+k)=(2:O)^(300+i.1)*(2:O)^(k-i.1):=(by rw[<- ee];congr 1;omega);rw[H4];field_simp [(_P :(2:O)^(k-i.1)≠0)]
      _<=200*(2:O)^(300+k)*8:=by
          refine dA ?_ _P
          have H5:(univ:Finset (Fin k)).image (fun i:Fin k=>k-i.1)⊆range (k+1):=(by intro d hd;rcases dW.mp hd with⟨i,_,rfl⟩;rw[dN];omega);have H6:Set.InjOn (fun i:Fin k=>k-i.1) ((univ:Finset (Fin k)):Set (Fin k)):=by intro i1 _ i2 _ h;dsimp only at h;exact dQ (by have:=i1.2;have:=i2.2;omega)
          have H7:∀d:ℕ,(d:O)/(2:O)^d<=2*((3:O)/4)^d:=by
            have H8:∀d:ℕ,(d:O)<=2*((3:O)/2)^d:=by
              intro d;induction d with
              | zero=>norm_num
              | succ n ih=>
                by_cases hn:n< 3
                · interval_cases n <;> norm_num
                · push_cast;rw[fp]
                  have Ht:(3:O)<=(n:O):=_M (_O :3<=n);linarith
            intro d;rw[mc _P];have hS:2*((3:O)/4)^d*(2:O)^d=2*((3:O)/2)^d:=(by rw[f0,<- eP];norm_num);rw[hS];exact H8 d
          calc ∑i:Fin k,((k-i.1:ℕ):O)/(2:O)^(k-i.1)
              = ∑d∈(univ:Finset (Fin k)).image (fun i:Fin k=>k-i.1),(d:O)/(2:O)^d:=(fr (f:=fun d:ℕ=>(d:O)/(2:O)^d) (fun a ha b hb h=>H6 ha hb h)).symm
            _<=∑d∈range (k+1),(d:O)/(2:O)^d:=dC H5 fun _ _ _=>ed (dK _) (fK _N _)
            _<=∑d∈range (k+1),2*((3:O)/4)^d:=dG fun d _=>H7 d
            _=2*((((3:O)/4)^(k+1)-1)/((3:O)/4-1)):=by rw[<- dP,fO (_N :((3:O)/4)≠1) (k+1)]
            _<=8:=by have hg:0<=((3:O)/4)^(k+1):=_P;have:2*((((3:O)/4)^(k+1)-1)/((3:O)/4-1))=8*(1-((3:O)/4)^(k+1)):=_R;rw[this];linarith
      _<=(2:O)^(k+315):=by
          rw[show k+315=(300+k)+15 by omega,ee (2:O) (300+k) 15]
          have hT:(1600:O)<=(2:O)^15:=_N;have hg:=fK (_N :(0:O)<=2) (300+k)
          calc 200*(2:O)^(300+k)*8=(2:O)^(300+k)*1600:=by ring
            _<=(2:O)^(300+k)*(2:O)^15:=dA hT hg
   have U':log (a:O)<=(2:O)^(k+315):=U;have Hk:8*(2:O)^(k+315)<=(j:O)*log 2:=by
    have hv:(2:O)^(k+500)<=(j:O):=_M z
    calc 8*(2:O)^(k+315)=(2:O)^(k+318):=by
          rw[show k+318=(k+315)+3 by omega,ee (2:O) (k+315) 3];norm_num;ring
      _<=(2:O)^(k+500)*(1/2):=by
          rw[show k+500=(k+318)+182 by omega,ee (2:O) (k+318) 182]
          have H9:(1:O)<=(2:O)^182*(1/2):=_N;have hg:=fK (_N :(0:O)<=2) (k+318)
          calc (2:O)^(k+318)=(2:O)^(k+318)*1:=(fv _).symm
            _<=(2:O)^(k+318)*((2:O)^182*(1/2)):=dA H9 hg
            _=(2:O)^(k+318)*(2:O)^182*(1/2):=_R
      _<=(j:O)*log 2:=en hv (_l a3) _N (dK j)
   linarith
  have hh:=H3 x j (hc.trans hr) hQ A h5;clear hj hQ H3 he h0 Q E;have hw:(log 2*(2*log 2)^k)/(4*2^108) *((k:O)^(k-1)/(2*(k.factorial:O)))<=∑a∈A,L a/(a:O):=by
   have hU:Set.PairwiseDisjoint (y:Set (Fin k->ℕ)) (ca 200 k):=fun b1 _ b2 _ H0=>cf 200 k H0;rw[kh hU];have hk:∀b∈y,(log 2*(2*log 2)^k)/(4*2^108) *(1/((∏i:Fin k,((b i).factorial:O))*cj b)) <=∑a∈ca 200 k b,L a/(a:O):=by
    intro b hb;have X:∑i:Fin k,b i=k:=(dB.mp (dB.mp hb).1).2;have Hl:=bT (ca 200 k b) (fun a ha=>(cg ha).1);have Ha:=ci b X (fun i=>((dB.mp hb).2 i).1);have hW:=ck (_O :1<=k) b X;have hy:0< cj b:=by have hV:(⟨k-1,_O⟩:Fin k)∈(univ:Finset (Fin k)):=dJ _;exact e9 _P (fi (fun _ _=>by positivity) hV)
    have hz:0< (2^108*(2*log 2)^k/∏i:Fin k,((b i).factorial:O))*cj b:=_P;have hl:=m9 _P Ha 2;have F:(log 2)*((2*log 2)^k/(2*∏i:Fin k,((b i).factorial:O)))^2 <=(∑a∈ca 200 k b,L a/(a:O)) *((2^108*(2*log 2)^k/∏i:Fin k,((b i).factorial:O))*cj b):=by
     calc _<=(log 2)*(∑a∈ca 200 k b,(a.divisors.card:O)/(a:O))^2:=
           dA hl e.le
       _<=(∑a∈ca 200 k b,L a/(a:O))*(∑a∈ca 200 k b,(W a:O)/(a:O)):=Hl
       _<=_:=dA hW (ea fun a _=>ed (bK a) (dK a))
    rw[<- mc hz]at F;refine gf ?_ F;have Hb:(∏i:Fin k,((b i).factorial:O))≠0:=_P;have hX:(2*log 2)^k≠0:=_P;field_simp [e.ne',Hb,hX,hy.ne'];norm_num
   calc _<=(log 2*(2*log 2)^k)/(4*2^108) *
           ∑b∈y,1/((∏i:Fin k,((b i).factorial:O))*cj b):=
         dA (cq hs) _P
     _=∑b∈y,(log 2*(2*log 2)^k)/(4*2^108) *(1/((∏i:Fin k,((b i).factorial:O))*cj b)):=dP ..
     _<=_:=dG hk
  have Hm:=a7 k _O;have hA:(k:O)^k=(k:O)*(k:O)^(k-1):=(by rw[<- fp,eN (_O :1<=k)]);have h6:(2*log 2*exp 1)^k/(exp 1*(k:O)*sqrt (k:O)) <=(2*log 2)^k*((k:O)^(k-1)/(k.factorial:O)):=(by have C:(0:O)< (k:O):=_P;have M:(2*log 2)^k*((k:O)^(k-1)/(exp 1*sqrt (k:O)*((k:O)/exp 1)^k)) <=(2*log 2)^k*((k:O)^(k-1)/(k.factorial:O)):=dA (dL _P _P Hm) _P;refine gf ?_ M;rw[ij,eP,eP];have hY:(exp 1)^k≠0:=_P;have hZ:(k:O)^(k-1)≠0:=_P;have hB:sqrt (k:O)≠0:=_P;field_simp [C.ne',hY,hZ,hB,(ez 1).ne'];rw[hA]);have Hc:2*log 2*exp 1=(2:O)^((2:O) - α):=(by have Hd:log 2*(2 - α)=log 2+1+log (log 2):=(by dsimp only[α];field_simp [e.ne'];ring);rw[fQ (_N :(0:O)< 2),Hd,gX,gX,eX _N,eX e];ring);have hC:(j:O)+1<=(2:O)^(k+502):=_M K;have N:0< α/\α< 1:=by
   dsimp only[α];have M:log (log 2)< 0:=log_neg e a4;have h2 : -log 2< log (log 2):=(by rw[<- log_inv];exact jS _P (_l a3));have h3:(1+log (log 2))/log 2< 1:=by
    rw[lF e];have Hr:log 2< 0.7:=_l ky;have Hn:0.69< log 2:=_l kz;have Hu:log (log 2)<=log 2-1:=eY e;have hD:log (log 2)< log 2-1:=by
     have:=k7 e a4.ne
     exact this
    linarith
   have h4:0< (1+log (log 2))/log 2:=(by rw[jI e];have M:1-(log 2)⁻¹<=log (log 2):=fl e;have Hs:(log 2)⁻¹< 2:=(by rw[mz e _N];linarith[a3]);linarith);exact⟨by linarith,_L⟩
  have R:(1/(2*log 2*exp 1)^502)*(((j:O)+1)^(-α))*((j:O)+1)^2 <=(2*log 2*exp 1)^k:=(by have q:(0:O)< (j:O)+1:=lZ (dK j) one_pos;have S:0< 2 - α:=_l N.2;have M:((j:O)+1)^(2 - α)<=((2:O)^(k+502))^(2 - α):=fx q.le hC S.le;have h2:((2:O)^(k+502))^(2 - α)=(2*log 2*exp 1)^k*(2*log 2*exp 1)^502:=(by rw[<- eK (2:O),<- gE _N,e8 ((k+502:ℕ):O),gE _N,<- Hc,eK,ee]);have h3:((j:O)+1)^(2 - α)=((j:O)+1)^(-α)*((j:O)+1)^2:=(by rw[show (2:O) - α=-α+2 by ring,gF q,rpow_two]);rw[h2,h3]at M;rw[f0,one_div_mul_eq_div,mc _P];linarith);have T:log ((2^(j+1):ℕ):O)<=(j:O)+1:=by
   rw[gx,g7,fm];push_cast;have hE:(0:O)<=(j:O)+1:=jT (dK j) eO
   calc ((j:O)+1)*log 2<=((j:O)+1)*1:=dA a4.le hE
     _=(j:O)+1:=fv _
  have P:(k:O)<=log ((j:O)+2)/log 2:=by
   rw[ma e];have M:(2:O)^k<=(j:O)+2:=by have ho:2^k<=j:=(dH _N (_O :k<=k+500)).trans z;have hR:(2:O)^k<=(j:O):=_M ho;linarith
   have h2:=dM _P M;rwa[fm]at h2
  have hp:(k:O)*sqrt (k:O)<=(log ((j:O)+2))^((3:O)/2)/(log 2)^((3:O)/2):=(by have C:(0:O)< (k:O):=_P;have hF:0< log ((j:O)+2):=et (_l (dK (α:=O) j));have He:(k:O)*sqrt (k:O)=(k:O)^((3:O)/2):=(by rw[ik,<- Real.rpow_one_add' C.le _N];norm_num);rw[He,<- div_rpow hF.le e.le];exact fx C.le P _N);have hq:(k:O)*sqrt (k:O)*(log ((2^(j+1):ℕ):O))^2 <=((j:O)+1)^2*(log ((j:O)+2))^((3:O)/2)/(log 2)^((3:O)/2):=by
   have Ho:(log ((2^(j+1):ℕ):O))^2<=((j:O)+1)^2:=m9 (f1 (_M (fY (n:=j+1)))) T 2;have Hf:0<=log ((j:O)+2):=f1 (_l (dK (α:=O) j))
   calc _<=((log ((j:O)+2))^((3:O)/2)/(log 2)^((3:O)/2))*((j:O)+1)^2:=
         en hp Ho _P _P
     _=_:=by ring
  have hP:0< log ((2^(j+1):ℕ):O):=et (_M (show 1< 2^(j+1) from kH _O));have D:(0:O)<=(x:O):=dK x;have q':(0:O)< (j:O)+1:=lZ (dK j) one_pos;have G:0< log ((j:O)+2):=et (_l (dK (α:=O) j));have J:0<=w j:=ed (rpow_nonneg q'.le _) (rpow_nonneg G.le _);have h7:v*((x:O)*w j) <=u*((x:O)/(log ((2^(j+1):ℕ):O))^2)*(∑a∈A,L a/(a:O)):=by
   have M:(u*log 2/(4*2^108*2*exp 1))*(x:O) *((2*log 2*exp 1)^k/((k:O)*sqrt (k:O)*(log ((2^(j+1):ℕ):O))^2)) <=u*((x:O)/(log ((2^(j+1):ℕ):O))^2)*(∑a∈A,L a/(a:O)):=by
    have hI:=dA hw (ek l.le (ed D (gR (log ((2^(j+1):ℕ):O)))));have hL:(u*log 2/(4*2^108*2*exp 1))*(x:O) *((2*log 2*exp 1)^k/((k:O)*sqrt (k:O)*(log ((2^(j+1):ℕ):O))^2)) <=u*((x:O)/(log ((2^(j+1):ℕ):O))^2) *((log 2*(2*log 2)^k)/(4*2^108)*((k:O)^(k-1)/(2*(k.factorial:O)))):=by
     have Hg:=dA h6
      (ed (ek (ek l.le e.le) D)
       (ek (_N :(0:O)<=4*2^108*2) (gR (log ((2^(j+1):ℕ):O)))))
     refine gf ?_ (Hg.trans_eq (by ring))
     have H0:exp 1≠0:=(ez 1).ne';have Hh:(log ((2^(j+1):ℕ):O))^2≠0:=_P;have Hi:(k:O)*sqrt (k:O)≠0:=_P;have Hj:(4*2^108*2:O)≠0:=_P;field_simp [H0,Hh,Hi,Hj];exact eR
    exact hL.trans hI
   refine gf ?_ M
   have hM:(1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2)*w j <=(2*log 2*exp 1)^k/((k:O)*sqrt (k:O)*(log ((2^(j+1):ℕ):O))^2):=by
    dsimp only[w]
    calc (1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2) *
          (((j:O)+1)^(-α)/(log ((j:O)+2))^((3:O)/2))
        = ((1/(2*log 2*exp 1)^502)*((j:O)+1)^(-α)*((j:O)+1)^2) /(((j:O)+1)^2*(log ((j:O)+2))^((3:O)/2)/(log 2)^((3:O)/2)):=by have M':(j:O)+1≠0:=q'.ne';have h2':(log 2)^((3:O)/2)≠0:=_P;have h3':(log ((j:O)+2))^((3:O)/2)≠0:=(k5 G _).ne';field_simp [M',h2',h3']
      _<=(2*log 2*exp 1)^k /((k:O)*sqrt (k:O)*(log ((2^(j+1):ℕ):O))^2):=mj _P R _P hq
   have Hp:v*((x:O)*w j) <=(u*log 2/(4*2^108*2*exp 1))*(x:O) *((1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2)*w j):=(by dsimp only[v];have hg:0<=(u*log 2/(4*2^108*2*exp 1))*(x:O) *((1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2)*w j):=ek (ek (ed (ek l.le e.le) _P) D) (ek (ek _P _P) J);have hS:(u*log 2/(4*2^108*2*exp 1*20)) *((1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2))*((x:O)*w j) =(1/20:O)*((u*log 2/(4*2^108*2*exp 1))*(x:O) *((1/(2*log 2*exp 1)^502)*(log 2)^((3:O)/2)*w j)):=(by ring);rw[hS];linarith);exact Hp.trans (dA hM
    (ek (ed (ek l.le e.le) _P) D))
  calc min v o*((x:O)*w j)
      <= v*((x:O)*w j):=dE (i7 _ _) (ek D J)
    _<=u*((x:O)/(log ((2^(j+1):ℕ):O))^2)*(∑a∈A,L a/(a:O)):=h7
    _<=((c6 x j).card:O):=hh
 ·
  push Not at hr
  have h8:(Icc 1 (x/2^j)).image (fun m=>m*2^j)⊆c6 x j:=(by intro n hn;rcases dW.mp hn with⟨m,hm,rfl⟩;rw[dT]at hm;rw[c7];refine⟨fP hm.1 (gr j),(eE _ hm.2).trans (eD x _),2^j,fW.mpr ⟨⟨m,_R⟩,(fP hm.1 (gr j)).ne'⟩,eR,Nat.pow_lt_pow_right _N _O⟩);have h9:((x/2^j:ℕ):O)<=((c6 x j).card:O):=by
   have ho:x/2^j<=(c6 x j).card:=by
    calc x/2^j=(Icc 1 (x/2^j)).card:=by simp
      _=((Icc 1 (x/2^j)).image (fun m=>m*2^j)).card:=(fs _ (mul_left_injective₀ (gr j).ne')).symm
      _<=(c6 x j).card:=er h8
   exact_mod_cast ho
  have hN:(x:O)/(2:O)^(J0+1)<=((x/2^j:ℕ):O):=by
   have Z:2^j<=2^J0:=dH _N _O;have M:x< (x/2^j+1)*2^j:=(by have:=gu x (2^j);have:=dY x (gr j);nlinarith);have h2:1<=x/2^j:=(by rw[dZ (gr j),gz];exact Z.trans ((dH _N (_O :J0<=J0+2)).trans hx));have h3:x<=2*(x/2^j)*2^J0:=by
    calc x<=(x/2^j+1)*2^j:=M.le
      _<=(2*(x/2^j))*2^J0:=eH _O Z
   rw[mc _P];have Hv:(x:O)<=2*((x/2^j:ℕ):O)*(2:O)^J0:=_M h3;rw[fc];linarith
  have H1:w j<=1/(log 2)^((3:O)/2):=by
   dsimp only[w];have H2:0<=α:=by dsimp only[α];have hD:log (log 2)< log 2-1:=k7 e a4.ne;have:(1+log (log 2))/log 2< 1:=(lF e).mpr _L;linarith
   have M:((j:O)+1)^(-α)<=1:=Real.rpow_le_one_of_one_le_of_nonpos (_l (dK (α:=O) j)) _L;have h2:(log 2)^((3:O)/2)<=(log ((j:O)+2))^((3:O)/2):=fx e.le (dM _N (_l (dK (α:=O) j))) _N;exact mj eO M _P h2
  have J:0<=w j:=by dsimp only[w];have:0< log ((j:O)+2):=et (_l (dK (α:=O) j));positivity
  calc min v o*((x:O)*w j)
      <= o*((x:O)*(1/(log 2)^((3:O)/2))):=en (gw _ _) (dA H1 (dK x)) (ek (dK x) J) _P
    _=(x:O)/(2:O)^(J0+1):=by dsimp only[o];field_simp [(_P :(log 2)^((3:O)/2)≠0)]
    _<=((x/2^j:ℕ):O):=hN
    _<=((c6 x j).card:O):=h9
def cr (k:ℕ) (a b:O):Set (Fin k->O):=
 {ξ | (∀i:Fin k,a<=ξ i/\ξ i<=b)/\Monotone ξ}
lemma cs (k:ℕ) (a b:O):MeasurableSet (cr k a b):=by
 have d:cr k a b =(⋂ i:Fin k,{ξ : Fin k->O | a<=ξ i}∩{ξ : Fin k->O | ξ i<=b}) ∩ (⋂ p:Fin k × Fin k,if p.1<=p.2 then {ξ : Fin k->O | ξ p.1<=ξ p.2} else Set.univ):=by
  ext ξ;simp only[cr,eM,kW,lK,Prod.forall];constructor
  ·rintro⟨hb,hmono⟩;refine⟨hb,fun i j=>?_⟩;split_ifs with c
   ·exact hmono c
   ·trivial
  ·rintro⟨hb,hm⟩;refine⟨hb,fun i j c=>?_⟩;have h:=hm i j;simpa[c] using h
 rw[d];refine kt ?_ ?_
 ·refine fI fun i=>kt ?_ ?_
  ·exact fV eV (dO i)
  ·exact fV (dO i) eV
 ·refine fI fun p=>?_
  split_ifs
  ·exact fV (dO p.1) (dO p.2)
  ·exact kI
set_option maxHeartbeats 800000 in
lemma ct (k:ℕ):∀(a b:O),a<=b -> volume (cr k a b)=ENNReal.ofReal ((b-a)^k/(k.factorial:O)):=by
 induction k with
 | zero=>
  intro a b _;have v:cr 0 a b=Set.univ:=(by ext ξ;simp[cr];intro i;exact i.elim0);rw[v];simp only[kQ,Nat.factorial_zero,eF,kO,ENNReal.ofReal_one];have E:(Set.univ:Set (Fin 0->O))=Set.univ.pi (fun _:Fin 0=>(Set.univ:Set O)):=(by ext;simp);rw[E,show (volume:Measure (Fin 0->O))=Measure.pi (fun _:Fin 0=>(volume:Measure O)) from rfl,gV];simp
 | succ k ih=>
  intro a b D;let e:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (k+1)=>O) (0:Fin (k+1));have F:MeasurePreserving e volume volume:=MeasureTheory.volume_preserving_piFinSuccAbove (fun _:Fin (k+1)=>O) (0:Fin (k+1));let T:Set (O × (Fin k->O)):={p | a<=p.1/\p.1<=b/\p.2∈cr k p.1 b};have q:cr (k+1) a b=e ⁻¹' T:=by
   ext ξ;simp only[cr,T,eL,eM,e,MeasurableEquiv.piFinSuccAbove_apply];constructor
   ·rintro⟨hb,hmono⟩;refine⟨(hb 0).1,(hb 0).2,fun i=>⟨hmono (Fin.zero_le i.succ),(hb i.succ).2⟩,fun i j o=>hmono (Fin.succ_le_succ_iff.mpr o)⟩
   ·rintro⟨ha0,h0b,hηb,hηm⟩;refine⟨fun i=>Fin.cases ⟨ha0,h0b⟩ (fun j=>⟨ha0.trans (hηb j).1,(hηb j).2⟩) i,?_⟩;intro i j o;cases i using Fin.cases with
    | zero=>
     cases j using Fin.cases with
     | zero=>exact eR
     | succ j'=>exact (hηb j').1
    | succ i'=>
     cases j using Fin.cases with
     | zero=>exact absurd o (by simp)
     | succ j'=>exact hηm (Fin.succ_le_succ_iff.mp o)
  have c:MeasurableSet T:=(by have w:T=e.symm ⁻¹' (cr (k+1) a b):=(by ext p;simp[q]);rw[w];exact (cs (k+1) a b).preimage e.symm.measurable);rw[q,F.measure_preimage c.nullMeasurableSet];change (volume.prod volume) T=_;rw[Measure.prod_apply c];have y:∀t:O,volume (Prod.mk t ⁻¹' T) =if t∈Set.Icc a b then ENNReal.ofReal ((b-t)^k/(k.factorial:O)) else 0:=by
   intro t;by_cases u:t∈Set.Icc a b
   ·rw[iM u];have G:Prod.mk t ⁻¹' T=cr k t b:=(by ext η;simp[T,u.1,u.2]);rw[G];exact ih t b u.2
   ·rw[gc u];have z:Prod.mk t ⁻¹' T=∅:=by
     ext η;simp only[eL,T,eM,iG,iC];rintro⟨w,J,_⟩;exact u ⟨w,J⟩
    rw[z,measure_empty]
  simp_rw [y]
  have A:(fun t=>if t∈Set.Icc a b then ENNReal.ofReal ((b-t)^k/(k.factorial:O)) else 0) =(Set.Icc a b).indicator (fun t=>ENNReal.ofReal ((b-t)^k/(k.factorial:O))):=(by ext t;simp[Set.indicator]);rw[A,MeasureTheory.lintegral_indicator kU];have d:ContinuousOn (fun t:O=>(b-t)^k/(k.factorial:O)) (Set.Icc a b):=(by fun_prop);have B:IntegrableOn (fun t:O=>(b-t)^k/(k.factorial:O)) (Set.Icc a b) volume:=d.integrableOn_Icc;have H:∀t∈Set.Icc a b,0<=(b-t)^k/(k.factorial:O):=fun t u=>
   ed (fK (sub_nonneg.mpr u.2) k) _P
  rw[<- MeasureTheory.ofReal_integral_eq_lintegral_ofReal B
   ((MeasureTheory.ae_restrict_iff' kU).mpr (hG H))]
  congr 1;rw[MeasureTheory.integral_Icc_eq_integral_Ioc,<- intervalIntegral.integral_of_le D];have l:∀t∈Set.uIcc a b,HasDerivAt (fun x:O=>-((b-x)^(k+1)/((k+1).factorial:O))) ((b-t)^k/(k.factorial:O)) t:=by
   intro t _;have w:HasDerivAt (fun x:O=>b-x) (-1) t:=(by simpa using (j6 t b).fun_sub (gh t));have J:=w.fun_pow (k+1);have N:=(J.div_const ((k+1).factorial:O)).fun_neg;have C : -(((k+1:ℕ):O)*(b-t)^(k+1-1)*-1/((k+1).factorial:O)) =(b-t)^k/(k.factorial:O):=by rw[e6,g3,gn];have K:((k+1:ℕ):O)≠0:=_P;have M:(k.factorial:O)≠0:=_P;field_simp [K,M]
   rwa[C]at N
  rw[intervalIntegral.integral_eq_sub_of_hasDerivAt l
   (d.intervalIntegrable_of_Icc D)]
  simp
set_option maxHeartbeats 800000 in
lemma cu {k:ℕ} (c d:O) (h:0< c) (S:Set (Fin k->O))
 (l:MeasurableSet S) :
 volume ((fun (ξ : Fin k->O) (i:Fin k)=>c*ξ i+d) ⁻¹' S) =ENNReal.ofReal (c⁻¹^k)*volume S:=by
 have j:(fun (ξ : Fin k->O) (i:Fin k)=>c*ξ i+d) =(fun η=>η+fun _=>d) ∘ (fun ξ=>c•ξ):=by ext ξ i;simp
 rw[j,Set.preimage_comp];have e:MeasurableSet ((fun η : Fin k->O=>η+fun _=>d) ⁻¹' S):=l.preimage (measurable_id.add eV);have b:(fun ξ : Fin k->O=>c•ξ) ⁻¹' ((fun η : Fin k->O=>η+fun _=>d) ⁻¹' S) =c⁻¹•((fun η : Fin k->O=>η+fun _=>d) ⁻¹' S):=by ext ξ;simp only[eL,Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero h.ne'),inv_inv]
 rw[b,Measure.addHaar_smul,Module.finrank_pi,fH,jE (fK (inv_nonneg.mpr h.le) k),kd volume (fun _:Fin k=>d) S]
def cv {k:ℕ} (l:Fin k) :
 (Fin k->O) ≃ᵐ O × (Fin l.1->O) × (Fin (k-1 - l.1)->O) where
 toFun ξ:=(ξ l,fun i=>ξ ⟨i.1,_O⟩,fun j=>ξ ⟨j.1+l.1+1,_O⟩)
 invFun p i:=
  if c:i.1< l.1 then p.2.1 ⟨i.1,c⟩
  else if d:i.1=l.1 then p.1
  else p.2.2 ⟨i.1-l.1-1,_O⟩
 left_inv ξ:=by
  funext i;dsimp only;split_ifs with c d
  ·rfl
  ·congr 1;exact dQ d.symm
  ·have:(⟨i.1-l.1-1+l.1+1,_O⟩:Fin k)=i:=dQ (by dsimp only;omega)
   rw[this]
 right_inv:=fun ⟨t,a,b⟩=>by
  refine iq (by simp) (iq (by funext i;simp[i.2]) ?_)
  funext j;have c:¬ (j.1+l.1+1< l.1):=_O;have d:¬ (j.1+l.1+1=l.1):=_O;simp only[c,d,↓reduceDIte];congr 1;exact dQ (by dsimp only;omega)
 measurable_toFun:=iX (dO l)
   (iX (eU _ fun _=>dO _)
    (eU _ fun _=>dO _))
 measurable_invFun:=eU _ fun i=>by
  simp only[g8];split_ifs
  ·exact (dO _).comp (lI.comp iR)
  ·exact lI
  ·exact (dO _).comp (iR.comp iR)
lemma cw {k:ℕ} (l:Fin k) (t:O) (a:Fin l.1->O)
 (b:Fin (k-1 - l.1)->O) (i:Fin k) (h:i.1< l.1) :
 (cv l).symm (t,a,b) i=a ⟨i.1,h⟩:=by
 simp only[cv,iH,gQ,g8];rw[eG h]
lemma cx {k:ℕ} (l:Fin k) (t:O) (a:Fin l.1->O)
 (b:Fin (k-1 - l.1)->O) :
 (cv l).symm (t,a,b) l=t:=by
 simp only[cv,iH,gQ,g8];simp
lemma cy {k:ℕ} (l:Fin k) (t:O) (a:Fin l.1->O)
 (b:Fin (k-1 - l.1)->O) (j:Fin (k-1 - l.1)) :
 (cv l).symm (t,a,b) ⟨j.1+l.1+1,_O⟩=b j:=by
 simp only[cv,iH,gQ,g8];have c:¬ (j.1+l.1+1< l.1):=_O;have d:¬ (j.1+l.1+1=l.1):=_O;rw[eA c,eA d];congr 1;exact dQ (by dsimp only;omega)
set_option maxHeartbeats 800000 in
lemma cz {k:ℕ} (l:Fin k) (S:Set (Fin k->O)) (K:MeasurableSet S) :
 volume S=volume ((cv l).symm ⁻¹' S):=by
 let e:=cv l;have z:MeasurePreserving e volume volume:=by
  refine⟨e.measurable,?_⟩
  have o:Measure.map e.symm volume=volume:=by
   symm;refine lY fun s J=>?_
   rw[l3 e.symm.measurable (ka J)];have u:e.symm ⁻¹' (Set.univ.pi s) =(s l)×ˢ((Set.univ.pi fun i:Fin l.1=>s ⟨i.1,_O⟩) ×ˢ
     (Set.univ.pi fun j:Fin (k-1 - l.1)=>s ⟨j.1+l.1+1,_O⟩)):=by
    ext ⟨t,a,b⟩;simp only[eL,lr,il];constructor
    ·intro h;refine⟨by simpa[e,cx] using h l,fun i=>by simpa[e,cw l t a b ⟨i.1,_O⟩ i.2] using h ⟨i.1,_O⟩,fun j=>by simpa[e,cy] using h ⟨j.1+l.1+1,_O⟩⟩
    ·rintro⟨ht,ha,hb⟩ i;by_cases q:i.1< l.1
     ·rw[show e.symm (t,a,b) i=a ⟨i.1,q⟩ from cw l t a b i q];exact ha ⟨i.1,q⟩
     ·by_cases H:i.1=l.1
      ·have hi:i=l:=dQ H;subst hi;rw[show e.symm (t,a,b) i=t from cx i t a b];exact ht
      ·let j:Fin (k-1 - l.1):=⟨i.1-l.1-1,_O⟩;have hi:(⟨j.1+l.1+1,_O⟩:Fin k)=i:=dQ (by dsimp[j];omega);rw[<- hi,show e.symm (t,a,b) ⟨j.1+l.1+1,_O⟩=b j from cy l t a b j];exact hb j
   rw[u];change (volume.prod (volume.prod volume)) _=_;rw[f5,f5];change volume (s l)*((Measure.pi fun _:Fin l.1=>(volume:Measure O)) _ *(Measure.pi fun _:Fin (k-1 - l.1)=>(volume:Measure O)) _)=_;rw[gV,gV];have d:(∏i:Fin k,volume (s i)) =volume (s l)*((∏i:Fin l.1,volume (s ⟨i.1,_O⟩)) *∏j:Fin (k-1 - l.1),volume (s ⟨j.1+l.1+1,_O⟩)):=by
    rw[<- ey univ (fun i:Fin k=>i.1< l.1)];have A:∏i∈univ.filter (fun i:Fin k=>i.1< l.1),volume (s i) =∏i:Fin l.1,volume (s ⟨i.1,_O⟩):=hJ (fun i hi=>⟨i.1,by simp at hi;exact hi⟩) (fun _ _=>dJ _) (fun _ _ _ _ h=>dQ (es h)) (fun i _=>⟨⟨i.1,_O⟩,dB.mpr ⟨dJ _,i.2⟩,rfl⟩) (fun _ _=>rfl)
    have m:l∈univ.filter (fun i:Fin k=>¬ i.1< l.1):=(by simp);rw[A,<- gk _ _ m];have B:∏i∈(univ.filter (fun i:Fin k=>¬ i.1< l.1)).erase l,volume (s i) =∏j:Fin (k-1 - l.1),volume (s ⟨j.1+l.1+1,_O⟩):=hJ (fun i hi=>⟨i.1-l.1-1,by
      rw[gS,dB]at hi;have:i.1≠l.1:=fun h=>hi.1 (dQ h);omega⟩)
      (fun _ _=>dJ _)
      (fun E w F y h=>by
       rw[gS,dB]at w y;have C:E.1≠l.1:=fun h=>w.1 (dQ h);have D:F.1≠l.1:=fun h=>y.1 (dQ h);have M:E.1-l.1-1=F.1-l.1-1:=es h;exact dQ _O)
      (fun j _=>⟨⟨j.1+l.1+1,_O⟩,by
       rw[gS,dB];exact⟨fun h=>by have:=es h;omega,dJ _,by dsimp only;omega⟩,
       dQ (by dsimp only;omega)⟩)
      (fun i hi=>by
       rw[gS,dB]at hi;have G:i.1≠l.1:=fun h=>hi.1 (dQ h);have v:(⟨i.1-l.1-1+l.1+1,_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rw[v])
    rw[B];ring
   exact d.symm
  calc Measure.map e volume=Measure.map e (Measure.map e.symm volume):=by rw[o]
    _=Measure.map (e ∘ e.symm) volume:=Measure.map_map e.measurable e.symm.measurable
    _=volume:=by simp
 have q:=z.measure_preimage (K.preimage e.symm.measurable).nullMeasurableSet;have c:e ⁻¹' (e.symm ⁻¹' S)=S:=by ext ξ;simp[e]
 rw[c]at q;exact q
def cA (k:ℕ) (u v:O):Set (Fin k->O):=
 {ξ∈cr k 0 1 | ∀i:Fin k,((i.1+1:ℕ):O)-u<=v*ξ i}
lemma cC (k:ℕ) (u v:O):MeasurableSet (cA k u v):=by
 refine (cs k 0 1).inter ?_
 change MeasurableSet {ξ : Fin k->O | ∀i:Fin k,((i.1+1:ℕ):O)-u<=v*ξ i};have b:{ξ : Fin k->O | ∀i:Fin k,((i.1+1:ℕ):O)-u<=v*ξ i} =⋂ i:Fin k,{ξ : Fin k->O | ((i.1+1:ℕ):O)-u<=v*ξ i}:=by ext;simp
 rw[b];exact fI fun i=>fV eV (eV.mul (dO i))
def cD (k:ℕ) (u v:O):O:=(k.factorial:O)*(volume (cA k u v)).toReal
lemma cE (k:ℕ) (u v:O):cD k u v<=1:=by
 unfold cD;have d:cA k u v⊆cr k 0 1:=fun _ h=>h.1;have b:volume (cA k u v)<=volume (cr k 0 1):=f4 d;rw[ct k 0 1 eO,kf,jQ]at b;have c:=fM ec b;rw[eZ _P]at c;have i:=dA c (_P :(0:O)<=(k.factorial:O));have e:(k.factorial:O)*(1/(k.factorial:O))=1:=by field_simp [(_P :(k.factorial:O)≠0)]
 linarith
set_option maxHeartbeats 800000 in
lemma cF {x y:O} (l:0<=y) (B:y<=x) (C:x< 1) :
 log (1-x)-log (1+y)<=-(x+y):=by
 have o:log (1-x)+x<=log (1-y)+y:=by have d:log ((1-x)/(1-y))<=(1-x)/(1-y)-1:=eY (gN _L _L);rw[gW _L _L]at d;have e:(1-x)/(1-y)-1<=y-x:=(by rw[div_sub_one _L,mc _L];nlinarith);linarith
 have q:log (1-y)-log (1+y)+2*y<=0:=by
  let h:O->O:=fun t=>log (1-t)-log (1+t)+2*t;have i:ContinuousOn h (Set.Icc 0 y):=by
   intro t b;have d:1-t≠0:=(by linarith[b.1,b.2]);have e:1+t≠0:=_l b.1;exact ((((continuousAt_const.sub lq).log d).sub
    ((continuousAt_const.add lq).log e)).add
    (continuousAt_const.mul lq)).continuousWithinAt
  have c:∀t∈Set.Ioo 0 y,deriv h t<=0:=by
   intro t b;have d:1-t≠0:=(by linarith[b.1,b.2]);have e:1+t≠0:=_l b.1;have u:HasDerivAt (fun s=>log (1-s)) (-1/(1-t)) t:=by
    have:=((j6 t (1:O)).sub (gh t)).log d
    simpa using this
   have v:HasDerivAt (fun s=>log (1+s)) (1/(1+t)) t:=by
    have:=((j6 t (1:O)).add (gh t)).log e
    simpa using this
   have w:HasDerivAt (fun s=>2*s) 2 t:=(by simpa using (gh t).const_mul 2);have A:HasDerivAt h (-1/(1-t)-1/(1+t)+2) t:=(u.sub v).add w;rw[A.deriv];have z : -1/(1-t)-1/(1+t)+2=-2*t^2/((1-t)*(1+t)):=(by field_simp [d,e];ring);rw[z];exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (ek (_l b.2) (_l b.1))
  have j:=antitoneOn_of_deriv_nonpos (convex_Icc 0 y) i
   (fun t b=>by
    rw[interior_Icc]at b;have d:1-t≠0:=(by linarith[b.1,b.2]);have e:1+t≠0:=_l b.1;exact (((((j6 t (1:O)).sub (gh t)).log d).sub
     (((j6 t (1:O)).add (gh t)).log e)).add
     ((gh t).const_mul 2)).differentiableAt.differentiableWithinAt)
   (fun t b=>by rw[interior_Icc]at b;exact c t b)
  have m:=j ⟨eR,l⟩ ⟨l,eR⟩ l;simp only[h,kf,i0,log_one,hK]at m;exact m
 linarith
set_option maxHeartbeats 800000 in
lemma cG (k:ℕ) (u v:O) (hu:0<=u) (hw:0<=u+v-(k:O)) :
 cD k u v<=200*(u+1)*(u+v-(k:O)+1)^2/((k:O)+1):=by
 let w:O:=u+v-(k:O);change cD k u v<=200*(u+1)*(w+1)^2/((k:O)+1);by_cases W:k< 100 ∨ (k:O)/10< u ∨ sqrt (k:O)< w
 ·
  have hT:=cE k u v;have h9:1<=200*(u+1)*(w+1)^2/((k:O)+1):=by
   rw[js _P];rcases W with M | H0 | H1
   ·have Hm:(k:O)<=99:=(by exact_mod_cast (_O :k<=99));have D:(1:O)<=(u+1)*(w+1)^2:=_Q;nlinarith
   ·have D:(1:O)<=(w+1)^2:=(by nlinarith);nlinarith
   ·have D:(k:O)<=w^2:=by
     have:=m9 (ld (k:O)) H1.le 2
     rwa[kN (dK k)]at this
    have F:(1:O)<=u+1:=_L;nlinarith
  exact hT.trans h9
 ·push Not at W
  rcases W with⟨M,H0,H1⟩;have ho:(0:O)< (k:O):=_M (_O :0< k);have Hc:9*(k:O)/10<=v:=_L;have o:0< v:=_L;let b:O:=1-(2*w+2)/v;have q:(2*w+2)/v<=1/2:=by
   rw[mc o];have hF:sqrt (k:O)<=(k:O)/10:=by rw[sqrt_le_left _P];have hI:(100:O)<=(k:O):=_M M;nlinarith
   have hI:(100:O)<=(k:O):=_M M;nlinarith
  have G:0< b:=(by dsimp only[b];linarith);have hp:b< 1:=(by have Hn:0< (2*w+2)/v:=_P;dsimp only[b];linarith);let d (l:Fin k) (B:O):Set (Fin k->O):=
   {ξ∈cr k 0 B |
     v*ξ l< ((l.1+1:ℕ):O)-u /\
     ∀i:Fin k,i.1< l.1->((i.1+1:ℕ):O)-u<=v*ξ i}
  have z:∀l B,MeasurableSet (d l B):=by
   intro l B;refine (cs k 0 B).inter (kt ?_ ?_)
   ·exact l5 (eV.mul (dO l)) eV
   ·change MeasurableSet {ξ : Fin k->O | ∀i:Fin k,i.1< l.1->((i.1+1:ℕ):O)-u<=v*ξ i};have ha:{ξ : Fin k->O | ∀i:Fin k,i.1< l.1->((i.1+1:ℕ):O)-u<=v*ξ i} =⋂ i:Fin k,if i.1< l.1 then {ξ : Fin k->O | ((i.1+1:ℕ):O)-u<=v*ξ i} else Set.univ:=by
     ext ξ;simp only[eM,lK];constructor
     ·intro h i;split_ifs with hi;exact h i hi;trivial
     ·intro h i hi;have:=h i;simpa[hi] using this
    rw[ha];refine fI fun i=>?_
    split_ifs
    ·exact fV eV (eV.mul (dO i))
    ·exact kI
  have hk:∀l:Fin k,ENNReal.ofReal (exp (2*w+2))*volume (d l b) <=volume (d l 1):=by
   intro l;let e:=cv l;rw[cz l (d l b) (z l b),cz l (d l 1) (z l 1)];let y (t:O):Set (Fin l.1->O):=
    {a∈cr l.1 0 t | ∀i:Fin l.1,((i.1+1:ℕ):O)-u<=v*a i}
   have hL:∀(B:O),0<=B -> e.symm ⁻¹' (d l B) ={p:O × (Fin l.1->O) × (Fin (k-1 - l.1)->O) |
       0<=p.1/\p.1<=B/\v*p.1< ((l.1+1:ℕ):O)-u /\
       (0< l.1->((l.1:ℕ):O)-u<=v*p.1) /\
       p.2.1∈y p.1/\p.2.2∈cr (k-1 - l.1) p.1 B}:=by
    intro B _;ext ⟨t,a,c⟩;simp only[eL,d,cr,y,eM];constructor
    ·rintro⟨⟨hbnd,hmono⟩,P,hprev⟩;have C:e.symm (t,a,c) l=t:=cx l t a c;have hq:0<=t:=(by rw[<- C];exact (hbnd l).1);have hr:t<=B:=(by rw[<- C];exact (hbnd l).2);have P':v*t< ((l.1+1:ℕ):O)-u:=(by rw[<- C];exact P);have hb:0< l.1->((l.1:ℕ):O)-u<=v*t:=by
      intro H2;let H:Fin k:=⟨l.1-1,_O⟩;have Q:H.1< l.1:=(by dsimp[H];omega);have D:=hprev H Q;have F:=hmono (show H<=l by exact mh.mpr _O)
      rw[cw l t a c H Q]at D F;rw[C]at F;have h5:H.1+1=l.1:=(by dsimp[H];omega);rw[h5]at D;nlinarith
     refine⟨hq,hr,P',hb,⟨⟨fun i=>⟨?_,?_⟩,?_⟩,?_⟩,⟨fun j=>⟨?_,?_⟩,?_⟩⟩
     ·have:=(hbnd ⟨i.1,_O⟩).1
      rwa[cw l t a c ⟨i.1,_O⟩ i.2]at this
     ·have:=hmono (show (⟨i.1,_O⟩:Fin k)<=l by exact mh.mpr _O)
      rwa[cw l t a c ⟨i.1,_O⟩ i.2,C]at this
     ·intro i1 i2 U;have:=hmono (show (⟨i1.1,_O⟩:Fin k)<=⟨i2.1,_O⟩ from U);rwa[cw l t a c ⟨i1.1,_O⟩ i1.2,cw l t a c ⟨i2.1,_O⟩ i2.2]at this
     ·intro i;have:=hprev ⟨i.1,_O⟩ i.2;rwa[cw l t a c ⟨i.1,_O⟩ i.2]at this
     ·have:=hmono (show l<=(⟨j.1+l.1+1,_O⟩:Fin k) by exact mh.mpr _O)
      rwa[C,cy l t a c j]at this
     ·have:=(hbnd ⟨j.1+l.1+1,_O⟩).2
      rwa[cy l t a c j]at this
     ·intro j1 j2 U;have:=hmono (show (⟨j1.1+l.1+1,_O⟩:Fin k)<=⟨j2.1+l.1+1,_O⟩ by
       exact mh.mpr (by have:j1.1<=j2.1:=U;omega))
      rwa[cy l t a c j1,cy l t a c j2]at this
    ·rintro⟨hq,hr,P',_,⟨⟨hab,ham⟩,hap⟩,⟨hcb,hcm⟩⟩;have C:e.symm (t,a,c) l=t:=cx l t a c;have A:∀i:Fin k,(i.1< l.1->0<=e.symm (t,a,c) i/\e.symm (t,a,c) i<=t) /\(i.1=l.1->e.symm (t,a,c) i=t) /\(l.1< i.1->t<=e.symm (t,a,c) i/\e.symm (t,a,c) i<=B):=by
      intro i;refine⟨fun hi=>?_,fun hi=>?_,fun hi=>?_⟩
      ·rw[cw l t a c i hi];exact hab ⟨i.1,hi⟩
      ·have:i=l:=dQ hi;subst this;exact C
      ·let j:Fin (k-1 - l.1):=⟨i.1-l.1-1,_O⟩;have hj:(⟨j.1+l.1+1,_O⟩:Fin k)=i:=dQ (by dsimp[j];omega);rw[<- hj,cy l t a c j];exact hcb j
     refine⟨⟨fun i=>?_,fun i1 i2 U=>?_⟩,by rw[C];exact P',fun i hi=>?_⟩
     ·rcases jC i.1 l.1 with D | F | h3
      ·exact⟨((A i).1 D).1,((A i).1 D).2.trans hr⟩
      ·rw[(A i).2.1 F];exact⟨hq,hr⟩
      ·exact⟨hq.trans ((A i).2.2 h3).1,((A i).2.2 h3).2⟩
     ·rcases jC i1.1 l.1 with D | D | D <;> rcases jC i2.1 l.1 with F | F | F
      ·rw[cw l t a c i1 D,cw l t a c i2 F];exact ham (show (⟨i1.1,D⟩:Fin l.1)<=⟨i2.1,F⟩ from U)
      ·rw[(A i2).2.1 F];exact ((A i1).1 D).2
      ·exact ((A i1).1 D).2.trans ((A i2).2.2 F).1
      ·exfalso;have:i1.1<=i2.1:=U;omega
      ·rw[(A i1).2.1 D,(A i2).2.1 F]
      ·rw[(A i1).2.1 D];exact ((A i2).2.2 F).1
      ·exfalso;have:i1.1<=i2.1:=U;omega
      ·exfalso;have:i1.1<=i2.1:=U;omega
      ·let j1:Fin (k-1 - l.1):=⟨i1.1-l.1-1,_O⟩;let j2:Fin (k-1 - l.1):=⟨i2.1-l.1-1,_O⟩;have Hd:(⟨j1.1+l.1+1,_O⟩:Fin k)=i1:=dQ (by dsimp[j1];omega);have He:(⟨j2.1+l.1+1,_O⟩:Fin k)=i2:=dQ (by dsimp[j2];omega);rw[<- Hd,<- He,cy l t a c j1,cy l t a c j2];exact hcm (mh.mpr (by have:i1.1<=i2.1:=U;omega))
     ·rw[cw l t a c i hi];exact hap ⟨i.1,hi⟩
   have h7:∀(B:O),0<=B -> volume (e.symm ⁻¹' (d l B)) =∫⁻ t,(if 0<=t/\t<=B/\v*t< ((l.1+1:ℕ):O)-u/\(0< l.1->((l.1:ℕ):O)-u<=v*t)
      then volume (y t)*ENNReal.ofReal ((B-t)^(k-1 - l.1)/((k-1 - l.1).factorial:O))
      else 0):=by
    intro B hB;have hM:MeasurableSet (e.symm ⁻¹' (d l B)):=(z l B).preimage e.symm.measurable;change (volume.prod volume) _=_;rw[Measure.prod_apply hM];refine MeasureTheory.lintegral_congr fun t=>?_
    rw[hL B hB];by_cases ht:0<=t/\t<=B/\v*t< ((l.1+1:ℕ):O)-u/\(0< l.1->((l.1:ℕ):O)-u<=v*t)
    ·rw[iM ht];have hU:Prod.mk t ⁻¹'
      {p:O × (Fin l.1->O) × (Fin (k-1 - l.1)->O) |
        0<=p.1/\p.1<=B/\v*p.1< ((l.1+1:ℕ):O)-u /\
        (0< l.1->((l.1:ℕ):O)-u<=v*p.1) /\
        p.2.1∈y p.1/\p.2.2∈cr (k-1 - l.1) p.1 B} =
      y t×ˢcr (k-1 - l.1) t B:=by
      ext ⟨a,c⟩;simp only[eL,eM,il];exact⟨fun h=>h.2.2.2.2,fun h=>⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,h⟩⟩
     rw[hU];change (volume.prod volume) _=_;rw[f5,ct (k-1 - l.1) t B ht.2.1]
    ·rw[gc ht];have hV:Prod.mk t ⁻¹'
      {p:O × (Fin l.1->O) × (Fin (k-1 - l.1)->O) |
        0<=p.1/\p.1<=B/\v*p.1< ((l.1+1:ℕ):O)-u /\
        (0< l.1->((l.1:ℕ):O)-u<=v*p.1) /\
        p.2.1∈y p.1/\p.2.2∈cr (k-1 - l.1) p.1 B}=∅:=by
      ext ⟨a,c⟩;simp only[eL,eM,iG,iC];rintro⟨D,F,h3,h4,_,_⟩;exact ht ⟨D,F,h3,h4⟩
     rw[hV,measure_empty]
   rw[h7 b G.le,h7 1 eO,<- MeasureTheory.lintegral_const_mul' _ _ ec];refine MeasureTheory.lintegral_mono fun t=>?_
   split_ifs with htb ht1
   ·rw[<- f0,e8 (ENNReal.ofReal (exp (2*w+2))) (volume (y t)),f0];gcongr;rw[<- jx (ez _).le];refine ENNReal.ofReal_le_ofReal ?_
    rw[gl];refine dI ?_ _P;have H3:(l.1:O)-u<=v*t:=by
     by_cases H2:0< l.1
     ·exact htb.2.2.2 H2
     ·have:l.1=0:=by omega
      rw[this,jc];have:=ek o.le htb.1;linarith
    let m:ℕ:=k-1 - l.1;let az:O:=((l.1+1:ℕ):O)-u - v*t;have hR:0< az:=(by dsimp only[az];linarith[htb.2.2.1]);have hS:az<=1:=(by dsimp only[az];push_cast;linarith);have H4:v*t<=(k:O)-u - w-2:=(by have D:=dA htb.2.1 o.le;have F:v*b=v-(2*w+2):=(by dsimp only[b];field_simp [o.ne']);linarith);have Hf:w+2-az<=(m:O):=(by have S:(m:O)=(k:O)-1 - (l.1:O):=(by simp only[m];rw[ei _O,ei _O,eF]);have:az=(l.1:O)+1-u - v*t:=(by dsimp only[az];push_cast;ring);linarith);have E:(0:O)< (m:O):=_L;have hs:v*(b-t)=(m:O)-(w+2-az):=(by have F:v*b=v-(2*w+2):=(by dsimp only[b];field_simp [o.ne']);have S:(m:O)=(k:O)-1 - (l.1:O):=(by simp only[m];rw[ei _O,ei _O,eF]);have:az=(l.1:O)+1-u - v*t:=(by dsimp only[az];push_cast;ring);linarith);have hv:v*(1-t)=(m:O)+(w+az):=(by have S:(m:O)=(k:O)-1 - (l.1:O):=(by simp only[m];rw[ei _O,ei _O,eF]);have:az=(l.1:O)+1-u - v*t:=(by dsimp only[az];push_cast;ring);linarith);by_cases hE:b=t
    ·subst hE;have Hp:1<=m:=by
      have:(1:O)<=(m:O):=_L
      exact_mod_cast this
     rw[sub_self,lC _O,hK];exact fK _L m
    ·have X:0< b-t:=ib (sub_nonneg.mpr htb.2.1) (sub_ne_zero.mpr hE).symm;have Z:0< 1-t:=_L;have hx:(w+2-az)/(m:O)< 1:=by
      rw[lF E];have:0< v*(b-t):=ko o X;linarith
     have hl:(w+az)/(m:O)<=(w+2-az)/(m:O):=dI _L E.le;have hN:=cF _P hl hx;have hy:(b-t)/(1-t)=(1-(w+2-az)/(m:O))/(1+(w+az)/(m:O)):=(by have D:(b-t)/(1-t)=(v*(b-t))/(v*(1-t)):=(by field_simp [o.ne']);rw[D,hs,hv];field_simp [E.ne']);have hc:log ((b-t)/(1-t))<=-(2*w+2)/(m:O):=(by rw[hy,gW _L _P];have ha : -((w+2-az)/(m:O)+(w+az)/(m:O))=-(2*w+2)/(m:O):=_R;linarith);have hz:=dA hc E.le;rw[<- fm,mC _ E.ne']at hz;have hm:=me.mpr (_L :2*w+2+log (((b-t)/(1-t))^m)<=0);rw[gX,eX (iN (gN X Z) m),lE,ij]at hm;have hW:0< (1-t)^m:=iN Z m;rw[gl,iy hW]at hm;exact hm
   ·exfalso;exact ht1 ⟨htb.1,htb.2.1.trans hp.le,htb.2.2.1,htb.2.2.2⟩
   ·simp
   ·simp
  have R:∀B:O,Pairwise (Function.onFun Disjoint (fun l:Fin k=>d l B)):=by
   intro B l1 l2 Hl;dsimp only[Function.onFun];rw[kX];intro ξ D F;rcases gI (jP Hl) with h6 | hgt
   ·linarith[D.2.1,F.2.2 l1 h6]
   ·linarith[F.2.1,D.2.2 l2 hgt]
  have hd:(⋃ l:Fin k,d l b)=cr k 0 b:=by
   ext ξ;simp only[eQ,d,l7];constructor
   ·rintro⟨_,h,_,_⟩;exact h
   ·intro hξ;have h0:∃n:ℕ,∃hn:n< k,v*ξ ⟨n,hn⟩< ((n+1:ℕ):O)-u:=by
     refine⟨k-1,by omega,?_⟩
     have D : ξ ⟨k-1,_O⟩<=b:=(hξ.1 ⟨k-1,_O⟩).2;have F:v*b=v-(2*w+2):=(by dsimp only[b];field_simp [o.ne']);have h3:v*ξ ⟨k-1,_O⟩<=v*b:=dA D o.le;have S:((k-1+1:ℕ):O)=(k:O):=(by congr 1;omega);rw[S];linarith
    classical
    let l0:=Nat.find h0;have he:=jF h0;rcases he with⟨T,N⟩;refine⟨⟨l0,T⟩,hξ,N,fun i hi=>?_⟩;by_contra h6;push Not at h6;exact jW h0 hi ⟨i.2,h6⟩
  have hf:(⋃ l:Fin k,d l 1)=cr k 0 1 \ cA k u v:=by
   ext ξ;simp only[eQ,d,cA,Set.mem_diff,l7,not_and];constructor
   ·rintro⟨l,hξ,P,_⟩;refine⟨hξ,fun _ hQ=>?_⟩;linarith[hQ l]
   ·rintro⟨hξ,h8⟩;have h8':=h8 hξ;push Not at h8';rcases h8' with⟨i,hi⟩;have h0:∃n:ℕ,∃hn:n< k,v*ξ ⟨n,hn⟩< ((n+1:ℕ):O)-u:=⟨i.1,i.2,hi⟩
    classical
    let l0:=Nat.find h0;rcases jF h0 with⟨T,N⟩;refine⟨⟨l0,T⟩,hξ,N,fun j hj=>?_⟩;by_contra h6;push Not at h6;exact jW h0 hj ⟨j.2,h6⟩
  have J:ENNReal.ofReal (exp (2*w+2))*volume (cr k 0 b) <=volume (cr k 0 1 \ cA k u v):=(by rw[<- hd,<- hf,lx (R b) (fun l=>z l b),lx (R 1) (fun l=>z l 1),tsum_fintype,tsum_fintype,dP];exact dG fun l _=>hk l);have H5:cD k u v<=1-exp (2*w+2)*b^k:=by
   have K:volume (cr k 0 1 \ cA k u v)+volume (cA k u v) =volume (cr k 0 1):=(by rw[<- lB disjoint_sdiff_self_left (cC k u v),Set.sdiff_union_of_subset (fun _ h=>h.1)]);rw[ct k 0 b G.le,kf]at J;rw[ct k 0 1 eO,kf,jQ]at K;have hC:ENNReal.ofReal (exp (2*w+2))*ENNReal.ofReal (b^k/(k.factorial:O)) +volume (cA k u v)<=ENNReal.ofReal (1/(k.factorial:O)):=(by rw[<- K];exact fd J eR);have hP:volume (cA k u v)≠⊤:=fz ec ((f4 (fun _ h=>h.1)).trans_eq
     (ct k 0 1 eO))
   rw[<- jx (ez _).le]at hC;have hD:=fM ec hC;rw[ENNReal.toReal_add ec hP,eZ _P,eZ _P]at hD;unfold cD;have Ho:=dA hD (_P :(0:O)<=(k.factorial:O));have D:(k.factorial:O)*(exp (2*w+2)*(b^k/(k.factorial:O))) =exp (2*w+2)*b^k:=(by field_simp [(_P :(k.factorial:O)≠0)]);have F:(k.factorial:O)*(1/(k.factorial:O))=1:=(by field_simp [(_P :(k.factorial:O)≠0)]);linarith
  let t:O:=(2*w+2)/v;have Hg:0<=t:=_P;have hA : -t-2*t^2<=log b:=by
   have D:=fl G;have ha:1-b⁻¹=-t/(1-t):=(by have hX:b=1-t:=rfl;have hY:1-t≠0:=_l q;rw[hX];field_simp [hY];ring);rw[ha]at D;have F : -t-2*t^2<=-t/(1-t):=(by rw[ma (by linarith[q]:0< 1-t)];have h3:0<=t^2*(1-2*t):=ek (gR t) (_l q);have h4:(-t-2*t^2)*(1-t)=-t-t^2*(1-2*t):=_R;linarith);linarith
  have hg : -(((2*w+2)*u)/v+2*(k:O)*t^2)<=(2*w+2)+(k:O)*log b:=by
   have D:(2*w+2)+(k:O)*(-t-2*t^2) =(2*w+2)/v*(v-(k:O))-2*(k:O)*t^2:=(by dsimp only[t];field_simp [o.ne'];ring);have F:(2*w+2)/v*(v-(k:O))=(2*w+2)*(w-u)/v:=by
    have:v-(k:O)=w-u:=by dsimp only[w];ring
    rw[this];ring
   have h3 : -((2*w+2)*u/v)<=(2*w+2)*(w-u)/v:=by
    have:0<=(2*w+2)*w/v:=_P
    linarith[show (2*w+2)*(w-u)/v=(2*w+2)*w/v-(2*w+2)*u/v by ring]
   have h4:(k:O)*(-t-2*t^2)<=(k:O)*log b:=dA hA ho.le;linarith
  have hZ:exp (-(((2*w+2)*u)/v+2*(k:O)*t^2)) <=exp (2*w+2)*b^k:=(by have ha:exp ((2*w+2)+(k:O)*log b)=exp (2*w+2)*b^k:=(by rw[gX,e8 (k:O) (log b),<- fQ G,eK]);rw[<- ha];exact me.mpr hg);have H6:1-exp (2*w+2)*b^k<=((2*w+2)*u)/v+2*(k:O)*t^2:=(by have D:=fB (-(((2*w+2)*u)/v+2*(k:O)*t^2));linarith);have H7:((2*w+2)*u)/v+2*(k:O)*t^2 <=200*(u+1)*(w+1)^2/((k:O)+1):=by
   have Hh:0<=w:=hw;have H8:(k:O)+1<=2*v:=(by have hI:(100:O)<=(k:O):=_M M;linarith);have H9:((2*w+2)*u)/v<=4*(u+1)*(w+1)^2/((k:O)+1):=by
    rw[mb o _P];have D:(2*w+2)*u<=2*(u+1)*(w+1)^2:=by
     have:(2*w+2)*u=2*u*(w+1):=_R
     have:0<=(w+1)*w:=ek _L Hh
     nlinarith
    have F:0<=(2*w+2)*u:=_P;nlinarith
   have Ha:2*(k:O)*t^2<=40*(u+1)*(w+1)^2/((k:O)+1):=by
    dsimp only[t];rw[ij,gl,mb (iN o 2) _P];have hh:(k:O)*((k:O)+1)<=2*v^2:=by have hI:(100:O)<=(k:O):=_M M;nlinarith
    have Hi:(2*w+2)^2=4*(w+1)^2:=_R;rw[Hi];have D:(1:O)<=u+1:=_L;have hF:0<=(w+1)^2:=gR (w+1);have Hj:0<=v^2:=gR v
    calc 2*(k:O)*(4*(w+1)^2)*((k:O)+1)
        = 8*((k:O)*((k:O)+1))*(w+1)^2:=_R
      _<=8*(2*v^2)*(w+1)^2:=dE (dA hh _N) hF
      _=16*1*((w+1)^2*v^2):=by ring
      _<=40*(u+1)*((w+1)^2*v^2):=dE _L (ek hF Hj)
      _=40*(u+1)*(w+1)^2*v^2:=by ring
   have Hq:0<=(u+1)*(w+1)^2/((k:O)+1):=_P;have Hk:4*(u+1)*(w+1)^2/((k:O)+1)+40*(u+1)*(w+1)^2/((k:O)+1) =44*((u+1)*(w+1)^2/((k:O)+1)):=_R;have Hb:200*(u+1)*(w+1)^2/((k:O)+1) =200*((u+1)*(w+1)^2/((k:O)+1)):=_R;linarith
  linarith
set_option maxHeartbeats 800000 in
lemma cH:∀(t r:ℕ),r< t -> ∑j∈range (t+1),(-1:O)^(t-j)*(dw t j:O)*(j:O)^r=0
 | 0,_,h=>absurd h (lv _)
 | t+1,0,_=>by
  simp only[kQ,fv]
  have h:=add_pow (1:O) (-1:O) (t+1)
  rw[lJ,lC (j7 t)]at h
  rw[h]
  refine dF rfl fun j _=>?_
  rw[jQ,gz,e8]
 | t+1,r+1,hlt=>by
  have i:∑j∈range (t+2),(-1:O)^(t+1-j)*(dw (t+1) j:O)*(j:O)^(r+1) =∑j∈range (t+1),(-1:O)^(t-j)*(dw (t+1) (j+1):O)*((j+1:ℕ):O)^(r+1):=by rw[sum_range_succ'];simp only[jc,lC (j7 r),hK,i0];refine dF rfl fun j _=>by simp
  rw[i];have e:∀j∈range (t+1),(dw (t+1) (j+1):O)*((j+1:ℕ):O)=((t+1:ℕ):O)*(dw t j:O):=by intro j _;have c:=Nat.add_one_mul_choose_eq t j;have l:((t+1:ℕ):O)*(dw t j:O)=(dw (t+1) (j+1):O)*((j+1:ℕ):O):=(by exact_mod_cast c);exact l.symm
  have m:∑j∈range (t+1),(-1:O)^(t-j)*(dw (t+1) (j+1):O)*((j+1:ℕ):O)^(r+1) =((t+1:ℕ):O)*∑s∈range (r+1),(dw r s:O) *∑j∈range (t+1),(-1:O)^(t-j)*(dw t j:O)*(j:O)^s:=by
   rw[dP];trans ∑j∈range (t+1),((t+1:ℕ):O) *∑s∈range (r+1),(dw r s:O) *((-1:O)^(t-j)*(dw t j:O)*(j:O)^s)
   ·refine dF rfl fun j q=>?_
    rw[fp,<- f0,f0 ((-1:O)^(t-j)),e j q];have d:((j+1:ℕ):O)^r=∑s∈range (r+1),(dw r s:O)*(j:O)^s:=by rw[jX,eF,add_pow];exact dF rfl fun s _=>by rw[jQ,fv,e8]
    rw[d,dP,dP];exact dF rfl fun s _=>_R
   ·rw[<- dP,hH,dP];refine dF rfl fun s _=>?_
    rw[dP,dP];exact (dP ..).symm
  rw[m];have b:∀s∈range (r+1),(dw r s:O) *∑j∈range (t+1),(-1:O)^(t-j)*(dw t j:O)*(j:O)^s=0:=by intro s o;rw[dN]at o;rw[cH t s _O,hK]
  rw[g0 b,hK]
set_option maxHeartbeats 800000 in
lemma cI (t:ℕ):∀(x y:O),∑j∈range (t+1),(dw t j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(y+((t-j:ℕ):O))^(t-j)=(x+y+(t:O))^t:=by
 induction t with
 | zero=>intro x y;simp
 | succ t ih=>
  intro x y;let F:O->O:=fun z=>
   (∑j∈range (t+2),(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(z+((t+1-j:ℕ):O))^(t+1-j))-(x+z+((t+1:ℕ):O))^(t+1)
  have b:∀z:O,HasDerivAt F 0 z:=by
   intro z;have o:∀j∈range (t+2),HasDerivAt (fun w=>(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(w+((t+1-j:ℕ):O))^(t+1-j))
     ((dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(((t+1-j:ℕ):O)*(z+((t+1-j:ℕ):O))^(t+1-j - 1))) z:=by
    intro j _;have v:HasDerivAt (fun w:O=>w+((t+1-j:ℕ):O)) 1 z:=(gh z).add_const ((t+1-j:ℕ):O);have A:HasDerivAt (fun w:O=>(w+((t+1-j:ℕ):O))^(t+1-j)) (((t+1-j:ℕ):O)*(z+((t+1-j:ℕ):O))^(t+1-j - 1)) z:=(by simpa[fv] using v.fun_pow (t+1-j));exact A.const_mul ((dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)))
   have e:=HasDerivAt.fun_sum o;have h:HasDerivAt (fun w:O=>(x+w+((t+1:ℕ):O))^(t+1)) (((t+1:ℕ):O)*(x+z+((t+1:ℕ):O))^t) z:=(by have v:HasDerivAt (fun w:O=>x+w+((t+1:ℕ):O)) 1 z:=((gh z).const_add x).add_const ((t+1:ℕ):O);have A:=v.fun_pow (t+1);simpa[fv] using A);have R:HasDerivAt F ((∑j∈range (t+2),(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(((t+1-j:ℕ):O)*(z+((t+1-j:ℕ):O))^(t+1-j - 1))) -((t+1:ℕ):O)*(x+z+((t+1:ℕ):O))^t) z:=e.fun_sub h;have c:(∑j∈range (t+2),(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(((t+1-j:ℕ):O)*(z+((t+1-j:ℕ):O))^(t+1-j - 1))) -((t+1:ℕ):O)*(x+z+((t+1:ℕ):O))^t=0:=by
    rw[jt];simp only[Nat.sub_self,jc,kP,hK,i0];have B:∑j∈range (t+1),(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *(((t+1-j:ℕ):O)*(z+((t+1-j:ℕ):O))^(t+1-j - 1)) =((t+1:ℕ):O)*∑j∈range (t+1),(dw t j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *((z+1)+((t-j:ℕ):O))^(t-j):=by
     rw[dP];refine dF rfl fun j Q=>?_
     rw[dN]at Q;have J:(dw (t+1) j:O)*((t+1-j:ℕ):O) =((t+1:ℕ):O)*(dw t j:O):=by
      have C:dw (t+1) j*(t+1-j)=(t+1)*dw t j:=by
       have v:=f7 (_O :j<=t);have A:=f7 (_O :j<=t+1);have S:(t+1-j).factorial=(t+1-j)*(t-j).factorial:=(by rw[show t+1-j=(t-j)+1 by omega,e6]);have T:(t+1).factorial=(t+1)*t.factorial:=e6 t;have D:0< j.factorial*(t-j).factorial:=fP (iV _) (iV _);have K:(dw (t+1) j*(t+1-j))*(j.factorial*(t-j).factorial) =((t+1)*dw t j)*(j.factorial*(t-j).factorial):=by
        calc _=dw (t+1) j*j.factorial*((t+1-j)*(t-j).factorial):=by ring
          _=(t+1).factorial:=by rw[<- S];exact A
          _=(t+1)*(dw t j*j.factorial*(t-j).factorial):=by rw[T,v]
          _=_:=by ring
       exact ii D K
      exact_mod_cast C
     have q:t+1-j - 1=t-j:=_O;have i:z+((t+1-j:ℕ):O)=(z+1)+((t-j:ℕ):O):=(by rw[show t+1-j=(t-j)+1 by omega];push_cast;ring);rw[q,i];linear_combination (if j=0 then (1:O) else x*(x+(j:O))^(j-1)) *((z+1)+((t-j:ℕ):O))^(t-j)*J
    rw[B,ih x (z+1)];have l:x+(z+1)+(t:O)=x+z+((t+1:ℕ):O):=(by push_cast;ring);rw[l];ring
   rwa[c]at R
  have m:F y=F (-x-((t+1:ℕ):O)):=is_const_of_deriv_eq_zero (fun z=>(b z).differentiableAt) (fun z=>(b z).deriv) y _;have M:F (-x-((t+1:ℕ):O))=0:=by
   dsimp only[F];have N:x+(-x-((t+1:ℕ):O))+((t+1:ℕ):O)=0:=_R;rw[N,lC (j7 t),kf];have E:∀j∈range (t+2),(dw (t+1) j:O)*(if j=0 then 1 else x*(x+(j:O))^(j-1)) *((-x-((t+1:ℕ):O))+((t+1-j:ℕ):O))^(t+1-j) =x*((-1:O)^(t+1-j)*(dw (t+1) j:O)*(x+(j:O))^t):=by
    intro j Q;rw[dN]at Q;have u:(-x-((t+1:ℕ):O))+((t+1-j:ℕ):O)=-(x+(j:O)):=(by rw[ei (_O :j<=t+1)];ring);rw[u,neg_eq_neg_one_mul,eP];by_cases H:j=0
    ·subst H;simp[fc];ring
    ·rw[gc H];have G:(j-1)+(t+1-j)=t:=_O
     calc (dw (t+1) j:O)*(x*(x+(j:O))^(j-1)) *
           ((-1:O)^(t+1-j)*(x+(j:O))^(t+1-j))
         = x*((-1:O)^(t+1-j)*(dw (t+1) j:O) *((x+(j:O))^(j-1)*(x+(j:O))^(t+1-j))):=by ring
       _=x*((-1:O)^(t+1-j)*(dw (t+1) j:O)*(x+(j:O))^t):=by rw[<- ee,G]
   rw[dF rfl E,<- dP];have d:∑j∈range (t+2),(-1:O)^(t+1-j)*(dw (t+1) j:O)*(x+(j:O))^t=0:=by
    trans ∑r∈range (t+1),(dw t r:O)*x^(t-r) *∑j∈range (t+2),(-1:O)^(t+1-j)*(dw (t+1) j:O)*(j:O)^r
    ·trans ∑j∈range (t+2),∑r∈range (t+1),(dw t r:O)*x^(t-r) *((-1:O)^(t+1-j)*(dw (t+1) j:O)*(j:O)^r)
     ·refine dF rfl fun j _=>?_
      rw[ip x (j:O),add_pow,dP];exact dF rfl fun r _=>_R
     ·rw[hH];exact dF rfl fun r _=>(dP ..).symm
    ·refine g0 fun r U=>?_
     rw[dN]at U;rw[cH (t+1) r _O,hK]
   rw[d,hK]
  have P:F y=0:=m.trans M;dsimp only[F]at P;linarith
set_option maxHeartbeats 800000 in
lemma cJ (t:ℕ) (Q:1<=t) {a b:O} (N:0< a) (P:0< b) :
 ∑j∈range (t+1),(dw t j:O)*(a+(j:O))^((j:ℤ)-1) *(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1) =
 (1/a+1/b)*((t:O)+a+b)^(t-1):=by
 have K:0< (t:O)+a+b:=_P;have C:a*b*((t:O)+a+b) *(∑j∈range (t+1),(dw t j:O)*(a+(j:O))^((j:ℤ)-1) *(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1)) =(a+b)*((t:O)+a+b)^t:=by
  rw[dP];have o:∀j∈range (t+1),a*b*((t:O)+a+b) *((dw t j:O)*(a+(j:O))^((j:ℤ)-1) *(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1)) =b*((dw t j:O)*(if j=0 then 1 else a*(a+(j:O))^(j-1)) *(b+((t-j:ℕ):O))^(t-j)) +a*((dw t (t-j):O)*(if t-j=0 then 1 else b*(b+((t-j:ℕ):O))^(t-j - 1)) *(a+(j:O))^j):=by
   intro j E;rw[dN]at E;have i:j<=t:=_O;have c:0< a+(j:O):=_P;have d:0< b+((t-j:ℕ):O):=_P;have l:(t:O)+a+b=(a+(j:O))+(b+((t-j:ℕ):O)):=(by rw[ei i];ring);have q:(a+(j:O))^((j:ℤ)-1)*(a+(j:O))=(a+(j:O))^j:=(by rw[zpow_sub_one₀ c.ne',mK c.ne',fo]);have u:(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1)*(b+((t-j:ℕ):O)) =(b+((t-j:ℕ):O))^(t-j):=(by rw[zpow_sub_one₀ d.ne',mK d.ne',fo]);have e:dw t (t-j)=dw t j:=Nat.choose_symm i;rw[e,l];have v:a*(a+(j:O))^((j:ℤ)-1)=if j=0 then 1 else a*(a+(j:O))^(j-1):=by
    by_cases F:j=0
    ·subst F;simp[N.ne']
    ·rw[gc F,show ((j:ℤ)-1)=((j-1:ℕ):ℤ) by omega,fo]
   have w:b*(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1) =if t-j=0 then 1 else b*(b+((t-j:ℕ):O))^(t-j - 1):=by
    by_cases m:t-j=0
    ·rw[iM m,m];simp[P.ne']
    ·rw[gc m,show (((t-j:ℕ):ℤ)-1)=((t-j - 1:ℕ):ℤ) by omega,fo]
   calc a*b*((a+(j:O))+(b+((t-j:ℕ):O))) *
         ((dw t j:O)*(a+(j:O))^((j:ℤ)-1) *(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1))
       = b*((dw t j:O)*(a*(a+(j:O))^((j:ℤ)-1)) *((b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1)*(b+((t-j:ℕ):O)))) +a*((dw t j:O)*(b*(b+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1)) *((a+(j:O))^((j:ℤ)-1)*(a+(j:O)))):=by ring
     _=_:=by rw[v,w,q,u]
  rw[dF rfl o,fD,<- dP,<- dP];have A:=cI t a b;have B:∑j∈range (t+1),(dw t (t-j):O)*(if t-j=0 then 1 else b*(b+((t-j:ℕ):O))^(t-j - 1)) *(a+(j:O))^j=(b+a+(t:O))^t:=by rw[<- cI t b a];refine fh (fun j _=>t-j) (fun j E=>by rw[dN]at E ⊢;omega) (fun R H S J h=>by rw[dN]at H J;omega) (fun r M=>⟨t-r,by rw[dN]at M ⊢;omega,by rw[dN]at M;omega⟩) (fun j E=>by rw[dN]at E;rw[show t-(t-j)=j by omega])
  rw[A,B];have y:a+b+(t:O)=(t:O)+a+b:=_R;have z:b+a+(t:O)=(t:O)+a+b:=_R;rw[y,z];ring
 have D:((t:O)+a+b)^t=((t:O)+a+b)*((t:O)+a+b)^(t-1):=by rw[<- fp,eN Q]
 have G:a*b*((t:O)+a+b)≠0:=_P;apply mul_left_cancel₀ G;rw[C,D];field_simp [N.ne',P.ne'];ring
set_option maxHeartbeats 800000 in
lemma cK (t:ℕ) (ht:2<=t) (a b:O) (hb:0<=b) (hr:0< (t:O)+a+b) :
 ∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),(dw t j:O)*(a+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1) <=
 exp 4*((t:O)+a+b)^(t-1):=by
 have e:∀(c:O),-1<=c -> ∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+c),(dw t j:O)*(c+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1) <=exp 4*((t:O)+c+b)^(t-1):=by
  intro c hA;let A:O:=max 1 c;let B:O:=max 1 b;have he:1<=A:=eo 1 c;have hf:1<=B:=eo 1 b;have hg:c<=A:=ep 1 c;have hh:b<=B:=ep 1 b;have m:∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+c),(dw t j:O)*(c+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1) <=∑j∈range (t+1),(dw t j:O)*(A+(j:O))^((j:ℤ)-1) *(B+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1):=by
   have w:(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+c)⊆range (t+1):=by intro j l;rw[dB,dT]at l;rw[dN];omega
   calc _<=∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+c),
             (dw t j:O)*(A+(j:O))^((j:ℤ)-1) *(B+((t-j:ℕ):O))^(((t-j:ℕ):ℤ)-1):=by
           refine dG fun j l=>?_
           rw[dB,dT]at l;rw[show ((j:ℤ)-1)=((j-1:ℕ):ℤ) by omega,fo,show (((t-j:ℕ):ℤ)-1)=((t-j - 1:ℕ):ℤ) by omega,fo]
           have M:(c+(j:O))^(j-1)<=(A+(j:O))^(j-1):=m9 (_l l.2) _L _;have N:(b+((t-j:ℕ):O))^(t-j - 1)<=(B+((t-j:ℕ):O))^(t-j - 1):=m9 _P _L _;gcongr
     _<=_:=dC w fun j _ _=>by
           have M:(0:O)< A+(j:O):=_l (dK (α:=O) j);have N:(0:O)< B+((t-j:ℕ):O):=_l (dK (α:=O) (t-j));positivity
  rw[cJ t _O (_L :0< A) (_L :0< B)]at m;have z:1/A+1/B<=2:=by have M:1/A<=1:=(iy _L).mpr he;have N:1/B<=1:=(iy _L).mpr hf;linarith
  have E:(t:O)+A+B<=(t:O)+c+b+3:=(by have hk:A<=c+2:=kC _L _L;have hl:B<=b+1:=kC _L _L;linarith);have hm:(1:O)<=(t:O)+c+b:=(by have hn:(2:O)<=(t:O):=_M ht;linarith);have Z:((t:O)+c+b+3)^(t-1) <=exp 3*((t:O)+c+b)^(t-1):=by
   have M:(1+3/((t:O)+c+b))^(t-1)<=exp 3:=by
    calc (1+3/((t:O)+c+b))^(t-1)
        <= (exp (3/((t:O)+c+b)))^(t-1):=m9 _P (_l (fB (3/((t:O)+c+b)))) _
      _=exp (((t-1:ℕ):O)*(3/((t:O)+c+b))):=(gg _ _).symm
      _<=exp 3:=by
          apply me.mpr
          rw[gl,mc _L];rw[ei (_O :1<=t),eF];linarith
   have h3:(t:O)+c+b+3=((t:O)+c+b)*(1+3/((t:O)+c+b)):=(by field_simp [(_L :(t:O)+c+b≠0)]);rw[h3,eP];nlinarith[fK (_L :0<=(t:O)+c+b) (t-1)]
  have hu:2*exp 3<=exp 4:=by
   rw[show (4:O)=1+3 by norm_num,gX]
   have:(2:O)<=exp 1:=_l lX
   nlinarith[ez 3]
  calc _<=(1/A+1/B)*((t:O)+A+B)^(t-1):=m
    _<=2*((t:O)+c+b+3)^(t-1):=en z (m9 _P E _) _P zero_le_two
    _<=2*(exp 3*((t:O)+c+b)^(t-1)):=_L
    _<=exp 4*((t:O)+c+b)^(t-1):=by nlinarith[fK (_L :0<=(t:O)+c+b) (t-1)]
 by_cases ha : -1<=a
 ·exact e a ha
 ·push Not at ha
  have h4:∀(x y:O),0< x->x<=y->0< x+(a+1) -> (1+(a+1)/x)^x<=(1+(a+1)/y)^y:=by
   intro x y hx W hc;have hy:0< y:=_L;have M:0< 1+(a+1)/x:=(by rw[show 1+(a+1)/x=(x+(a+1))/x by field_simp [hx.ne']];positivity);have N:0< 1+(a+1)/y:=(by rw[show 1+(a+1)/y=(y+(a+1))/y by field_simp [hy.ne']];exact gN _L hy);rw[<- kj (k5 M x) (k5 N y),kR M,kR N];let g:O->O:=fun s=>s*log (1+(a+1)/s);have q:∀s∈Set.Icc x y,0< s/\0< 1+(a+1)/s:=by
    intro s D;have h:0< s:=_l D.1;refine⟨h,?_⟩;rw[show 1+(a+1)/s=(s+(a+1))/s by field_simp [h.ne']]
    exact gN (_l D.1) h
   have i:∀s∈Set.Icc x y,HasDerivAt g (log (1+(a+1)/s)-((a+1)/s)/(1+(a+1)/s)) s:=by
    intro s D;have ⟨hs0,h1s⟩:=q s D;have F:HasDerivAt (fun u=>(a+1)/u) (-(a+1)/s^2) s:=by have h0:=(hasDerivAt_inv hs0.ne').const_mul (a+1);have C:(a+1)*-(s^2)⁻¹=-(a+1)/s^2:=_R;have ho:(fun u:O=>(a+1)*u⁻¹)=(fun u:O=>(a+1)/u):=(by ext u;rw[ic]);rwa[ho,C]at h0
    have G:HasDerivAt (fun u=>log (1+(a+1)/u)) ((-(a+1)/s^2)/(1+(a+1)/s)) s:=(F.const_add 1).log h1s.ne';have hd:HasDerivAt g (1*log (1+(a+1)/s)+s*((-(a+1)/s^2)/(1+(a+1)/s))) s:=(gh s).fun_mul G;have C:1*log (1+(a+1)/s)+s*((-(a+1)/s^2)/(1+(a+1)/s)) =log (1+(a+1)/s)-((a+1)/s)/(1+(a+1)/s):=(by field_simp [hs0.ne',h1s.ne'];ring);rwa[C]at hd
   have P:=monotoneOn_of_deriv_nonneg (convex_Icc x y) (fun s D=>(i s D).continuousAt.continuousWithinAt) (fun s D=>(i s (lp D)).differentiableAt.differentiableWithinAt)
    (fun s D=>by
     rw[(i s (lp D)).deriv];have ⟨hs0,h1s⟩:=q s (lp D);have hq:=fl h1s;have h3:1-(1+(a+1)/s)⁻¹=((a+1)/s)/(1+(a+1)/s):=by have h5:1+(a+1)/s≠0:=h1s.ne';rw[inv_eq_one_div,one_sub_div h5];ring
     linarith)
   exact P ⟨eR,W⟩ ⟨W,eR⟩ W
  have X:(0:O)< ((t-1:ℕ):O):=_M (_O :0< t-1);have o:((t-1:ℕ):O)=(t:O)-1:=(by rw[ei (_O :1<=t),eF]);by_cases K:(t:O)+a<=0
  ·have h6:(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a)=∅:=by
    ext j;simp only[dB,dT,fq,iC];rintro⟨⟨_,l⟩,hc⟩;have:(j:O)<=(t:O)-1:=by
     have:(j:O)<=((t-1:ℕ):O):=_M l
     linarith
    linarith
   rw[h6,gG];positivity
  ·push Not at K
   have Q:∀j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),(a+(j:O))^(j-1) <=(((t:O)+a)/((t:O)-1))^(t-1)*((-1:O)+(j:O))^(j-1):=by
    intro j l;rw[dB,dT]at l;have hv:2<=j:=by by_contra hp;push Not at hp;have:j=1:=_O;subst this;simp at l;linarith
    have H:(0:O)< ((j-1:ℕ):O):=_M (_O :0< j-1);have h7:((j-1:ℕ):O)=(j:O)-1:=(by rw[ei (_O :1<=j),eF]);have d:=h4 ((j-1:ℕ):O) ((t-1:ℕ):O) H (_M (_O :j-1<=t-1)) (_l l.2);rw[eK,eK]at d;have M:(1+(a+1)/((j-1:ℕ):O))=(a+(j:O))/((-1:O)+(j:O)):=(by rw[h7];have h8:(j:O)-1≠0:=_L;have h9:(-1:O)+(j:O)≠0:=_L;field_simp [h8,h9];ring);have N:(1+(a+1)/((t-1:ℕ):O))=((t:O)+a)/((t:O)-1):=(by rw[o];field_simp [(_L :(t:O)-1≠0)];ring);rw[M,N,ij,mc (iN (_L :0< (-1:O)+(j:O)) _)]at d;exact d
   have w:(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a) ⊆ (Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+(-1:O)):=(by intro j l;simp only[dB]at l ⊢;exact⟨l.1,_L⟩);have J :
    ∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),(dw t j:O)*(a+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1) <=
    (((t:O)+a)/((t:O)-1))^(t-1) *∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+(-1:O)),(dw t j:O)*((-1:O)+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1):=by
    calc _<=∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),
              (((t:O)+a)/((t:O)-1))^(t-1) *((dw t j:O)*((-1:O)+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1)):=by
            refine dG fun j l=>?_
            have hw:=Q j l;have hz:0<=(dw t j:O)*(b+((t-j:ℕ):O))^(t-j - 1):=_P;nlinarith
      _=(((t:O)+a)/((t:O)-1))^(t-1) *∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),(dw t j:O)*((-1:O)+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1):=(dP ..).symm
      _<=_:=dA
            (dC w fun j l _=>by
              rw[dB]at l;have:0<=(-1:O)+(j:O):=_l l.2;positivity)
            (fK (ed K.le _L) _)
   have R:=e (-1) eR;have v:(((t:O)+a)/((t:O)-1))*((t:O)+(-1)+b)<=(t:O)+a+b:=by rw[gm,mc (_L :0< (t:O)-1)];nlinarith
   calc _<=(((t:O)+a)/((t:O)-1))^(t-1)*(exp 4*((t:O)+(-1)+b)^(t-1)):=
         J.trans (dA R (fK (ed K.le _L) _))
     _=exp 4*((((t:O)+a)/((t:O)-1))*((t:O)+(-1)+b))^(t-1):=by rw[eP];ring
     _<=exp 4*((t:O)+a+b)^(t-1):=dA (m9 (by
           have hn:(2:O)<=(t:O):=_M ht;have S:0<=(t:O)+a:=K.le;have T:0< (t:O)-1:=_L;have U:0<=(t:O)+(-1)+b:=_L;exact ek (ed S T.le) U) v _) (ez 4).le
set_option maxHeartbeats 800000 in
lemma cL (g k s u v:ℕ) (Hm:1<=g) (Ht:g+1<=k) (Hn:k<=10*v)
 (Hu:k+1<=u+v) :
 let R:Set (Fin k->O):=
  {ξ∈cA k (u:O) (v:O) |
    ∃l:Fin k,g<=l.1 /\((l.1+1:ℕ):O)-(u:O)<=(v:O)*ξ l /\(v:O)*ξ l<=((l.1+1:ℕ):O)-(u:O)+1 /\((l.1+1:ℕ):O)-(u:O)-(s:O)<=(v:O)*ξ ⟨l.1-g,_O⟩}
 (volume R).toReal <=80000*exp 14*((g:O)+3)^2*(10*((s:O)+1))^g/(g.factorial:O) *(((u:O)+1)*(((u+v-k:ℕ):O)+1)^2/((k+1).factorial:O)):=by
 intro R;have m:(0:O)< (v:O):=_M (_O :0< v);let Rl (l:Fin k):Set (Fin k->O):=
  {ξ∈cA k (u:O) (v:O) |
    ((l.1+1:ℕ):O)-(u:O)<=(v:O)*ξ l /\
    (v:O)*ξ l<=((l.1+1:ℕ):O)-(u:O)+1 /\
    ((l.1+1:ℕ):O)-(u:O)-(s:O)<=(v:O)*ξ ⟨l.1-g,_O⟩}
 have H0:R⊆⋃ l∈univ.filter (fun l:Fin k=>g<=l.1),Rl l:=by intro ξ hξ;rcases hξ with⟨hS,l,hy,z,C,U⟩;exact k6 (dB.mpr ⟨dJ l,hy⟩) ⟨hS,z,C,U⟩
 have hn:∀l:Fin k,g<=l.1 -> (volume (Rl l)).toReal <=if l.1+1< u then 0
   else
    (40000*((s:O)+1)^g*((u:O)+1)*((g:O)+3)^2 *(((u+v-k:ℕ):O)+1)^2) /
    ((g.factorial:O)*(v:O)^k*((k+1-g).factorial:O)) *
    ((dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1))):=by
  intro l hy;by_cases hz:l.1+1< u
  ·rw[iM hz];have hM:Rl l⊆{ξ : Fin k->O | ξ l=0}:=by
    intro ξ hξ;have z:0<=ξ l:=(hξ.1.1.1 l).1;have C:(v:O)*ξ l<=0:=by
     have:((l.1+1:ℕ):O)-(u:O)+1<=0:=by
      have:l.1+2<=u:=_O
      have hR:((l.1+2:ℕ):O)<=(u:O):=_M this;push_cast at hR ⊢;linarith
     linarith[hξ.2.2.1]
    have U : ξ l<=0:=nonpos_of_mul_nonpos_right C m;exact i8 U z
   have hN:volume {ξ : Fin k->O | ξ l=0}=0:=(by have h:=cz l {ξ : Fin k->O | ξ l=0} (measurableSet_eq_fun (dO l) eV);rw[h];have h9:(cv l).symm ⁻¹' {ξ : Fin k->O | ξ l=0} ={(0:O)}×ˢ(Set.univ×ˢSet.univ):=(by ext ⟨t,a,c⟩;simp only[eL,eM,il,Set.mem_singleton_iff,Set.mem_univ,and_true,cx]);rw[h9];change (volume.prod (volume.prod volume)) _=0;rw[f5,Real.volume_singleton,kP]);have H1:volume (Rl l)<=0:=(f4 hM).trans_eq hN;rw[nonpos_iff_eq_zero.mp H1];simp
  ·rw[gc hz];push Not at hz;let o:ℕ:=l.1-g;let q:ℕ:=k-1 - l.1;let N:(Fin k->O) ≃ᵐ (Fin o->O) × (Fin g->O) × O × (Fin q->O):=
    { toFun:=fun ξ=>
        (fun i=>ξ ⟨i.1,_O⟩,fun i=>ξ ⟨o+i.1,_O⟩,ξ l,fun i=>ξ ⟨l.1+1+i.1,_O⟩)
      invFun:=fun p i=>
        if z:i.1< o then p.1 ⟨i.1,z⟩
        else if C:i.1< l.1 then p.2.1 ⟨i.1-o,_O⟩
        else if U:i.1=l.1 then p.2.2.1
        else p.2.2.2 ⟨i.1-l.1-1,_O⟩
      left_inv:=fun ξ=>by
        funext i;dsimp only;split_ifs with z C U
        · rfl
        · congr 1;exact dQ (by dsimp only;omega)
        · congr 1;exact dQ U.symm
        · congr 1;exact dQ (by dsimp only;omega)
      right_inv:=fun ⟨a,b,t,c⟩=>by
        refine iq (by funext i;simp[i.2])
          (iq (by
            funext i;dsimp only;have z:¬ o+i.1< o:=_O;have C:o+i.1< l.1:=_O;rw[eA z,eG C];congr 1;exact dQ (by dsimp only;omega))
            (iq (by
              dsimp only;have z:¬ l.1< o:=_O;have C:¬ l.1< l.1:=gU _;rw[eA z,eA C,eG rfl])
              (by
                funext i;dsimp only;have z:¬ l.1+1+i.1< o:=_O;have C:¬ l.1+1+i.1< l.1:=_O;have U:¬ l.1+1+i.1=l.1:=_O;rw[eA z,eA C,eA U];congr 1;exact dQ (by dsimp only;omega))))
      measurable_toFun:=iX (eU _ fun _=>dO _)
        (iX (eU _ fun _=>dO _)
          (iX (dO l) (eU _ fun _=>dO _)))
      measurable_invFun:=eU _ fun i=>by
        simp only[g8];split_ifs
        · exact (dO _).comp lI
        · exact (dO _).comp (lI.comp iR)
        · exact lI.comp (iR.comp iR)
        · exact (dO _).comp (iR.comp (iR.comp iR))}
   have H2:MeasurePreserving N volume volume:=by
    refine⟨N.measurable,?_⟩
    have hP:Measure.map N.symm volume=volume:=by
     symm;refine lY fun s hs=>?_
     rw[l3 N.symm.measurable (ka hs)];have h9:N.symm ⁻¹' (Set.univ.pi s) =(Set.univ.pi fun i:Fin o=>s ⟨i.1,_O⟩) ×ˢ
      ((Set.univ.pi fun i:Fin g=>s ⟨o+i.1,_O⟩) ×ˢ
      ((s l)×ˢ(Set.univ.pi fun i:Fin q=>s ⟨l.1+1+i.1,_O⟩))):=by
      ext ⟨a,b,t,c⟩;simp only[eL,lr,il,N,iH,gQ,g8];constructor
      ·intro h;refine⟨fun i=>by have hi:=h ⟨i.1,_O⟩;rwa[eG i.2]at hi,fun i=>by
         have hi:=h ⟨o+i.1,_O⟩;have z:¬ o+i.1< o:=_O;have C:o+i.1< l.1:=_O;rw[eA z,eG C]at hi;simpa[show (⟨o+i.1-o,_O⟩:Fin g)=i from dQ (by dsimp only;omega)] using hi,
        by
         have hi:=h l;have z:¬ l.1< o:=_O;have C:¬ l.1< l.1:=gU _;rwa[eA z,eA C,eG rfl]at hi,
        fun i=>by
         have hi:=h ⟨l.1+1+i.1,_O⟩;have z:¬ l.1+1+i.1< o:=_O;have C:¬ l.1+1+i.1< l.1:=_O;have U:¬ l.1+1+i.1=l.1:=_O;rw[eA z,eA C,eA U]at hi;simpa[show (⟨l.1+1+i.1-l.1-1,_O⟩:Fin q)=i from dQ (by dsimp only;omega)] using hi⟩
      ·rintro⟨ha,hb,ht,hc⟩ i;by_cases z:i.1< o
       ·rw[eG z];exact ha ⟨i.1,z⟩
       ·rw[eA z];by_cases C:i.1< l.1
        ·rw[eG C];have:=hb ⟨i.1-o,_O⟩;have B:(⟨o+(i.1-o),_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rwa[B]at this
        ·rw[eA C];by_cases U:i.1=l.1
         ·rw[eG U];have hi:i=l:=dQ U;rwa[hi]
         ·rw[eA U];have:=hc ⟨i.1-l.1-1,_O⟩;have B:(⟨l.1+1+(i.1-l.1-1),_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rwa[B]at this
     rw[h9];change (volume.prod (volume.prod (volume.prod volume))) _=_;rw[f5,f5,f5];change (Measure.pi fun _:Fin o=>(volume:Measure O)) _ *((Measure.pi fun _:Fin g=>(volume:Measure O)) _ *(volume (s l)*(Measure.pi fun _:Fin q=>(volume:Measure O)) _))=_;rw[gV,gV,gV];have ho:(∏i:Fin k,volume (s i)) =(∏i:Fin o,volume (s ⟨i.1,_O⟩)) *((∏i:Fin g,volume (s ⟨o+i.1,_O⟩)) *(volume (s l)*∏i:Fin q,volume (s ⟨l.1+1+i.1,_O⟩))):=by
      rw[<- ey univ (fun i:Fin k=>i.1< o)];congr 1
      ·exact hJ (fun i hi=>⟨i.1,by simp at hi;exact hi⟩) (fun _ _=>dJ _) (fun _ _ _ _ h=>dQ (es h)) (fun i _=>⟨⟨i.1,_O⟩,by simp[i.2],rfl⟩) (fun _ _=>rfl)
      ·rw[<- ey _ (fun i:Fin k=>i.1< l.1)];congr 1
       ·refine hJ (fun i hi=>⟨i.1-o,by simp at hi;omega⟩) (fun _ _=>dJ _) (fun i1 hA i2 hB h=>by simp at hA hB;have hv:=es h;exact dQ _O)
         (fun i _=>⟨⟨o+i.1,_O⟩,dB.mpr ⟨dB.mpr ⟨dJ _,by dsimp only;omega⟩,by dsimp only;omega⟩,dQ (by dsimp only;omega)⟩)
         (fun i hi=>by
          simp at hi;have G:(⟨o+(i.1-o),_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rw[G])
       ·have hp:l∈(univ.filter (fun i:Fin k=>¬ i.1< o)).filter (fun i:Fin k=>¬ i.1< l.1):=by
         simp;omega
        rw[<- gk _ _ hp];congr 1;refine hJ (fun i hi=>⟨i.1-l.1-1,by
         rw[gS,dB,dB]at hi;have:i.1≠l.1:=fun h=>hi.1 (dQ h);omega⟩)
         (fun _ _=>dJ _)
         (fun i1 hA i2 hB h=>by
          rw[gS,dB,dB]at hA hB;have Ho:i1.1≠l.1:=fun h=>hA.1 (dQ h);have Hp:i2.1≠l.1:=fun h=>hB.1 (dQ h);have hv:=es h;exact dQ _O)
         (fun i _=>⟨⟨l.1+1+i.1,_O⟩,by
          rw[gS,dB,dB];exact⟨fun h=>by have:=es h;omega,⟨dJ _,by dsimp only;omega⟩,by dsimp only;omega⟩,
          dQ (by dsimp only;omega)⟩)
         (fun i hi=>by
          rw[gS,dB,dB]at hi;have Hq:i.1≠l.1:=fun h=>hi.1 (dQ h);have G:(⟨l.1+1+(i.1-l.1-1),_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rw[G])
     exact ho.symm
    calc Measure.map N volume=Measure.map N (Measure.map N.symm volume):=by rw[hP]
      _=Measure.map (N ∘ N.symm) volume:=Measure.map_map N.measurable N.symm.measurable
      _=volume:=by simp
   let e:O:=((l.1+1:ℕ):O)-(u:O)+1;have H:0< e:=(by dsimp only[e];have:(u:O)<=((l.1+1:ℕ):O):=_M hz;linarith);let E1:Set (Fin o->O):=(fun (a:Fin o->O) (i:Fin o)=>(v:O)/e*a i+0) ⁻¹' cA o (u:O) e;let E2:Set (Fin g->O):=cr g ((((l.1+1:ℕ):O)-(u:O)-(s:O))/(v:O)) (e/(v:O));let E3:Set O:=Set.Icc ((((l.1+1:ℕ):O)-(u:O))/(v:O)) (e/(v:O));let w:O:=((u+v-(l.1+1):ℕ):O);have D:0< w:=(by dsimp only[w];exact_mod_cast (_O :0< u+v-(l.1+1)));let E4:Set (Fin q->O):=(fun (c:Fin q->O) (i:Fin q)=>
     (v:O)/w*c i+(-((((l.1+1:ℕ):O)-(u:O))/w))) ⁻¹' cA q 0 w
   have Z:Rl l⊆N ⁻¹' (E1×ˢ(E2×ˢ(E3×ˢE4))):=by
    intro ξ hξ;rcases hξ with⟨⟨⟨hL,A⟩,hS⟩,hl_lo,hl_hi,hlg⟩;simp only[eL,il,N,gQ,Equiv.coe_fn_mk];refine⟨?_,?_,?_,?_⟩
    ·
     simp only[E1,eL,i0,cA,cr,eM];refine⟨⟨fun i=>⟨ek _P (hL ⟨i.1,_O⟩).1,?_⟩,fun i1 i2 hm=>dA (A (mh.mpr (by exact hm))) _P⟩,fun i=>?_⟩
     ·rw[gm,iy H];exact (dA (A (mh.mpr _O)) m.le).trans hl_hi
     ·have B:e*((v:O)/e*ξ ⟨i.1,_O⟩)=(v:O)*ξ ⟨i.1,_O⟩:=by
       field_simp [H.ne']
      rw[B];exact hS ⟨i.1,_O⟩
    ·
     simp only[E2,cr,eM];refine⟨fun i=>⟨?_,?_⟩,fun i1 i2 hm=>A (mh.mpr (by have:i1.1<=i2.1:=hm;omega))⟩
     ·rw[mc m,e8];exact hlg.trans (dA (A (mh.mpr (by dsimp only[o];omega))) m.le)
     ·rw[ma m,e8];exact (dA (A (mh.mpr (by dsimp only[o];omega))) m.le).trans hl_hi
    ·
     simp only[E3,Set.mem_Icc];exact⟨(mc m).mpr (by rw[e8];exact hl_lo),(ma m).mpr (by rw[e8];exact hl_hi)⟩
    ·
     simp only[E4,eL,cA,cr,eM];have h0:w=(u:O)+(v:O)-((l.1+1:ℕ):O):=(by dsimp only[w];rw[ei _O,jX]);refine⟨⟨fun i=>⟨?_,?_⟩,fun i1 i2 hm=>by
      dsimp only;have Ha:(⟨l.1+1+i1.1,_O⟩:Fin k)<=⟨l.1+1+i2.1,_O⟩:=mh.mpr (by have:i1.1<=i2.1:=hm;omega);have:=dA (A Ha) (_P :(0:O)<=(v:O)/w);linarith⟩,fun i=>?_⟩
     ·have z:((l.1+1:ℕ):O)-(u:O)<=(v:O)*ξ ⟨l.1+1+i.1,_O⟩:=hl_lo.trans (dA (A (mh.mpr _O)) m.le);have C:=dI z D.le;have B:(v:O)*ξ ⟨l.1+1+i.1,_O⟩/w=(v:O)/w*ξ ⟨l.1+1+i.1,_O⟩:=_R;linarith
     ·have z:(v:O)*ξ ⟨l.1+1+i.1,_O⟩<=(v:O):=by
       have:=(hL ⟨l.1+1+i.1,_O⟩).2;nlinarith
      have B:(v:O)/w*ξ ⟨l.1+1+i.1,_O⟩+-((((l.1+1:ℕ):O)-(u:O))/w) =((v:O)*ξ ⟨l.1+1+i.1,_O⟩ - (((l.1+1:ℕ):O)-(u:O)))/w:=_R;rw[B,iy D,h0];linarith
     ·have z:=hS ⟨l.1+1+i.1,_O⟩;have B:w*((v:O)/w*ξ ⟨l.1+1+i.1,_O⟩+-((((l.1+1:ℕ):O)-(u:O))/w)) =(v:O)*ξ ⟨l.1+1+i.1,_O⟩ - (((l.1+1:ℕ):O)-(u:O)):=(by field_simp [D.ne'];ring);rw[B];have J:((l.1+1+i.1+1:ℕ):O)=((l.1+1:ℕ):O)+((i.1+1:ℕ):O):=(by push_cast;ring);linarith
   have P:MeasurableSet (E1×ˢ(E2×ˢ(E3×ˢE4))):=(by have Hb:MeasurableSet E1:=(cC o (u:O) e).preimage (eU _ fun i=>(eV.mul (dO i)).add eV);have Hc:MeasurableSet E2:=cs g _ _;have Hd:MeasurableSet E3:=kU;have He:MeasurableSet E4:=(cC q 0 w).preimage (eU _ fun i=>(eV.mul (dO i)).add eV);exact Hb.prod (Hc.prod (Hd.prod He)));have he:volume (Rl l)<=volume E1*volume E2*volume E3*volume E4:=by
    calc volume (Rl l)<=volume (N ⁻¹' (E1×ˢ(E2×ˢ(E3×ˢE4)))):=f4 Z
      _=volume (E1×ˢ(E2×ˢ(E3×ˢE4))):=H2.measure_preimage P.nullMeasurableSet
      _=volume E1*(volume E2*(volume E3*volume E4)):=by change (volume.prod (volume.prod (volume.prod volume))) _=_;rw[f5,f5,f5]
      _=volume E1*volume E2*volume E3*volume E4:=by ring
   have hC:volume E1=ENNReal.ofReal ((e/(v:O))^o)*volume (cA o (u:O) e):=(by rw[cu ((v:O)/e) 0 _P (cA o (u:O) e) (cC ..),inv_div]);have hD:volume E2=ENNReal.ofReal ((((s:O)+1)/(v:O))^g/(g.factorial:O)):=(by rw[ct g _ _ (dI (by dsimp only[e];linarith) m.le)];congr 2;dsimp only[e];ring);have hE:volume E3=ENNReal.ofReal (1/(v:O)):=(by rw[Real.volume_Icc];congr 1;dsimp only[e];ring);have hF:volume E4=ENNReal.ofReal ((w/(v:O))^q)*volume (cA q 0 w):=(by rw[cu ((v:O)/w) _ _P (cA q 0 w) (cC ..),inv_div]);have hq:volume (cA o (u:O) e)≠⊤:=fz ec ((f4 (fun _ h=>h.1)).trans_eq
     (ct o 0 1 eO))
   have hr:volume (cA q 0 w)≠⊤:=fz ec ((f4 (fun _ h=>h.1)).trans_eq
     (ct q 0 1 eO))
   have h4:volume E1*volume E2*volume E3*volume E4≠⊤:=by
    rw[hC,hD,hE,hF];exact iA (iA (iA
     (iA ec hq) ec)
     ec) (iA ec hr)
   have hf:=fM h4 he;rw[hC,hD,hE,hF]at hf;simp only[ENNReal.toReal_mul,eZ (_P :0<=(e/(v:O))^o),eZ (_P :0<=(((s:O)+1)/(v:O))^g/(g.factorial:O)),eZ (_P :0<=1/(v:O)),eZ (_P :0<=(w/(v:O))^q)]at hf;have hQ:=cG o (u:O) e (dK u) (by
    dsimp only[e,o];rw[ei hy];push_cast;linarith)
   have hT:=cG q 0 w eR (by
    have y:q<=u+v-(l.1+1):=(by dsimp only[q];omega);have hR:(q:O)<=w:=(by dsimp only[w];exact_mod_cast y);linarith)
   have H8:(volume (cA o (u:O) e)).toReal <=200*((u:O)+1)*((g:O)+3)^2/((o+1).factorial:O):=(by unfold cD at hQ;have Hf:(u:O)+e-(o:O)+1=(g:O)+3:=(by dsimp only[e,o];rw[ei hy];push_cast;ring);rw[Hf]at hQ;rw[e6,g3,<- div_div,ma _P];have J:((o+1:ℕ):O)=(o:O)+1:=(by push_cast;ring);rw[J,e8];exact hQ);have H9:(volume (cA q 0 w)).toReal <=200*(((u+v-k:ℕ):O)+1)^2/((q+1).factorial:O):=by
    unfold cD at hT;have Hg:(0:O)+w-(q:O)+1=((u+v-k:ℕ):O)+1:=by have y:u+v-(l.1+1)=(u+v-k)+q:=(by dsimp only[q];omega);have hR:w=((u+v-k:ℕ):O)+(q:O):=(by dsimp only[w];exact_mod_cast y);linarith
    rw[Hg,zero_add,fv]at hT;rw[e6,g3,<- div_div,ma _P];have J:((q+1:ℕ):O)=(q:O)+1:=(by push_cast;ring);rw[J,e8];exact hT
   have h5:((o+1).factorial:O)*((q+1).factorial:O) =((k+1-g).factorial:O)/(dw (k+1-g) (l.1+1-g):O):=by
    have y:=f7 (_O :l.1+1-g<=k+1-g);have W:l.1+1-g=o+1:=_O;have hg:(k+1-g)-(l.1+1-g)=q+1:=_O;rw[hg,W]at y;have hR:(dw (k+1-g) (l.1+1-g):O)*((o+1).factorial:O)*((q+1).factorial:O) =((k+1-g).factorial:O):=by
     have:dw (k+1-g) (l.1+1-g)*(o+1).factorial*(q+1).factorial =(k+1-g).factorial:=by rw[W];exact y
     exact_mod_cast this
    have E:(0:O)< (dw (k+1-g) (l.1+1-g):O):=(by exact_mod_cast lM (_O :l.1+1-g<=k+1-g));rw[eq_div_iff E.ne'];linarith
   have hu:(v:O)^o*(v:O)^g*(v:O)*(v:O)^q=(v:O)^k:=(by rw[<- ee,<- fc,<- ee];congr 1;omega);have Q:e=((l.1+1-u+1:ℤ):O):=(by dsimp only[e];push_cast;ring);refine hf.trans ?_
   have hU : (e/(v:O))^o*(volume (cA o (u:O) e)).toReal *((((s:O)+1)/(v:O))^g/(g.factorial:O))*(1/(v:O)) *((w/(v:O))^q*(volume (cA q 0 w)).toReal) <=(e/(v:O))^o*(200*((u:O)+1)*((g:O)+3)^2/((o+1).factorial:O)) *((((s:O)+1)/(v:O))^g/(g.factorial:O))*(1/(v:O)) *((w/(v:O))^q*(200*(((u+v-k:ℕ):O)+1)^2/((q+1).factorial:O))):=(by gcongr);refine hU.trans_eq ?_
   rw[ij,ij,ij,<- Q];have F:(g.factorial:O)≠0/\(v:O)^k≠0/\((k+1-g).factorial:O)≠0 /\((o+1).factorial:O)≠0/\((q+1).factorial:O)≠0:=(by refine⟨by positivity,by positivity,by positivity,by positivity,_P⟩);have E:(dw (k+1-g) (l.1+1-g):O)≠0:=by exact_mod_cast (lM (_O :l.1+1-g<=k+1-g)).ne'
   calc e^o/(v:O)^o*(200*((u:O)+1)*((g:O)+3)^2/((o+1).factorial:O)) *
         (((s:O)+1)^g/(v:O)^g/(g.factorial:O))*(1/(v:O)) *
         (w^q/(v:O)^q*(200*(((u+v-k:ℕ):O)+1)^2/((q+1).factorial:O)))
       = 40000*((s:O)+1)^g*((u:O)+1)*((g:O)+3)^2 *(((u+v-k:ℕ):O)+1)^2*e^o*w^q /((g.factorial:O)*((v:O)^o*(v:O)^g*(v:O)*(v:O)^q) *(((o+1).factorial:O)*((q+1).factorial:O))):=by ring
     _=_:=by rw[hu,h5];field_simp [F.1,F.2.1,F.2.2.1,E];ring
 have h6:(volume R).toReal <=∑l∈univ.filter (fun l:Fin k=>g<=l.1),(volume (Rl l)).toReal:=by have G:∀l∈univ.filter (fun l:Fin k=>g<=l.1),volume (Rl l)≠⊤:=(by intro l _;exact fz ec ((f4 (fun _ h=>h.1.1)).trans_eq (ct k 0 1 eO)));have z:volume R<=∑l∈univ.filter (fun l:Fin k=>g<=l.1),volume (Rl l):=(f4 H0).trans (g1 _ _);have C:=fM (mu.mpr G) z;rwa[kK G]at C
 let t:ℕ:=k+1-g;have Hh:2<=t:=_O;let a:O:=((g+1:ℕ):O)-(u:O);let b:O:=((u+v-k - 1:ℕ):O);have M:(t:O)+a+b=(v:O)+1:=by dsimp only[t,a,b];rw[ei _O,ei _O,ei _O];push_cast;ring
 have H3:=cK t Hh a b (dK _) (by rw[M];positivity);rw[M]at H3;have S :
  ∑l∈univ.filter (fun l:Fin k=>g<=l.1),(if l.1+1< u then (0:O)
    else (dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1))) <=
  exp 4*((v:O)+1)^(t-1):=by
  have h7:∑l∈univ.filter (fun l:Fin k=>g<=l.1),(if l.1+1< u then (0:O)
    else (dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1))) =
   ∑l∈(univ.filter (fun l:Fin k=>g<=l.1)).filter (fun l=>¬ l.1+1< u),(dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1)):=by
   conv_rhs=>rw[f8]
   refine dF rfl fun l _=>?_
   split_ifs <;> rfl
  rw[h7];have H4:∑l∈(univ.filter (fun l:Fin k=>g<=l.1)).filter (fun l=>¬ l.1+1< u),(dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1)) =∑j∈(Icc 1 (t-1)).filter (fun (j:ℕ)=>0< (j:O)+a),(dw t j:O)*(a+(j:O))^(j-1)*(b+((t-j:ℕ):O))^(t-j - 1):=by
   refine fh (fun l _=>l.1+1-g) ?_ ?_ ?_ ?_
   ·intro l hl;simp only[dB,dJ,dV,dT]at hl ⊢;refine⟨⟨by omega,_O⟩,?_⟩
    dsimp only[a];have T:((l.1+1-g:ℕ):O)=((l.1+1:ℕ):O)-(g:O):=(by rw[ei _O]);rw[T];push_cast;have:(u:O)<=(l.1:O)+1:=_M (_O :u<=l.1+1);linarith
   ·intro l1 Hk l2 Hl h;simp only[dB]at Hk Hl;exact dQ _O
   ·intro j hj;simp only[dB,dT]at hj;have Hr:u<=j+g:=by
     have z:(u:O)< ((j+g+1:ℕ):O):=(by dsimp only[a]at hj;push_cast at hj ⊢;linarith[hj.2]);have y:u< j+g+1:=_M z;omega
    refine⟨⟨j+g-1,_O⟩,?_,by dsimp only;omega⟩
    simp only[dB,dJ,dV];omega
   ·intro l hl;simp only[dB]at hl;have W:a+((l.1+1-g:ℕ):O)=((l.1+1-u+1:ℤ):O):=(by dsimp only[a];rw[ei _O];push_cast;ring);have hg:b+((t-(l.1+1-g):ℕ):O)=((u+v-(l.1+1):ℕ):O):=by
     have y:(u+v-k - 1)+(t-(l.1+1-g))=u+v-(l.1+1):=(by dsimp only[t];omega);dsimp only[b];exact_mod_cast y
    have hV:l.1+1-g - 1=l.1-g:=_O;have hW:t-(l.1+1-g)-1=k-1 - l.1:=_O;rw[W,hg,hV,hW]
  rw[H4];exact H3
 have hh:((v:O)+1)^(t-1)<=exp 10*(v:O)^(k-g):=by
  have Hi:t-1=k-g:=_O;rw[Hi];have z:(1+1/(v:O))^(k-g)<=exp 10:=by
   calc (1+1/(v:O))^(k-g)<=(exp (1/(v:O)))^(k-g):=
         m9 _P (_l (fB (1/(v:O)))) _
     _=exp (((k-g:ℕ):O)*(1/(v:O))):=(gg _ _).symm
     _<=exp 10:=by
         apply me.mpr
         rw[iE,mc m];have:k-g<=10*v:=_O;exact_mod_cast this
  have B:(v:O)+1=(v:O)*(1+1/(v:O)):=(by field_simp [m.ne']);rw[B,eP];nlinarith[fK m.le (k-g)]
 have K:(v:O)^(k-g)/((v:O)^k*((k+1-g).factorial:O)) <=2*(10:O)^g/((k+1).factorial:O):=by
  have H5:(k:O)<=10*(v:O):=_M Hn;have hX:((k+1).factorial:O)<=2*(k:O)^g*((k+1-g).factorial:O):=by
   have y:(k+1).factorial<=2*k^g*(k+1-g).factorial:=by
    have hY:∀d:ℕ,d<=k->k.factorial<=k^d*(k-d).factorial:=by
     intro d;induction d with
     | zero=>intro _;simp
     | succ d ih=>
      intro hd;have z:=ih _O;have hI:k-d=(k-(d+1))+1:=_O;have H6:(k-d).factorial=(k-d)*(k-(d+1)).factorial:=by conv_lhs=>rw[hI,e6,<- hI]
      calc k.factorial<=k^d*(k-d).factorial:=z
        _=k^d*((k-d)*(k-(d+1)).factorial):=by rw[H6]
        _<=k^d*(k*(k-(d+1)).factorial):=dR _ (eE _ (i4 k d))
        _=k^(d+1)*(k-(d+1)).factorial:=by rw[fc];ring
    have X:=hY (g-1) _O;have hk:k-(g-1)=k+1-g:=_O;rw[hk]at X;have Hj:k+1<=2*k:=_O;have H7:k*k^(g-1)=k^g:=by rw[<- fp,eN Hm]
    calc (k+1).factorial=(k+1)*k.factorial:=e6 k
      _<=(2*k)*(k^(g-1)*(k+1-g).factorial):=eH Hj X
      _=2*(k*k^(g-1))*(k+1-g).factorial:=by ring
      _=2*k^g*(k+1-g).factorial:=by rw[H7]
   exact_mod_cast y
  rw[mb _P _P];have hZ:(v:O)^k=(v:O)^(k-g)*(v:O)^g:=(by rw[<- ee,eN (_O :g<=k)]);have Hs:(k:O)^g<=(10:O)^g*(v:O)^g:=by rw[<- eP];exact m9 (dK k) H5 g
  calc (v:O)^(k-g)*((k+1).factorial:O)
      <= (v:O)^(k-g)*(2*(k:O)^g*((k+1-g).factorial:O)):=dA hX _P
    _<=(v:O)^(k-g)*(2*((10:O)^g*(v:O)^g)*((k+1-g).factorial:O)):=by gcongr
    _=2*(10:O)^g*((v:O)^(k-g)*(v:O)^g*((k+1-g).factorial:O)):=_R
    _=2*(10:O)^g*((v:O)^k*((k+1-g).factorial:O)):=by rw[hZ]
 let C0:O:=40000*((s:O)+1)^g*((u:O)+1)*((g:O)+3)^2 *(((u+v-k:ℕ):O)+1)^2/((g.factorial:O)*(v:O)^k*((k+1-g).factorial:O));have h8:(volume R).toReal<=C0*(exp 4*((v:O)+1)^(t-1)):=by
  calc (volume R).toReal
      <= ∑l∈univ.filter (fun l:Fin k=>g<=l.1),(volume (Rl l)).toReal:=h6
    _<=∑l∈univ.filter (fun l:Fin k=>g<=l.1),C0*(if l.1+1< u then (0:O)
                else (dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1))):=by
          refine dG fun l hl=>?_
          have h:=hn l (dB.mp hl).2;split_ifs at h ⊢
          · simpa using h
          · exact h
    _=C0*∑l∈univ.filter (fun l:Fin k=>g<=l.1),(if l.1+1< u then (0:O)
           else (dw (k+1-g) (l.1+1-g):O) *(((l.1+1-u+1:ℤ):O)^(l.1-g)) *(((u+v-(l.1+1):ℕ):O)^(k-1 - l.1))):=(dP ..).symm
    _<=C0*(exp 4*((v:O)+1)^(t-1)):=dA S _P
 refine h8.trans ?_
 have hw:exp 4*exp 10=exp 14:=by rw[<- gX];norm_num
 have hx:(10*((s:O)+1))^g=(10:O)^g*((s:O)+1)^g:=eP 10 _ g
 calc C0*(exp 4*((v:O)+1)^(t-1))
     <= C0*(exp 4*(exp 10*(v:O)^(k-g))):=dA (dA hh (ez 4).le) _P
   _=40000*exp 14*((g:O)+3)^2*((s:O)+1)^g/(g.factorial:O) *(((u:O)+1)*(((u+v-k:ℕ):O)+1)^2) *((v:O)^(k-g)/((v:O)^k*((k+1-g).factorial:O))):=by dsimp only[C0];rw[<- hw];ring
   _<=40000*exp 14*((g:O)+3)^2*((s:O)+1)^g/(g.factorial:O) *(((u:O)+1)*(((u+v-k:ℕ):O)+1)^2) *(2*(10:O)^g/((k+1).factorial:O)):=dA K _P
   _=80000*exp 14*((g:O)+3)^2*(10*((s:O)+1))^g/(g.factorial:O) *(((u:O)+1)*(((u+v-k:ℕ):O)+1)^2/((k+1).factorial:O)):=by rw[hx];ring
def cM (k v γ : ℕ):Set (Fin k->O):=
 {ξ∈cr k 0 1 | ∀j:Fin k,(2:O)^(((j.1+1:ℕ):O)-(γ : O)) <=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i)}
lemma cN (k v γ : ℕ):MeasurableSet (cM k v γ):=by
 have b:cM k v γ=cr k 0 1 ∩
  ⋂ j:Fin k,{ξ : Fin k->O | (2:O)^(((j.1+1:ℕ):O)-(γ : O)) <=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i)}:=by
  ext ξ;simp[cM]
 rw[b];refine (cs k 0 1).inter (fI fun j=>?_);refine fV eV ?_
 refine Finset.measurable_sum _ fun i _=>?_
 exact eV.pow ((eV.mul (dO i)))
set_option maxHeartbeats 800000 in
lemma cO :
 ∃o:O,0< o/\∀m:ℕ,(((2^m:ℕ):O)+3)^2*(10*((2*m:ℕ):O)+10)^(2^m) /((2^m).factorial:O)<=o/(2:O)^(2^(m+3)):=by
 let f:ℕ->O:=fun m=>
  (((2^m:ℕ):O)+3)^2*(10*((2*m:ℕ):O)+10)^(2^m) /((2^m).factorial:O)*(2:O)^(2^(m+3))
 let o:O:=max 1 (∑m∈range 20,f m);refine⟨o,e9 i5 (eo _ _),fun m=>?_⟩;rw[ma _P];by_cases e:m< 20
 · calc f m<=∑j∈range 20,f j:=
         fi (fun j _=>by dsimp only[f];positivity) (dN.mpr e)
     _<=o:=ep _ _
 · push Not at e
   suffices y:f m<=1 from y.trans (eo _ _)
   dsimp only[f]
   have b:15360*(2*m+1)<=2^m:=by
     induction m,e using fe with
     | base=>norm_num
     | succ n hn ih=>
       have i:15360*(2*(n+1)+1)<=2*(15360*(2*n+1)):=_O
       calc 15360*(2*(n+1)+1)<=2*(15360*(2*n+1)):=i
         _<=2*2^n:=dR 2 ih
         _=2^(n+1):=by ring
   set g:ℕ:=2^m;have h:1<=g:=fY
   have v:(((g:ℕ):O)+3)^2<=(2:O)^g:=by
     have w:16<=g:=by have:15360*(2*m+1)<=g:=b;omega
     have c:∀N:ℕ,16<=N->(N+3)^2<=2^N:=by
       intro N D;induction N,D using fe with
       | base=>norm_num
       | succ n hn ih=>
         have y:(n+1+3)^2<=2*(n+3)^2:=_Q
         calc (n+1+3)^2<=2*(n+3)^2:=y
           _<=2*2^n:=dR 2 ih
           _=2^(n+1):=by ring
     exact_mod_cast c g w
   have d:((g:O)/exp 1)^g<=(g.factorial:O):=by
     have A:=a6 g;have B:(1:O)<=sqrt (2*π*(g:O)):=(by rw[one_le_sqrt];have:(1:O)<=(g:O):=_M h;nlinarith[lh]);have z:0<=((g:O)/exp 1)^g:=_P;nlinarith
   have q:(2:O)^(2^(m+3))=(256:O)^g:=(by have u:2^(m+3)=8*g:=(by dsimp only[g];rw[ee];norm_num;ring);rw[u,it,show (2:O)^8=256 by norm_num]);have l:2*(10*((2*m:ℕ):O)+10)*256<=(g:O)/exp 1:=(by have C:exp 1<=3:=_l gT;rw[ma (ez 1)];have E:(15360:O)*(2*(m:O)+1)<=(g:O):=_M b;have z:0<=2*(10*((2*m:ℕ):O)+10)*256:=_P;have u:2*(10*((2*m:ℕ):O)+10)*256*3=15360*(2*(m:O)+1):=(by push_cast;ring);nlinarith);rw[q,gm,iy _P]
   calc (((g:ℕ):O)+3)^2*(10*((2*m:ℕ):O)+10)^g*(256:O)^g
       <= (2:O)^g*(10*((2*m:ℕ):O)+10)^g*(256:O)^g:=by gcongr
     _=(2*(10*((2*m:ℕ):O)+10)*256)^g:=by rw[<- eP,<- eP]
     _<=((g:O)/exp 1)^g:=m9 _P l g
     _<=(g.factorial:O):=d
set_option maxHeartbeats 800000 in
lemma cP (N:ℕ) :
 ∑d∈range N,((d:O)+1)^3/(2:O)^d<=256:=by
 have b:∀d:ℕ,((d:O)+1)^3/(2:O)^d<=64*((3:O)/4)^d:=by
  intro d;rw[mc _P];have c:64*((3:O)/4)^d*(2:O)^d=64*((3:O)/2)^d:=(by rw[f0,<- eP];norm_num);rw[c];have e:∀d:ℕ,((d:O)+1)^3<=64*((3:O)/2)^d:=by
   intro d;induction d with
   | zero=>norm_num
   | succ n ih=>
    by_cases l:n< 10
    ·interval_cases n <;> norm_num
    ·push Not at l
     have h:(11:O)<=(n:O)+1:=_M (_O :11<=n+1);have i:(((n+1:ℕ):O)+1)^3<=(3/2:O)*((n:O)+1)^3:=(by push_cast;nlinarith[gR ((n:O)+1)]);rw[fp ((3:O)/2)]
     calc (((n+1:ℕ):O)+1)^3<=(3/2:O)*((n:O)+1)^3:=i
       _<=(3/2:O)*(64*((3:O)/2)^n):=dA ih _N
       _=64*((3:O)/2*((3:O)/2)^n):=_R
  exact e d
 calc ∑d∈range N,((d:O)+1)^3/(2:O)^d
     <= ∑d∈range N,64*((3:O)/4)^d:=dG fun d _=>b d
   _=64*∑d∈range N,((3:O)/4)^d:=(dP ..).symm
   _=64*((((3:O)/4)^N-1)/((3:O)/4-1)):=by rw[fO _N]
   _<=256:=by have j:(0:O)<=((3:O)/4)^N:=_P;have c:64*((((3:O)/4)^N-1)/((3:O)/4-1))=256*(1-((3:O)/4)^N):=_R;rw[c];linarith
lemma cQ (N:ℕ) :
 ∑d∈range N,(1:O)/(2:O)^d<=2:=by
 have c:∑d∈range N,(1:O)/(2:O)^d =∑d∈range N,((1:O)/2)^d:=dF rfl fun d _=>by rw[i6]
 rw[c,fO _N];have e:(0:O)<=((1:O)/2)^N:=_P;have b:(((1:O)/2)^N-1)/((1:O)/2-1)=2*(1-((1:O)/2)^N):=_R;rw[b];linarith
set_option maxHeartbeats 800000 in
lemma cR:∃C:O,0< C/\∀(k v γ : ℕ),1<=k->k<=10*v ->
 let b:ℤ:=(k:ℤ)-(v:ℤ)
 let Y:O:=if (γ : ℤ)+5<=b then (b:O) else (((γ : ℤ)+5-b:ℤ):O)^2*((γ : O)+1)
 let e:O:=if b<=(γ : ℤ) then 1 else (2:O)^(2^(Int.toNat (b-(γ : ℤ))))
 (volume (cM k v γ)).toReal<=C*Y/(e*((k+1).factorial:O)):=by
 obtain⟨Cm,Hl,HF⟩:=cO;let C1:O:=200*24*65536;let C2:O:=80000*exp 14*Cm*2*2*63;refine⟨C1+C2,by positivity,?_⟩
 intro k v γ hk1 hkv b Y e;have hA:(0:O)< (v:O):=_M (_O :0< v);have Hn:0< Y:=by
  dsimp only[Y];split_ifs with h
  ·have:(5:ℤ)<=b:=by omega
   have:(5:O)<=(b:O):=_M this
   linarith
  ·have J:(1:ℤ)<=(γ : ℤ)+5-b:=(by omega);have K:(1:O)<=(((γ : ℤ)+5-b:ℤ):O):=_M J;positivity
 have hW:0< e:=by dsimp only[e];split_ifs <;> positivity
 let r:ℕ:=max 5 (Int.toNat (b-(γ : ℤ)));have HL:5<=r:=eo _ _;let V1:Set (Fin k->O):={ξ∈cM k v γ |
   ∀j:Fin k,((j.1+1:ℕ):O)-(γ : O)-(r:O)< (v:O)*ξ j}
 let V2:Set (Fin k->O):={ξ∈cM k v γ |
   ∃j:Fin k,(v:O)*ξ j<=((j.1+1:ℕ):O)-(γ : O)-(r:O)}
 have Hd:cM k v γ⊆V1∪V2:=by
   intro ξ hξ;by_cases U:∀j:Fin k,((j.1+1:ℕ):O)-(γ : O)-(r:O)< (v:O)*ξ j
   · exact Or.inl ⟨hξ,U⟩
   · push Not at U;exact Or.inr ⟨hξ,U⟩
 have M:(volume (cM k v γ)).toReal <=(volume V1).toReal+(volume V2).toReal:=by have N:volume V1≠⊤:=fz (by rw[ct k 0 1 eO];exact ec) (f4 fun _ h=>h.1.1);have P:volume V2≠⊤:=fz (by rw[ct k 0 1 eO];exact ec) (f4 fun _ h=>h.1.1);have J:=(f4 Hd).trans (measure_union_le (μ:=volume) V1 V2);have K:=fM (ENNReal.add_ne_top.mpr ⟨N,P⟩) J;rwa[ENNReal.toReal_add N P]at K
 have hB:(volume V1).toReal<=C1*Y/(e*((k+1).factorial:O)):=by
   by_cases W:(γ : ℤ)+5<=b
   · have hb:V1=∅:=by
       ext ξ;simp only[V1,eM,iG,iC];rintro⟨hT,U⟩;have Hr:=U ⟨k-1,_O⟩;have HH : ξ ⟨k-1,_O⟩<=1:=(hT.1.1 ⟨k-1,_O⟩).2;have J:(v:O)*ξ ⟨k-1,_O⟩<=(v:O):=_Q;have q:r=Int.toNat (b-(γ : ℤ)):=jU _O;have HM:(r:O)=(k:O)-(v:O)-(γ : O):=(by have hZ:(r:ℤ)=(k:ℤ)-(v:ℤ)-(γ : ℤ):=(by rw[q,Int.toNat_of_nonneg _O]);exact_mod_cast hZ);have Hs:((k-1+1:ℕ):O)=(k:O):=_M (_O :k-1+1=k);linarith
     rw[hb];simp;positivity
   · have q:r=5:=lj _O
     have w:V1⊆cA k ((γ+5:ℕ):O) (v:O):=(by intro ξ ⟨hT,U⟩;refine⟨hT.1,fun j=>?_⟩;have hj:=U j;rw[q]at hj;push_cast at hj ⊢;linarith);have hw:0<=((γ+5:ℕ):O)+(v:O)-(k:O):=(by have hZ:(0:ℤ)<=((γ+5:ℕ):ℤ)+(v:ℤ)-(k:ℤ):=(by dsimp only[b]at W;omega);exact_mod_cast hZ);have hQ:=cG k ((γ+5:ℕ):O) (v:O) _P hw;have hC:(volume V1).toReal <=cD k ((γ+5:ℕ):O) (v:O)/(k.factorial:O):=(by unfold cD;have hX:volume (cA k ((γ+5:ℕ):O) (v:O))≠⊤:=fz ec ((f4 (fun _ h=>h.1)).trans_eq (ct k 0 1 eO));have hm:=fM hX (f4 w);rw[mul_div_cancel_left₀ _ _P];exact hm);have hY:((k+1).factorial:O)=((k:O)+1)*(k.factorial:O):=by rw[e6];push_cast;ring
     have Z:e<=65536:=by
       dsimp only[e];split_ifs with H8
       · norm_num
       · have h4:Int.toNat (b-(γ : ℤ))<=4:=by omega
         calc (2:O)^(2^Int.toNat (b-(γ : ℤ)))<=(2:O)^(2^4):=
               mg _N (dH _N h4)
           _=65536:=by norm_num
     have D:Y=(((γ : ℤ)+5-b:ℤ):O)^2*((γ : O)+1):=gc W
     have Q:(1:O)<=(((γ : ℤ)+5-b:ℤ):O):=by
       have:(1:ℤ)<=(γ : ℤ)+5-b:=_O
       exact_mod_cast this
     have h6:((γ+5:ℕ):O)+(v:O)-(k:O)=(((γ : ℤ)+5-b:ℤ):O):=(by have hZ:((γ+5:ℕ):ℤ)+(v:ℤ)-(k:ℤ)=(γ : ℤ)+5-b:=(by dsimp only[b];omega);exact_mod_cast hZ);have E:200*(((γ+5:ℕ):O)+1)*(((γ+5:ℕ):O)+(v:O)-(k:O)+1)^2 <=(C1/65536)*Y:=by rw[h6,D];push_cast;have J:(γ : O)+5+1<=6*((γ : O)+1):=_L;have K:((((γ : ℤ)+5-b:ℤ):O)+1)^2<=4*(((γ : ℤ)+5-b:ℤ):O)^2:=_Q;have hD:C1/65536=200*24:=(by dsimp only[C1];norm_num);rw[hD];have h3:((γ : O)+5+1)*((((γ : ℤ)+5-b:ℤ):O)+1)^2 <=(6*((γ : O)+1))*(4*(((γ : ℤ)+5-b:ℤ):O)^2):=en J K _P _P;have h4:(6*((γ : O)+1))*(4*(((γ : ℤ)+5-b:ℤ):O)^2) =24*((((γ : ℤ)+5-b:ℤ):O)^2*((γ : O)+1)):=_R;have h5:=dA (h3.trans_eq h4) (_N :(0:O)<=200);push_cast at h5;linarith
     calc (volume V1).toReal
         <= (200*(((γ+5:ℕ):O)+1)*(((γ+5:ℕ):O)+(v:O)-(k:O)+1)^2/((k:O)+1)) /(k.factorial:O):=hC.trans (dI hQ _P)
       _=200*(((γ+5:ℕ):O)+1)*(((γ+5:ℕ):O)+(v:O)-(k:O)+1)^2/((k+1).factorial:O):=by rw[div_div,hY]
       _<=(C1/65536)*Y/((k+1).factorial:O):=dI E _P
       _=C1*Y/(65536*((k+1).factorial:O)):=_R
       _<=C1*Y/(e*((k+1).factorial:O)):=dL _P _P (dE Z _P)
 let y:ℕ->ℕ->Set (Fin k->O):=fun h m=>
   if G:2^m+1<=k then
     {ξ∈cA k ((γ+h:ℕ):O) (v:O) |
       ∃l:Fin k,2^m<=l.1 /\((l.1+1:ℕ):O)-((γ+h:ℕ):O)<=(v:O)*ξ l /\(v:O)*ξ l<=((l.1+1:ℕ):O)-((γ+h:ℕ):O)+1 /\((l.1+1:ℕ):O)-((γ+h:ℕ):O)-((2*m:ℕ):O) <=(v:O)*ξ ⟨l.1-2^m,gJ (i4 _ _) l.2⟩}
   else ∅
 have hc:V2⊆⋃ h∈Icc (r+1) (k+1),⋃ m∈Icc (h-3) k,y h m:=by
   intro ξ ⟨hT,hA2⟩;have Ht:(univ:Finset (Fin k)).Nonempty:=⟨⟨0,_O⟩,dJ _⟩;let f:Fin k->O:=fun j=>(v:O)*ξ j-(((j.1+1:ℕ):O)-(γ : O));obtain⟨l,_,X⟩:=Finset.exists_min_image univ f Ht;have Ho:f l<=-(r:O):=(by rcases hA2 with⟨j0,HS⟩;exact (X j0 (dJ j0)).trans (by dsimp only[f];linarith));let h:ℕ:=⌊-f l⌋₊+1
   have he:r+1<=h:=by
     have:r<=⌊-f l⌋₊:=g2 _L
     omega
   have H0:h<=k+1:=by have h0:0<=(v:O)*ξ l:=ek hA.le (hT.1.1 l).1;have Hp : -(k:O)<=f l:=(by dsimp only[f];have HN:((l.1+1:ℕ):O)<=(k:O):=_M l.2;linarith);have H1 : ⌊-f l⌋₊<=k:=Nat.floor_le_of_le _L;omega
   have hf : -f l< (h:O):=by
     have:(h:O)=(⌊-f l⌋₊ : O)+1:=by dsimp only[h];push_cast;ring
     rw[this];exact f6 _
   have hU:(h:O)-1<=-f l:=(by have J:(⌊-f l⌋₊ : O)<=-f l:=fC _L;have K:(h:O)=(⌊-f l⌋₊ : O)+1:=(by dsimp only[h];push_cast;ring);linarith);have z:f l=(v:O)*ξ l-(((l.1+1:ℕ):O)-(γ : O)):=rfl
   have hξ_S : ξ∈cA k ((γ+h:ℕ):O) (v:O):=by
     refine⟨hT.1,fun j=>?_⟩
     have hj:=X j (dJ j);have Hu:f j=(v:O)*ξ j-(((j.1+1:ℕ):O)-(γ : O)):=rfl;have He' : -(f l)< (h:O):=hf;rw[z]at He';rw[z,Hu]at hj;push_cast at hj He' ⊢;linarith
   have H2:((l.1+1:ℕ):O)-((γ+h:ℕ):O)<=(v:O)*ξ l:=(by rw[z]at hf;push_cast at hf ⊢;linarith);have hg:(v:O)*ξ l<=((l.1+1:ℕ):O)-((γ+h:ℕ):O)+1:=by rw[z]at hU;push_cast at hU ⊢;linarith
   have H3:∃m∈Icc (h-3) k,∃hm_le:2^m<=l.1,((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O) <=(v:O)*ξ ⟨l.1-2^m,gJ (i4 _ _) l.2⟩:=by
     by_contra Hm;push Not at Hm;have HI:=hT.2 l;let u:=univ.filter (fun i:Fin k=>i.1<=l.1);let c:=u.filter (fun i:Fin k=>l.1< i.1+2^(h-3))
     let o:ℕ->Finset (Fin k):=fun m=>
       u.filter (fun i:Fin k=>i.1+2^m<=l.1/\l.1< i.1+2^(m+1))
     have hE:u⊆c∪(Icc (h-3) k).biUnion o:=by
       intro i hi;by_cases hV:l.1< i.1+2^(h-3)
       · exact e0 _ (dB.mpr ⟨hi,hV⟩)
       · push Not at hV
         apply eu
         rw[g4];have HO:1<=l.1-i.1:=(by have:1<=2^(h-3):=fY;omega);let m:=Nat.log 2 (l.1-i.1);have Hv:2^m<=l.1-i.1:=gB 2 _O;have Hw:l.1-i.1< 2^(m+1):=jJ _N _;have H4:h-3<=m:=(by by_contra HG;push Not at HG;have:2^(m+1)<=2^(h-3):=dH _N _O;omega);have hk:m<=k:=(by have J:m< 2^m:=gC;have K:l.1< k:=l.2;omega);exact⟨m,dT.mpr ⟨H4,hk⟩,dB.mpr ⟨hi,by omega,_O⟩⟩
     have R:c.card<=2^(h-3):=by
       have w:c.image (fun i:Fin k=>l.1-i.1)⊆range (2^(h-3)):=by intro d hd;rcases dW.mp hd with⟨i,hi,rfl⟩;simp only[c,u,dB,dN]at hi ⊢;omega
       have A:Set.InjOn (fun i:Fin k=>l.1-i.1) (c:Set (Fin k)):=by
         intro i1 hx i2 hy hp;dsimp only at hp;simp only[eB,c,u,dB]at hx hy;have:i1.1<=l.1:=hx.1.2;have:i2.1<=l.1:=hy.1.2;exact dQ _O
       calc c.card=(c.image (fun i:Fin k=>l.1-i.1)).card:=
             (gA A).symm
         _<=(range (2^(h-3))).card:=er w
         _=2^(h-3):=fy _
     have Hc:∑i∈c,(2:O)^((v:O)*ξ i) <=(1/4:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by
       have B:∀i∈c,(2:O)^((v:O)*ξ i) <=(2:O)^(((l.1+1:ℕ):O)-(γ : O)-(h:O)+1):=by
         intro i hi;have T:i<=l:=(dB.mp (dB.mp hi).1).2;have H5 : ξ i<=ξ l:=hT.1.2 T;refine eT _N ?_
         push_cast at hg;nlinarith
       calc ∑i∈c,(2:O)^((v:O)*ξ i)
           <= (c.card:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)-(h:O)+1):=by
             calc _<=∑_i∈c,(2:O)^(((l.1+1:ℕ):O)-(γ : O)-(h:O)+1):=
                   dG B
               _=_:=by rw[ex,e3]
         _<=((2^(h-3):ℕ):O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)-(h:O)+1):=dE (_M R) _P
         _=(1/4:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by have Hf:((2^(h-3):ℕ):O)=(2:O)^((h:O)-3):=(by have h3:((h-3:ℕ):O)=(h:O)-3:=(by rw[ei _O];norm_num);rw[gx,g7,<- eK,h3]);rw[Hf,<- gF (_N :(0:O)< 2)];have hl:(h:O)-3+(((l.1+1:ℕ):O)-(γ : O)-(h:O)+1) =(-2:O)+(((l.1+1:ℕ):O)-(γ : O)):=_R;rw[hl,gF (_N :(0:O)< 2)];have Hg:(2:O)^(-2:O)=1/4:=(by rw[show (-2:O)=-(2:ℕ) by norm_num,lD _N,eK];norm_num);rw[Hg]
     have hF:∀m∈Icc (h-3) k,∑i∈o m,(2:O)^((v:O)*ξ i) <=(1/(2:O)^m)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by
       intro m hm;by_cases Ha:2^m<=l.1
       · have hn:(o m).card<=2^m:=by
           have w:(o m).image (fun i:Fin k=>l.1-i.1-2^m)⊆range (2^m):=by intro d hd;rcases dW.mp hd with⟨i,hi,rfl⟩;simp only[o,u,dB,dN]at hi ⊢;have:2^(m+1)=2^m+2^m:=_R;omega
           have A:Set.InjOn (fun i:Fin k=>l.1-i.1-2^m) (o m:Set (Fin k)):=by
             intro i1 hx i2 hy hp;dsimp only at hp;simp only[eB,o,u,dB]at hx hy;have:i1.1+2^m<=l.1:=hx.2.1;have:i2.1+2^m<=l.1:=hy.2.1;exact dQ _O
           calc (o m).card=((o m).image (fun i:Fin k=>l.1-i.1-2^m)).card:=
                 (gA A).symm
             _<=(range (2^m)).card:=er w
             _=2^m:=fy _
         have Hx:=Hm m hm Ha
         have B:∀i∈o m,(2:O)^((v:O)*ξ i) <=(2:O)^(((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O)):=by
           intro i hi;have T:i<=⟨l.1-2^m,_O⟩:=(by have:=(dB.mp hi).2.1;exact mh.mpr _O);have H5 : ξ i<=ξ ⟨l.1-2^m,_O⟩:=hT.1.2 T;refine eT _N ?_
           nlinarith
         calc ∑i∈o m,(2:O)^((v:O)*ξ i)
             <= ((o m).card:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O)):=by
               calc _<=∑_i∈o m,(2:O)^(((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O)):=
                     dG B
                 _=_:=by rw[ex,e3]
           _<=((2^m:ℕ):O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O)):=dE (_M hn) _P
           _=(1/(2:O)^m)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by rw[gx,g7,<- eK,<- gF (_N :(0:O)< 2)];have hl:(m:O)+(((l.1+1:ℕ):O)-(γ : O)-((2*m:ℕ):O)) =-(m:O)+(((l.1+1:ℕ):O)-(γ : O)):=(by push_cast;ring);rw[hl,gF (_N :(0:O)< 2),lD _N,eK,g9]
       · have hb:o m=∅:=by
           ext i;simp only[o,u,dB,fq,iC];omega
         rw[hb,gG];positivity
     have Hq:∑i∈(Icc (h-3) k).biUnion o,(2:O)^((v:O)*ξ i) <=∑m∈Icc (h-3) k,∑i∈o m,(2:O)^((v:O)*ξ i):=by
       have Hh:∀(S:Finset ℕ),∑i∈S.biUnion o,(2:O)^((v:O)*ξ i) <=∑m∈S,∑i∈o m,(2:O)^((v:O)*ξ i):=by
         intro S;induction S using eW with
         | empty=>simp
         | @insert a S ha ih=>
           rw[iS,i3 ha];have hu:=fb (s₁:=o a) (s₂:=S.biUnion o) (f:=fun i:Fin k=>(2:O)^((v:O)*ξ i));have Hy:0<=∑i∈o a∩S.biUnion o,(2:O)^((v:O)*ξ i):=ea fun _ _=>_P;linarith
       exact Hh _
     have H6:∑m∈Icc (h-3) k,(1:O)/(2:O)^m<=1/4:=by
       have w:Icc (h-3) k⊆(range (k+1)).image (fun d=>(h-3)+d):=(by intro m hm;rw[dT]at hm;rw[dW];exact⟨m-(h-3),dN.mpr _O,_O⟩);have A:Function.Injective (fun d=>(h-3)+d):=kr (h-3)
       calc ∑m∈Icc (h-3) k,(1:O)/(2:O)^m
           <= ∑m∈(range (k+1)).image (fun d=>(h-3)+d),(1:O)/(2:O)^m:=dC w fun _ _ _=>_P
         _=∑d∈range (k+1),(1:O)/(2:O)^((h-3)+d):=fr (fun a _ b _ hz=>A hz)
         _=(1/(2:O)^(h-3))*∑d∈range (k+1),(1:O)/(2:O)^d:=by rw[dP];refine dF rfl fun d _=>by rw[ee];ring
         _<=(1/8:O)*2:=by
             have h8:(8:O)<=(2:O)^(h-3):=by
               have h3:3<=h-3:=_O
               calc (8:O)=(2:O)^(3:ℕ):=by norm_num
                 _<=(2:O)^(h-3):=mg _N h3
             have Hi:1/(2:O)^(h-3)<=1/8:=dX _N h8;exact en Hi (cQ (k+1)) (ea fun _ _=>by positivity) _N
         _=1/4:=by ring
     have HJ:∑i∈u,(2:O)^((v:O)*ξ i) <=(1/2:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by
       have hu:=fb (s₁:=c) (s₂:=(Icc (h-3) k).biUnion o) (f:=fun i:Fin k=>(2:O)^((v:O)*ξ i));have Hy:0<=∑i∈c∩(Icc (h-3) k).biUnion o,(2:O)^((v:O)*ξ i):=ea fun _ _=>_P
       have J:∑i∈u,(2:O)^((v:O)*ξ i) <=∑i∈c,(2:O)^((v:O)*ξ i) +∑i∈(Icc (h-3) k).biUnion o,(2:O)^((v:O)*ξ i):=by
         have hs:=dC hE (f:=fun i:Fin k=>(2:O)^((v:O)*ξ i)) (fun _ _ _=>by positivity)
         linarith
       have K:∑m∈Icc (h-3) k,∑i∈o m,(2:O)^((v:O)*ξ i) <=(1/4:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=by
         calc _<=∑m∈Icc (h-3) k,
               (1/(2:O)^m)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=dG hF
           _=(∑m∈Icc (h-3) k,(1:O)/(2:O)^m) *(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=(jn ..).symm
           _<=(1/4:O)*(2:O)^(((l.1+1:ℕ):O)-(γ : O)):=dE H6 _P
       linarith
     have HK:(0:O)< (2:O)^(((l.1+1:ℕ):O)-(γ : O)):=_P;linarith
   obtain⟨m,hS,Ha,Hb⟩:=H3;have G:2^m+1<=k:=(by have:=l.2;omega);simp only[eQ];refine⟨h,dT.mpr ⟨he,H0⟩,m,hS,?_⟩;simp only[y,G,↓reduceDIte,l7];refine⟨hξ_S,l,Ha,H2,hg,?_⟩;push_cast at Hb ⊢;linarith
 have ho:(volume V2).toReal <=∑h∈Icc (r+1) (k+1),∑m∈Icc (h-3) k,(volume (y h m)).toReal:=by
   have H:∀h m,volume (y h m)≠⊤:=by
     intro h m;dsimp only[y];split_ifs
     · exact fz (by rw[ct k 0 1 eO];exact ec) (f4 fun _ hξ=>hξ.1.1)
     · simp
   have J:volume V2 <=∑h∈Icc (r+1) (k+1),∑m∈Icc (h-3) k,volume (y h m):=(f4 hc).trans
       ((g1 _ _).trans
         (dG fun h _=>g1 _ _))
   have h7:(∑h∈Icc (r+1) (k+1),∑m∈Icc (h-3) k,volume (y h m))≠⊤:=mu.mpr fun h _=>mu.mpr fun m _=>H h m;have K:=fM h7 J;rw[kK (fun h _=>mu.mpr fun m _=>H h m)]at K;refine K.trans_eq (dF rfl fun h _=>?_);exact kK (fun m _=>H h m)
 have h9:∀h∈Icc (r+1) (k+1),∀m∈Icc (h-3) k,(volume (y h m)).toReal <=(80000*exp 14*Cm)*(((γ+h:ℕ):O)+1) *((((γ+h)+v-k:ℕ):O)+1)^2/(((k+1).factorial:O)*(2:O)^(2^(m+3))):=by
   intro h hh m _;rw[dT]at hh;dsimp only[y];split_ifs with G
   · have Hz:k+1<=(γ+h)+v:=by
       have H7:b-(γ : ℤ)<=(r:ℤ):=by
         have:Int.toNat (b-(γ : ℤ))<=r:=ep _ _
         omega
       dsimp only[b]at H7;omega
     have Hj:=cL (2^m) k (2*m) (γ+h) v fY G hkv Hz;have HP:=HF m;have HA:10*(((2*m:ℕ):O)+1)=10*((2*m:ℕ):O)+10:=_R;rw[HA]at Hj
     calc (volume _).toReal
         <= 80000*exp 14*(((2^m:ℕ):O)+3)^2 *(10*((2*m:ℕ):O)+10)^(2^m)/((2^m).factorial:O) *((((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/((k+1).factorial:O)):=Hj
       _=80000*exp 14 *((((2^m:ℕ):O)+3)^2*(10*((2*m:ℕ):O)+10)^(2^m)/((2^m).factorial:O)) *((((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/((k+1).factorial:O)):=_R
       _<=80000*exp 14*(Cm/(2:O)^(2^(m+3))) *((((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/((k+1).factorial:O)):=by gcongr
       _=_:=by ring
   · simp;positivity
 have hI:∀h∈Icc (r+1) (k+1),∑m∈Icc (h-3) k,(1:O)/(2:O)^(2^(m+3))<=2/(2:O)^(2^h):=by
   intro h hh;rw[dT]at hh;have w:Icc (h-3) k⊆(range (k+1)).image (fun d=>(h-3)+d):=(by intro m hm;rw[dT]at hm;rw[dW];exact⟨m-(h-3),dN.mpr _O,_O⟩);have A:Function.Injective (fun d=>(h-3)+d):=kr (h-3)
   calc ∑m∈Icc (h-3) k,(1:O)/(2:O)^(2^(m+3))
       <= ∑m∈(range (k+1)).image (fun d=>(h-3)+d),(1:O)/(2:O)^(2^(m+3)):=dC w fun _ _ _=>_P
     _=∑d∈range (k+1),(1:O)/(2:O)^(2^((h-3)+d+3)):=fr (fun a _ b _ hz=>A hz)
     _<=∑d∈range (k+1),(1:O)/(2:O)^(2^h+d):=by
         refine dG fun d _=>dX _P (mg _N ?_)
         have hp:(h-3)+d+3=h+d:=_O;rw[hp,ee];have J:1+d<=2^d:=(by have:=gC (n:=d);omega);have K:1<=2^h:=fY;nlinarith
     _=(1/(2:O)^(2^h))*∑d∈range (k+1),(1:O)/(2:O)^d:=by rw[dP];refine dF rfl fun d _=>by rw[ee];ring
     _<=(1/(2:O)^(2^h))*2:=dA (cQ _) _P
     _=2/(2:O)^(2^h):=_R
 have hL:(volume V2).toReal<=C2*Y/(e*((k+1).factorial:O)):=by
   have hM:(volume V2).toReal <=(80000*exp 14*Cm*2/((k+1).factorial:O)) *∑h∈Icc (r+1) (k+1),(((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/(2:O)^(2^h):=by
     refine ho.trans ?_
     rw[dP];refine dG fun h hh=>?_
     calc ∑m∈Icc (h-3) k,(volume (y h m)).toReal
         <= ∑m∈Icc (h-3) k,(80000*exp 14*Cm)*(((γ+h:ℕ):O)+1) *((((γ+h)+v-k:ℕ):O)+1)^2/(((k+1).factorial:O)*(2:O)^(2^(m+3))):=dG fun m hm=>h9 h hh m hm
       _=((80000*exp 14*Cm)*(((γ+h:ℕ):O)+1) *((((γ+h)+v-k:ℕ):O)+1)^2/((k+1).factorial:O)) *∑m∈Icc (h-3) k,(1:O)/(2:O)^(2^(m+3)):=by rw[dP];refine dF rfl fun m _=>_R
       _<=((80000*exp 14*Cm)*(((γ+h:ℕ):O)+1) *((((γ+h)+v-k:ℕ):O)+1)^2/((k+1).factorial:O)) *(2/(2:O)^(2^h)):=dA (hI h hh) _P
       _=_:=by ring
   have hN:∑h∈Icc (r+1) (k+1),(((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/(2:O)^(2^h) <=2*(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2/(2:O)^(2^(r+1)):=by
     have w:Icc (r+1) (k+1)⊆(range (k+1)).image (fun d=>(r+1)+d):=(by intro h hh;rw[dT]at hh;rw[dW];exact⟨h-(r+1),dN.mpr _O,_O⟩);have A:Function.Injective (fun d=>(r+1)+d):=kr (r+1)
     calc _<=∑h∈(range (k+1)).image (fun d=>(r+1)+d),
             (((γ+h:ℕ):O)+1)*((((γ+h)+v-k:ℕ):O)+1)^2/(2:O)^(2^h):=
           dC w fun _ _ _=>_P
       _=∑d∈range (k+1),(((γ+(r+1+d):ℕ):O)+1)*((((γ+(r+1+d))+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1+d)):=fr (fun a _ b _ hz=>A hz)
       _<=∑d∈range (k+1),((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1)))*((1:O)/(2:O)^d):=by
           refine dG fun d _=>?_
           have J:(((γ+(r+1+d):ℕ):O)+1)<=(((γ+r+1:ℕ):O)+1)*((d:O)+1):=(by push_cast;nlinarith);have K:((((γ+(r+1+d))+v-k:ℕ):O)+1) <=((((γ+r+1)+v-k:ℕ):O)+1)*((d:O)+1):=by have H7:b-(γ : ℤ)<=(r:ℤ):=(by have:Int.toNat (b-(γ : ℤ))<=r:=ep _ _;omega);have H8 : γ+(r+1+d)+v-k=(γ+r+1+v-k)+d:=(by dsimp only[b]at H7;omega);rw[H8];push_cast;nlinarith
           have h3:(2:O)^(2^(r+1)+4*d)<=(2:O)^(2^(r+1+d)):=by
             refine mg _N ?_
             have HB:64<=2^(r+1):=by
               calc 64=2^6:=by norm_num
                 _<=2^(r+1):=dH _N _O
             have HC:1+d<=2^d:=by have:=gC (n:=d);omega
             have hq:2^(r+1)+2^(r+1)*d<=2^(r+1)*2^d:=by
               have:2^(r+1)+2^(r+1)*d=2^(r+1)*(1+d):=_R
               rw[this];exact dR _ HC
             have hP:64*d<=2^(r+1)*d:=eE d HB
             calc 2^(r+1)+4*d<=2^(r+1)+64*d:=by omega
               _<=2^(r+1)+2^(r+1)*d:=Nat.add_le_add_left hP _
               _<=2^(r+1)*2^d:=hq
               _=2^(r+1+d):=(ee 2 (r+1) d).symm
           have HD:((d:O)+1)^3<=(2:O)^(3*d):=by
             have hr:(d+1)^3<=2^(3*d):=by
               have HE:d+1<=2^d:=Nat.succ_le_of_lt gC
               calc (d+1)^3<=(2^d)^3:=fA HE 3
                 _=2^(3*d):=by rw[<- it,e8]
             exact_mod_cast hr
           have E:(((γ+(r+1+d):ℕ):O)+1) *((((γ+(r+1+d))+v-k:ℕ):O)+1)^2 <=(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 *((d:O)+1)^3:=by
             have ht:((((γ+(r+1+d))+v-k:ℕ):O)+1)^2 <=(((((γ+r+1)+v-k:ℕ):O)+1)*((d:O)+1))^2:=m9 _P K 2
             calc _<=((((γ+r+1:ℕ):O)+1)*((d:O)+1)) *
                   (((((γ+r+1)+v-k:ℕ):O)+1)*((d:O)+1))^2:=
                 en J ht _P _P
               _=_:=by ring
           calc _<=((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 *
                   ((d:O)+1)^3)/(2:O)^(2^(r+1)+4*d):=
                 mj _P E _P h3
             _<=((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 *(2:O)^(3*d))/(2:O)^(2^(r+1)+4*d):=by gcongr
             _=((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1)))*((1:O)/(2:O)^d):=by have h4:(2:O)^(2^(r+1)+4*d) =(2:O)^(2^(r+1))*(2:O)^(3*d)*(2:O)^d:=(by rw[f0,<- ee,<- ee];congr 1;ring);rw[h4];field_simp
       _=((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1)))*∑d∈range (k+1),(1:O)/(2:O)^d:=(dP ..).symm
       _<=_:=by
           have Hk:=dA (cQ (k+1))
             (show (0:O)<=(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1)) by positivity)
           exact Hk.trans_eq (by ring)
   have H9:(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1))<=63*Y/e:=by
     by_cases W:(γ : ℤ)+5<=b
     · have q:r=Int.toNat (b-(γ : ℤ)):=jU _O
       have D:Y=(b:O):=iM W;have hv:e=(2:O)^(2^r):=(by dsimp only[e];rw[gc _O,q]);have J:(((γ+r+1:ℕ):O)+1)<=2*(b:O):=(by have hZ:((γ+r+1:ℕ):ℤ)+1=b+2:=(by rw[q];dsimp only[b];omega);have hR:(((γ+r+1:ℕ):O)+1)=(b:O)+2:=_M hZ;have HQ:(5:O)<=(b:O):=_M (_O :(5:ℤ)<=b);linarith);have K:(((γ+r+1)+v-k:ℕ):O)+1=2:=(by have hr:(γ+r+1)+v-k=1:=(by rw[q];dsimp only[b]at W ⊢;omega);rw[hr];norm_num);have F:(2:O)^(2^r)<=(2:O)^(2^(r+1)):=mg _N (dH _N _O);rw[D,hv,K];have E:(((γ+r+1:ℕ):O)+1)*(2:O)^2<=63*(b:O):=_L;have HR:(0:O)<=(b:O):=_M (_O :(0:ℤ)<=b);exact mj _P E _P F
     · have q:r=5:=lj _O
       have D:Y=(((γ : ℤ)+5-b:ℤ):O)^2*((γ : O)+1):=gc W;have Q:(1:O)<=(((γ : ℤ)+5-b:ℤ):O):=(by exact_mod_cast (_O :(1:ℤ)<=(γ : ℤ)+5-b));have J:(((γ+r+1:ℕ):O)+1)<=7*((γ : O)+1):=by rw[q];push_cast;linarith
       have K:((((γ+r+1)+v-k:ℕ):O)+1)<=3*(((γ : ℤ)+5-b:ℤ):O):=by
         have hZ:(((γ+r+1)+v-k:ℕ):ℤ)+1=(γ : ℤ)+7-b:=by rw[q];dsimp only[b]at W ⊢;omega
         have hR:((((γ+r+1)+v-k:ℕ):O)+1)=(((γ : ℤ)+5-b:ℤ):O)+2:=by
           have:(γ : ℤ)+7-b=((γ : ℤ)+5-b)+2:=_O
           rw[this]at hZ;exact_mod_cast hZ
         linarith
       have F:e<=(2:O)^(2^(r+1)):=by
         rw[q];dsimp only[e];split_ifs with H8
         · exact mo _N
         · exact mg _N (dH _N _O)
       rw[D]
       have E:(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 <=63*((((γ : ℤ)+5-b:ℤ):O)^2*((γ : O)+1)):=by
         have ht:=m9 _P K 2
         calc _<=(7*((γ : O)+1))*(3*(((γ : ℤ)+5-b:ℤ):O))^2:=
               en J ht _P _P
           _=_:=by ring
       exact mj _P E _P F
   calc (volume V2).toReal
       <= (80000*exp 14*Cm*2/((k+1).factorial:O)) *(2*(((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1))):=hM.trans (dA hN _P)
     _=(80000*exp 14*Cm*2*2/((k+1).factorial:O)) *((((γ+r+1:ℕ):O)+1)*((((γ+r+1)+v-k:ℕ):O)+1)^2 /(2:O)^(2^(r+1))):=by ring
     _<=(80000*exp 14*Cm*2*2/((k+1).factorial:O))*(63*Y/e):=dA H9 _P
     _=C2*Y/(e*((k+1).factorial:O)):=by dsimp only[C2];ring
 calc (volume (cM k v γ)).toReal
     <= (volume V1).toReal+(volume V2).toReal:=M
   _<=C1*Y/(e*((k+1).factorial:O))+C2*Y/(e*((k+1).factorial:O)):=fd hB hL
   _=(C1+C2)*Y/(e*((k+1).factorial:O)):=_R
def cS (k v:ℕ) (ξ : Fin k->O):O:=(range (k+1)).inf' ⟨0,dN.mpr (gO k)⟩ fun j=>
  (2:O)^(-(j:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))
def cT (k v:ℕ):O:=∫ ξ in cr k 0 1,cS k v ξ
set_option maxHeartbeats 800000 in
lemma cU:∃C:O,0< C/\∀(k v:ℕ),1<=k->k<=10*v -> cT k v<=C*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2) /(((k+1).factorial:O)*((2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1)):=by
 obtain⟨CU,hN,H5⟩:=cR;refine⟨2*CU*(72*512*33+32*512*2),by positivity,?_⟩
 intro k v H6 H7;let b:ℤ:=(k:ℤ)-(v:ℤ);have hR:∀ ξ∈cr k 0 1,cS k v ξ <=∑m∈range (k+1),(cM k v (m+1)).indicator (fun _=>(2:O)^(1-(m:O))) ξ:=by
  intro ξ hξ;have Z:cS k v ξ<=1:=by have h0:=inf'_le (s:=range (k+1)) (f:=fun j=>(2:O)^(-(j:O)) *(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))) (dN.mpr (gO k));simp only[jc,neg_zero,rpow_zero,gz,lv,filter_false,gG,i0]at h0;exact h0
  have E:(2:O)^(-(k:O))<=cS k v ξ:=by
   unfold cS;refine ie _ _ fun j hj=>?_
   rw[dN]at hj;have hT:(j:O)<=(k:O):=_M (_O :j<=k);have o:(2:O)^(-(k:O))<=(2:O)^(-(j:O)):=eT _N _L;have w:(1:O)<=1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i):=by have hA:0<=∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i):=ea fun _ _=>_P;linarith
   nlinarith[k5 (_N :(0:O)< 2) (-(j:O))]
  have l:0< cS k v ξ:=e9 _P E;let m:ℕ:=⌊-log (cS k v ξ)/log 2⌋₊;have e:0< log 2:=_l a3;have hk:log (cS k v ξ)<=0:=Real.log_nonpos l.le Z;have hz : -(k:O)*log 2<=log (cS k v ξ):=(by have o:=dM _P E;rwa[kR (_N :(0:O)< 2)]at o);have hU:m<=k:=(by have o:(m:O)<=-log (cS k v ξ)/log 2:=fC (ed _L e.le);have w : -log (cS k v ξ)/log 2<=(k:O):=(by rw[mc e];linarith);exact_mod_cast o.trans w);have F:cS k v ξ< (2:O)^(1-(m:O)):=(by have o:(m:O)<=-log (cS k v ξ)/log 2:=fC (ed _L e.le);have w:log (cS k v ξ)<=-(m:O)*log 2:=(by have:=(ma e).mp o;linarith);have h3:log (cS k v ξ)< (1-(m:O))*log 2:=_L;have h4:=mF.mpr h3;rw[eX l,e8,<- fQ (_N :(0:O)< 2)]at h4;exact h4);have hB:(2:O)^(-(m:O)-1)<=cS k v ξ:=(by have o : -log (cS k v ξ)/log 2< (m:O)+1:=f6 _;have w:(-(m:O)-1)*log 2< log (cS k v ξ):=(by have:=(mm e).mp o;linarith);have h3:=mF.mpr w;rw[eX l,e8,<- fQ (_N :(0:O)< 2)]at h3;exact h3.le);have hξ_T : ξ∈cM k v (⌈-log (cS k v ξ)/log 2⌉₊+1):=by
   let m':ℕ:=⌈-log (cS k v ξ)/log 2⌉₊;have hl':(2:O)^(-(m':O))<=cS k v ξ:=(by have o : -log (cS k v ξ)/log 2<=(m':O):=g6 _;have w : -(m':O)*log 2<=log (cS k v ξ):=(by have:=(mc e).mp o;linarith);have h3:=me.mpr w;rwa[eX l,e8,<- fQ (_N :(0:O)< 2)]at h3);refine⟨hξ,fun j=>?_⟩;have hj:=(inf'_le (s:=range (k+1)) (f:=fun r=>(2:O)^(-(r:O)) *(1+∑i∈univ.filter (fun i:Fin k=>i.1< r),(2:O)^((v:O)*ξ i)))
    (dN.mpr (_O :j.1+1< k+1)))
   have ho:univ.filter (fun i:Fin k=>i.1< j.1+1) =univ.filter (fun i:Fin k=>i.1<=j.1):=(by ext i;simp[mx]);rw[ho]at hj;have hp:(⟨0,_O⟩:Fin k)∈univ.filter (fun i:Fin k=>i.1<=j.1):=dB.mpr ⟨dJ _,g5 _⟩;have H8:(1:O)<=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i):=by
    calc (1:O)=(2:O)^(0:O):=by norm_num
      _<=(2:O)^((v:O)*ξ ⟨0,_O⟩):=eT _N (ek (dK v) (hξ.1 _).1)
      _<=_:=fi (f:=fun i:Fin k=>(2:O)^((v:O)*ξ i)) (fun _ _=>by positivity) hp
   have hV:(2:O)^(-(m':O)) <=(2:O)^(-((j.1+1:ℕ):O))*(2*∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i)):=hl'.trans (hj.trans (dA _L _P));have hh:=dA hV (_P :(0:O)<=(2:O)^(((j.1+1:ℕ):O)-1));have H9:(2:O)^(((j.1+1:ℕ):O)-1)*(2:O)^(-(m':O)) =(2:O)^(((j.1+1:ℕ):O)-((m'+1:ℕ):O)):=(by rw[<- gF (_N :(0:O)< 2)];congr 1;push_cast;ring);have Ha:(2:O)^(((j.1+1:ℕ):O)-1)*((2:O)^(-((j.1+1:ℕ):O)) *(2*∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i))) =∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i):=by
    have hW:(2:O)^(((j.1+1:ℕ):O)-1)*(2:O)^(-((j.1+1:ℕ):O))*2=1:=(by rw[<- gF (_N :(0:O)< 2),show ((j.1+1:ℕ):O)-1+-((j.1+1:ℕ):O)=-(1:O) by ring,rpow_neg_one];norm_num);set G:=∑i∈univ.filter (fun i:Fin k=>i.1<=j.1),(2:O)^((v:O)*ξ i)
    calc (2:O)^(((j.1+1:ℕ):O)-1)*((2:O)^(-((j.1+1:ℕ):O))*(2*G))
        = ((2:O)^(((j.1+1:ℕ):O)-1)*(2:O)^(-((j.1+1:ℕ):O))*2)*G:=_R
      _=G:=by rw[hW,gz]
   linarith
  let m':ℕ:=⌈-log (cS k v ξ)/log 2⌉₊;have h5:m'<=k:=my.mpr (by rw[mc e];linarith);have F':cS k v ξ<=(2:O)^(1-(m':O)):=by
   have o:(m':O)< -log (cS k v ξ)/log 2+1:=jm (ed _L e.le);have w:log (cS k v ξ)<=(1-(m':O))*log 2:=by
    have:=(lt_div_iff₀ e).mp (_L :(m':O)-1< -log (cS k v ξ)/log 2)
    linarith
   have h3:=me.mpr w;rwa[eX l,e8,<- fQ (_N :(0:O)< 2)]at h3
  calc cS k v ξ
      <= (2:O)^(1-(m':O)):=F'
    _=(cM k v (m'+1)).indicator (fun _=>(2:O)^(1-(m':O))) ξ:=by rw[Set.indicator_of_mem hξ_T]
    _<=∑r∈range (k+1),(cM k v (r+1)).indicator (fun _=>(2:O)^(1-(r:O))) ξ:=fi (f:=fun r=>(cM k v (r+1)).indicator (fun _=>(2:O)^(1-(r:O))) ξ) (fun r _=>Set.indicator_nonneg (fun _ _=>by positivity) _) (dN.mpr (Nat.lt_succ_of_le h5))
 have q:volume (cr k 0 1)< ⊤:=by rw[ct k 0 1 eO];exact ENNReal.ofReal_lt_top
 have h6:IntegrableOn (cS k v) (cr k 0 1):=by
  have hq:Continuous (cS k v):=by
   unfold cS;have hC:∀(S:Finset ℕ) (hS:S.Nonempty),Continuous (fun ξ : Fin k->O=>S.inf' hS fun j=>
     (2:O)^(-(j:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))):=by
    intro S hS;induction S using eW with
    | empty=>exact (Finset.not_nonempty_empty hS).elim
    | @insert a S ha ih=>
     by_cases hP:S=∅
     ·subst hP;have hr:(fun ξ : Fin k->O=>(insert a (∅ : Finset ℕ)).inf' hS fun j=>
       (2:O)^(-(j:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))) =
       fun ξ=>(2:O)^(-(a:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< a),(2:O)^((v:O)*ξ i)):=by
       ext ξ;exact Finset.inf'_singleton ..
      rw[hr];refine continuous_const.mul (continuous_const.add (continuous_finset_sum _ fun i _=>?_));exact continuous_const.rpow (continuous_const.mul (l6 i)) (fun _=>Or.inl _N)
     ·have H:S.Nonempty:=mf.mpr hP;have J:(fun ξ : Fin k->O=>(insert a S).inf' hS fun j=>
       (2:O)^(-(j:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))) =
       fun ξ=>min ((2:O)^(-(a:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< a),(2:O)^((v:O)*ξ i))) (S.inf' H fun j=>(2:O)^(-(j:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))):=by
       ext ξ;exact Finset.inf'_insert H _
      rw[J];refine Continuous.min ?_ (ih H);refine continuous_const.mul (continuous_const.add (continuous_finset_sum _ fun i _=>?_));exact continuous_const.rpow (continuous_const.mul (l6 i)) (fun _=>Or.inl _N)
   exact hC _ _
  haveI:IsFiniteMeasure (volume.restrict (cr k 0 1)):=⟨by simpa using q⟩
  refine Integrable.mono' (integrable_const (1:O)) hq.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (cs k 0 1)] with ξ hξ
  rw[Real.norm_eq_abs,jE]
  ·have h0:=inf'_le (s:=range (k+1)) (f:=fun j=>(2:O)^(-(j:O)) *(1+∑i∈univ.filter (fun i:Fin k=>i.1< j),(2:O)^((v:O)*ξ i))) (dN.mpr (gO k));simp only[jc,neg_zero,rpow_zero,gz,lv,filter_false,gG,i0]at h0;exact h0
  ·unfold cS;exact ie _ _ fun j _=>_P
 have u:∀m∈range (k+1),IntegrableOn ((cM k v (m+1)).indicator (fun _=>(2:O)^(1-(m:O)))) (cr k 0 1):=by
  intro m _;haveI:IsFiniteMeasure (volume.restrict (cr k 0 1)):=⟨by simpa using q⟩
  exact (integrable_const ((2:O)^(1-(m:O)))).indicator (cN k v (m+1))
 have h7:cT k v<=∑m∈range (k+1),(2:O)^(1-(m:O))*(volume (cM k v (m+1))).toReal:=by
  unfold cT;have o:=setIntegral_mono_on h6 (iB _ u) (cs k 0 1) hR;refine o.trans_eq ?_
  rw[iZ _ u];refine dF rfl fun m _=>?_
  rw[MeasureTheory.setIntegral_indicator (cN k v (m+1)),Set.inter_eq_right.mpr (fun _ h=>h.1),iT,lf,Measure.real,e8]
 have K:cT k v<=(2*CU/((k+1).factorial:O)) *∑m∈range (k+1),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
     else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
    (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))):=by
  refine h7.trans ?_
  rw[dP];refine dG fun m _=>?_
  have hX:(2:O)^(1-(m:O))=2*(1/(2:O)^m):=(by rw[sub_eq_add_neg,gF (_N :(0:O)< 2),rpow_one,lD _N,eK,g9]);rw[hX];have M:=H5 k v (m+1) H6 H7;dsimp only at M;have hh:=dA M (_P :(0:O)<=2*(1/(2:O)^m));exact hh.trans_eq (by ring)
 have N:∑m∈range (k+1),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
    else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
   (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
  (72*512*33+32*512*2)*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2) /((2:O)^((b:O))+1):=by
  have h8:((((v:ℤ)-(k:ℤ):ℤ):O))^2=(b:O)^2:=by
   have:((((v:ℤ)-(k:ℤ):ℤ):O))=-(b:O):=by dsimp only[b];push_cast;ring
   rw[this,neg_sq]
  rw[h8];by_cases hy:b<=5
  ·have hQ:(2:O)^(b:O)+1<=33:=by
    have o:(2:O)^(b:O)<=(2:O)^(5:O):=eT _N (_M hy);have He:(2:O)^(5:O)=32:=(by rw[show (5:O)=(5:ℕ) by norm_num,eK];norm_num);linarith
   have A:∀m∈range (k+1),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
      else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
     (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
    2*((6:O)-(b:O))^2*(((m:O)+1)^3/(2:O)^m):=by
    intro m _;rw[gc (_O :¬ ((m+1:ℕ):ℤ)+5<=b)];have P:(1:O)<=if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ))):=(by split_ifs;exact eR;exact mo _N);have Q:((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1) <=2*((6:O)-(b:O))^2*((m:O)+1)^3:=by
     have Hb:(b:O)<=5:=_M hy;have Hf:(1:O)<=6-(b:O):=_L;have o:((((m+1:ℕ):ℤ)+5-b:ℤ):O)<=(6-(b:O))*((m:O)+1):=(by push_cast;nlinarith);have w:(((m+1:ℕ):O)+1)<=2*((m:O)+1):=(by push_cast;linarith);have hE:0<=((((m+1:ℕ):ℤ)+5-b:ℤ):O):=(by push_cast;linarith);have hF:=m9 hE o 2
     calc _<=((6-(b:O))*((m:O)+1))^2*(2*((m:O)+1)):=
           en hF w _P _P
       _=_:=by ring
    calc _<=(1/(2:O)^m)*((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)/1:=by
          rw[f0];exact dL _P i5 P
      _=(1/(2:O)^m)*(((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)):=_R
      _<=(1/(2:O)^m)*(2*((6:O)-(b:O))^2*((m:O)+1)^3):=dA Q _P
      _=_:=by ring
   have h9:((6:O)-(b:O))^2<=72*(1+(b:O)^2):=by nlinarith[gR ((6:O)+(b:O))]
   calc _<=∑m∈range (k+1),2*((6:O)-(b:O))^2*(((m:O)+1)^3/(2:O)^m):=
         dG A
     _=2*((6:O)-(b:O))^2*∑m∈range (k+1),((m:O)+1)^3/(2:O)^m:=(dP ..).symm
     _<=2*(72*(1+(b:O)^2))*256:=en (dA h9 _N) (cP _) (ea fun _ _=>by positivity) _P
     _=72*512*(1+(b:O)^2):=_R
     _<=(72*512*33+32*512*2)*(1+(b:O)^2)/((2:O)^(b:O)+1):=by rw[ma _P];have hA:0<=1+(b:O)^2:=_P;nlinarith
  ·
   push Not at hy
   let c:ℕ:=Int.toNat b;have hc:(c:ℤ)=b:=Int.toNat_of_nonneg _O;have Hc:6<=c:=_O;have B:(b:O)=(c:O):=_M hc.symm;have he:(2:O)^(b:O)=(2:O)^c:=(by rw[B,eK]);rw[<- eh (range (k+1)) (fun m=>((m+1:ℕ):ℤ)+5<=b)];have hY:∑m∈(range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
      else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
     (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
    2*(b:O)/(2:O)^c:=by
    have Hd:(range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b) ⊆ (range c).image (fun d=>c-6 - d):=(by intro m X;simp only[dB,dN]at X;rw[dW];exact⟨c-6 - m,dN.mpr _O,_O⟩);have hf:∀m∈(range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
       else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
      (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
     ((b:O)/(2:O)^c)*(1/(2:O)^(c-6 - m)):=by
     intro m X;have hs:=(dB.mp X).2;rw[iM hs,gc (_O :¬ b<=((m+1:ℕ):ℤ))];have hI:c+(c-6 - m)<=m+2^Int.toNat (b-((m+1:ℕ):ℤ)):=by
      let d:=Int.toNat (b-((m+1:ℕ):ℤ));have H0:d=c-m - 1:=_O;have H1:5<=d:=_O;have R:∀D:ℕ,5<=D->2*D<=2^D:=by
       intro D hD;induction D,hD using fe with
       | base=>norm_num
       | succ n hn ih=>
        calc 2*(n+1)<=2*(2*n):=by omega
          _<=2*2^n:=dR 2 ih
          _=2^(n+1):=by ring
      have Hg:2*d<=2^d:=R d H1;change c+(c-6 - m)<=m+2^d;omega
     have T:(2:O)^(c+(c-6 - m)) <=(2:O)^m*(2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ))):=by rw[<- ee];exact mg _N hI
     calc (1/(2:O)^m)*(b:O)/(2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))
         = (b:O)/((2:O)^m*(2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))):=_R
       _<=(b:O)/(2:O)^(c+(c-6 - m)):=dL (by rw[B];positivity) _P T
       _=((b:O)/(2:O)^c)*(1/(2:O)^(c-6 - m)):=by rw[ee];ring
    calc _<=∑m∈(range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b),
            ((b:O)/(2:O)^c)*(1/(2:O)^(c-6 - m)):=dG hf
      _=((b:O)/(2:O)^c) *∑m∈(range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b),(1:O)/(2:O)^(c-6 - m):=(dP ..).symm
      _<=((b:O)/(2:O)^c)*2:=by
          refine dA ?_ (by rw[B];positivity)
          have U:Set.InjOn (fun m=>c-6 - m) (((range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b):Finset ℕ):Set ℕ):=(by intro m1 hw m2 hx J;dsimp only at J;simp only[eB,dB]at hw hx;omega);have y:((range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b)).image (fun m=>c-6 - m)⊆range c:=by intro d hd;rcases dW.mp hd with⟨m,X,rfl⟩;rw[dN];omega
          calc _=∑d∈((range (k+1)).filter (fun m=>((m+1:ℕ):ℤ)+5<=b)).image
                  (fun m=>c-6 - m),(1:O)/(2:O)^d:=
                (fr (f:=fun d=>(1:O)/(2:O)^d) (fun a ha b hb h=>U ha hb h)).symm
            _<=∑d∈range c,(1:O)/(2:O)^d:=dC y fun _ _ _=>_P
            _<=2:=cQ c
      _=2*(b:O)/(2:O)^c:=_R
   have H2:∑m∈(range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
      else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
     (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
    32*256*(b:O)/(2:O)^c:=by
    have hg:∀m∈(range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b),(1/(2:O)^m) *(if ((m+1:ℕ):ℤ)+5<=b then (b:O)
       else ((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)) /
      (if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ)))) <=
     (32*(b:O)/(2:O)^c)*(((m-(c-5):ℕ):O)+1)^3/(2:O)^(m-(c-5)):=by
     intro m X;have hs:=(dB.mp X).2;rw[gc hs];have H3:c-5<=m:=_O;have P:(1:O)<=if b<=((m+1:ℕ):ℤ) then 1 else (2:O)^(2^Int.toNat (b-((m+1:ℕ):ℤ))):=(by split_ifs;exact eR;exact mo _N);let d:ℕ:=m-(c-5);have H4:m=(c-5)+d:=_O;have o:((((m+1:ℕ):ℤ)+5-b:ℤ):O)=(d:O)+1:=by have hZ:((m+1:ℕ):ℤ)+5-b=(d:ℤ)+1:=_O;exact_mod_cast hZ
     have w:(((m+1:ℕ):O)+1)<=(b:O)*((d:O)+1):=(by have hL:m+2<=c*(d+1):=(by have o:m+2=c-3+d:=_O;have w:c+d<=c*(d+1):=_Q;omega);rw[B];push_cast;exact_mod_cast hL);have T:(2:O)^m*32=(2:O)^c*(2:O)^d:=by
      have:m+5=c+d:=_O
      calc (2:O)^m*32=(2:O)^m*(2:O)^(5:ℕ):=by norm_num
        _=(2:O)^(m+5):=(ee _ _ _).symm
        _=(2:O)^(c+d):=by rw[this]
        _=(2:O)^c*(2:O)^d:=ee _ _ _
     calc _<=(1/(2:O)^m)*((((m+1:ℕ):ℤ)+5-b:ℤ):O)^2*(((m+1:ℕ):O)+1)/1:=by
           rw[f0];exact dL _P i5 P
       _=(1/(2:O)^m)*(((d:O)+1)^2*(((m+1:ℕ):O)+1)):=by rw[o];ring
       _<=(1/(2:O)^m)*(((d:O)+1)^2*((b:O)*((d:O)+1))):=dA (dA w _P) _P
       _=(32*(b:O)/(2:O)^c)*((d:O)+1)^3/(2:O)^d:=by have hM:(2:O)^m≠0:=_P;have ht:(2:O)^c≠0:=_P;have hu:(2:O)^d≠0:=_P;field_simp [hM,ht,hu];exact T.symm
    calc _<=∑m∈(range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b),
            (32*(b:O)/(2:O)^c)*((((m-(c-5):ℕ):O)+1)^3/(2:O)^(m-(c-5))):=by
          refine dG fun m X=>?_
          exact (hg m X).trans_eq (by ring)
      _=(32*(b:O)/(2:O)^c) *∑m∈(range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b),(((m-(c-5):ℕ):O)+1)^3/(2:O)^(m-(c-5)):=(dP ..).symm
      _<=(32*(b:O)/(2:O)^c)*256:=by
          refine dA ?_ (by rw[B];positivity)
          have U:Set.InjOn (fun m=>m-(c-5)) (((range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b):Finset ℕ):Set ℕ):=(by intro m1 hw m2 hx J;dsimp only at J;simp only[eB,dB]at hw hx;omega);have y:((range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b)).image (fun m=>m-(c-5))⊆range (k+1):=by intro d hd;rcases dW.mp hd with⟨m,X,rfl⟩;simp only[dB,dN]at X ⊢;omega
          calc _=∑d∈((range (k+1)).filter (fun m=>¬ ((m+1:ℕ):ℤ)+5<=b)).image
                  (fun m=>m-(c-5)),((d:O)+1)^3/(2:O)^d:=
                (fr (f:=fun (d:ℕ)=>((d:O)+1)^3/(2:O)^d)
                  (g:=fun m=>m-(c-5)) (fun a ha b hb h=>U ha hb h)).symm
            _<=∑d∈range (k+1),((d:O)+1)^3/(2:O)^d:=dC y fun _ _ _=>_P
            _<=256:=cP (k+1)
      _=32*256*(b:O)/(2:O)^c:=_R
   rw[he];have W:(2:O)^c+1<=2*(2:O)^c:=(by have:(1:O)<=(2:O)^c:=mo _N;linarith);have hv:(b:O)<=1+(b:O)^2:=by nlinarith[gR ((b:O)-1)]
   calc _<=2*(b:O)/(2:O)^c+32*256*(b:O)/(2:O)^c:=fd hY H2
     _<=32*512*(b:O)/(2:O)^c:=by have hA:(0:O)<=(b:O)/(2:O)^c:=(by rw[B];positivity);have o:2*(b:O)/(2:O)^c+32*256*(b:O)/(2:O)^c=8194*((b:O)/(2:O)^c):=_R;have w:32*512*(b:O)/(2:O)^c=16384*((b:O)/(2:O)^c):=_R;linarith
     _<=32*512*2*(1+(b:O)^2)/((2:O)^c+1):=by rw[mb _P _P];have o:(b:O)*((2:O)^c+1)<=(1+(b:O)^2)*(2*(2:O)^c):=en hv W _P _P;nlinarith
     _<=(72*512*33+32*512*2)*(1+(b:O)^2)/((2:O)^c+1):=by
         refine dI ?_ _P
         have:0<=1+(b:O)^2:=_P
         nlinarith
 have z:(2*CU/((k+1).factorial:O)) *((72*512*33+32*512*2)*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2)/((2:O)^(b:O)+1)) =2*CU*(72*512*33+32*512*2)*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2) /(((k+1).factorial:O)*((2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1)):=by dsimp only[b];rw[div_mul_div_comm];ring
 exact K.trans ((dA N _P).trans_eq z)
def cV (t:ℕ):Finset ℕ:=(dv t).powerset.image fun S=>∏p∈S,p
def cW (a:ℕ):ℕ:=
 if h:a.primeFactors.Nonempty then a.primeFactors.max' h else 0
lemma cX {a:ℕ} (h:2<=a) :
 (cW a).Prime/\cW a∣a:=by
 have c:a.primeFactors.Nonempty:=by obtain⟨p,e,d⟩:=jK (_O :a≠1);exact⟨p,md.mpr ⟨e,d,_O⟩⟩
 have b:cW a∈a.primeFactors:=by unfold cW;rw[eG c];exact kg _ c
 exact⟨dD b,dS b⟩
lemma cY {a p:ℕ} (b:p∈a.primeFactors):p<=cW a:=by unfold cW;rw[eG ⟨p,b⟩];exact gK _ _ b
lemma cZ (S:Finset ℕ) (b:∀p∈S,p.Prime) :
 (∏p∈S,p).primeFactors=S:=by
 classical
 induction S using eW with
 | empty=>simp
 | @insert p S hpS ih=>
  rw[fN hpS];have e:p.Prime:=b p (ev p S);have b':∀q∈S,q.Prime:=fun q d=>b q (fa d);have c:∏q∈S,q≠0:=mi.mpr fun q d=>(b' q d).ne_zero;rw[jh e.ne_zero c,e.primeFactors,ih b'];ext q;simp
lemma d3 (S:Finset ℕ) (b:∀p∈S,p.Prime) :
 Squarefree (∏p∈S,p):=by
 classical
 induction S using eW with
 | empty=>simp
 | @insert p S hpS ih=>
  rw[fN hpS];have e:p.Prime:=b p (ev p S);have b':∀q∈S,q.Prime:=fun q d=>b q (fa d);have c:Nat.Coprime p (∏q∈S,q):=fL fun q d=>
    (ft e (b' q d)).mpr (fun h=>hpS (h ▸ d))
  exact (Nat.squarefree_mul c).mpr ⟨e.squarefree,ih b'⟩
lemma d4 {a:ℕ} (l:1<=a) (d:Squarefree a) :
 ∏p∈a.primeFactors,p=a:=by
 conv_rhs=>rw[<- ew (_O :a≠0),Finsupp.prod]
 rw[ej];refine f9 rfl fun p j=>?_
 have b:=dD j;have e:1<=a.factorization p:=(b.dvd_iff_one_le_factorization _O).mp (dS j);have h:a.factorization p<=1:=by
  by_contra i;push Not at i;have c:p*p∣a:=(show p*p∣p^a.factorization p by rw[<- sq];exact jj p i).trans (gd a p)
  exact b.ne_one (mn.mp (d p c))
 rw[show a.factorization p=1 by omega,pow_one]
lemma d5 (t a:ℕ) :
 a∈cV t↔1<=a/\Squarefree a/\∀p∈a.primeFactors,p<=t:=by
 constructor
 ·intro e;rcases dW.mp e with⟨S,d,rfl⟩;rw[eS]at d;have c:∀p∈S,p.Prime:=fun p b=>(e7.mp (d b)).2;refine⟨fX (mi.mpr fun p b=>(c p b).ne_zero),d3 S c,?_⟩;rw[cZ S c];exact fun p b=>(e7.mp (d b)).1
 ·rintro⟨e,hsq,hle⟩;refine dW.mpr ⟨a.primeFactors,eS.mpr fun p b=>
   e7.mpr ⟨hle p b,dD b⟩,
   d4 e hsq⟩
lemma d6 {t1 t2:ℕ} (h:t1<=t2):cV t1⊆cV t2:=by intro a b;rw[d5]at b ⊢;exact⟨b.1,b.2.1,fun p c=>(b.2.2 p c).trans h⟩
lemma d7 (t:ℕ):1∈cV t:=by rw[d5];exact⟨eR,lG,by simp⟩
def d8 (t:ℕ):O:=∑a∈cV t,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2)
lemma d9 (t:ℕ):0<=d8 t:=ea fun a _=>ed (bK a) _P
lemma da (X z:ℕ) (l:2<=z) (i:z<=X) :
 (aK X z:O)<=128*(X:O)/log (z:O):=by
 have c:0< log (z:O):=et (_M (_O :1< z));by_cases e:2*z<=X
 ·exact (b7 X z l e).trans (dI
   (_l (dK (α:=O) X)) c.le)
 ·have d:aK X z<=aK (2*z) z:=by
   unfold aK;refine er fun b h=>?_
   simp only[dB,dT]at h ⊢;exact⟨⟨h.1.1,_O⟩,h.2⟩
  have m:(aK X z:O)<=(aK (2*z) z:O):=_M d;have e':=b7 (2*z) z l eR;have j:(z:O)<=(X:O):=_M i
  calc (aK X z:O)<=(aK (2*z) z:O):=m
    _<=64*((2*z:ℕ):O)/log (z:O):=e'
    _=128*(z:O)/log (z:O):=by push_cast;ring
    _<=128*(X:O)/log (z:O):=dI _L c.le
set_option maxHeartbeats 800000 in
lemma db (x1 y1:ℕ) (Hv:24<=y1) (HI:96*y1<=x1) :
 let A:=(Ioc (x1/2) x1).filter fun n=>
  Squarefree n/\∃d∈n.divisors,y1< d/\d<=2*y1
 (A.card:O)<=(50000/log 2)*(x1:O)*(d8 (2*y1)+d8 (x1/y1)):=by
 classical
 intro A;have hM:0< log 2:=_l a3;have W:∀(m:O) (c:ℕ),(24:O)<=m->2*m<=(c:O) -> (c:O)<=4*m ->
  let B:=A.filter fun n=>∃o w:ℕ,n=o*w/\m< (o:O)/\(o:O)<=(c:O) /\2<=o/\2<=w/\cW o< cW w;(B.card:O)<=(25000/log 2)*(x1:O)*d8 c:=by
  intro m c HA _hYZ_lo hL B;have hz:0< m:=_L;let e (a:ℕ):O:=max (cW a:O) (m/(a:O));have z:∀a∈cV c,4<=e a:=by
   intro a S;by_cases hD:4<=cW a
   ·exact gf (_M hD) (eo _ _)
   ·push Not at hD
    have hA:a<=6:=by
     have hj:a.primeFactors⊆{2,3}:=(by intro q K;have T:=dD K;have Hn:=(cY K).trans_lt hD;have hN:=T.two_le;simp only[ga,eg];omega);have h1:=d4 ((d5 _ _).mp S).1 ((d5 _ _).mp S).2.1
     calc a=∏q∈a.primeFactors,q:=h1.symm
       _<=∏q∈({2,3}:Finset ℕ),q:=Finset.prod_le_prod_of_subset_of_one_le' hj fun q K _=>by
           simp only[ga,eg]at K;omega
       _=6:=by norm_num
    have l:(0:O)< (a:O):=_M ((d5 _ _).mp S).1;have Hw:(a:O)<=6:=_M hA;exact gf (by rw[ma l];linarith) (ep _ _)
  let C (a:ℕ):Finset ℕ:=(Icc ⌈e a⌉₊ ⌊2*m⌋₊).filter fun p=>p.Prime/\log (m/(p:O))∈LL a;let D (a:ℕ):Finset ℕ:=(Icc ⌈e a⌉₊ ⌊2*(2*m)⌋₊).filter fun p=>p.Prime/\log ((2*m)/(p:O))∈LL a;let i (a:ℕ):Finset ℕ:=C a∪D a;let j' (a p:ℕ):Finset ℕ:=((Icc 1 (x1/(a*p))).filter fun b=>∀q ≤ p,q.Prime->¬ q∣b).filter (p< ·);let T':=(cV c).biUnion fun a=>(i a).biUnion fun p=>(j' a p).image fun b=>a*p*b;have hB':B⊆T':=by
   intro n hn;simp only[B,A,dB,fw]at hn;rcases hn with⟨⟨⟨_,hy⟩,hsqn,_⟩,o,w,N,hm1_lo,hm1_hi,H,P,hp_lt⟩;have hC:1<=n:=(by have:=fP (_O :0< o) (_O :0< w);omega);set p:=cW o;have v:p.Prime:=(cX H).1;have u:p∣o:=(cX H).2;have h9:p∣n:=u.trans ⟨w,N⟩;have hl:p<=c:=by have H1:p<=o:=el _O u;have H2:o<=c:=_M hm1_hi;exact H1.trans H2
   let a:=∏q∈n.primeFactors.filter (·< p),q;let b:=∏q∈n.primeFactors.filter (p< ·),q;have h7:a∈cV c:=(by rw[d5];have hP:∀q∈n.primeFactors.filter (·< p),q.Prime:=fun q K=>dD (dB.mp K).1;refine⟨fX (mi.mpr fun q K=>(hP q K).ne_zero),d3 _ hP,?_⟩;rw[cZ _ hP];intro q K;exact ((dB.mp K).2.le).trans hl);have hQ:a.primeFactors=n.primeFactors.filter (·< p):=cZ _ fun q K=>dD (dB.mp K).1;have hR:b.primeFactors=n.primeFactors.filter (p< ·):=cZ _ fun q K=>dD (dB.mp K).1;have H3:n=a*p*b:=by
    have hS:=d4 hC hsqn;have Hj:p∈n.primeFactors:=md.mpr ⟨v,h9,_O⟩;have hT:n.primeFactors=(n.primeFactors.filter (·< p))∪({p}∪n.primeFactors.filter (p< ·)):=by
     ext q;simp only[ff,dB,eg];constructor
     ·intro K;rcases jC q p with h1 | h2 | h3
      ·exact Or.inl ⟨K,h1⟩
      ·exact Or.inr (Or.inl h2)
      ·exact Or.inr (Or.inr ⟨K,h3⟩)
     ·rintro (⟨K,_⟩ | rfl | ⟨K,_⟩) <;> assumption
    have H4:Disjoint (n.primeFactors.filter (·< p)) ({p}∪n.primeFactors.filter (p< ·)):=(by rw[eb];intro q h1 h2;simp only[dB,ff,eg]at h1 h2;omega);have Ho:Disjoint ({p}:Finset ℕ) (n.primeFactors.filter (p< ·)):=(by rw[eb];intro q h1 h2;simp only[eg,dB]at h1 h2;omega);rw[<- hS,hT,kD H4,kD Ho,prod_singleton,f0]
   have l:1<=a:=((d5 _ _).mp h7).1;have h8:1<=b:=fX (mi.mpr fun q K=>
    (dD (dB.mp K).1).ne_zero)
   have ho:p< b:=by
    have hN:=cX P;have hr:cW w∈n.primeFactors.filter (p< ·):=dB.mpr ⟨md.mpr ⟨hN.1,hN.2.trans ⟨o,by rw[N,e8]⟩,_O⟩,hp_lt⟩
    exact e9 hp_lt (el h8 (ji _ hr))
   let d:=o/p;have E:o=d*p:=(jw u).symm;have U:1<=d:=ia (el _O u) v.pos;have Q:d∣a:=by
    have H5:Squarefree d:=hsqn.squarefree_of_dvd ⟨p*w,by rw[N,E];ring⟩
    have hs:d.primeFactors⊆n.primeFactors.filter (·< p):=by
     intro q K;have T:=dD K;have R:=dS K;have M:q∣o:=R.trans ⟨p,E⟩;have hb:q∣n:=M.trans ⟨w,N⟩;have H6:q<=p:=cY (md.mpr ⟨T,M,_O⟩);have H7:q≠p:=by intro h4;subst h4;have hU:p*p∣o:=(by obtain⟨k,hk⟩:=R;exact⟨k,by rw[E,hk];ring⟩);exact v.ne_one (mn.mp (hsqn p (hU.trans ⟨w,N⟩)))
     exact dB.mpr ⟨md.mpr ⟨T,hb,_O⟩,_O⟩
    rw[<- d4 U H5];exact iF _ _ id hs
   have J:d∈a.divisors:=fW.mpr ⟨Q,_O⟩;have ht:d<=a:=el l Q;have F:e a<=(p:O):=by
    refine kC ?_ ?_
    ·unfold cW;split_ifs with h
     ·have hm:a.primeFactors.max' h∈n.primeFactors.filter (·< p):=hQ ▸ kg _ h;exact_mod_cast (dB.mp hm).2.le
     ·simp
    ·rw[mc (_M l)];have h1:(o:O)=(d:O)*(p:O):=_M E;have h2:(d:O)<=(a:O):=_M ht;nlinarith[show (0:O)< (p:O) by exact_mod_cast v.pos]
   have X : ⌈e a⌉₊<=p:=my.mpr F;have hv:p∈i a:=by
    have G:(0:O)< (p:O):=_M v.pos;have Z:(0:O)< (d:O):=_M U;have H8:(o:O)=(d:O)*(p:O):=_M E;have H4:(1:O)<=(d:O):=_M U;by_cases hZ:(o:O)<=2*m
    ·apply e0
     refine dB.mpr ⟨dT.mpr ⟨X,g2 (by nlinarith)⟩,v,?_⟩
     simp only[LL,eQ,fF];refine⟨d,J,?_,?_⟩
     ·rw[<- gW Z.ne' _N];exact dM _P (by rw[mb _N G];linarith)
     ·exact jS _P ((mm G).mpr _L)
    ·push Not at hZ
     apply eu
     refine dB.mpr ⟨dT.mpr ⟨X,g2 (by nlinarith)⟩,v,?_⟩
     simp only[LL,eQ,fF];refine⟨d,J,?_,?_⟩
     ·rw[<- gW Z.ne' _N];exact dM _P (by rw[mb _N G];linarith)
     ·exact jS _P ((mm G).mpr _L)
   have hw':b∈j' a p:=by
    refine dB.mpr ⟨dB.mpr ⟨dT.mpr ⟨h8,?_⟩,?_⟩,ho⟩
    ·rw[dZ (fP l v.pos),e8];omega
    ·intro q HH Hh Hu;have Hp:q∈b.primeFactors:=md.mpr ⟨Hh,Hu,_O⟩;rw[hR,dB]at Hp;omega
   exact g4.mpr ⟨a,h7,g4.mpr ⟨p,hv,dW.mpr ⟨b,hw',H3.symm⟩⟩⟩
  have hc:(B.card:O)<=∑a∈cV c,∑p∈i a,((j' a p).card:O):=by
   have h0:B.card<=∑a∈cV c,∑p∈i a,(j' a p).card:=by
    calc B.card<=T'.card:=er hB'
      _<=∑a∈cV c,((i a).biUnion fun p=>(j' a p).image fun b=>a*p*b).card:=gq
      _<=∑a∈cV c,∑p∈i a,((j' a p).image fun b=>a*p*b).card:=dG fun a _=>gq
      _<=∑a∈cV c,∑p∈i a,(j' a p).card:=dG fun a _=>dG fun p _=>ja
   exact_mod_cast h0
  have hx:∀a∈cV c,∀p∈i a,((j' a p).card:O)<=128*(x1:O)/((a:O)*(p:O)*log (e a)):=by
   intro a S p hp;have h5:=z a S;have y:0< log (e a):=et _L;have l:1<=a:=((d5 _ _).mp S).1;have F:e a<=(p:O):=by
    have hV : ⌈e a⌉₊<=p:=by
     rcases ff.mp hp with h1 | h2
     ·exact (dT.mp (dB.mp h1).1).1
     ·exact (dT.mp (dB.mp h2).1).1
    exact my.mp hV
   have hD:4<=p:=_M (h5.trans F);by_cases Hi:(j' a p).Nonempty
   ·rcases Hi with⟨b0,Hg⟩;have Hk:b0<=x1/(a*p):=(dT.mp (dB.mp (dB.mp Hg).1).1).2;have H0:p< b0:=(dB.mp Hg).2;have hj:(j' a p).card<=aK (x1/(a*p)) p:=er (fj _ _);have Hq:=da (x1/(a*p)) p _O _O;have hW:((x1/(a*p):ℕ):O)<=(x1:O)/((a:O)*(p:O)):=by
     rw[ma _P];exact_mod_cast eD x1 (a*p)
    have he:log (e a)<=log (p:O):=dM _L F
    calc ((j' a p).card:O)<=(aK (x1/(a*p)) p:O):=by exact_mod_cast hj
      _<=128*((x1/(a*p):ℕ):O)/log (p:O):=Hq
      _<=128*((x1:O)/((a:O)*(p:O)))/log (e a):=mj _P (dA hW _N) y he
      _=128*(x1:O)/((a:O)*(p:O)*log (e a)):=_R
   ·rw[mI.mp Hi,card_empty,jc];positivity
  have hE:∀a∈cV c,∑p∈i a,(1:O)/(p:O)<=(48/log 2)*L a/log (e a):=by
   intro a S;have h5:=z a S;have h1:=c5 (Y:=m) (V:=e a) (a:=a) hz h5;have h2:=c5 (Y:=2*m) (V:=e a) (a:=a) _P h5;have hu:∑p∈i a,(1:O)/(p:O) <=∑p∈C a,(1:O)/(p:O)+∑p∈D a,(1:O)/(p:O):=by have h:=fb (s₁:=C a) (s₂:=D a) (f:=fun p=>(1:O)/(p:O));have Hr:0<=∑p∈C a∩D a,(1:O)/(p:O):=ea fun _ _=>_P;linarith
   dsimp only[C,D]at hu;have HB:(24/log 2)*L a/log (e a)+(24/log 2)*L a/log (e a) =(48/log 2)*L a/log (e a):=(by ring);linarith
  have hf:∀a∈cV c,log (max 4 (max (cW a:O) ((c:O)/(a:O))))<=2*log (e a):=by
   intro a S;have h5:=z a S;have l:(0:O)< (a:O):=_M ((d5 _ _).mp S).1;have hX:max (4:O) (max (cW a:O) ((c:O)/(a:O)))<=4*e a:=by
    refine kC _L (kC ?_ ?_)
    ·linarith[eo (cW a:O) (m/(a:O))]
    · calc (c:O)/(a:O)<=(4*m)/(a:O):=dI hL l.le
        _=4*(m/(a:O)):=_R
        _<=4*e a:=dA (ep _ _) _N
   calc log (max 4 (max (cW a:O) ((c:O)/(a:O))))
       <= log (4*e a):=dM _P hX
     _=log 4+log (e a):=log_mul _N _L
     _<=log (e a)+log (e a):=by linarith[dM _N h5]
     _=2*log (e a):=by ring
  calc (B.card:O)<=∑a∈cV c,∑p∈i a,((j' a p).card:O):=hc
    _<=∑a∈cV c,∑p∈i a,128*(x1:O)/((a:O)*(p:O)*log (e a)):=dG fun a S=>dG fun p hp=>hx a S p hp
    _=∑a∈cV c,(128*(x1:O)/((a:O)*log (e a)))*∑p∈i a,(1:O)/(p:O):=by
        refine dF rfl fun a _=>?_
        rw[dP];refine dF rfl fun p _=>_R
    _<=∑a∈cV c,(128*(x1:O)/((a:O)*log (e a)))*((48/log 2)*L a/log (e a)):=by
        refine dG fun a S=>?_
        have y:0< log (e a):=et (_l (z a S));exact dA (hE a S) _P
    _<=∑a∈cV c,(25000/log 2)*(x1:O) *(L a/((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2)):=by
        refine dG fun a S=>?_
        have h5:=z a S;have y:0< log (e a):=et _L;have h6:0< log (max 4 (max (cW a:O) ((c:O)/(a:O)))):=et (e9 _N (eo _ _));have hF:(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2<=4*(log (e a))^2:=(by have:=m9 h6.le (hf a S) 2;linarith);have l:(0:O)< (a:O):=_M ((d5 _ _).mp S).1;have Hx:0<=L a:=bK a
        calc 128*(x1:O)/((a:O)*log (e a))*((48/log 2)*L a/log (e a))
            = (24576/log 2)*(x1:O)*L a/((a:O)*(4*(log (e a))^2)):=_R
          _<=(24576/log 2)*(x1:O)*L a /((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2):=dL _P _P (dA hF l.le)
          _<=(25000/log 2)*(x1:O) *(L a/((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2)):=by have Hr:0<=(x1:O)*L a/(log 2*((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2)):=_P;have h1:(24576/log 2)*(x1:O)*L a/((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2) =24576*((x1:O)*L a/(log 2*((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2))):=_R;have h2:(25000/log 2)*(x1:O)*(L a/((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2)) =25000*((x1:O)*L a/(log 2*((a:O)*(log (max 4 (max (cW a:O) ((c:O)/(a:O)))))^2))):=_R;linarith
    _=(25000/log 2)*(x1:O)*d8 c:=by unfold d8;rw[<- dP]
 let B1:=A.filter fun n=>∃o w:ℕ,n=o*w/\(y1:O)< (o:O)/\(o:O)<=((2*y1:ℕ):O) /\2<=o/\2<=w/\cW o< cW w;let B2:=A.filter fun n=>∃o w:ℕ,n=o*w/\((x1:O)/(4*(y1:O)))< (o:O) /\(o:O)<=((x1/y1:ℕ):O)/\2<=o/\2<=w/\cW o< cW w;have H9:A⊆B1∪B2:=by
  intro n hn;have Ha:=hn;simp only[A,dB,fw]at hn;rcases hn with⟨⟨Ht,hy⟩,hsqn,d,hd,hd_lo,hd_hi⟩;have hI:d∣n:=ef hd;let o:=d;let w:=n/d;have N:n=o*w:=(eC hI).symm;have H:2<=o:=_O;have hg:(x1:O)/(4*(y1:O))< (w:O):=by have h1:x1< 2*n:=(by have:=gu x1 2;have:=dY x1 (_N :0< 2);omega);have HC:(x1:O)< 2*((o:O)*(w:O)):=(by exact_mod_cast (by rw[<- N];exact h1));have HD:(o:O)<=2*(y1:O):=_M hd_hi;rw[mm _P];nlinarith[dK (α:=O) w]
  have hh:(w:O)<=((x1/y1:ℕ):O):=by
   have h0:w<=x1/y1:=by
    rw[dZ _O]
    calc w*y1<=w*o:=dR w _O
      _=n:=by rw[N,e8]
      _<=x1:=hy
   exact_mod_cast h0
  have P:2<=w:=(by have HE:(24:O)<=(x1:O)/(4*(y1:O)):=(by rw[ma _P];exact_mod_cast (_O :24*(4*y1)<=x1));have:(2:O)< (w:O):=_L;exact_mod_cast this.le);have hY:cW o≠cW w:=(by intro h4;have Hb:=cX H;have Hc:=cX P;rw[<- h4]at Hc;have hU:cW o*cW o∣n:=(by rw[N];exact mul_dvd_mul Hb.2 Hc.2);exact Hb.1.ne_one (mn.mp (hsqn (cW o) hU)));rcases gI hY with hlt | hgt
  ·exact e0 _ (dB.mpr ⟨Ha,o,w,N,by exact_mod_cast hd_lo,by exact_mod_cast hd_hi,H,P,hlt⟩)
  ·exact eu _ (dB.mpr ⟨Ha,w,o,by rw[N,e8],hg,hh,P,H,hgt⟩)
 have Hd:=W (y1:O) (2*y1) (_M Hv) (by push_cast;linarith) (by push_cast;linarith);have HF:(B2.card:O)<=(25000/log 2)*(x1:O)*d8 (x1/y1):=by
  refine W ((x1:O)/(4*(y1:O))) (x1/y1) ?_ ?_ ?_
  ·rw[ma _P];exact_mod_cast (_O :24*(4*y1)<=x1)
  ·have h1:x1< (x1/y1+1)*y1:=by
    have:=gu x1 y1;have:=dY x1 (_O :0< y1);nlinarith
   have h2:96<=x1/y1:=(by rw[dZ _O];omega);have h3:x1<=2*(x1/y1)*y1:=_Q;have HG:(x1:O)<=2*((x1/y1:ℕ):O)*(y1:O):=_M h3;have h4:2*((x1:O)/(4*(y1:O)))=(x1:O)/(2*(y1:O)):=_R;rw[h4,mc _P];linarith
  ·have Hs:(x1/y1)*y1<=x1:=eD x1 y1;have He:((x1/y1:ℕ):O)*(y1:O)<=(x1:O):=_M Hs;have h4:4*((x1:O)/(4*(y1:O)))=(x1:O)/(y1:O):=(by field_simp [(_P :(y1:O)≠0)]);rw[h4,ma _P];exact He
 have Hf:(A.card:O)<=(B1.card:O)+(B2.card:O):=by have h0:A.card<=B1.card+B2.card:=(er H9).trans (jD B1 B2);exact_mod_cast h0
 have Hd':(B1.card:O)<=(25000/log 2)*(x1:O)*d8 (2*y1):=Hd;have Hl:=d9 (2*y1);have Hm:=d9 (x1/y1);have h4:(50000/log 2)*(x1:O)*(d8 (2*y1)+d8 (x1/y1)) =2*((25000/log 2)*(x1:O)*d8 (2*y1)) +2*((25000/log 2)*(x1:O)*d8 (x1/y1)):=_R;have Hy:0<=(25000/log 2)*(x1:O)*d8 (2*y1):=_P;have Hz:0<=(25000/log 2)*(x1:O)*d8 (x1/y1):=_P;linarith
set_option maxHeartbeats 800000 in
lemma dc (x2 y1 z_lo z_hi:ℕ) (M:O) (hM:0<=M)
 (h4:24<=y1) (G:z_lo<=2*y1) (B:2*y1<=z_hi)
 (C:x2<=z_hi)
 (P:max (96*y1) (z_lo*y1)*(4*(⌈(log (y1:O))^2⌉₊+1))<=x2)
 (hS:∀t∈Icc z_lo z_hi,d8 t<=M) :
 let H:=(Icc 1 x2).filter fun n=>Squarefree n/\∃d∈n.divisors,y1< d/\d<=2*y1
 (H.card:O)<=(x2:O)/(log (y1:O))^2+(200000/log 2)*(x2:O)*M:=by
 classical
 intro H;have J:0< log (y1:O):=et (_M (_O :1< y1));let v:ℕ:=⌈(log (y1:O))^2⌉₊+1;let R:ℕ:=Nat.log 2 v+1;have w:v<=2^R:=(jJ _N v).le;have y:2^R<=4*v:=by have Q:2^Nat.log 2 v<=v:=gB 2 _O;dsimp only[R];rw[fc];omega
 let b:=H.filter fun n=>n<=x2/2^R;let c (r:ℕ):=(Ioc ((x2/2^r)/2) (x2/2^r)).filter fun n=>
  Squarefree n/\∃d∈n.divisors,y1< d/\d<=2*y1
 have K:H⊆b∪(range R).biUnion c:=by
  intro n E;by_cases o:n<=x2/2^R
  ·exact e0 _ (dB.mpr ⟨E,o⟩)
  ·push Not at o
   apply eu
   have S:∃r∈range R,n<=x2/2^r/\x2/2^(r+1)< n:=by
    have q:((range R).filter fun r=>n<=x2/2^r).Nonempty:=⟨0,dB.mpr ⟨dN.mpr _O,by
      simpa using (dT.mp (dB.mp E).1).2⟩⟩
    let r:=((range R).filter fun r=>n<=x2/2^r).max' q;have e:=kg _ q;rw[dB,dN]at e;refine⟨r,dN.mpr e.1,e.2,?_⟩;by_contra o';push Not at o';by_cases F:r+1=R
    ·rw[F]at o';omega
    ·have N':r+1∈(range R).filter fun r=>n<=x2/2^r:=dB.mpr ⟨dN.mpr _O,o'⟩;have:=gK _ (r+1) N';omega
   rcases S with⟨r,Z,h0,h3⟩;refine g4.mpr ⟨r,Z,dB.mpr ⟨fw.mpr ⟨?_,h0⟩,(dB.mp E).2⟩⟩;rw[Nat.div_div_eq_div_mul,<- fc];exact h3
 have m:(b.card:O)<=(x2:O)/(log (y1:O))^2:=by
  have u:b.card<=x2/2^R:=by
   calc b.card<=(Icc 1 (x2/2^R)).card:=er fun n E=>by
         rw[dB]at E;exact dT.mpr ⟨(dT.mp (dB.mp E.1).1).1,E.2⟩
     _=x2/2^R:=by simp
  have Q:((x2/2^R:ℕ):O)<=(x2:O)/(2:O)^R:=(by rw[ma _P];exact_mod_cast eD x2 (2^R));have h2:(log (y1:O))^2<=(2:O)^R:=by have D:(log (y1:O))^2<=(v:O):=(by dsimp only[v];push_cast;linarith[g6 ((log (y1:O))^2)]);exact D.trans (_M w)
  calc (b.card:O)<=((x2/2^R:ℕ):O):=by exact_mod_cast u
    _<=(x2:O)/(2:O)^R:=Q
    _<=(x2:O)/(log (y1:O))^2:=dL (dK _) _P h2
 have h:∀r∈range R,((c r).card:O)<=(100000/log 2)*((x2:O)/(2:O)^r)*M:=by
  intro r Z;rw[dN]at Z;have z:2^r<=4*v:=(dH _N (_O :r<=R)).trans y;have l:max (96*y1) (z_lo*y1)<=x2/2^r:=by rw[dZ (gr r)];exact (dR _ z).trans P
  have T:=db (x2/2^r) y1 h4 ((eo _ _).trans l);have h5:d8 (2*y1)<=M:=hS (2*y1) (dT.mpr ⟨G,B⟩);have h6:d8 ((x2/2^r)/y1)<=M:=by
   refine hS _ (dT.mpr ⟨?_,?_⟩)
   ·rw[dZ _O];exact (ep _ _).trans l
   ·exact (gs _ _).trans ((gs _ _).trans C)
  have U:((x2/2^r:ℕ):O)<=(x2:O)/(2:O)^r:=(by rw[ma _P];exact_mod_cast eD x2 (2^r));have i:0< log 2:=_l a3;have W:0<=d8 (2*y1)+d8 ((x2/2^r)/y1):=jT (d9 _) (d9 _)
  calc ((c r).card:O)
      <= (50000/log 2)*((x2/2^r:ℕ):O)*(d8 (2*y1)+d8 ((x2/2^r)/y1)):=T
    _<=(50000/log 2)*((x2:O)/(2:O)^r)*(M+M):=by gcongr
    _=(100000/log 2)*((x2:O)/(2:O)^r)*M:=_R
 have A:∑r∈range R,((x2:O)/(2:O)^r)<=2*(x2:O):=by have X:∑r∈range R,((x2:O)/(2:O)^r)=(x2:O)*∑r∈range R,((1:O)/2)^r:=(by rw[dP];refine dF rfl fun r _=>by rw[i6];ring);rw[X,fO (_N :((1:O)/2)≠1) R];have h7:0<=((1:O)/2)^R:=_P;have Q:(((1:O)/2)^R-1)/((1:O)/2-1)=2*(1-((1:O)/2)^R):=_R;rw[Q];nlinarith[dK (α:=O) x2]
 have j:(H.card:O)<=(b.card:O)+∑r∈range R,((c r).card:O):=by
  have u:H.card<=b.card+∑r∈range R,(c r).card:=by
   calc H.card<=(b∪(range R).biUnion c).card:=er K
     _<=b.card+((range R).biUnion c).card:=jD _ _
     _<=b.card+∑r∈range R,(c r).card:=Nat.add_le_add_left gq _
  exact_mod_cast u
 have i:0< log 2:=_l a3
 calc (H.card:O)<=(b.card:O)+∑r∈range R,((c r).card:O):=j
   _<=(x2:O)/(log (y1:O))^2+∑r∈range R,(100000/log 2)*((x2:O)/(2:O)^r)*M:=fd m (dG h)
   _=(x2:O)/(log (y1:O))^2+((100000/log 2)*M)*∑r∈range R,((x2:O)/(2:O)^r):=by congr 1;rw[dP];refine dF rfl fun r _=>_R
   _<=(x2:O)/(log (y1:O))^2+((100000/log 2)*M)*(2*(x2:O)):=fd eR (dA A _P)
   _=(x2:O)/(log (y1:O))^2+(200000/log 2)*(x2:O)*M:=_R
def dd (m:ℕ):Prop:=1<=m/\∀p∈m.primeFactors,2<=m.factorization p
instance (m:ℕ):Decidable (dd m):=by
 unfold dd;infer_instance
set_option maxHeartbeats 800000 in
lemma de {m:ℕ} (J:dd m) :
 ∃u v:ℕ,1<=u/\1<=v/\m=u^2*v^3:=by
 have e:m≠0:=by have:=J.1;omega
 let v:=∏p∈m.primeFactors.filter (fun p=>m.factorization p % 2=1),p;have l:1<=v:=fX (mi.mpr fun p b=>
  (dD (dB.mp b).1).ne_zero)
 have c:v^3∣m:=by
  have E:v^3=∏p∈m.primeFactors.filter (fun p=>m.factorization p % 2=1),p^3:=(prod_pow _ _ _).symm;rw[E];have A:m=∏p∈m.primeFactors,p^m.factorization p:=by
   conv_lhs=>rw[<- ew e,Finsupp.prod]
   rw[ej]
  conv_rhs=>rw[A]
  calc ∏p∈m.primeFactors.filter (fun p=>m.factorization p % 2=1),p^3
      ∣ ∏p∈m.primeFactors.filter (fun p=>m.factorization p % 2=1),p^m.factorization p:=by
        refine prod_dvd_prod_of_dvd _ _ fun p b=>?_
        have K:=J.2 p (dB.mp b).1;have M:=(dB.mp b).2;exact jj p _O
    _∣∏p∈m.primeFactors,p^m.factorization p:=iF _ _ _ (fj _ _)
 let q:=m/v^3;have D:1<=q:=ia (el J.1 c) _P;have B:m=q*v^3:=(jw c).symm;let u:=∏p∈q.primeFactors,p^(q.factorization p/2);have o:1<=u:=fX (mi.mpr fun p b=>
  jg _ (dD b).ne_zero)
 have F:u^2=q:=by
  have i:v.primeFactors=m.primeFactors.filter (fun p=>m.factorization p % 2=1):=cZ _ fun p b=>dD (dB.mp b).1;have w:Squarefree v:=d3 _ fun p b=>dD (dB.mp b).1;have y:∀p:ℕ,v.factorization p=if p∈m.primeFactors/\m.factorization p % 2=1 then 1 else 0:=by
   intro p;by_cases b:p∈m.primeFactors/\m.factorization p % 2=1
   ·rw[iM b];have d:p∈v.primeFactors:=(by rw[i,dB];exact b);have z:=dD d;have N:=(z.dvd_iff_one_le_factorization _O).mp (dS d);have P:v.factorization p<=1:=by
     by_contra Q;push Not at Q;exact z.ne_one (mn.mp (w p
      ((show p*p∣p^v.factorization p by rw[<- sq];exact jj p Q).trans (gd v p))))
    omega
   ·rw[gc b];by_contra C;have d:p∈v.primeFactors:=(by rw[<- ej];exact Finsupp.mem_support_iff.mpr C);rw[i,dB]at d;exact b d
  have j:∀p∈q.primeFactors,q.factorization p % 2=0:=by
   intro p b;have G:m.factorization p=q.factorization p+3*v.factorization p:=by rw[B,j4 _O _P,Nat.factorization_pow];simp[Finsupp.add_apply,Finsupp.smul_apply]
   have H:=y p;split_ifs at H with h
   ·omega
   ·by_cases d:p∈m.primeFactors
    ·have:m.factorization p % 2≠1:=fun E=>h ⟨d,E⟩
     omega
    ·have:m.factorization p=0:=by
      by_contra C;have z:=dD b;have R:p∣m:=(dS b).trans ⟨v^3,B⟩;exact d (md.mpr ⟨z,R,e⟩)
     omega
  calc u^2=∏p∈q.primeFactors,(p^(q.factorization p/2))^2:=(prod_pow _ _ _).symm
    _=∏p∈q.primeFactors,p^q.factorization p:=by
        refine f9 rfl fun p b=>?_
        rw[<- it,show q.factorization p/2*2=q.factorization p by have:=j p b;omega]
    _=q:=by
        conv_rhs=>rw[<- ew (_O :q≠0),Finsupp.prod]
        rw[ej]
 exact⟨u,v,o,l,by rw[F,B]⟩
set_option maxHeartbeats 800000 in
lemma df {n:ℕ} (P:1<=n) :
 ∃e h:ℕ,n=e*h/\1<=e/\Squarefree e/\dd h/\Nat.Coprime e h:=by
 let e:=∏p∈n.primeFactors.filter (fun p=>n.factorization p=1),p;let h:=∏p∈n.primeFactors.filter (fun p=>2<=n.factorization p),p^n.factorization p;have i:1<=e:=fX (mi.mpr fun p b=>
  (dD (dB.mp b).1).ne_zero)
 have j:1<=h:=fX (mi.mpr fun p b=>
  jg _ (dD (dB.mp b).1).ne_zero)
 have l:Squarefree e:=d3 _ fun p b=>dD (dB.mp b).1;have c:n=e*h:=by
  have y:n=∏p∈n.primeFactors,p^n.factorization p:=by
   conv_lhs=>rw[<- ew (_O :n≠0),Finsupp.prod]
   rw[ej]
  have z:n.primeFactors=n.primeFactors.filter (fun p=>n.factorization p=1) ∪
   n.primeFactors.filter (fun p=>2<=n.factorization p):=by
   ext p;simp only[ff,dB];constructor
   ·intro b;have d:=dD b;have B:=(d.dvd_iff_one_le_factorization _O).mp (dS b);by_cases v:n.factorization p=1
    ·exact Or.inl ⟨b,v⟩
    ·exact Or.inr ⟨b,_O⟩
   ·rintro (⟨b,_⟩ | ⟨b,_⟩) <;> exact b
  have A:Disjoint (n.primeFactors.filter (fun p=>n.factorization p=1)) (n.primeFactors.filter (fun p=>2<=n.factorization p)):=(by rw[eb];intro p v K;simp only[dB]at v K;omega);have m:e=∏p∈n.primeFactors.filter (fun p=>n.factorization p=1),p^n.factorization p:=f9 rfl fun p b=>by rw[(dB.mp b).2,pow_one]
  rw[y,z,kD A,<- m]
 have u:Nat.Coprime e h:=by
  refine Nat.Coprime.prod_left fun p b=>fL fun q N=>?_
  have d:=dD (dB.mp b).1;have G:=dD (dB.mp N).1;have H:p≠q:=(by intro J;subst J;have v:=(dB.mp b).2;have K:=(dB.mp N).2;omega);exact ((ft d G).mpr H).pow_right _
 have o:dd h:=by
  refine⟨j,fun p b=>?_⟩
  have d:=dD b;have C:p∣h:=dS b;have w:¬ p∣e:=fun v=>d.not_dvd_one (u.gcd_eq_one ▸ Nat.dvd_gcd v C);have D:e.factorization p=0:=(kx w);have E:n.factorization p=h.factorization p:=(by rw[c,j4 _O _O,Finsupp.add_apply,D,zero_add]);have F:p∈n.primeFactors:=md.mpr ⟨d,C.trans ⟨e,by rw[c,e8]⟩,_O⟩
  have B:=(d.dvd_iff_one_le_factorization _O).mp (dS F);have M:n.factorization p≠1:=fun v=>
   w (ji _ (dB.mpr ⟨F,v⟩))
  omega
 exact⟨e,h,c,i,l,o,u⟩
set_option maxHeartbeats 800000 in
lemma dg (x A B:ℕ) (R:1<=A) (T:1<=B) :
 let E:=(Icc 1 x).filter fun m=>dd m/\A^2*B^3< m
 ∑m∈E,(1:O)/(m:O)<=2/(A:O)+2/(B:O):=by
 classical
 intro E;let i:=(Ioc A x)×ˢ(Icc 1 x);let j:=(Icc 1 x)×ˢ(Ioc B x);have y:E⊆(i∪j).image fun d=>d.1^2*d.2^3:=by
  intro m K;rw[dB,dT]at K;obtain⟨u,v,z,C,rfl⟩:=de K.2.1;have e:u<=x:=by
   have:u<=u^2*v^3:=by nlinarith[iN (_O :0< v) 3]
   omega
  have h:v<=x:=by
   have:v<=u^2*v^3:=by
    calc v<=v*v^2:=m6 v (iN C 2)
      _=v^3:=by ring
      _<=u^2*v^3:=k3 _ (iN z 2)
   omega
  refine dW.mpr ⟨(u,v),?_,rfl⟩
  by_cases q:A< u
  ·exact e0 _ (ki.mpr ⟨fw.mpr ⟨q,e⟩,dT.mpr ⟨C,h⟩⟩)
  ·push Not at q
   have F:B< v:=(by by_contra D;push Not at D;have w:u^2*v^3<=A^2*B^3:=eH (fA q 2) (fA D 3);omega);exact eu _ (ki.mpr ⟨dT.mpr ⟨z,e⟩,fw.mpr ⟨F,h⟩⟩)
 have c:∑n∈Icc 1 x,(1:O)/((n:O)^2)<=2:=by
  by_cases H:x=0
  ·subst H;simp
  ·have l:Icc 1 x={1}∪Ioc 1 x:=by
    ext n;simp only[dT,ff,eg,fw];omega
   have o:Disjoint ({1}:Finset ℕ) (Ioc 1 x):=(by rw[eb];intro n w G;simp only[eg,fw]at w G;omega);rw[l,jr o,jA];have w:=ab 1 x eR;norm_num at w ⊢;linarith
 have b:∀S:Finset ℕ,(∀n∈S,1<=n) -> ∑n∈S,(1:O)/((n:O)^3)<=∑n∈S,(1:O)/((n:O)^2):=fun S P=>
  dG fun n Q=>by
   have M:(1:O)<=(n:O):=_M (P n Q);exact dL eO _P (by nlinarith)
 have w:∑d∈i,(1:O)/((d.1^2*d.2^3:ℕ):O)<=2/(A:O):=by
  rw[lc]
  calc ∑u∈Ioc A x,∑v∈Icc 1 x,(1:O)/((u^2*v^3:ℕ):O)
      = (∑u∈Ioc A x,(1:O)/((u:O)^2))*(∑v∈Icc 1 x,(1:O)/((v:O)^3)):=by
        rw[jn];refine dF rfl fun u _=>?_
        rw[dP];refine dF rfl fun v _=>by push_cast;ring
    _<=(1/(A:O))*2:=en (ab A x R) ((b _ fun v J=>(dT.mp J).1).trans c) (ea fun _ _=>by positivity) _P
    _=2/(A:O):=_R
 have G:∑d∈j,(1:O)/((d.1^2*d.2^3:ℕ):O)<=2/(B:O):=by
  rw[lc]
  calc ∑u∈Icc 1 x,∑v∈Ioc B x,(1:O)/((u^2*v^3:ℕ):O)
      = (∑u∈Icc 1 x,(1:O)/((u:O)^2))*(∑v∈Ioc B x,(1:O)/((v:O)^3)):=by
        rw[jn];refine dF rfl fun u _=>?_
        rw[dP];refine dF rfl fun v _=>by push_cast;ring
    _<=2*(1/(B:O)):=en c ((b _ fun v J=>by have:=(fw.mp J).1;omega).trans (ab B x T)) (ea fun _ _=>by positivity) _N
    _=2/(B:O):=_R
 calc ∑m∈E,(1:O)/(m:O)
     <= ∑m∈(i∪j).image (fun d:ℕ × ℕ=>(d.1^2*d.2^3:ℕ)),(1:O)/(m:O):=dC y fun _ _ _=>_P
   _<=∑d∈i∪j,(1:O)/((d.1^2*d.2^3:ℕ):O):=jY fun _ _=>_P
   _<=∑d∈i,(1:O)/((d.1^2*d.2^3:ℕ):O)+∑d∈j,(1:O)/((d.1^2*d.2^3:ℕ):O):=by have U:=fb (s₁:=i) (s₂:=j) (f:=fun d:ℕ × ℕ=>(1:O)/((d.1^2*d.2^3:ℕ):O));have N:0<=∑d∈i∩j,(1:O)/((d.1^2*d.2^3:ℕ):O):=ea fun _ _=>_P;linarith
   _<=2/(A:O)+2/(B:O):=fd w G
set_option maxHeartbeats 800000 in
lemma dh (T:ℕ) :
 ∑m∈(Icc 1 T).filter dd,(m.divisors.card:O)/(m:O)<=exp 24:=by
 classical
 let i:=dv T;let c:Finset ℕ:={0}∪Icc 2 (T+2);let Φ:=Fintype.piFinset fun _:i=>c;let f:ℕ->(i->ℕ):=fun m p=>m.factorization p.1;have q:∀m∈(Icc 1 T).filter dd,f m∈Φ/\m=∏p:i,p.1^f m p/\(m.divisors.card:O)=∏p:i,((f m p+1:ℕ):O):=by
  intro m D;rw[dB,dT]at D;have E:f m∈Φ:=by
   rw[e5];intro p;by_cases o:p.1∈m.primeFactors
   ·apply eu;rw[dT]
    dsimp only[f];refine⟨D.2.2 p.1 o,?_⟩;have J:2^m.factorization p.1<=m:=by
     calc 2^m.factorization p.1<=p.1^m.factorization p.1:=
           fA (dD o).two_le _
       _<=m:=el D.1.1 (gd m p.1)
    have h5:=gC (n:=m.factorization p.1);omega
   ·apply e0;rw[eg]
    dsimp only[f];by_contra X;have u:=(e7.mp p.2).2;have Z:p.1∣m:=(u.dvd_iff_one_le_factorization _O).mpr _O;exact o (md.mpr ⟨u,Z,_O⟩)
  have j:m.primeFactors⊆i:=fun p o=>
   e7.mpr ⟨(el D.1.1 (dS o)).trans D.1.2,dD o⟩
  have y':m=∏p:i,p.1^f m p:=by
   have w:∏p:i,p.1^f m p=∏p∈i,p^m.factorization p:=(by exact hJ (fun p _=>p.1) (fun p _=>p.2) (fun _ _ _ _ h=>i9 h) (fun p o=>⟨⟨p,o⟩,dJ _,rfl⟩) (fun _ _=>rfl));rw[w];have J:∏p∈i,p^m.factorization p=∏p∈m.primeFactors,p^m.factorization p:=by
    symm;refine lg j fun p o C=>?_
    have v:m.factorization p=0:=(by by_contra X;have u:=(e7.mp o).2;exact C (md.mpr ⟨u,(u.dvd_iff_one_le_factorization _O).mpr _O,_O⟩));rw[v,kQ]
   rw[J];conv_lhs=>rw[<- ew (_O :m≠0),Finsupp.prod]
   rw[ej]
  have P:(m.divisors.card:O)=∏p:i,((f m p+1:ℕ):O):=by
   have Q:m.divisors.card=∏p:i,(f m p+1):=by
    rw[Nat.card_divisors (_O :m≠0)];change ∏p∈m.factorization.support,(m.factorization p+1)=_;rw[ej];have w:∏p:i,(f m p+1)=∏p∈i,(m.factorization p+1):=hJ (fun p _=>p.1) (fun p _=>p.2) (fun _ _ _ _ h=>i9 h) (fun p o=>⟨⟨p,o⟩,dJ _,rfl⟩) (fun _ _=>rfl);rw[w];refine lg j fun p o C=>?_
    have v:m.factorization p=0:=(by by_contra X;have u:=(e7.mp o).2;exact C (md.mpr ⟨u,(u.dvd_iff_one_le_factorization _O).mpr _O,_O⟩));rw[v,zero_add]
   exact_mod_cast Q
  exact⟨E,y',P⟩
 have F:Set.InjOn f (((Icc 1 T).filter dd:Finset ℕ):Set ℕ):=by intro m1 w m2 J h4;rw[(q m1 w).2.1,(q m2 J).2.1];exact f9 rfl fun p _=>by rw[gH h4 p]
 have z:∑m∈(Icc 1 T).filter dd,(m.divisors.card:O)/(m:O) <=∑e∈Φ,∏p:i,((e p+1:ℕ):O)/(p.1:O)^(e p):=by
  have w:∑m∈(Icc 1 T).filter dd,(m.divisors.card:O)/(m:O) =∑e∈((Icc 1 T).filter dd).image f,∏p:i,((e p+1:ℕ):O)/(p.1:O)^(e p):=by
   rw[fr (fun a ha b hb h=>F ha hb h)];refine dF rfl fun m D=>?_
   rw[(q m D).2.2,gM];congr 1;conv_lhs=>rw[(q m D).2.1]
   push_cast;rfl
  rw[w];refine dC (fun e he=>?_) (fun _ _ _=>prod_nonneg fun _ _=>by positivity)
  rcases dW.mp he with⟨m,D,rfl⟩;exact (q m D).1
 have A:∑e∈Φ,∏p:i,((e p+1:ℕ):O)/(p.1:O)^(e p) =∏p:i,∑k∈c,((k+1:ℕ):O)/(p.1:O)^k:=(j9 (t:=fun _:i=>c) (f:=fun (p:i) (k:ℕ)=>((k+1:ℕ):O)/(p.1:O)^k)).symm;have B:∀p:i,∑k∈c,((k+1:ℕ):O)/(p.1:O)^k<=exp (12/(p.1:O)^2):=by
  intro p;have h0:(2:O)<=(p.1:O):=_M (e7.mp p.2).2.two_le;have K:Disjoint ({0}:Finset ℕ) (Icc 2 (T+2)):=(by rw[eb];intro k w J;simp only[eg,dT]at w J;omega);have G:∑k∈c,((k+1:ℕ):O)/(p.1:O)^k<=1+12/(p.1:O)^2:=by
   dsimp only[c];rw[jr K,jA];rw[show ((0+1:ℕ):O)/(p.1:O)^0=1 by simp]
   refine fd eR ?_
   have M:∀k∈Icc 2 (T+2),((k+1:ℕ):O)/(p.1:O)^k<=(3/(p.1:O)^2)*((3:O)/4)^(k-2):=by
    intro k W;rw[dT]at W;have R:((k+1:ℕ):O)<=3*((3:O)/2)^(k-2):=by
     have S:∀d:ℕ,((2+d+1:ℕ):O)<=3*((3:O)/2)^d:=by
      intro d;induction d with
      | zero=>norm_num
      | succ n ih=>
       push_cast at ih ⊢;rw[fp];have w:(1:O)<=((3:O)/2)^n:=mo _N;linarith
     obtain⟨d,rfl⟩:=Nat.exists_eq_add_of_le W.1;rw[show 2+d-2=d by omega]
     exact S d
    have H:(p.1:O)^k=(p.1:O)^2*(p.1:O)^(k-2):=(by rw[<- ee,iW W.1]);have h3:(2:O)^(k-2)<=(p.1:O)^(k-2):=m9 _N h0 _;rw[H]
    calc ((k+1:ℕ):O)/((p.1:O)^2*(p.1:O)^(k-2))
        <= (3*((3:O)/2)^(k-2))/((p.1:O)^2*(2:O)^(k-2)):=mj _P R _P (dA h3 _P)
      _=(3/(p.1:O)^2)*((3:O)/4)^(k-2):=by rw[ij,ij];field_simp [(_L :(p.1:O)≠0),(_P :(2:O)^(k-2)≠0)];rw[show (4:O)^(k-2)=(2:O)^(k-2)*(2:O)^(k-2) by rw[<- eP];norm_num];ring
   have N:∑k∈Icc 2 (T+2),((3:O)/4)^(k-2)<=4:=by
    have j:(Icc 2 (T+2)).image (fun k=>k-2)⊆range (T+1):=(by intro d Z;rcases dW.mp Z with⟨k,W,rfl⟩;rw[dT]at W;rw[dN];omega);have U:Set.InjOn (fun k=>k-2) ((Icc 2 (T+2):Finset ℕ):Set ℕ):=by intro k1 w k2 J h;simp only[eB,dT]at w J;dsimp only at h;omega
    calc ∑k∈Icc 2 (T+2),((3:O)/4)^(k-2)
        = ∑d∈(Icc 2 (T+2)).image (fun k=>k-2),((3:O)/4)^d:=(fr (fun a ha b hb h=>U ha hb h)).symm
      _<=∑d∈range (T+1),((3:O)/4)^d:=dC j fun _ _ _=>_P
      _=(((3:O)/4)^(T+1)-1)/((3:O)/4-1):=fO (_N :((3:O)/4)≠1) (T+1)
      _<=4:=by have h6:0<=((3:O)/4)^(T+1):=_P;have:(((3:O)/4)^(T+1)-1)/((3:O)/4-1)=4*(1-((3:O)/4)^(T+1)):=_R;rw[this];linarith
   calc ∑k∈Icc 2 (T+2),((k+1:ℕ):O)/(p.1:O)^k
       <= ∑k∈Icc 2 (T+2),(3/(p.1:O)^2)*((3:O)/4)^(k-2):=dG M
     _=(3/(p.1:O)^2)*∑k∈Icc 2 (T+2),((3:O)/4)^(k-2):=(dP ..).symm
     _<=(3/(p.1:O)^2)*4:=dA N _P
     _=12/(p.1:O)^2:=_R
  exact G.trans (_l (fB (12/(p.1:O)^2)))
 have l:∑p:i,(12:O)/(p.1:O)^2<=24:=by
  have w:∑p:i,(12:O)/(p.1:O)^2=12*∑p∈i,(1:O)/(p:O)^2:=(by rw[dP];exact fh (fun p _=>p.1) (fun p _=>p.2) (fun _ _ _ _ h=>i9 h) (fun p o=>⟨⟨p,o⟩,dJ _,rfl⟩) (fun _ _=>by ring));rw[w];have j:i⊆Ioc 1 T:=fun p o=>
   fw.mpr ⟨(e7.mp o).2.one_lt,(e7.mp o).1⟩
  have h7:∑p∈i,(1:O)/(p:O)^2<=1:=(dC j fun _ _ _=>by positivity).trans (by
    have:=ab 1 T eR;norm_num at this;simpa[g9] using this)
  linarith
 calc ∑m∈(Icc 1 T).filter dd,(m.divisors.card:O)/(m:O)
     <= ∏p:i,∑k∈c,((k+1:ℕ):O)/(p.1:O)^k:=z.trans_eq A
   _<=∏p:i,exp (12/(p.1:O)^2):=im (fun _ _=>ea fun _ _=>by positivity) (fun p _=>B p)
   _=exp (∑p:i,(12:O)/(p.1:O)^2):=(exp_sum _ _).symm
   _<=exp 24:=me.mpr l
set_option maxHeartbeats 800000 in
lemma di :
 ∃K:O,0< K/\∀(x j:ℕ) (M:O),2000<=j->2*j<=Nat.log 2 x->0<=M -> (∀t∈Icc (2^(j/2)) x,d8 t<=M) -> ((c6 x j).card:O)<=K*(x:O)*(1/(log ((2^j:ℕ):O))^2+M):=by
 classical
 let K:O:=10+exp 24*(4+200000/log 2);have h5:0< log 2:=_l a3;refine⟨K,by positivity,?_⟩
 intro x j M hj hZ hM hS;set y:ℕ:=2^j;have hw:0< y:=gr j;have hc:y^2<=x:=by have H4:2^(2*j)<=x:=(dH _N hZ).trans (gB 2 (by intro h0;subst h0;simp at hZ;omega));have:y^2=2^(2*j):=(by dsimp only[y];rw[sq,<- ee,two_mul]);omega
 have C:(1000:O)<=log (y:O):=by dsimp only[y];rw[gx,g7,fm];have:(2000:O)<=(j:O):=_M hj;nlinarith[a3]
 have l:0< log (y:O):=_L;let A:ℕ:=⌈(log (y:O))^2⌉₊;have Q:1<=A:=Nat.one_le_iff_ne_zero.mpr (by
  intro h;have h0:(A:O)=0:=_M h;have Hm:(log (y:O))^2<=(A:O):=g6 _;nlinarith[C])
 have R:(log (y:O))^2<=(A:O):=g6 _;have hx:(A:O)<=2*(log (y:O))^2:=by
  have:=jm (_P :0<=(log (y:O))^2)
  nlinarith
 let T:ℕ:=A^2*A^3;have S:T<=2^(j/4):=by
  have he:log (y:O)<=(j:O):=(by dsimp only[y];rw[gx,g7,fm];nlinarith[a4]);have H5:(T:O)<=32*(j:O)^10:=by
   dsimp only[T];push_cast;have D:(A:O)^2*(A:O)^3=(A:O)^5:=_R;rw[D]
   calc (A:O)^5<=(2*(log (y:O))^2)^5:=m9 _P hx 5
     _=32*(log (y:O))^10:=_R
     _<=32*(j:O)^10:=dA (m9 l.le he 10) _N
  have hy:32*(j:O)^10<=(2:O)^(j/4):=by
   have v:32*j^10<=2^(j/4):=by
    have hE:∀n:ℕ,500<=n->32*(4*n+3)^10<=2^n:=by
     intro n hn;induction n,hn using fe with
     | base=>
      calc 32*(4*500+3)^10<=2^5*(2^11)^10:=eH _N (fA _N 10)
        _=2^115:=by rw[<- it,<- ee]
        _<=2^500:=dH _N _O
     | succ n hn ih=>
      have hF:(4*(n+1)+3)^10<=2*(4*n+3)^10:=by
       have D':20*(4*(n+1)+3)<=21*(4*n+3):=_O;have G':(20*(4*(n+1)+3))^10<=(21*(4*n+3))^10:=fA D' 10;rw[eP,eP]at G';have h3':21^10<=2*20^10:=_N;have h4:20^10*(4*(n+1)+3)^10<=20^10*(2*(4*n+3)^10):=by
        calc 20^10*(4*(n+1)+3)^10<=21^10*(4*n+3)^10:=G'
          _<=(2*20^10)*(4*n+3)^10:=eE _ h3'
          _=20^10*(2*(4*n+3)^10):=by ring
       exact Nat.le_of_mul_le_mul_left h4 _P
      calc 32*(4*(n+1)+3)^10<=32*(2*(4*n+3)^10):=dR 32 hF
        _=2*(32*(4*n+3)^10):=by ring
        _<=2*2^n:=dR 2 ih
        _=2^(n+1):=by rw[fp]
    have hT:j<=4*(j/4)+3:=_O;exact (dR 32 (fA hT 10)).trans (hE (j/4) _O)
   exact_mod_cast v
  exact_mod_cast H5.trans hy
 let D0:=(Icc 1 x).filter fun n=>y∣n;let D1:=((Icc 1 x).filter fun m=>dd m/\T< m).biUnion fun m=>
  (Icc 1 (x/m)).image fun q=>q*m
 let b:=(Icc 1 T).filter dd;let c (x2 y1:ℕ):=(Icc 1 x2).filter fun n=>
  Squarefree n/\∃d∈n.divisors,y1< d/\d<=2*y1
 let J:=b.biUnion fun m=>m.divisors.biUnion fun f=>
  (c (x/m) (y/f)).image fun e=>e*m
 let J':=b.biUnion fun m=>m.divisors.biUnion fun f=>
  ((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).image fun e=>e*m
 have hU:c6 x j⊆D0∪D1∪J∪J':=by
  intro n hn;rw[c7]at hn;rcases hn with⟨h8,hY,d,hd,Hd,He⟩;by_cases Hf:d=y
  ·apply e0;apply e0;apply e0
   exact dB.mpr ⟨dT.mpr ⟨h8,hY⟩,Hf ▸ ef hd⟩
  ·have H6:y< d:=(by omega);have hV:d<=2*y:=by
    have:2^(j+1)=2*y:=by dsimp only[y];rw[fp]
    omega
   obtain⟨e,n2,H,B,hu,i,Hl⟩:=df h8;by_cases hv:T< n2
   ·apply e0;apply e0;apply eu
    have hh:n2<=x:=(k3 n2 B).trans (H ▸ hY);refine g4.mpr ⟨n2,dB.mpr ⟨dT.mpr ⟨i.1,hh⟩,i,hv⟩,dW.mpr ⟨e,dT.mpr ⟨B,?_⟩,H.symm⟩⟩;rw[dZ i.1];omega
   ·push Not at hv
    let f:=Nat.gcd d n2;let d1:=d/f;have u:f∣n2:=kY d n2;have N:f∣d:=l8 d n2;have w:1<=f:=Nat.gcd_pos_of_pos_right d i.1;have h6:d=d1*f:=(jw N).symm;have E:d1∣e:=by
     have H0:d1*f∣e*n2:=(by rw[<- h6,<- H];exact ef hd);have ho:Nat.Coprime d1 (n2/f):=(by have hg:=Nat.gcd_div N u;rwa[Nat.div_self w]at hg);have H7:d1∣e*(n2/f):=by
      have:d1*f∣(e*(n2/f))*f:=by rwa[f0,jw u]
      exact (Nat.mul_dvd_mul_iff_right w).mp this
     exact ho.dvd_of_dvd_mul_right H7
    have W:n2∈b:=dB.mpr ⟨dT.mpr ⟨i.1,hv⟩,i⟩;have h9:f∈n2.divisors:=fW.mpr ⟨u,by have:=i.1;omega⟩
    have ha:e<=x/n2:=(by rw[dZ i.1];omega);have hz:y/f< d1:=(by have D:f*(y/f)<=y:=lL y f;have G:f*(y/f)< f*d1:=(by rw[e8 f d1,<- h6];omega);exact lS G);have H1:d1<=2*(y/f)+1:=(by have D:y< f*(y/f+1):=(by have:=gu y f;have:=dY y w;nlinarith);have G:f*d1< f*(2*(y/f)+2):=(by rw[e8 f d1,<- h6];linarith);have h3:=lS G;omega);by_cases hl:d1=2*(y/f)+1
    ·apply eu
     refine g4.mpr ⟨n2,W,g4.mpr ⟨f,h9,dW.mpr ⟨e,dB.mpr ⟨dT.mpr ⟨B,ha⟩,hl ▸ E⟩,H.symm⟩⟩⟩
    ·apply e0;apply eu
     refine g4.mpr ⟨n2,W,g4.mpr ⟨f,h9,dW.mpr ⟨e,dB.mpr ⟨dT.mpr ⟨B,ha⟩,hu,d1,fW.mpr ⟨E,_O⟩,hz,_O⟩,H.symm⟩⟩⟩
 have H2:(D0.card:O)<=(x:O)/(log (y:O))^2:=by
  have v:D0.card<=x/y:=by
   have hp:D0⊆(Icc 1 (x/y)).image fun q=>q*y:=by
    intro n hn;rw[dB,dT]at hn;rcases hn.2 with⟨q,rfl⟩;refine dW.mpr ⟨q,dT.mpr ⟨?_,?_⟩,_R⟩
    ·by_contra h0;push Not at h0;have:q=0:=by omega
     subst this;simp at hn
    ·rw[dZ hw,e8];exact hn.1.2
   calc D0.card<=((Icc 1 (x/y)).image fun q=>q*y).card:=er hp
     _<=(Icc 1 (x/y)).card:=ja
     _=x/y:=by simp
  have D:((x/y:ℕ):O)<=(x:O)/(y:O):=(by rw[ma _P];exact_mod_cast eD x y);have G:(log (y:O))^2<=(y:O):=by have hD:=kl l.le 4;simp[jt,Nat.factorial]at hD;rw[eX _P]at hD;nlinarith[C,gR (log (y:O))]
  calc (D0.card:O)<=((x/y:ℕ):O):=by exact_mod_cast v
    _<=(x:O)/(y:O):=D
    _<=(x:O)/(log (y:O))^2:=dL (dK _) _P G
 have H3:(D1.card:O)<=4*(x:O)/(log (y:O))^2:=by
  have v:D1.card<=∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),x/m:=by
   calc D1.card<=∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),
           ((Icc 1 (x/m)).image fun q=>q*m).card:=gq
     _<=∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),(Icc 1 (x/m)).card:=dG fun _ _=>ja
     _=_:=dF rfl fun _ _=>by simp
  have hI:=dg x A A Q Q;have D:(D1.card:O)<=(x:O)*∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),(1:O)/(m:O):=by
   calc (D1.card:O)<=∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),((x/m:ℕ):O):=by exact_mod_cast v
     _<=∑m∈(Icc 1 x).filter (fun m=>dd m/\T< m),(x:O)*((1:O)/(m:O)):=by
         refine dG fun m hm=>?_
         have U:0< m:=(dT.mp (dB.mp hm).1).1;rw[iE,ma _P];exact_mod_cast eD x m
     _=_:=(dP ..).symm
  have hA:2/(A:O)+2/(A:O)<=4/(log (y:O))^2:=by have Hn:2/(A:O)+2/(A:O)=4/(A:O):=_R;have:4/(A:O)<=4/(log (y:O))^2:=dL _N _P R;linarith
  calc (D1.card:O)<=(x:O)*(2/(A:O)+2/(A:O)):=
        D.trans (dA hI (dK _))
    _<=(x:O)*(4/(log (y:O))^2):=dA hA (dK _)
    _=4*(x:O)/(log (y:O))^2:=_R
 have h7:∀m∈b,∀f∈m.divisors,((c (x/m) (y/f)).card:O) +(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O) <=((x:O)/(m:O))*(4/(log (y:O))^2+(200000/log 2)*M):=by
  intro m hm f hf;rw[dB,dT]at hm;have U:1<=m:=hm.1.1;have X:m<=T:=hm.1.2;have w:1<=f:=em hf;have hq:f<=T:=(el U (ef hf)).trans X;have z:2^(3*j/4-1)<=y/f:=by
   rw[dZ w]
   calc 2^(3*j/4-1)*f<=2^(3*j/4-1)*2^(j/4):=dR _ (hq.trans S)
     _=2^((3*j/4-1)+j/4):=(ee 2 _ _).symm
     _<=2^j:=dH _N _O
  have hB:24<=y/f:=(_N :24<=2^5).trans ((dH _N _O).trans z);have o:log (y:O)/2<=log ((y/f:ℕ):O):=by
   have D:(2:O)^(j/2)<=((y/f:ℕ):O):=(by exact_mod_cast (dH _N (_O :j/2<=3*j/4-1)).trans z);have G:=dM _P D;rw[fm]at G;have h3:log (y:O)=(j:O)*log 2:=(by dsimp only[y];rw[gx,g7,fm]);have h4:(j:O)/2<=((j/2:ℕ):O)+1:=by
    have:j<=2*(j/2)+1:=_O
    have hR:(j:O)<=2*((j/2:ℕ):O)+1:=_M this;linarith
   have D':(2:O)^(j/2+2)<=((y/f:ℕ):O):=(by exact_mod_cast (dH _N (_O :j/2+2<=3*j/4-1)).trans z);have G':=dM _P D';rw[fm]at G';push_cast at G';rw[h3];nlinarith[a3]
  have hW:max (96*(y/f)) (2^(j/2)*(y/f))*(4*(⌈(log ((y/f:ℕ):O))^2⌉₊+1))<=x/m:=by
   have hr:log ((y/f:ℕ):O)<=log (y:O):=dM _P (_M (gs y f));have hk:4*(⌈(log ((y/f:ℕ):O))^2⌉₊+1)<=2^(j/4):=by
    have D : ⌈(log ((y/f:ℕ):O))^2⌉₊<=A:=Nat.ceil_mono (m9 (f1 (_M (_O :1<=y/f))) hr 2);have G:4*(A+1)<=T:=by
     dsimp only[T];have Hg:10<=A:=by
      have:(10:O)<=(A:O):=by nlinarith[R,C]
      exact_mod_cast this
     have Ho:100<=A^2:=_Q;have Hp:1000<=A^3:=by
      have:A^3=A*A^2:=_R
      nlinarith
     nlinarith
    exact (dR 4 (Nat.add_le_add_right D 1)).trans (G.trans S)
   have hs:max (96*(y/f)) (2^(j/2)*(y/f))<=2^(j/2)*y:=by
    refine kC ?_ (dR _ (gs y f))
    have H8:96<=2^(j/2):=(_N :96<=2^7).trans (dH _N _O);exact eH H8 (gs y f)
   rw[dZ U]
   calc max (96*(y/f)) (2^(j/2)*(y/f))*(4*(⌈(log ((y/f:ℕ):O))^2⌉₊+1))*m
       <= (2^(j/2)*y)*2^(j/4)*2^(j/4):=eH (eH hs hk) (X.trans S)
     _=y*2^(j/2+j/4+j/4):=by rw[ee,ee];ring
     _<=y*y:=dR y (dH _N _O)
     _=y^2:=(sq y).symm
     _<=x:=hc
  have ht:=dc (x/m) (y/f) (2^(j/2)) x M hM hB ((dH _N (_O :j/2<=3*j/4-1)).trans (z.trans _O))
   (by have D:2*(y/f)<=2*y:=dR 2 (gs y f);have G:2*y<=y^2:=(by rw[sq];exact eE y (by dsimp only[y];exact (_N :2<=2^1).trans (dH _N _O)));omega)
   (gs x m) hW hS
  have hb:((x/m:ℕ):O)<=(x:O)/(m:O):=(by rw[ma _P];exact_mod_cast eD x m);have F:0< log ((y/f:ℕ):O):=_L;have P:1/(log ((y/f:ℕ):O))^2<=4/(log (y:O))^2:=(by have H9:(log (y:O))^2/4<=(log ((y/f:ℕ):O))^2:=(by have:=m9 _P o 2;linarith);rw[mb (jB F) (jB l)];linarith);have hL:(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O) <=((x:O)/(m:O))*(1/(log (y:O))^2):=by
   set Z:=2*(y/f)+1;have v:((Icc 1 (x/m)).filter fun e=>Z∣e).card<=(x/m)/Z:=by
    have hp:(Icc 1 (x/m)).filter (fun e=>Z∣e)⊆(Icc 1 ((x/m)/Z)).image fun q=>q*Z:=by
     intro e h8;rw[dB,dT]at h8;rcases h8.2 with⟨q,rfl⟩;refine dW.mpr ⟨q,dT.mpr ⟨?_,?_⟩,_R⟩
     ·by_contra h0;push Not at h0;have:q=0:=by omega
      subst this;simp at h8
     ·rw[dZ _O,e8];exact h8.1.2
    calc _<=((Icc 1 ((x/m)/Z)).image fun q=>q*Z).card:=er hp
      _<=(Icc 1 ((x/m)/Z)).card:=ja
      _=(x/m)/Z:=by simp
   have hC:(log (y:O))^2<=(Z:O):=by
    have D:A<=Z:=by
     have Ha:A<=T:=by
      dsimp only[T]
      calc A<=A*A:=k3 A Q
        _=A^2:=(sq A).symm
        _<=A^2*A^3:=m6 _ (iN Q 3)
     have G:2^(j/4)<=2^(3*j/4-1):=dH _N _O;have:=Ha.trans S;omega
    exact R.trans (_M D)
   have D:(((x/m)/Z:ℕ):O)<=((x/m:ℕ):O)/(Z:O):=by rw[ma _P];exact_mod_cast eD (x/m) Z
   calc (((Icc 1 (x/m)).filter fun e=>Z∣e).card:O)
       <= (((x/m)/Z:ℕ):O):=_M v
     _<=((x/m:ℕ):O)/(Z:O):=D
     _<=((x:O)/(m:O))/(log (y:O))^2:=mj _P hb _P hC
     _=((x:O)/(m:O))*(1/(log (y:O))^2):=_R
  have o':(2:O)/3*log (y:O)<=log ((y/f:ℕ):O):=by
   have D':(2:O)^(2*j/3+2)<=((y/f:ℕ):O):=(by exact_mod_cast (dH _N (_O :2*j/3+2<=3*j/4-1)).trans z);have G':=dM _P D';rw[fm]at G';push_cast at G';have h3:log (y:O)=(j:O)*log 2:=(by dsimp only[y];rw[gx,g7,fm]);have h4:2*(j:O)/3<=((2*j/3:ℕ):O)+1:=by
    have:2*j<=3*(2*j/3)+2:=_O
    have hR:2*(j:O)<=3*((2*j/3:ℕ):O)+2:=_M this;linarith
   rw[h3]
   calc (2:O)/3*((j:O)*log 2)=(2*(j:O)/3)*log 2:=by ring
     _<=(((2*j/3:ℕ):O)+2)*log 2:=dE _L h5.le
     _<=log ((y/f:ℕ):O):=G'
  have P':1/(log ((y/f:ℕ):O))^2<=3/(log (y:O))^2:=(by have H9:(4:O)/9*(log (y:O))^2<=(log ((y/f:ℕ):O))^2:=(by have:=m9 _P o' 2;linarith);rw[mb (jB F) (jB l)];linarith);have ht':((c (x/m) (y/f)).card:O) <=((x:O)/(m:O))*(3/(log (y:O))^2+(200000/log 2)*M):=by
   calc ((c (x/m) (y/f)).card:O)
       <= ((x/m:ℕ):O)/(log ((y/f:ℕ):O))^2+(200000/log 2)*((x/m:ℕ):O)*M:=ht
     _<=((x:O)/(m:O))*(3/(log (y:O))^2)+(200000/log 2)*((x:O)/(m:O))*M:=by
         refine fd ?_ (by gcongr)
         rw[div_eq_mul_one_div];exact en hb P' _P _P
     _=_:=by ring
  calc ((c (x/m) (y/f)).card:O) +
        (((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O)
      <= ((x:O)/(m:O))*(3/(log (y:O))^2+(200000/log 2)*M) +((x:O)/(m:O))*(1/(log (y:O))^2):=fd ht' hL
    _=((x:O)/(m:O))*(4/(log (y:O))^2+(200000/log 2)*M):=_R
 have hX:(J.card:O)+(J'.card:O) <=exp 24*(x:O)*(4/(log (y:O))^2+(200000/log 2)*M):=by
  have hN:J.card<=∑m∈b,∑f∈m.divisors,(c (x/m) (y/f)).card:=by
   calc J.card<=∑m∈b,(m.divisors.biUnion fun f=>(c (x/m) (y/f)).image fun e=>e*m).card:=
         gq
     _<=∑m∈b,∑f∈m.divisors,((c (x/m) (y/f)).image fun e=>e*m).card:=dG fun _ _=>gq
     _<=_:=dG fun _ _=>dG fun _ _=>ja
  have hP:J'.card<=∑m∈b,∑f∈m.divisors,((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:=by
   calc J'.card<=∑m∈b,(m.divisors.biUnion fun f=>
           ((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).image fun e=>e*m).card:=
         gq
     _<=∑m∈b,∑f∈m.divisors,(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).image fun e=>e*m).card:=dG fun _ _=>gq
     _<=_:=dG fun _ _=>dG fun _ _=>ja
  have D:(J.card:O)+(J'.card:O) <=∑m∈b,∑f∈m.divisors,(((c (x/m) (y/f)).card:O) +(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O)):=by
   have D':(J.card:O)<=∑m∈b,∑f∈m.divisors,((c (x/m) (y/f)).card:O):=_M hN;have G':(J'.card:O)<=∑m∈b,∑f∈m.divisors,(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O):=_M hP
   calc (J.card:O)+(J'.card:O)
       <= (∑m∈b,∑f∈m.divisors,((c (x/m) (y/f)).card:O)) +(∑m∈b,∑f∈m.divisors,(((Icc 1 (x/m)).filter fun e=>(2*(y/f)+1)∣e).card:O)):=fd D' G'
     _=_:=by rw[<- fD];exact dF rfl fun m _=>(fD).symm
  calc (J.card:O)+(J'.card:O)
      <= ∑m∈b,∑f∈m.divisors,(((x:O)/(m:O))*(4/(log (y:O))^2+(200000/log 2)*M)):=D.trans (dG fun m hm=>dG fun f hf=>h7 m hm f hf)
    _=(∑m∈b,(m.divisors.card:O)/(m:O))*((x:O)*(4/(log (y:O))^2+(200000/log 2)*M)):=by
        rw[jn];refine dF rfl fun m _=>?_
        rw[ex,e3];ring
    _<=exp 24*((x:O)*(4/(log (y:O))^2+(200000/log 2)*M)):=dE (dh T) _P
    _=_:=by ring
 have hQ:((c6 x j).card:O)<=(D0.card:O)+(D1.card:O)+((J.card:O)+(J'.card:O)):=by have v:(c6 x j).card<=D0.card+D1.card+(J.card+J'.card):=(by have D:=(er hU).trans (jD _ _);have G:=jD (D0∪D1) J;have h3:=jD D0 D1;omega);exact_mod_cast v
 have Hb:(x:O)/(log (y:O))^2+4*(x:O)/(log (y:O))^2 +exp 24*(x:O)*(4/(log (y:O))^2+(200000/log 2)*M) <=K*(x:O)*(1/(log (y:O))^2+M):=by dsimp only[K];have Hh:0<=(x:O)/(log (y:O))^2:=_P;have Hi:0<=(x:O)*M:=_P;have Hj:0<=exp 24:=(ez 24).le;have Hc:(10+exp 24*(4+200000/log 2))*(x:O)*(1/(log (y:O))^2+M) -((x:O)/(log (y:O))^2+4*(x:O)/(log (y:O))^2 +exp 24*(x:O)*(4/(log (y:O))^2+(200000/log 2)*M)) =5*((x:O)/(log (y:O))^2)+(10+4*exp 24)*((x:O)*M) +(200000/log 2)*exp 24*((x:O)/(log (y:O))^2):=_R;have Hk:0<=5*((x:O)/(log (y:O))^2)+(10+4*exp 24)*((x:O)*M) +(200000/log 2)*exp 24*((x:O)/(log (y:O))^2):=_P;linarith
 linarith
set_option maxHeartbeats 800000 in
lemma dj (m:ℕ) :
 ∃C_m:O,0< C_m/\∀p:ℕ,∑b∈cV p,L b*(log (b:O))^m/(b:O) <=C_m*(log (max 4 (p:O)))^m*∑b∈cV p,L b/(b:O):=by
 classical
 induction m with
 | zero=>
  refine⟨1,i5,fun p=>by simp⟩
 | succ m ih=>
  obtain⟨Cm,Q,h0⟩:=ih;refine⟨2^(m+2)*(1+Cm),by positivity,fun p=>?_⟩
  have R:0< log (max 4 (p:O)):=et (e9 _N (eo _ _));have S:0<=∑b∈cV p,L b/(b:O):=ea fun b _=>ed (bK b) (dK b);have B:∀b∈cV p,log (b:O)=∑q∈b.primeFactors,log (q:O):=by
   intro b A;have G:=d4 ((d5 _ _).mp A).1 ((d5 _ _).mp A).2.1;conv_lhs=>rw[<- G]
   rw[fu,iP fun q o=>by exact_mod_cast (dD o).ne_zero]
  have J:∑b∈cV p,L b*(log (b:O))^(m+1)/(b:O) =∑q∈dv p,(log (q:O)/(q:O)) *∑c∈(cV p).filter (fun c=>¬ q∣c),L (q*c)*(log (q:O)+log (c:O))^m/(c:O):=by
   have G:∑b∈cV p,L b*(log (b:O))^(m+1)/(b:O) =∑b∈cV p,∑q∈dv p,if q∈b.primeFactors then L b*(log (b:O))^m*log (q:O)/(b:O) else 0:=by
    refine dF rfl fun b A=>?_
    rw[fc,B b A,<- f0,dP,kM,<- f8];have K:(dv p).filter (fun q=>q∈b.primeFactors)=b.primeFactors:=by
     ext q;simp only[dB];constructor
     ·exact fun h=>h.2
     ·intro o;exact⟨e7.mpr ⟨((d5 _ _).mp A).2.2 q o,dD o⟩,o⟩
    rw[K]
   rw[G,hH];refine dF rfl fun q o=>?_
   have d:q.Prime:=(e7.mp o).2;have C:q<=p:=(e7.mp o).1;rw[<- f8,dP];refine fh (fun b _=>b/q) ?_ ?_ ?_ ?_
   ·intro b A;rw[dB]at A;have i:=(d5 p b).mp A.1;have D:q∣b:=dS A.2;have e:1<=b/q:=ia (el i.1 D) d.pos;have E:b=q*(b/q):=(eC D).symm;refine dB.mpr ⟨(d5 p (b/q)).mpr ⟨e,i.2.1.squarefree_of_dvd ⟨q,by rw[e8,<- E]⟩,fun r T=>i.2.2 r (k9 ⟨q,by rw[e8,<- E]⟩ _O T)⟩,?_⟩
    intro h5;have U:q*q∣b:=(by rw[E];exact mul_dvd_mul_left q h5);exact d.ne_one (mn.mp (i.2.1 q U))
   ·intro b1 G b2 M h6;rw[dB]at G M;rw[<- eC (dS G.2),<- eC (dS M.2),h6]
   ·intro c F;rw[dB]at F;have l:=(d5 p c).mp F.1;have N:Nat.Coprime q c:=d.coprime_iff_not_dvd.mpr F.2;refine⟨q*c,dB.mpr ⟨(d5 p (q*c)).mpr
     ⟨fP d.pos l.1,(Nat.squarefree_mul N).mpr ⟨d.squarefree,l.2.1⟩,fun r T=>?_⟩,
     md.mpr ⟨d,ir q c,(fP d.pos l.1).ne'⟩⟩,gb c d.pos⟩
    rw[jh d.ne_zero _O,ff]at T;rcases T with hr1 | hr2
    ·rw[d.primeFactors,eg]at hr1;omega
    ·exact l.2.2 r hr2
   ·intro b A;rw[dB]at A;have i:=(d5 p b).mp A.1;have D:q∣b:=dS A.2;have e:1<=b/q:=ia (el i.1 D) d.pos;have E:b=q*(b/q):=(eC D).symm;conv_lhs=>rw[E]
    rw[g3,log_mul (_M d.ne_zero) (_M (_O :b/q≠0))];ring
  have u:∀x y:O,0<=x->0<=y->(x+y)^m<=(2:O)^m*(x^m+y^m):=by
   intro x y hx hy;have G:x+y<=2*max x y:=(by linarith[eo x y,ep x y]);have M:=m9 _L G m;rw[eP]at M;rcases le_total x y with hxy | hyx
   ·rw[jU hxy]at M;have:0<=x^m:=fK hx m;nlinarith[fK (_N :(0:O)<=2) m]
   ·rw[lj hyx]at M;have:0<=y^m:=fK hy m;nlinarith[fK (_N :(0:O)<=2) m]
  have v:∀q∈dv p,∑c∈(cV p).filter (fun c=>¬ q∣c),L (q*c)*(log (q:O)+log (c:O))^m/(c:O) <=(2:O)^(m+1)*((log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)) +∑c∈cV p,L c*(log (c:O))^m/(c:O)):=by
   intro q o;have d:=(e7.mp o).2;have C:(q:O)<=max 4 (p:O):=gf (_M (e7.mp o).1) (ep _ _);have j:0<=log (q:O):=f1 (_M d.one_lt.le);have w:log (q:O)<=log (max 4 (p:O)):=dM (_M d.pos) C
   calc _<=∑c∈(cV p).filter (fun c=>¬ q∣c),
           (2:O)^(m+1)*((log (max 4 (p:O)))^m*(L c/(c:O)) +L c*(log (c:O))^m/(c:O)):=by
         refine dG fun c F=>?_
         rw[dB]at F;have e:1<=c:=((d5 _ _).mp F.1).1;have W:L (q*c)<=2*L c:=bQ d F.2;have z:0<=log (c:O):=f1 (_M e);have X:=u (log (q:O)) (log (c:O)) j z;have h8:(log (q:O))^m<=(log (max 4 (p:O)))^m:=m9 j w m
         have P:L (q*c)*(log (q:O)+log (c:O))^m <=(2:O)^(m+1)*((log (max 4 (p:O)))^m*L c+L c*(log (c:O))^m):=by
           calc L (q*c)*(log (q:O)+log (c:O))^m
               <= (2*L c)*((2:O)^m*((log (q:O))^m+(log (c:O))^m)):=en W X _P (ek _N (bK c))
             _<=(2*L c)*((2:O)^m*((log (max 4 (p:O)))^m+(log (c:O))^m)):=by have:=bK c;gcongr
             _=_:=by rw[fp];ring
         calc L (q*c)*(log (q:O)+log (c:O))^m/(c:O)
             <= (2:O)^(m+1)*((log (max 4 (p:O)))^m*L c+L c*(log (c:O))^m)/(c:O):=dI P (dK c)
           _=_:=by ring
     _<=∑c∈cV p,(2:O)^(m+1)*((log (max 4 (p:O)))^m*(L c/(c:O)) +L c*(log (c:O))^m/(c:O)):=dC (fj _ _) fun c F _=>by
           have:=bK c
           have:0<=log (c:O):=f1 (_M ((d5 _ _).mp F).1)
           positivity
     _=(2:O)^(m+1)*((log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)) +∑c∈cV p,L c*(log (c:O))^m/(c:O)):=by rw[<- dP,fD,<- dP]
  have H:∑q∈dv p,log (q:O)/(q:O)<=2*log (max 4 (p:O)):=by
   by_cases h7:p=0
   ·subst h7;have h4:0<=log 4:=f1 _N;simp[dv];linarith
   ·have G:=aj p _O;have M:log (p:O)<=log (max 4 (p:O)):=dM _P (ep _ _);have h3:log 4<=log (max 4 (p:O)):=dM _N (eo _ _);linarith
  rw[J]
  calc ∑q∈dv p,(log (q:O)/(q:O)) *
          ∑c∈(cV p).filter (fun c=>¬ q∣c),L (q*c)*(log (q:O)+log (c:O))^m/(c:O)
      <= ∑q∈dv p,(log (q:O)/(q:O)) *((2:O)^(m+1)*((log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)) +∑c∈cV p,L c*(log (c:O))^m/(c:O))):=dG fun q o=>dA (v q o) (ed (f1 (_M (e7.mp o).2.one_lt.le)) (dK q))
    _=(∑q∈dv p,log (q:O)/(q:O)) *((2:O)^(m+1)*((log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)) +∑c∈cV p,L c*(log (c:O))^m/(c:O))):=(jn ..).symm
    _<=(2*log (max 4 (p:O))) *((2:O)^(m+1)*((log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)) +Cm*(log (max 4 (p:O)))^m*(∑c∈cV p,L c/(c:O)))):=by
        have Z:0<=∑c∈cV p,L c*(log (c:O))^m/(c:O):=ea fun c F=>by
            have:=bK c
            have:0<=log (c:O):=f1 (_M ((d5 _ _).mp F).1)
            positivity
        exact en H (dA (fd eR (h0 p)) _P)
          _P _P
    _=2^(m+2)*(1+Cm)*(log (max 4 (p:O)))^(m+1)*∑b∈cV p,L b/(b:O):=by rw[fc,fc];ring
set_option maxHeartbeats 800000 in
lemma dk :
 ∃C22:O,0< C22/\∀t:ℕ,16<=t -> d8 t<=C22/(log (t:O))^2*∑a∈cV t,L a/(a:O):=by
 classical
 obtain⟨E,hj,hD⟩:=dj 3;refine⟨16+256*E,by positivity,?_⟩
 intro t ht;have e:0< log (t:O):=et (_M (_O :1< t));have hk:0<=∑a∈cV t,L a/(a:O):=ea fun a _=>ed (bK a) (dK a);let F:Finset ℕ:=(cV t).filter fun (a:ℕ)=>(t:O)< (a:O)^2/\(cW a:O)^4<=(t:O);let P2:Finset ℕ:=(cV t) \ F;have H:d8 t =(∑a∈F,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2)) +(∑a∈P2,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2)):=by unfold d8;rw[<- sum_sdiff (s₁:=F) (s₂:=cV t) (fj _ _),ip]
 have J:∑a∈P2,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=16/(log (t:O))^2*∑a∈cV t,L a/(a:O):=by
  have m:∀a∈P2,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=(16/(log (t:O))^2)*(L a/(a:O)):=by
   intro a v;rw[gj]at v;have d:(0:O)< (a:O):=_M ((d5 _ _).mp v.1).1;have A:log (t:O)/4<=log (max 4 (max (cW a:O) ((t:O)/(a:O)))):=by
    have hl:0< max (4:O) (max (cW a:O) ((t:O)/(a:O))):=e9 _N (eo _ _);have h3:(t:O)<=(max (4:O) (max (cW a:O) ((t:O)/(a:O))))^4:=by
     simp only[F,dB,not_and]at v;by_cases M:(a:O)^2<=(t:O)
     ·have hI:(t:O)<=((t:O)/(a:O))^2:=by
       rw[ij,ma (iN d 2)];nlinarith[show (0:O)< (t:O) by positivity]
      have hc:(t:O)<=((t:O)/(a:O))^4:=by
       have l:(1:O)<=((t:O)/(a:O))^2:=_l (show (1:O)<=(t:O) by exact_mod_cast (_O :1<=t))
       have:((t:O)/(a:O))^4=(((t:O)/(a:O))^2)^2:=_R
       rw[this];nlinarith
      exact hc.trans (m9 _P ((ep _ _).trans (ep _ _)) 4)
     ·push Not at M
      have ho:(t:O)< (cW a:O)^4:=(by have:=v.2 v.1 M;linarith);exact ho.le.trans (m9 _P ((eo _ _).trans (ep _ _)) 4)
    have l:=dM _P h3;rw[fm]at l;linarith
   have hr:(log (t:O))^2/16<=(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2:=(by have:=m9 _P A 2;linarith);have l:L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=L a/((a:O)*((log (t:O))^2/16)):=dL (bK a) _P (dA hr d.le);exact l.trans_eq (by ring)
  calc _<=∑a∈P2,(16/(log (t:O))^2)*(L a/(a:O)):=dG m
    _<=∑a∈cV t,(16/(log (t:O))^2)*(L a/(a:O)):=dC Finset.sdiff_subset fun a _ _=>
          ek _P (ed (bK a) (dK a))
    _=_:=(dP ..).symm
 have K:∑a∈F,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=256*E/(log (t:O))^2*∑a∈cV t,L a/(a:O):=by
  let Q:Finset ℕ:=(dv t).filter fun (p:ℕ)=>(p:O)^4<=(t:O);have w:F⊆Q.biUnion fun p=>
   ((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image fun b=>p*b:=by
   intro a v;rw[dB]at v;have o:=(d5 t a).mp v.1;have M:2<=a:=by by_contra l;push Not at l;have hs:a=1:=_O;subst hs;norm_num at v;omega
   set p:=cW a;have j:=cX M;have i:p<=t:=o.2.2 p (md.mpr ⟨j.1,j.2,_O⟩);have z:p∈Q:=dB.mpr ⟨e7.mpr ⟨i,j.1⟩,v.2.2⟩;let b:=a/p;have B:a=p*b:=(eC j.2).symm;have u:1<=b:=ia (el o.1 j.2) j.1.pos;have he:b∈cV p:=by
    rw[d5];refine⟨u,o.2.1.squarefree_of_dvd ⟨p,by rw[e8,<- B]⟩,fun q hq=>?_⟩
    exact cY (k9 ⟨p,by rw[e8,<- B]⟩ _O hq)
   have hv:¬ p∣b:=fun hd=>j.1.ne_one (mn.mp (o.2.1 p (by rw[B];exact mul_dvd_mul_left p hd)));have hw:(t:O)< (b:O)^4:=(by have l:(t:O)^2< (a:O)^4:=(by nlinarith[v.2.1,show (0:O)< (t:O) by positivity]);have X:(a:O)^4=(p:O)^4*(b:O)^4:=(by rw[B];push_cast;ring);rw[X]at l;nlinarith[v.2.2,show (0:O)< (t:O) by positivity,show (0:O)< (b:O)^4 by positivity]);exact g4.mpr ⟨p,z,dW.mpr ⟨b,dB.mpr ⟨he,hv,hw⟩,B.symm⟩⟩
  have N:∑a∈F,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=∑p∈Q,∑b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),L (p*b)/(((p*b:ℕ):O)*(log (max 4 (p:O)))^2):=by
   have h5:∀a∈F,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2) <=L a/((a:O)*(log (max 4 (cW a:O)))^2):=(by intro a v;have d:(0:O)< (a:O):=_M ((d5 _ _).mp (dB.mp v).1).1;have C:log (max 4 (cW a:O))<=log (max 4 (max (cW a:O) ((t:O)/(a:O)))):=dM _P (max_le_max_left 4 (eo _ _));have h6:0< log (max 4 (cW a:O)):=et (e9 _N (eo _ _));exact dL (bK a) _P (dA (m9 h6.le C 2) d.le));have hx:∀p∈Q,∀b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),cW (p*b)=p:=by
    intro p j b G;have c:=(e7.mp (dB.mp j).1).2;have Z:=(d5 p b).mp (dB.mp G).1;have hf:2<=p*b:=(by have:=c.two_le;have:=Z.1;nlinarith);have hE:p<=cW (p*b):=cY (md.mpr ⟨c,ir p b,_O⟩);have hF:cW (p*b)<=p:=by
     have hm:=cX hf;have h0:cW (p*b)∈(p*b).primeFactors:=md.mpr ⟨hm.1,hm.2,_O⟩;rw[jh c.ne_zero _O,ff]at h0;rcases h0 with l | X
     ·rw[c.primeFactors,eg]at l;omega
     ·exact Z.2.2 _ X
    omega
   calc _<=∑a∈F,L a/((a:O)*(log (max 4 (cW a:O)))^2):=dG h5
     _<=∑a∈Q.biUnion (fun p=>((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image fun b=>p*b),L a/((a:O)*(log (max 4 (cW a:O)))^2):=dC w fun a _ _=>ed (bK a) _P
     _<=∑p∈Q,∑a∈((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image (fun b=>p*b),L a/((a:O)*(log (max 4 (cW a:O)))^2):=by
         have hg:∀S:Finset ℕ,∑a∈S.biUnion (fun p=>((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image fun b=>p*b),L a/((a:O)*(log (max 4 (cW a:O)))^2) <=∑p∈S,∑a∈((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image (fun b=>p*b),L a/((a:O)*(log (max 4 (cW a:O)))^2):=by
           intro S;induction S using eW with
           | empty=>simp
           | @insert y S hy ih=>
             rw[iS,i3 hy];let s1:=((cV y).filter fun b=>¬ y∣b/\(t:O)< (b:O)^4).image (fun b=>y*b);let s2:=S.biUnion fun p=>((cV p).filter fun b=>¬ p∣b/\(t:O)< (b:O)^4).image fun b=>p*b;have hu:=fb (f:=fun a=>L a/((a:O)*(log (max 4 (cW a:O)))^2)) (s₁:=s1) (s₂:=s2);have hz:0<=∑a∈s1∩s2,L a/((a:O)*(log (max 4 (cW a:O)))^2):=ea fun a _=>ed (bK a) _P;dsimp only[s1,s2]at hu hz;linarith
         exact hg Q
     _<=∑p∈Q,∑b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),L (p*b)/(((p*b:ℕ):O)*(log (max 4 (p:O)))^2):=by
         refine dG fun p j=>?_
         have h7:p≠0:=(e7.mp (dB.mp j).1).2.ne_zero;rw[fr (fun _ _ _ _ h=>mul_left_cancel₀ h7 h)];exact le_of_eq (dF rfl fun b G=>by rw[hx p j b G])
  have P:∀p∈Q,∑b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),L (p*b)/(((p*b:ℕ):O)*(log (max 4 (p:O)))^2) <=(128*E/(log (t:O))^3)*(log (max 4 (p:O))/(p:O)) *∑a∈cV t,L a/(a:O):=by
   intro p j;have c:=(e7.mp (dB.mp j).1).2;have i:=(e7.mp (dB.mp j).1).1;have R:0< log (max 4 (p:O)):=et (e9 _N (eo _ _));have m:∀b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),L (p*b)/(((p*b:ℕ):O)*(log (max 4 (p:O)))^2) <=(128/((p:O)*(log (max 4 (p:O)))^2*(log (t:O))^3)) *(L b*(log (b:O))^3/(b:O)):=by
    intro b G;rw[dB]at G;have u:(0:O)< (b:O):=_M ((d5 _ _).mp G.1).1;have h8:log (t:O)/4<=log (b:O):=by have l:=dM _P G.2.2.le;rw[fm]at l;push_cast at l;linarith
    have hA:(log (t:O))^3/64<=(log (b:O))^3:=(by have:=m9 _P h8 3;linarith);have hB:L (p*b)<=2*L b:=bQ c G.2.1;have l:L (p*b)<=(128/(log (t:O))^3)*(L b*(log (b:O))^3):=by
     have hC:1<=64*(log (b:O))^3/(log (t:O))^3:=by rw[js _P];linarith
     calc L (p*b)<=2*L b:=hB
       _<=(2*L b)*(64*(log (b:O))^3/(log (t:O))^3):=jZ (ek _N (bK b)) hC
       _=_:=by ring
    calc L (p*b)/(((p*b:ℕ):O)*(log (max 4 (p:O)))^2)
        <= ((128/(log (t:O))^3)*(L b*(log (b:O))^3)) /(((p:O)*(b:O))*(log (max 4 (p:O)))^2):=by rw[g3];exact dI l _P
      _=_:=by ring
   have T:∑b∈cV p,L b/(b:O)<=∑a∈cV t,L a/(a:O):=dC (d6 i) fun a _ _=>ed (bK a) (dK a)
   calc _<=∑b∈(cV p).filter (fun b=>¬ p∣b/\(t:O)< (b:O)^4),
           (128/((p:O)*(log (max 4 (p:O)))^2*(log (t:O))^3)) *(L b*(log (b:O))^3/(b:O)):=dG m
     _<=∑b∈cV p,(128/((p:O)*(log (max 4 (p:O)))^2*(log (t:O))^3)) *(L b*(log (b:O))^3/(b:O)):=dC (fj _ _) fun b G _=>by
           have:=bK b
           have:0<=log (b:O):=f1 (_M ((d5 _ _).mp G).1)
           positivity
     _=(128/((p:O)*(log (max 4 (p:O)))^2*(log (t:O))^3)) *∑b∈cV p,L b*(log (b:O))^3/(b:O):=(dP ..).symm
     _<=(128/((p:O)*(log (max 4 (p:O)))^2*(log (t:O))^3)) *(E*(log (max 4 (p:O)))^3*∑a∈cV t,L a/(a:O)):=dA ((hD p).trans (dA T _P)) _P
     _=(128*E/(log (t:O))^3)*(log (max 4 (p:O))/(p:O)) *∑a∈cV t,L a/(a:O):=by field_simp [R.ne',e.ne',(show (p:O)≠0 by exact_mod_cast c.ne_zero)]
  have U:∑p∈Q,log (max 4 (p:O))/(p:O)<=2*log (t:O):=by
   have D:∀p∈Q,log (max 4 (p:O))/(p:O) <=log (p:O)/(p:O)+if p< 4 then log 4/(p:O) else 0:=by
    intro p j;have c:=(e7.mp (dB.mp j).1).2;by_cases h4:p< 4
    ·rw[iM h4,lj (_M h4.le)];have:0<=log (p:O)/(p:O):=ed (f1 (_M c.one_lt.le)) (dK p);linarith
    ·push Not at h4
     rw[gc _O,i0,jU (_M h4)]
   have W:∑p∈Q,(if p< 4 then log 4/(p:O) else 0)<=log 4:=by
    rw[<- f8];have hh:Q.filter (·< 4)⊆{2,3}:=by intro p j;rw[dB]at j;have X:=(e7.mp (dB.mp j.1).1).2.two_le;simp only[ga,eg];omega
    calc ∑p∈Q.filter (·< 4),log 4/(p:O)
        <= ∑p∈({2,3}:Finset ℕ),log 4/(p:O):=dC hh fun _ _ _=>_P
      _=log 4*(1/2+1/3):=by norm_num;ring
      _<=log 4:=by linarith[et (_N :(1:O)< 4)]
   have h9:∑p∈Q,log (p:O)/(p:O)<=log (t:O)+log 4:=by
    refine (dC (fj _ _) fun p j _=>
     ed (f1 (_M (e7.mp j).2.one_lt.le)) (dK p)).trans ?_
    exact aj t _O
   have hn:2*log 4<=log (t:O):=by have l:(4:O)^2<=(t:O):=_M (_O :16<=t);have X:=dM _N l;rw[fm]at X;push_cast at X;exact X
   calc ∑p∈Q,log (max 4 (p:O))/(p:O)
       <= ∑p∈Q,(log (p:O)/(p:O)+if p< 4 then log 4/(p:O) else 0):=dG D
     _=(∑p∈Q,log (p:O)/(p:O))+∑p∈Q,(if p< 4 then log 4/(p:O) else 0):=fD
     _<=(log (t:O)+log 4)+log 4:=fd h9 W
     _<=2*log (t:O):=_L
  calc _<=∑p∈Q,(128*E/(log (t:O))^3)*(log (max 4 (p:O))/(p:O)) *
            ∑a∈cV t,L a/(a:O):=N.trans (dG P)
    _=((128*E/(log (t:O))^3)*∑a∈cV t,L a/(a:O)) *∑p∈Q,log (max 4 (p:O))/(p:O):=by rw[dP];refine dF rfl fun p _=>_R
    _<=((128*E/(log (t:O))^3)*∑a∈cV t,L a/(a:O))*(2*log (t:O)):=dA U _P
    _=256*E/(log (t:O))^2*∑a∈cV t,L a/(a:O):=by field_simp [e.ne'];ring
 rw[H]
 calc (∑a∈F,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2)) +
       (∑a∈P2,L a/((a:O)*(log (max 4 (max (cW a:O) ((t:O)/(a:O)))))^2))
     <= (256*E/(log (t:O))^2*∑a∈cV t,L a/(a:O)) +(16/(log (t:O))^2*∑a∈cV t,L a/(a:O)):=fd K J
   _=(16+256*E)/(log (t:O))^2*∑a∈cV t,L a/(a:O):=_R
def dl (P k:ℕ):O:=∑a∈(cV P).filter (fun a=>a.primeFactors.card=k),L a/(a:O)
set_option maxHeartbeats 800000 in
lemma dm (D:Finset ℕ) (G:∀p∈D,1<=p) (k:ℕ) :
 ∑T∈D.powersetCard k,(1:O)/((∏p∈T,p:ℕ):O) <=(∑p∈D,(1:O)/(p:O))^k/(k.factorial:O):=by
 classical
 let c:=(Fintype.piFinset fun _:Fin k=>D).filter Function.Injective;have q:(k.factorial:O)*∑T∈D.powersetCard k,(1:O)/((∏p∈T,p:ℕ):O) =∑f∈c,∏i:Fin k,(1:O)/(f i:O):=by
  rw[dP];have j:c=(D.powersetCard k).biUnion fun T=>c.filter fun f=>univ.image f=T:=by
   ext f;simp only[g4,dB,fU];constructor
   ·intro d;refine⟨univ.image f,⟨fun x v=>?_,?_⟩,d,rfl⟩
    ·rcases dW.mp v with⟨i,_,rfl⟩;exact (e5.mp (dB.mp d).1) i
    ·rw[fs _ (dB.mp d).2,j5,fH]
   ·rintro⟨_,_,d,_⟩;exact d
  rw[j,kh]
  ·refine dF rfl fun T y=>?_
   rw[fU]at y;have b:(c.filter fun f=>univ.image f=T).card=k.factorial:=by
    have m:Fintype.card (Fin k)=Fintype.card T:=(by simp[jO,y.2]);have l:(univ:Finset (Fin k ≃ T)).card=k.factorial:=(by rw[j5,Fintype.card_equiv (Fintype.equivOfCardEq m),fH]);rw[<- l];symm;refine hO (fun (e:Fin k ≃ T) _=>fun i=>(e i).1) ?_ ?_ ?_
    ·intro e _;refine dB.mpr ⟨dB.mpr ⟨e5.mpr fun i=>y.1 (e i).2,fun z A h=>e.injective (i9 h)⟩,?_⟩;ext x;simp only[dW,dJ,dV];constructor
     ·rintro⟨i,rfl⟩;exact (e i).2
     ·intro v;exact⟨e.symm ⟨x,v⟩,by simp⟩
    ·intro B _ C _ h;apply Equiv.ext;intro i;exact i9 (gH h i)
    ·intro f d;rw[dB,dB]at d;let e:Fin k ≃ T:=Equiv.ofBijective (fun i=>⟨f i,by rw[<- d.2];exact iL f (dJ i)⟩) ((ke _).mpr ⟨fun z A h=>d.1.2 (fT Subtype.val h),m⟩)
     exact⟨e,dJ _,rfl⟩
   have o:∀f∈c.filter (fun f=>univ.image f=T),∏i:Fin k,(1:O)/(f i:O)=(1:O)/((∏p∈T,p:ℕ):O):=(by intro f d;rw[dB,dB]at d;rw[<- d.2,jR (fun _ _ _ _ h=>d.1.2 h),fu,g9,<- gL];exact f9 rfl fun i _=>g9 _);rw[dF rfl o,ex,b,e3]
  ·intro E _ F _ w;dsimp only[Function.onFun];rw[eb];intro f q u;exact w ((dB.mp q).2.symm.trans (dB.mp u).2)
 have u:∑f∈c,∏i:Fin k,(1:O)/(f i:O)<=(∑p∈D,(1:O)/(p:O))^k:=by
  calc _<=∑f∈Fintype.piFinset (fun _:Fin k=>D),∏i:Fin k,(1:O)/(f i:O):=
        dC (fj _ _) fun _ _ _=>prod_nonneg fun _ _=>_P
    _=∏_i:Fin k,∑p∈D,(1:O)/(p:O):=(j9 (t:=fun _:Fin k=>D) (f:=fun (_:Fin k) (p:ℕ)=>(1:O)/(p:O))).symm
    _=(∑p∈D,(1:O)/(p:O))^k:=by simp
 rw[ma _P,e8,q];exact u
def dn (k1 k2:ℕ) :
 (Fin (k1+k2)->O) ≃ᵐ (Fin k1->O) × (Fin k2->O) where
 toFun ξ:=(fun i=>ξ (Fin.castAdd k2 i),fun j=>ξ (Fin.natAdd k1 j))
 invFun p i:=if h:i.1< k1 then p.1 ⟨i.1,h⟩ else p.2 ⟨i.1-k1,_O⟩
 left_inv ξ:=by
  funext i;dsimp only;split_ifs with h
  ·congr 1
  ·congr 1;exact dQ (by dsimp only[Fin.natAdd];omega)
 right_inv p:=by
  ext i
  ·dsimp only[Fin.castAdd,Fin.castLE];rw[eG i.2]
  ·dsimp only[Fin.natAdd];rw[eA _O];exact congrArg p.2 (dQ (by dsimp only;omega))
 measurable_toFun:=(eU _ fun i=>dO _).prodMk (eU _ fun j=>dO _)
 measurable_invFun:=by
  refine eU _ fun i=>?_
  simp only[g8];split_ifs with h
  ·exact (dO _).comp lI
  ·exact (dO _).comp iR
lemma dp (k1 k2:ℕ) :
 MeasurePreserving (dn k1 k2) volume volume:=by
 have c:MeasurePreserving (dn k1 k2).symm (volume.prod volume) volume:=by
  refine⟨(dn k1 k2).symm.measurable,?_⟩
  symm;refine lY fun s m=>?_
  rw[l3 (dn k1 k2).symm.measurable (ka m)];have e:(dn k1 k2).symm ⁻¹' Set.univ.pi s =(Set.univ.pi fun i:Fin k1=>s (Fin.castAdd k2 i)) ×ˢ (Set.univ.pi fun j:Fin k2=>s (Fin.natAdd k1 j)):=by
   ext ⟨x,y⟩;simp only[eL,lr,il];constructor
   ·intro h;refine⟨fun i=>?_,fun j=>?_⟩
    ·have b:=h (Fin.castAdd k2 i);change (if hi:(Fin.castAdd k2 i).1< k1 then x ⟨(Fin.castAdd k2 i).1,hi⟩ else y ⟨(Fin.castAdd k2 i).1-k1,_O⟩)∈_ at b;dsimp only[Fin.castAdd,Fin.castLE]at b;rwa[eG i.2]at b
    ·have b:=h (Fin.natAdd k1 j);change (if hi:(Fin.natAdd k1 j).1< k1 then x ⟨(Fin.natAdd k1 j).1,hi⟩ else y ⟨(Fin.natAdd k1 j).1-k1,_O⟩)∈_ at b;dsimp only[Fin.natAdd]at b;rw[eA _O]at b;have l:(⟨k1+j.1-k1,_O⟩:Fin k2)=j:=dQ (by dsimp only;omega);rw[l]at b;exact b
   ·rintro⟨hx,hy⟩ i;change (if hi:i.1< k1 then x ⟨i.1,hi⟩ else y ⟨i.1-k1,_O⟩)∈s i;split_ifs with h
    ·exact hx ⟨i.1,h⟩
    ·have:=hy ⟨i.1-k1,_O⟩
     convert this using 2;exact dQ (by dsimp only[Fin.natAdd];omega)
  rw[e,f5];change (Measure.pi fun _:Fin k1=>(volume:Measure O)) _ *(Measure.pi fun _:Fin k2=>(volume:Measure O)) _=_;rw[gV,gV];have d:(∏i:Fin (k1+k2),volume (s i)) =(∏i:Fin k1,volume (s (Fin.castAdd k2 i)))*(∏j:Fin k2,volume (s (Fin.natAdd k1 j))):=Fin.prod_univ_add (fun i=>volume (s i));exact d.symm
 exact c.symm (dn k1 k2).symm
lemma dq {k:ℕ} (i:Fin k) (c:O) :
 volume {ξ : Fin k->O | ξ i=c}=0:=by
 have d:MeasurableSet {ξ : Fin k->O | ξ i=c}:=measurableSet_eq_fun (dO i) eV;rw[cz i _ d];have b:(cv i).symm ⁻¹' {ξ : Fin k->O | ξ i=c} =({c}:Set O)×ˢ((Set.univ:Set (Fin i.1->O))×ˢ(Set.univ:Set (Fin (k-1 - i.1)->O))):=by ext ⟨x,y,z⟩;simp only[eL,eM,il,Set.mem_singleton_iff,Set.mem_univ,and_true];change (if h1:i.1< i.1 then y ⟨i.1,h1⟩ else if h2:i.1=i.1 then x else z ⟨i.1-i.1-1,_O⟩)=c↔x=c;rw[eA (gU _),eG rfl]
 rw[b];change (volume.prod volume) _=0;rw[f5,Real.volume_singleton,kP]
set_option maxHeartbeats 800000 in
lemma dr (M:ℕ) (hM:1<=M) :
 ∀(r:ℕ) (_hr:r<=M) (k:ℕ) (j:Fin k->Fin M),Monotone j->(∀i:Fin k,(j i).1< r) -> volume {ξ : Fin k->O | (∀i:Fin k,((j i).1:O)/(M:O)<=ξ i/\ξ i<=(((j i).1+1:ℕ):O)/(M:O))/\Monotone ξ} =ENNReal.ofReal (1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O))):=by
 intro r hr;induction r with
 | zero=>
  intro k j _ hk;have he:k=0:=(by by_contra h;have:=hk ⟨0,fX h⟩;omega);subst he;have W:{ξ : Fin 0->O | (∀i:Fin 0,((j i).1:O)/(M:O)<=ξ i/\ξ i<=(((j i).1+1:ℕ):O)/(M:O))/\Monotone ξ} =cr 0 0 1:=(by ext ξ;simp[cr,Monotone]);rw[W,ct 0 0 1 eO];simp[Nat.factorial]
 | succ r ih=>
  intro k j y w;let c:=(univ.filter fun i:Fin k=>(j i).1< r).card;let A:=(univ.filter fun i:Fin k=>(j i).1=r).card;have K:c+A=k:=by have X:Disjoint (univ.filter fun i:Fin k=>(j i).1< r) (univ.filter fun i:Fin k=>(j i).1=r):=(by rw[eb];intro i U T;simp only[dB]at U T;omega);have R:(univ.filter fun i:Fin k=>(j i).1< r) ∪ (univ.filter fun i:Fin k=>(j i).1=r)=univ:=(by ext i;simp only[ff,dB,dJ,dV,iff_true];have:=w i;omega);rw[<- card_union_of_disjoint X,R,j5,fH]
  have D:∀i:Fin k,(j i).1< r↔i.1< c:=by
   have h9:univ.filter (fun i:Fin k=>(j i).1< r)=univ.filter (fun i:Fin k=>i.1< c):=by
    by_contra hd;have Z:∀a b:Fin k,a<=b->b∈univ.filter (fun i:Fin k=>(j i).1< r) -> a∈univ.filter (fun i:Fin k=>(j i).1< r):=by intro a b u Q;simp only[dB,dJ,dV]at Q ⊢;exact gJ (y u) Q
    have h0:univ.filter (fun i:Fin k=>(j i).1< r)⊆univ.filter (fun i:Fin k=>i.1< c):=by
     intro i hi;simp only[dB,dJ,dV];by_contra hl;push Not at hl;have N:univ.filter (fun t:Fin k=>t.1<=i.1)⊆univ.filter (fun t:Fin k=>(j t).1< r):=fun t ht=>Z t i (mh.mpr (dB.mp ht).2) hi;have E:(univ.filter (fun t:Fin k=>t.1<=i.1)).card=i.1+1:=by
      conv_rhs=>rw[<- fy (i.1+1)]
      exact hO (fun (t:Fin k) _=>t.1) (fun t ht=>by simp only[dB,dJ,dV]at ht;rw[dN];omega) (fun _ _ _ _ h=>dQ h)
       (fun m z=>⟨⟨m,by rw[dN]at z;have:=i.2;omega⟩,by rw[dN]at z;simp only[dB,dJ,dV];omega,rfl⟩)
     have:=er N
     rw[E]at this;omega
    have S:(univ.filter (fun i:Fin k=>i.1< c)).card=c:=by
     conv_rhs=>rw[<- fy c]
     exact hO (fun (t:Fin k) _=>t.1) (fun t ht=>by simp only[dB,dJ,dV]at ht;rw[dN];exact ht) (fun _ _ _ _ h=>dQ h)
      (fun m z=>⟨⟨m,by rw[dN]at z;omega⟩,by rw[dN]at z;simp only[dB,dJ,dV];exact z,rfl⟩)
    exact hd (m3 h0 (by rw[S]))
   intro i;have:=Finset.ext_iff.mp h9 i;simpa only[dB,dJ,dV] using this
  let F:Fin c->Fin M:=fun i=>j ⟨i.1,_O⟩;have G:Monotone F:=fun a b u=>y (mh.mpr u);have q:∀i:Fin c,(F i).1< r:=fun i=>(D ⟨i.1,_O⟩).mpr i.2;let S1:Set (Fin c->O):=
   {ξ | (∀i:Fin c,((F i).1:O)/(M:O)<=ξ i/\ξ i<=(((F i).1+1:ℕ):O)/(M:O))/\Monotone ξ}
  let S2:Set (Fin A->O):=cr A ((r:O)/(M:O)) (((r+1:ℕ):O)/(M:O));have H:MeasurableSet S1:=by
   have W:S1=(⋂ i:Fin c,{ξ : Fin c->O | ((F i).1:O)/(M:O)<=ξ i} ∩
    {ξ : Fin c->O | ξ i<=(((F i).1+1:ℕ):O)/(M:O)}) ∩
    (⋂ p:Fin c × Fin c,if p.1<=p.2 then {ξ : Fin c->O | ξ p.1<=ξ p.2} else Set.univ):=by
    ext ξ;simp only[S1,eM,kW,lK,Prod.forall,Monotone];constructor
    ·rintro⟨Q,z⟩;exact⟨Q,fun a b=>by split_ifs with h;exact z h;trivial⟩
    ·rintro⟨Q,z⟩;exact⟨Q,fun a b h=>by have:=z a b;rwa[iM h]at this⟩
   rw[W];refine (fI fun i=>(fV eV (dO i)).inter
    (fV (dO i) eV)).inter ?_
   refine fI fun p=>?_
   split_ifs
   ·exact fV (dO p.1) (dO p.2)
   ·exact kI
  let o:(Fin k->O) ≃ᵐ (Fin (c+A)->O):=MeasurableEquiv.piCongrLeft (fun _=>O) (finCongr K.symm);have B:MeasurePreserving o volume volume:=volume_measurePreserving_piCongrLeft (fun _=>O) (finCongr K.symm);let e:=o.trans (dn c A);have h3:MeasurePreserving e volume volume:=(dp c A).comp B;have hc:{ξ : Fin k->O | (∀i:Fin k,((j i).1:O)/(M:O)<=ξ i/\ξ i<=(((j i).1+1:ℕ):O)/(M:O))/\Monotone ξ} =e ⁻¹' (S1×ˢS2):=by
   ext ξ;simp only[eL,il,S1,S2,cr,eM,e,MeasurableEquiv.trans_apply];have d:∀i:Fin c,(dn c A (o ξ)).1 i=ξ ⟨i.1,_O⟩:=fun i=>by
    change o ξ (Fin.castAdd A i)=_;simp[o,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,finCongr];rfl
   have l:∀i:Fin A,(dn c A (o ξ)).2 i=ξ ⟨c+i.1,_O⟩:=fun i=>by
    change o ξ (Fin.natAdd c i)=_;simp[o,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,finCongr];rfl
   constructor
   ·rintro⟨Q,z⟩;refine⟨⟨fun i=>by rw[d i];exact Q ⟨i.1,_O⟩,fun a b u=>by rw[d a,d b];exact z (mh.mpr u)⟩,⟨fun i=>by
      rw[l i];have h4:(j ⟨c+i.1,_O⟩).1=r:=by have U:=w ⟨c+i.1,_O⟩;have T:¬ (j ⟨c+i.1,_O⟩).1< r:=(by rw[D];dsimp only;omega);omega
      have:=Q ⟨c+i.1,_O⟩
      rwa[h4]at this,
     fun a b u=>by rw[l a,l b];exact z (mh.mpr _O)⟩⟩
   ·rintro⟨⟨hb1,hm1⟩,⟨hb2,hm2⟩⟩;refine⟨fun i=>?_,fun a b u=>?_⟩
    ·by_cases hi:i.1< c
     ·have:=hb1 ⟨i.1,hi⟩;rwa[d]at this
     ·have h4:(j i).1=r:=by
       have U:=w i;have T:¬ (j i).1< r:=(by rw[D];omega);omega
      rw[h4];have:=hb2 ⟨i.1-c,_O⟩;rw[l]at this;have hf:(⟨c+(i.1-c),_O⟩:Fin k)=i:=dQ (by dsimp only;omega);rwa[hf]at this
    ·by_cases ha:a.1< c <;> by_cases Q':b.1< c
     ·have:=hm1 (mh.mpr u:(⟨a.1,ha⟩:Fin c)<=⟨b.1,Q'⟩)
      rwa[d,d]at this
     ·have U:=(hb1 ⟨a.1,ha⟩).2;rw[d]at U;have T:=(hb2 ⟨b.1-c,_O⟩).1;rw[l]at T;have h5:((F ⟨a.1,ha⟩).1+1:ℕ)<=r:=q ⟨a.1,ha⟩;have h6:(((F ⟨a.1,ha⟩).1+1:ℕ):O)/(M:O)<=(r:O)/(M:O):=dI (_M h5) (dK M);have h7:(⟨c+(b.1-c),_O⟩:Fin k)=b:=dQ (by dsimp only;omega);rw[h7]at T;exact (U.trans h6).trans T
     ·exfalso;have:a.1<=b.1:=u;omega
     ·have hg:(⟨a.1-c,_O⟩:Fin A)<=⟨b.1-c,_O⟩:=mh.mpr (by have:a.1<=b.1:=u;omega);have:=hm2 hg;rw[l,l]at this;have hh:(⟨c+(a.1-c),_O⟩:Fin k)=a:=dQ (by dsimp only;omega);have h7:(⟨c+(b.1-c),_O⟩:Fin k)=b:=dQ (by dsimp only;omega);rwa[hh,h7]at this
  rw[hc,h3.measure_preimage (H.prod (cs A _ _)).nullMeasurableSet];change (volume.prod volume) (S1×ˢS2)=_;rw[f5,ih _O c F G q,ct A ((r:O)/(M:O)) (((r+1:ℕ):O)/(M:O))
    (dI (by push_cast;linarith) (dK M))]
  rw[<- jx _P];congr 1;have h8:(((r+1:ℕ):O)/(M:O))-((r:O)/(M:O))=1/(M:O):=(by push_cast;ring);rw[h8,i6];have C:(∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O)) =(∏m:Fin M,((univ.filter fun i:Fin c=>F i=m).card.factorial:O))*(A.factorial:O):=by
   let v:Fin M:=⟨r,hr⟩;rw[<- gk univ _ (dJ v),<- gk univ _ (dJ v)];have P:(univ.filter fun i:Fin k=>j i=v).card=A:=(by congr 1;ext i;simp only[dB,dJ,dV,v,Fin.ext_iff]);have J:(univ.filter fun i:Fin c=>F i=v).card=0:=(by rw[mA,jl];intro i _;intro h;have:=q i;rw[h]at this;exact gU r this);have hj:∀m∈univ.erase v,(univ.filter fun i:Fin k=>j i=m).card =(univ.filter fun i:Fin c=>F i=m).card:=by
    intro m z;have hd:m.1≠r:=fun h=>(gS.mp z).1 (dQ h);by_cases hn:m.1< r
    ·refine hO (fun i hi=>⟨i.1,(D i).mp (by rw[(dB.mp hi).2];exact hn)⟩) (fun i hi=>by simp only[dB,dJ,dV]at hi ⊢;exact hi) (fun _ _ _ _ h=>dQ (es h)) (fun i hi=>⟨⟨i.1,_O⟩,by simp only[dB,dJ,dV]at hi ⊢;exact hi,dQ rfl⟩)
    ·have U:(univ.filter fun i:Fin k=>j i=m)=∅:=by
      rw[jl];intro i _ h;have:=w i;rw[h]at this;omega
     have T:(univ.filter fun i:Fin c=>F i=m)=∅:=(by rw[jl];intro i _ h;have:=q i;rw[h]at this;omega);simp[U,T]
   rw[P,J,Nat.factorial_zero,eF,gz,f9 rfl fun m z=>by rw[hj m z],e8]
  rw[C,<- K,ee];field_simp [(_P :(M:O)≠0)]
set_option maxHeartbeats 800000 in
lemma ds {P k:ℕ} (hP:3<=P)
 (HB:200<=⌊log (log (P:O))/log 2⌋₊)
 (HF:1<=k) (HC:k<=10*⌊log (log (P:O))/log 2⌋₊) :
 let v:=⌊log (log (P:O))/log 2⌋₊
 dl P k<=(2:O)^203*exp 1020*(2*log (log (P:O)))^k*cT k v:=by
 classical
 intro v;have l:0< log 2:=_l a3;have h9:(2:O)^v<=log (P:O):=by
  have H0:(v:O)*log 2<=log (log (P:O)):=by
   have A:(v:O)<=log (log (P:O))/log 2:=fC (by
     have Hv:exp 1<=(P:O):=(by linarith[gT,show (3:O)<=(P:O) by exact_mod_cast hP]);have A:1<=log (P:O):=(by rw[<- iu 1];exact dM (ez 1) Hv);exact ed (f1 A) l.le)
   exact (ma l).mp A
  have B:0< log (P:O):=et (_M (_O :1< P));have A:=me.mpr H0;rw[eX B,gg,eX _N]at A;exact A
 have G:0< log (log (P:O)):=by have A:(1:O)< (2:O)^v:=one_lt_pow₀ _N _O;exact et (e9 A h9)
 have Hg:log (P:O)< (2:O)^(v+1):=by have A:log (log (P:O))/log 2< (v:O)+1:=f6 _;have h2:log (log (P:O))< ((v+1:ℕ):O)*log 2:=(by push_cast;exact (mm l).mp A);have h3:=mF.mpr h2;have B:0< log (P:O):=et (_M (_O :1< P));rw[eX B,gg,eX _N]at h3;exact h3
 let M:ℕ:=v+102;have hq:1<=M:=_O;have D:P< az M:=by have A:=(aJ M _O).1;have hr:((M:ℤ)-100)=((v+2:ℕ):ℤ):=(by dsimp only[M];omega);rw[hr,fo]at A;have hs:log (P:O)< log (az M:O):=(by have h2:(2:O)^(v+1)< (2:O)^(v+2):=pow_lt_pow_right₀ _N _O;linarith);have hR:(P:O)< (az M:O):=(log_lt_log_iff _P (_M (aD M))).mp hs;exact_mod_cast hR
 have Q:∀p∈dv P,∃m:Fin M,p∈aA (m.1+1):=by
  intro p H;have Hh:=(e7.mp H).2;have K:=(e7.mp H).1;have hb:∃n:ℕ,p<=az n:=⟨M,K.trans D.le⟩;let n:=Nat.find hb;have R:p<=az n:=jF hb;have Hw:n<=M:=Nat.find_min' hb (K.trans D.le);have Hs:1<=n:=by by_contra h0;have:n=0:=_O;rw[this,az]at R;have:=Hh.two_le;omega
  have H1:az (n-1)< p:=(by by_contra hL;push Not at hL;exact jW hb (_O :n-1< n) hL);refine⟨⟨n-1,_O⟩,?_⟩;unfold aA;rw[gc _O,show n-1+1-1=n-1 by omega,show n-1+1=n by omega]
  exact dB.mpr ⟨fw.mpr ⟨H1,R⟩,Hh⟩
 let q (p:ℕ):Fin M:=
  if h:p∈dv P then (Q p h).choose else ⟨0,_O⟩
 have u:∀p∈dv P,p∈aA ((q p).1+1):=fun p H=>by
  dsimp only[q];rw[eG H];exact (Q p H).choose_spec
 have h4:∀p1∈dv P,∀p2∈dv P,p1<=p2->q p1<=q p2:=by intro p1 A p2 h2 hL;by_contra hY;push Not at hY;have H2:=u p1 A;have H3:=u p2 h2;unfold aA at H2 H3;rw[gc _O]at H2 H3;have Ht:az (q p1).1< p1:=(fw.mp (dB.mp H2).1).1;have Hu:p2<=az ((q p2).1+1):=(fw.mp (dB.mp H3).1).2;have Hi:az ((q p2).1+1)<=az (q p1).1:=aC.monotone (by have:(q p2).1< (q p1).1:=hY;omega);omega
 let J:Finset (Fin k->Fin M):=univ.filter Monotone;let d (a:ℕ):Fin k->Fin M:=fun i=>
  let ps:=a.primeFactors.sort (·<=·);if h:i.1< ps.length then q (ps.get ⟨i.1,h⟩) else ⟨0,_O⟩
 have hc:∀a∈(cV P).filter (fun a=>a.primeFactors.card=k),d a∈J:=by
  intro a Z;rw[dB]at Z;have w:=(d5 P a).mp Z.1;have F:(a.primeFactors.sort (·<=·)).length=k:=(by rw[lk];exact Z.2);refine dB.mpr ⟨dJ _,fun i1 i2 HA=>?_⟩;dsimp only[d];rw[eG _O,eG _O];have H4:(a.primeFactors.sort (·<=·)).get ⟨i1.1,_O⟩∈dv P:=by have hm:(a.primeFactors.sort (·<=·)).get ⟨i1.1,_O⟩∈a.primeFactors:=(iO (r:=(·<=·))).mp (jq _ _);exact e7.mpr ⟨w.2.2 _ hm,dD hm⟩
  have H5:(a.primeFactors.sort (·<=·)).get ⟨i2.1,_O⟩∈dv P:=(by have hm:(a.primeFactors.sort (·<=·)).get ⟨i2.1,_O⟩∈a.primeFactors:=(iO (r:=(·<=·))).mp (jq _ _);exact e7.mpr ⟨w.2.2 _ hm,dD hm⟩);have H6:=lW a.primeFactors (·<=·);have H7:(a.primeFactors.sort (·<=·)).get ⟨i1.1,_O⟩<=(a.primeFactors.sort (·<=·)).get ⟨i2.1,_O⟩:=by
   rcases eq_or_lt_of_le (show i1.1<=i2.1 from HA) with hC | hs
   ·exact le_of_eq (congrArg (a.primeFactors.sort (·<=·)).get (dQ hC))
   ·exact List.pairwise_iff_get.mp H6 ⟨i1.1,_O⟩ ⟨i2.1,_O⟩ hs
  exact h4 _ H4 _ H5 H7
 let o (j:Fin k->Fin M):O:=(range (k+1)).inf' ⟨0,dN.mpr (gO k)⟩ fun g=>
   (2:O)^(-(g:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(j i).1)
 have ht:∀a∈(cV P).filter (fun a=>a.primeFactors.card=k),L a<=(2:O)^101*(2:O)^k*o (d a):=by
  intro a Z;rw[dB]at Z;have w:=(d5 P a).mp Z.1;let ps:=a.primeFactors.sort (·<=·);have F:ps.length=k:=(by dsimp only[ps];rw[lk];exact Z.2);have hd:ps.prod=a:=by rw[<- d4 w.1 w.2.1];exact (sort_perm_toList a.primeFactors (·<=·)).prod_eq.trans (prod_toList a.primeFactors)
  have E:∀p∈ps,p.Prime:=fun p H=>dD ((iO (r:=fun x y:ℕ=>x<=y)).mp H);have hV:ps.Pairwise (·< ·):=((lW a.primeFactors (·<=·)).and (sort_nodup a.primeFactors (·<=·))).imp (fun h=>ib h.1 h.2);dsimp only[o];obtain⟨g,hg,hU⟩:=lU (⟨0,dN.mpr (gO k)⟩:(range (k+1)).Nonempty) (fun g:ℕ=>(2:O)^(-(g:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(d a i).1));rw[hU];rw[dN]at hg;have Hj:=bR ps E hV g _O;rw[hd,F]at Hj;have h5:log ((ps.take g).prod:O)+log 2 <=(2:O)^101*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(d a i).1):=by
   have he:∀g' ≤ k,log ((ps.take g').prod:O) =∑i∈univ.filter (fun i:Fin k=>i.1< g'),log ((ps.get ⟨i.1,_O⟩:ℕ):O):=by
    intro g' hg';induction g' with
    | zero=>
     have h0:univ.filter (fun i:Fin k=>i.1< 0)=∅:=(by ext i;simp);simp[h0]
    | succ m ih=>
     have H8:ps.take (m+1)=ps.take m ++ [ps.get ⟨m,_O⟩]:=List.take_succ_eq_append_getElem (_O :m< ps.length);have hf:(ps.take m).prod≠0:=List.prod_ne_zero fun h0=>(E 0 (kn h0)).ne_zero rfl;rw[H8,List.prod_append,List.prod_cons,List.prod_nil,fv,g3,log_mul (_M hf)
       (_M (E _ (jq _ _)).ne_zero),ih _O]
     have H9:univ.filter (fun i:Fin k=>i.1< m+1) =insert (⟨m,_O⟩:Fin k) (univ.filter (fun i:Fin k=>i.1< m)):=(by ext i;simp only[dB,dJ,dV,ga,Fin.ext_iff];omega);have hw:(⟨m,_O⟩:Fin k) ∉ univ.filter (fun i:Fin k=>i.1< m):=(by simp);rw[H9,i3 hw,ip]
   rw[he g _O];have h6:∀i∈univ.filter (fun i:Fin k=>i.1< g),log ((ps.get ⟨i.1,_O⟩:ℕ):O)<=(2:O)^101*(2:O)^(d a i).1:=by
    intro i _;have hx:ps.get ⟨i.1,_O⟩∈a.primeFactors:=(iO (·<=·)).mp (jq _ _);have hy:ps.get ⟨i.1,_O⟩∈dv P:=e7.mpr ⟨w.2.2 _ hx,dD hx⟩;have hD:=u _ hy;unfold aA at hD;rw[gc _O]at hD;have K:ps.get ⟨i.1,_O⟩<=az ((q (ps.get ⟨i.1,_O⟩)).1+1):=(fw.mp (dB.mp hD).1).2;have hz:d a i=q (ps.get ⟨i.1,_O⟩):=by have F':(a.primeFactors.sort (·<=·)).length=k:=F;dsimp only[d,ps];rw[eG _O]
    rw[hz];have Ha:log ((ps.get ⟨i.1,_O⟩:ℕ):O)<=log (az ((q (ps.get ⟨i.1,_O⟩)).1+1):O):=dM (_M (E _ (jq _ _)).pos) (_M K);have hA:=(aJ ((q (ps.get ⟨i.1,_O⟩)).1+1) _O).2;have hr:((((q (ps.get ⟨i.1,_O⟩)).1+1:ℕ):ℤ)+100)=((101+(q (ps.get ⟨i.1,_O⟩)).1:ℕ):ℤ):=_O;rw[hr,fo,ee]at hA;exact Ha.trans hA
   have hB:=dG h6;rw[<- dP]at hB;have HE:log 2<=(2:O)^101:=(by linarith[a4,show (1:O)<=(2:O)^101 by norm_num]);linarith
  calc L a<=(2:O)^(k-g)*(log ((ps.take g).prod:O)+log 2):=Hj
    _<=(2:O)^(k-g)*((2:O)^101*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(d a i).1)):=dA h5 _P
    _=(2:O)^101*(2:O)^k*((2:O)^(-(g:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(d a i).1)):=by have Hk:(2:O)^(k-g)=(2:O)^k*(2:O)^(-(g:O)):=(by rw[lD _N,eK,<- ic,eq_div_iff _P,<- ee,eN _O]);rw[Hk];ring
 have hh:∀j∈J,∑a∈((cV P).filter (fun a=>a.primeFactors.card=k)).filter (fun a=>d a=j),(1:O)/(a:O) <=(log 2)^k/∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O):=by
  intro j hj;let b (m:Fin M):ℕ:=(univ.filter fun i:Fin k=>j i=m).card;have hW:∑m:Fin M,b m=k:=by have h:=card_eq_sum_card_fiberwise (s:=(univ:Finset (Fin k))) (t:=(univ:Finset (Fin M))) (f:=j) (fun _ _=>dJ _);simpa[b] using h.symm
  let U:=(Fintype.piFinset fun m:Fin M=>(aA (m.1+1)).powersetCard (b m)).image fun S=>∏m:Fin M,∏p∈S m,p;have hk:((cV P).filter (fun a=>a.primeFactors.card=k)).filter (fun a=>d a=j)⊆U:=by
   intro a Z;rw[dB,dB]at Z;have w:=(d5 P a).mp Z.1.1;let S:Fin M->Finset ℕ:=fun m=>a.primeFactors.filter fun p=>q p=m;refine dW.mpr ⟨S,e5.mpr fun m=>fU.mpr ⟨?_,?_⟩,?_⟩
   ·intro p H;rw[dB]at H;have hy:=e7.mpr ⟨w.2.2 p H.1,dD H.1⟩;rw[<- H.2];exact u p hy
   ·
    dsimp only[b];rw[<- Z.2];let ps:=a.primeFactors.sort (·<=·);have F:ps.length=k:=(by dsimp only[ps];rw[lk];exact Z.1.2);have Hx:ps.Nodup:=sort_nodup a.primeFactors (·<=·);symm;refine hO (fun (i:Fin k) _=>ps.get ⟨i.1,_O⟩) ?_ ?_ ?_
    ·intro i hi;rw[dB]at hi;have hv:d a i=m:=hi.2;have F':(a.primeFactors.sort (·<=·)).length=k:=F;dsimp only[d]at hv;rw[eG _O]at hv;exact dB.mpr ⟨(iO (r:=fun x y:ℕ=>x<=y)).mp (jq _ _),hv⟩
    ·intro i1 _ i2 _ hC;have:=(List.nodup_iff_injective_get.mp Hx) hC;exact dQ (es this)
    ·intro p H;rw[dB]at H;have Hb:p∈ps:=(iO (r:=fun x y:ℕ=>x<=y)).mpr H.1;obtain⟨Hr,rfl⟩:=List.mem_iff_get.mp Hb;refine⟨⟨Hr.1,_O⟩,dB.mpr ⟨dJ _,?_⟩,rfl⟩;dsimp only[d,ps];rw[eG Hr.2];exact H.2
   ·rw[<- d4 w.1 w.2.1];exact lP (s:=a.primeFactors) (t:=(univ:Finset (Fin M))) (g:=q) (fun _ _=>dJ _) (fun p=>p)
  calc _<=∑a∈U,(1:O)/(a:O):=
        dC hk fun _ _ _=>_P
    _<=∑S∈Fintype.piFinset (fun m:Fin M=>(aA (m.1+1)).powersetCard (b m)),(1:O)/((∏m:Fin M,∏p∈S m,p:ℕ):O):=jY fun _ _=>_P
    _=∏m:Fin M,∑T∈(aA (m.1+1)).powersetCard (b m),(1:O)/((∏p∈T,p:ℕ):O):=by
        rw[j9];refine dF rfl fun S _=>?_
        rw[fu,g9,<- gL];exact f9 rfl fun m _=>(g9 _).symm
    _<=∏m:Fin M,(log 2)^(b m)/((b m).factorial:O):=by
        refine im (fun _ _=>ea fun _ _=>by positivity) fun m _=>?_
        have A:=dm (aA (m.1+1)) (fun p H=>by
          unfold aA at H;rw[gc _O]at H;exact (dB.mp H).2.pos) (b m)
        have h2:∑p∈aA (m.1+1),(1:O)/(p:O)<=log 2:=aG (m.1+1) _O;exact A.trans (dI (m9 (ea fun _ _=>by positivity) h2 _) _P)
    _=(log 2)^k/∏m:Fin M,((b m).factorial:O):=by rw[gM,kq,hW]
 let c (j:Fin k->Fin M):Set (Fin k->O):=
  {ξ∈cr k 0 1 | ∀i:Fin k,((j i).1:O)/(M:O)< ξ i/\ξ i< (((j i).1+1:ℕ):O)/(M:O)}
 let e (j:Fin k->Fin M):Set (Fin k->O):=
  {ξ | (∀i:Fin k,((j i).1:O)/(M:O)<=ξ i/\ξ i<=(((j i).1+1:ℕ):O)/(M:O))/\Monotone ξ}
 have z:∀j∈J,MeasurableSet (c j):=by
  intro j _;have hC:c j=cr k 0 1∩⋂ i:Fin k,{ξ : Fin k->O | ((j i).1:O)/(M:O)< ξ i}∩{ξ : Fin k->O | ξ i< (((j i).1+1:ℕ):O)/(M:O)}:=(by ext ξ;simp[c]);rw[hC];exact (cs k 0 1).inter (fI fun i=>
   (l5 eV (dO i)).inter
   (l5 (dO i) eV))
 have C:∀j∈J,volume (c j)=ENNReal.ofReal (1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O))):=by
  intro j hj;have W:c j⊆e j:=fun ξ h=>⟨fun i=>⟨(h.2 i).1.le,(h.2 i).2.le⟩,h.1.2⟩;have h7:e j \ c j ⊆
   ⋃ i:Fin k,({ξ : Fin k->O | ξ i=((j i).1:O)/(M:O)} ∪
    {ξ : Fin k->O | ξ i=(((j i).1+1:ℕ):O)/(M:O)}):=by
   intro ξ ⟨hcl,hw⟩;have Hc : ξ∈cr k 0 1:=by
    refine⟨fun i=>⟨?_,?_⟩,hcl.2⟩
    ·exact gf _P (hcl.1 i).1
    ·exact (hcl.1 i).2.trans (div_le_one_of_le₀ (_M (show (j i).1+1<=M from (j i).2)) (dK M))
   have hX:¬ ∀i:Fin k,((j i).1:O)/(M:O)< ξ i/\ξ i< (((j i).1+1:ℕ):O)/(M:O):=fun h=>hw ⟨Hc,h⟩;push Not at hX;rcases hX with⟨i,hi⟩;refine eQ.mpr ⟨i,?_⟩;by_cases A:((j i).1:O)/(M:O)< ξ i
   ·exact Or.inr (i8 (hcl.1 i).2 (hi A))
   ·exact Or.inl (i8 (not_lt.mp A) (hcl.1 i).1)
  have X:volume (e j \ c j)=0:=by
   refine measure_mono_null h7 ?_
   refine measure_iUnion_null fun i=>measure_union_null (dq i _) (dq i _)
  have hE:volume (c j)=volume (e j):=(by have hu:c j∪(e j \ c j)=e j:=Set.union_diff_cancel W;have hF:volume (c j)<=volume (e j):=f4 W;have Hl:volume (e j)<=volume (c j):=(by rw[<- hu];exact (measure_union_le _ _).trans (by rw[X,i0]));exact i8 hF Hl);rw[hE];exact dr M hq M eR k j (dB.mp hj).2 (fun i=>(j i).2)
 have hI:Set.PairwiseDisjoint (J:Set (Fin k->Fin M)) c:=by
  intro j1 _ j2 _ hX;rw[Function.onFun,kX];intro ξ A h2;have hb:∃i:Fin k,j1 i≠j2 i:=(by by_contra hZ;push Not at hZ;exact hX (funext hZ));rcases hb with⟨i,hi⟩;have h8:(0:O)< (M:O):=_M hq;rcases gI (jP hi) with hs | hY
  ·have A':=(A.2 i).2;have h2':=(h2.2 i).1;have hL:(((j1 i).1+1:ℕ):O)/(M:O)<=((j2 i).1:O)/(M:O):=dI (_M hs) h8.le;linarith
  ·have A':=(A.2 i).1;have h2':=(h2.2 i).2;have hL:(((j2 i).1+1:ℕ):O)/(M:O)<=((j1 i).1:O)/(M:O):=dI (_M hY) h8.le;linarith
 have hN:∀j∈J,∀ ξ∈c j,o j<=(2:O)^102*cS k v ξ:=by
  intro j _ ξ hξ;dsimp only[o];unfold cS;obtain⟨g,hg,hU⟩:=lU (nonempty_range_iff.mpr (j7 k)) (fun g:ℕ=>(2:O)^(-(g:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^((v:O)*ξ i)));rw[hU];refine (inf'_le _ hg).trans ?_
  have Hm:1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(j i).1 <=(2:O)^102*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^((v:O)*ξ i)):=by
   have A:(1:O)<=(2:O)^102:=_N;have h2:∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^(j i).1 <=(2:O)^102*∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^((v:O)*ξ i):=by
    rw[dP];refine dG fun i _=>?_
    have hMξ : ((j i).1:O)<=(M:O)*ξ i:=(by have:=(hξ.2 i).1;rw[mm _P]at this;linarith);have hξ1 : ξ i<=1:=(hξ.1.1 i).2;have Hd:(M:O)*ξ i<=(v:O)*ξ i+102:=by dsimp only[M];push_cast;nlinarith
    calc (2:O)^(j i).1=(2:O)^((j i).1:O):=(eK 2 _).symm
      _<=(2:O)^((v:O)*ξ i+102):=eT _N (hMξ.trans Hd)
      _=(2:O)^(102:O)*(2:O)^((v:O)*ξ i):=by rw[ip,gF _N]
      _=(2:O)^102*(2:O)^((v:O)*ξ i):=_N
   linarith
  have HD:=dA Hm (_P :(0:O)<=(2:O)^(-(g:O)));linarith
 have N:IntegrableOn (cS k v) (cr k 0 1) volume:=by
  have hl:volume (cr k 0 1)< ⊤:=(by rw[ct k 0 1 eO];exact ENNReal.ofReal_lt_top);have He:Continuous (cS k v):=by
   unfold cS;have A:∀g∈range (k+1),Continuous fun ξ : Fin k->O=>
    (2:O)^(-(g:O))*(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^((v:O)*ξ i)):=
    fun g _=>continuous_const.mul (continuous_const.add (continuous_finsetSum _ fun i _=>
     continuous_const.rpow (continuous_const.mul (l6 i)) (fun _=>Or.inl _N)))
   exact Continuous.finset_inf'_apply ⟨0,dN.mpr (gO k)⟩ A
  have Hn:∀ ξ∈cr k 0 1,‖cS k v ξ‖<=1:=by
   intro ξ _;have Hy:0<=cS k v ξ:=ie _ _ fun g _=>ek _P (jT eO (ea fun _ _=>by positivity))
   have hF:cS k v ξ<=1:=by
    unfold cS;refine (inf'_le (s:=range (k+1))
     (f:=fun g:ℕ=>(2:O)^(-(g:O)) *(1+∑i∈univ.filter (fun i:Fin k=>i.1< g),(2:O)^((v:O)*ξ i)))
     (dN.mpr (gO k))).trans_eq (by simp)
   rw[Real.norm_of_nonneg Hy];exact hF
  exact IntegrableOn.of_bound hl He.aestronglyMeasurable 1 ((ae_restrict_iff' (cs k 0 1)).mpr (hG Hn))
 have hQ:∀ ξ,0<=cS k v ξ:=fun ξ=>
  ie _ _ fun g _=>ek _P (jT eO (ea fun _ _=>by positivity))
 have hn:∑j∈J,o j*(1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O))) <=(2:O)^102*cT k v:=by
  have h6:∀j∈J,o j*(1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O))) <=∫ ξ in c j,(2:O)^102*cS k v ξ:=by intro j hj;have Ho:c j⊆cr k 0 1:=fun _ h=>h.1;have hS:(volume (c j)).toReal =1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O)):=(by rw[C j hj,eZ _P]);rw[<- hS,e8,<- Measure.real_def,<- lf,<- iT];refine setIntegral_mono_on (ju (by rw[C j hj];exact ec)) ((N.mono_set Ho).const_mul _) (z j hj) (hN j hj)
  calc _<=∑j∈J,∫ ξ in c j,(2:O)^102*cS k v ξ:=dG h6
    _=∫ ξ in (⋃ j∈J,c j),(2:O)^102*cS k v ξ:=by
        rw[integral_biUnion_finset J (fun j hj=>z j hj) hI
          (fun j hj=>(N.mono_set fun _ h=>h.1).const_mul _)]
    _<=∫ ξ in cr k 0 1,(2:O)^102*cS k v ξ:=by
        refine setIntegral_mono_set (N.const_mul _) (hG fun ξ=>ek _P (hQ ξ))
          (hG fun ξ hξ=>by
            rcases Set.mem_iUnion₂.mp hξ with⟨j,_,hjξ⟩;exact hjξ.1)
    _=(2:O)^102*cT k v:=by unfold cT;exact kF _ _
 have Hp:((M:O)*log 2)^k<=exp 1020*(log (log (P:O)))^k:=by
  have hT:(v:O)*log 2<=log (log (P:O)):=(by have A:=fC (ed G.le l.le);exact (ma l).mp A);have ho:((M:O)/(v:O))^k<=exp 1020:=by
   have A:(M:O)/(v:O)=1+102/(v:O):=(by dsimp only[M];push_cast;field_simp [(_P :(v:O)≠0)]);rw[A]
   calc (1+102/(v:O))^k<=(exp (102/(v:O)))^k:=
         m9 _P (_l (fB (102/(v:O)))) k
     _=exp ((k:O)*(102/(v:O))):=(gg _ _).symm
     _<=exp 1020:=me.mpr (by
         rw[gl,mc _P];have:(k:O)<=10*(v:O):=_M HC;linarith)
  have Hq:(M:O)*log 2=((M:O)/(v:O))*((v:O)*log 2):=(by field_simp [(_P :(v:O)≠0)]);rw[Hq,eP];exact en ho (m9 _P hT k) _P (ez 1020).le
 unfold dl;rw[<- jG hc]
 calc ∑j∈J,∑a∈((cV P).filter (fun a=>a.primeFactors.card=k)).filter (fun a=>d a=j),L a/(a:O)
     <= ∑j∈J,∑a∈((cV P).filter (fun a=>a.primeFactors.card=k)).filter (fun a=>d a=j),((2:O)^101*(2:O)^k*o j)*((1:O)/(a:O)):=by
       refine dG fun j _=>dG fun a Z=>?_
       rw[dB]at Z;rw[iE,<- Z.2];exact dI (ht a Z.1) (dK a)
   _=∑j∈J,((2:O)^101*(2:O)^k*o j) *∑a∈((cV P).filter (fun a=>a.primeFactors.card=k)).filter (fun a=>d a=j),(1:O)/(a:O):=dF rfl fun j _=>(dP ..).symm
   _<=∑j∈J,((2:O)^101*(2:O)^k*o j) *((log 2)^k/∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O)):=by
       refine dG fun j hj=>dA (hh j hj) ?_
       have Hz:0<=o j:=ie _ _ fun _ _=>_P;positivity
   _=(2:O)^101*(2*((M:O)*log 2))^k *∑j∈J,o j*(1/((M:O)^k*∏m:Fin M,((univ.filter fun i:Fin k=>j i=m).card.factorial:O))):=by
       rw[dP];refine dF rfl fun j _=>?_
       rw[eP,eP];field_simp [(_P :(M:O)^k≠0)]
   _<=(2:O)^101*(2*((M:O)*log 2))^k*((2:O)^102*cT k v):=dA hn _P
   _<=(2:O)^101*((2:O)^k*(exp 1020*(log (log (P:O)))^k))*((2:O)^102*cT k v):=by have Hf:0<=cT k v:=kE (cs k 0 1) fun ξ _=>hQ ξ;rw[eP];gcongr
   _=(2:O)^203*exp 1020*(2*log (log (P:O)))^k*cT k v:=by rw[eP];ring
lemma dt (N:ℕ) :
 ∑d∈range N,(1+(d:O)^2)*((3:O)/4)^d<=100:=by
 have b:∀n:ℕ,(∑d∈range n,(1+(d:O)^2)*((3:O)/4)^d) +(4*(n:O)^2+24*(n:O)+88)*((3:O)/4)^n=88:=by
  intro n;induction n with
  | zero=>norm_num
  | succ n ih=>
   rw[jt,fc ((3:O)/4) n];push_cast;linarith[ih]
 have c:0<=(4*(N:O)^2+24*(N:O)+88)*((3:O)/4)^N:=_P;linarith[b N]
set_option maxHeartbeats 800000 in
lemma du :
 let α : O:=1-(1+log (log 2))/log 2
 ∃G:O,0< G/\∃Q:ℕ,16<=Q/\∀P:ℕ,Q<=P -> d8 P<=G*(log (P:O))^(-α)/(log (log (P:O)))^((3:O)/2):=by
 classical
 intro α;obtain⟨ht,hD,Hb⟩:=dk;obtain⟨CU,hX,hY⟩:=cU;have c:0< log 2:=_l a3;obtain⟨Q,T,hj⟩:∃Q:ℕ,16<=Q/\200<=log (log (Q:O))/log 2:=by let Q:=max 16 ⌈exp (exp (200*log 2))⌉₊;refine⟨Q,eo _ _,?_⟩;rw[ma c];have u:exp (exp (200*log 2))<=(Q:O):=(g6 _).trans (_M (ep 16 _));have R:exp (200*log 2)<=log (Q:O):=(by rw[<- iu (exp (200*log 2))];exact dM (ez _) u);rw[<- iu (200*log 2)];exact dM (ez _) R
 let m:O:=(2:O)^203*exp 1020*CU;let U:O:=5+400*m;let G:O:=ht*U*exp 1*(2*log 2)^((3:O)/2);refine⟨G,by positivity,Q,T,?_⟩
 intro P hP;have hE:16<=P:=T.trans hP;have w:0< log (P:O):=et (_M (_O :1< P));have l:200*log 2<=log (log (P:O)):=by have u:log (Q:O)<=log (P:O):=dM _P (_M hP);have R:log (log (Q:O))<=log (log (P:O)):=dM (et (_M (_O :1< Q))) u;have h3:=(ma c).mp hj;linarith
 have i:0< log (log (P:O)):=e9 _P l;obtain⟨v,j⟩:∃v:ℕ,v=⌊log (log (P:O))/log 2⌋₊:=⟨_,rfl⟩;have H:200<=v:=by rw[j];exact g2 (by rw[ma c];exact l)
 have hv:(v:O)*log 2<=log (log (P:O)):=by rw[<- ma c,j];exact fC (ed i.le c.le)
 have hw:log (log (P:O))<=((v+1:ℕ):O)*log 2:=by push_cast;rw[<- mc c,j];exact (f6 _).le
 let B:O:=(2*((v+1:ℕ):O)*log 2)^v/((v+1).factorial:O);have hZ:1<=B:=by
  dsimp only[B];rw[js _P];have h5:=a7 (v+1) _O;have H1:(1:O)< 2*log 2:=_l a3;have W:exp 1*sqrt ((v+1:ℕ):O)*((v+1:ℕ):O)<=(exp 1)^(v+1):=by
   have H0:sqrt ((v+1:ℕ):O)<=((v+1:ℕ):O):=(by rw[sqrt_le_left _P];nlinarith[show (1:O)<=((v+1:ℕ):O) by exact_mod_cast (_O :1<=v+1)]);have u:(2:O)^(v+1)<=(exp 1)^(v+1):=m9 _N (_l (fB (1:O))) _;have R:3*((v+1:ℕ):O)^2<=(2:O)^(v+1):=by
    have C:3*(v+1)^2<=2^(v+1):=by
     have D:∀n:ℕ,10<=n->3*n^2<=2^n:=by
      intro n hn;induction n,hn using fe with
      | base=>norm_num
      | succ n hn ih=>
       have u:3*(n+1)^2<=2*(3*n^2):=_Q
       calc 3*(n+1)^2<=2*(3*n^2):=u
         _<=2*2^n:=dR 2 ih
         _=2^(n+1):=(fp 2 n).symm
     exact D (v+1) _O
    exact_mod_cast C
   have H2:exp 1<=3:=_l gT
   calc exp 1*sqrt ((v+1:ℕ):O)*((v+1:ℕ):O)
       <= 3*((v+1:ℕ):O)*((v+1:ℕ):O):=by gcongr
     _=3*((v+1:ℕ):O)^2:=_R
     _<=(2:O)^(v+1):=R
     _<=(exp 1)^(v+1):=u
  have h6:1<=(2*log 2)^v:=mo H1.le
  calc ((v+1).factorial:O)
      <= exp 1*sqrt ((v+1:ℕ):O)*(((v+1:ℕ):O)/exp 1)^(v+1):=h5
    _=(exp 1*sqrt ((v+1:ℕ):O)*((v+1:ℕ):O)/(exp 1)^(v+1)) *((v+1:ℕ):O)^v:=by rw[ij,fc];ring
    _<=1*((v+1:ℕ):O)^v:=by
        refine dE ?_ _P
        rw[iy _P];exact W
    _=((v+1:ℕ):O)^v:=gz _
    _<=((v+1:ℕ):O)^v*(2*log 2)^v:=jZ _P h6
    _=(2*((v+1:ℕ):O)*log 2)^v:=by rw[<- eP];congr 1;ring
 have X:∑a∈cV P,L a/(a:O)=∑k∈range (P+1),dl P k:=by
  have hF:∀a∈cV P,a.primeFactors.card∈range (P+1):=by
   intro a F;rw[dN];have e:a.primeFactors⊆Icc 1 P:=fun p hp=>
    dT.mpr ⟨(dD hp).pos,((d5 P a).mp F).2.2 p hp⟩
   have Hg:=(er e).trans (by simp :(Icc 1 P).card<=P);omega
  exact (jG hF _).symm
 have Hh:dl P 0<=B:=by
  have hx:(cV P).filter (fun a=>a.primeFactors.card=0)={1}:=by
   ext a;simp only[dB,eg];constructor
   ·rintro⟨F,h0⟩;have u:=d4 ((d5 P a).mp F).1 ((d5 P a).mp F).2.1;rw[mA.mp h0,prod_empty]at u;exact u.symm
   ·rintro rfl;exact⟨d7 P,by simp⟩
  unfold dl;rw[hx,jA,bL,eF,kO];linarith[a4]
 have H3:∑k∈Icc 1 v,dl P k<=100*m*B:=by
  have y:∀k∈Icc 1 v,dl P k<=m*B*((1+((v-k:ℕ):O)^2)*((3:O)/4)^(v-k)):=by
   intro k E;rw[dT]at E;have h7:=ds (_O :3<=P) (j ▸ H) E.1 _O;have hU:=hY k v E.1 _O;rw[<- j]at h7;have o:(2*log (log (P:O)))^k<=(2*((v+1:ℕ):O)*log 2)^k:=m9 _P _L k;have hl:(2*((v+1:ℕ):O)*log 2)^k/((k+1).factorial:O) <=B*((3:O)/4)^(v-k):=by
    dsimp only[B];have hu:((v+1).factorial:O)<=((v+1:ℕ):O)^(v-k)*((k+1).factorial:O):=by
     have C:(v+1).factorial<=(v+1)^(v-k)*(k+1).factorial:=by
      have D:∀d:ℕ,d<=v->(v+1).factorial<=(v+1)^d*(v+1-d).factorial:=by
       intro d;induction d with
       | zero=>intro _;simp
       | succ d ih=>
        intro hd;have e:v+1-d=(v+1-(d+1))+1:=_O;have hf:(v+1-d).factorial=(v+1-d)*(v+1-(d+1)).factorial:=by conv_lhs=>rw[e,e6,<- e]
        calc (v+1).factorial<=(v+1)^d*(v+1-d).factorial:=ih _O
          _=(v+1)^d*((v+1-d)*(v+1-(d+1)).factorial):=by rw[hf]
          _<=(v+1)^d*((v+1)*(v+1-(d+1)).factorial):=dR _ (eE _ (i4 _ _))
          _=(v+1)^(d+1)*(v+1-(d+1)).factorial:=by rw[fc];ring
      simpa[show v+1-(v-k)=k+1 by omega] using D (v-k) _O
     exact_mod_cast C
    have hI:1/(2*log 2)<=3/4:=(by rw[mb _P _N];linarith[kz]);have hm:(2*((v+1:ℕ):O)*log 2)^v =(2*((v+1:ℕ):O)*log 2)^k*(2*((v+1:ℕ):O)*log 2)^(v-k):=(by rw[<- ee,iW E.2]);rw[gm,mb _P _P,hm]
    calc (2*((v+1:ℕ):O)*log 2)^k*((v+1).factorial:O)
        <= (2*((v+1:ℕ):O)*log 2)^k*(((v+1:ℕ):O)^(v-k)*((k+1).factorial:O)):=dA hu _P
      _=(2*((v+1:ℕ):O)*log 2)^k*(2*((v+1:ℕ):O)*log 2)^(v-k) *(1/(2*log 2))^(v-k)*((k+1).factorial:O):=by rw[i6,eP,eP];field_simp [(_P :(2:O)^(v-k)≠0),(_P :(log 2)^(v-k)≠0)];rw[<- eP];congr 1;ring
      _<=(2*((v+1:ℕ):O)*log 2)^k*(2*((v+1:ℕ):O)*log 2)^(v-k) *((3:O)/4)^(v-k)*((k+1).factorial:O):=by gcongr
   have Z:(1:O)<=(2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1:=_l (show (0:O)< (2:O)^(((k:ℤ)-(v:ℤ):ℤ):O) by positivity)
   have q:((((v:ℤ)-(k:ℤ):ℤ):O))^2=((v-k:ℕ):O)^2:=by rw[ei E.2];push_cast;rfl
   calc dl P k<=(2:O)^203*exp 1020*(2*log (log (P:O)))^k*cT k v:=h7
     _<=(2:O)^203*exp 1020*(2*((v+1:ℕ):O)*log 2)^k *(CU*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2)/(((k+1).factorial:O)*((2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1))):=en (dA o _P) hU
           (kE (cs k 0 1) fun ξ _=>
             ie _ _ fun _ _=>ek _P (jT eO (ea fun _ _=>by positivity)))
           _P
     _<=(2:O)^203*exp 1020*(2*((v+1:ℕ):O)*log 2)^k *(CU*(1+((v-k:ℕ):O)^2)/((k+1).factorial:O)):=by rw[q];refine dA ?_ _P;exact dL _P _P (jZ _P Z)
     _=m*((2*((v+1:ℕ):O)*log 2)^k/((k+1).factorial:O))*(1+((v-k:ℕ):O)^2):=by dsimp only[m];ring
     _<=m*(B*((3:O)/4)^(v-k))*(1+((v-k:ℕ):O)^2):=by gcongr
     _=m*B*((1+((v-k:ℕ):O)^2)*((3:O)/4)^(v-k)):=_R
  have e:(Icc 1 v).image (fun k=>v-k)⊆range (v+1):=(by intro d hd;rcases dW.mp hd with⟨k,E,rfl⟩;rw[dT]at E;rw[dN];omega);have h8:Set.InjOn (fun k=>v-k) ((Icc 1 v:Finset ℕ):Set ℕ):=by intro k1 u k2 R h;simp only[eB,dT]at u R;dsimp only at h;omega
  calc ∑k∈Icc 1 v,dl P k
      <= ∑k∈Icc 1 v,m*B*((1+((v-k:ℕ):O)^2)*((3:O)/4)^(v-k)):=dG y
    _=m*B*∑k∈Icc 1 v,(1+((v-k:ℕ):O)^2)*((3:O)/4)^(v-k):=(dP ..).symm
    _=m*B*∑d∈(Icc 1 v).image (fun k=>v-k),(1+(d:O)^2)*((3:O)/4)^d:=by rw[fr (fun a F b hb h=>h8 F hb h)]
    _<=m*B*∑d∈range (v+1),(1+(d:O)^2)*((3:O)/4)^d:=dA (dC e fun _ _ _=>by positivity) _P
    _<=m*B*100:=dA (dt (v+1)) _P
    _=100*m*B:=by ring
 have H4:∑k∈Icc (v+1) (10*v),dl P k<=100*m*B:=by
  have y:∀k∈Icc (v+1) (10*v),dl P k<=m*B*((1+((k-v:ℕ):O)^2)*((3:O)/4)^(k-v)):=by
   intro k E;rw[dT]at E;have h7:=ds (_O :3<=P) (j ▸ H) (_O :1<=k) _O;have hU:=hY k v (_O :1<=k) _O;rw[<- j]at h7;have o:(2*log (log (P:O)))^k<=(2*((v+1:ℕ):O)*log 2)^k:=m9 _P _L k;have hl:(2*((v+1:ℕ):O)*log 2)^k/(((k+1).factorial:O)*(2:O)^(k-v)) <=B*((3:O)/4)^(k-v):=by
    dsimp only[B];have hu:((v+1).factorial:O)*((v+1:ℕ):O)^(k-v)<=((k+1).factorial:O):=by
     have C:(v+1).factorial*(v+1)^(k-v)<=(k+1).factorial:=by
      have D:∀d:ℕ,(v+1).factorial*(v+1)^d<=(v+1+d).factorial:=by
       intro d;induction d with
       | zero=>simp
       | succ d ih=>
        rw[fc,<- f0];conv_rhs=>rw[show v+1+(d+1)=(v+1+d)+1 by omega,e6,e8]
        exact eH ih _O
      simpa[show v+1+(k-v)=k+1 by omega] using D (k-v)
     exact_mod_cast C
    have ho:(2*((v+1:ℕ):O)*log 2)^k =(2*((v+1:ℕ):O)*log 2)^v*(2*((v+1:ℕ):O)*log 2)^(k-v):=(by rw[<- ee,iW (_O :v<=k)]);have hq:log 2<=3/4:=_l ky;rw[gm,mb _P _P,ho]
    calc (2*((v+1:ℕ):O)*log 2)^v*(2*((v+1:ℕ):O)*log 2)^(k-v)*((v+1).factorial:O)
        = (2*((v+1:ℕ):O)*log 2)^v*(log 2)^(k-v) *(((v+1).factorial:O)*((v+1:ℕ):O)^(k-v))*(2:O)^(k-v):=by rw[eP,eP];ring
      _<=(2*((v+1:ℕ):O)*log 2)^v*((3:O)/4)^(k-v) *((k+1).factorial:O)*(2:O)^(k-v):=by have u:=m9 c.le hq (k-v);gcongr
      _=(2*((v+1:ℕ):O)*log 2)^v*((3:O)/4)^(k-v)*(((k+1).factorial:O)*(2:O)^(k-v)):=_R
   have h9:(2:O)^(k-v)<=(2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1:=by
    have:(((k:ℤ)-(v:ℤ):ℤ):O)=((k-v:ℕ):O):=by rw[ei _O];push_cast;rfl
    rw[this,eK];linarith
   have q:((((v:ℤ)-(k:ℤ):ℤ):O))^2=((k-v:ℕ):O)^2:=by rw[ei (_O :v<=k)];push_cast;ring
   calc dl P k<=(2:O)^203*exp 1020*(2*log (log (P:O)))^k*cT k v:=h7
     _<=(2:O)^203*exp 1020*(2*((v+1:ℕ):O)*log 2)^k *(CU*(1+(((v:ℤ)-(k:ℤ):ℤ):O)^2)/(((k+1).factorial:O)*((2:O)^(((k:ℤ)-(v:ℤ):ℤ):O)+1))):=en (dA o _P) hU
           (kE (cs k 0 1) fun ξ _=>
             ie _ _ fun _ _=>ek _P (jT eO (ea fun _ _=>by positivity)))
           _P
     _<=(2:O)^203*exp 1020*(2*((v+1:ℕ):O)*log 2)^k *(CU*(1+((k-v:ℕ):O)^2)/(((k+1).factorial:O)*(2:O)^(k-v))):=by rw[q];refine dA ?_ _P;exact dL _P _P (dA h9 _P)
     _=m*((2*((v+1:ℕ):O)*log 2)^k/(((k+1).factorial:O)*(2:O)^(k-v)))*(1+((k-v:ℕ):O)^2):=by dsimp only[m];ring
     _<=m*(B*((3:O)/4)^(k-v))*(1+((k-v:ℕ):O)^2):=by gcongr
     _=m*B*((1+((k-v:ℕ):O)^2)*((3:O)/4)^(k-v)):=_R
  have e:(Icc (v+1) (10*v)).image (fun k=>k-v)⊆range (10*v+1):=(by intro d hd;rcases dW.mp hd with⟨k,E,rfl⟩;rw[dT]at E;rw[dN];omega);have h8:Set.InjOn (fun k=>k-v) ((Icc (v+1) (10*v):Finset ℕ):Set ℕ):=by intro k1 u k2 R h;simp only[eB,dT]at u R;dsimp only at h;omega
  calc ∑k∈Icc (v+1) (10*v),dl P k
      <= ∑k∈Icc (v+1) (10*v),m*B*((1+((k-v:ℕ):O)^2)*((3:O)/4)^(k-v)):=dG y
    _=m*B*∑k∈Icc (v+1) (10*v),(1+((k-v:ℕ):O)^2)*((3:O)/4)^(k-v):=(dP ..).symm
    _=m*B*∑d∈(Icc (v+1) (10*v)).image (fun k=>k-v),(1+(d:O)^2)*((3:O)/4)^d:=by rw[fr (fun a F b hb h=>h8 F hb h)]
    _<=m*B*∑d∈range (10*v+1),(1+(d:O)^2)*((3:O)/4)^d:=dA (dC e fun _ _ _=>by positivity) _P
    _<=m*B*100:=dA (dt (10*v+1)) _P
    _=100*m*B:=by ring
 have hL:∑k∈Icc (10*v+1) P,dl P k<=4*B:=by
  have hy:2*∑p∈dv P,(1:O)/(p:O)<=2*(v:O):=(by have u:=ao P _O;have hr:(200:O)<=(v:O):=_M H;have H5:log 2< 0.7:=_l ky;have R:log (log (P:O))+35<=(v:O):=(by have hM:((v+1:ℕ):O)=(v:O)+1:=(by push_cast;rfl);nlinarith[hw,H5,hr]);linarith);have y:∀k∈Icc (10*v+1) P,dl P k<=((3:O)/5)^k:=by
   intro k E;rw[dT]at E;have H6:dl P k<=log 2*(2*∑p∈dv P,(1:O)/(p:O))^k/(k.factorial:O):=by
    unfold dl;have e:(cV P).filter (fun a=>a.primeFactors.card=k) ⊆ ((dv P).powersetCard k).image fun S=>∏p∈S,p:=by
     intro a F;rw[dB]at F;have z:=(d5 P a).mp F.1;exact dW.mpr ⟨a.primeFactors,fU.mpr
      ⟨fun p hp=>e7.mpr ⟨z.2.2 p hp,dD hp⟩,F.2⟩,
      d4 z.1 z.2.1⟩
    have u:∀a∈(cV P).filter (fun a=>a.primeFactors.card=k),L a/(a:O)<=(2:O)^k*log 2*((1:O)/(a:O)):=by
     intro a F;rw[dB]at F;have z:=(d5 P a).mp F.1;have hN:a.divisors.card=2^k:=by
      rw[Nat.card_divisors (by have:=z.1;omega :a≠0)];change ∏p∈a.factorization.support,(a.factorization p+1)=2^k;rw[ej];have hz:∏p∈a.primeFactors,(a.factorization p+1)=∏_p∈a.primeFactors,2:=by
       refine f9 rfl fun p hp=>?_
       have hQ:=dD hp;have Hc:=(hQ.dvd_iff_one_le_factorization _O).mp (dS hp);have hR:a.factorization p<=1:=by
        by_contra R;push Not at R;exact hQ.ne_one (mn.mp (z.2.1 p
         ((show p*p∣p^a.factorization p by rw[<- sq];exact jj p R).trans (gd a p))))
       omega
      rw[hz,prod_const,F.2]
     have H7:L a<=(2:O)^k*log 2:=(by have:=bM a;rw[hN]at this;push_cast at this;exact this);rw[iE];exact dI H7 (dK a)
    calc ∑a∈(cV P).filter (fun a=>a.primeFactors.card=k),L a/(a:O)
        <= ∑a∈(cV P).filter (fun a=>a.primeFactors.card=k),(2:O)^k*log 2*((1:O)/(a:O)):=dG u
      _=(2:O)^k*log 2*∑a∈(cV P).filter (fun a=>a.primeFactors.card=k),(1:O)/(a:O):=(dP ..).symm
      _<=(2:O)^k*log 2*∑a∈((dv P).powersetCard k).image (fun S=>∏p∈S,p),(1:O)/(a:O):=dA (dC e fun _ _ _=>by positivity) _P
      _<=(2:O)^k*log 2*∑S∈(dv P).powersetCard k,(1:O)/((∏p∈S,p:ℕ):O):=dA (jY fun _ _=>by positivity) _P
      _<=(2:O)^k*log 2*((∑p∈dv P,(1:O)/(p:O))^k/(k.factorial:O)):=dA (dm _ (fun p hp=>(e7.mp hp).2.pos) k) _P
      _=log 2*(2*∑p∈dv P,(1:O)/(p:O))^k/(k.factorial:O):=by rw[eP];ring
   have h5:=a6 k;have hc:1<=sqrt (2*π*(k:O)):=(by rw[one_le_sqrt];have:(1:O)<=(k:O):=_M (_O :1<=k);nlinarith[lh]);have he:((k:O)/exp 1)^k<=(k.factorial:O):=(le_mul_of_one_le_left _P hc).trans h5;have hs:(0:O)< (k:O):=_M (_O :0< k);have hA:2*(v:O)*exp 1/(k:O)<=3/5:=by rw[mc hs];have Hd:10*(v:O)<=(k:O):=_M (_O :10*v<=k);have H2:exp 1< 3:=_l gT;nlinarith[show (0:O)<=(v:O) by positivity]
   calc dl P k<=log 2*(2*(v:O))^k/(k.factorial:O):=
         H6.trans (dI (dA
           (m9 _P hy k) c.le) _P)
     _<=1*(2*(v:O))^k/((k:O)/exp 1)^k:=mj _P (dE a4.le _P) _P he
     _=(2*(v:O)*exp 1/(k:O))^k:=by rw[gz,<- ij];congr 1;field_simp [(_P :(k:O)≠0),(ez 1).ne']
     _<=((3:O)/5)^k:=m9 _P hA k
  have e:Icc (10*v+1) P⊆range (P+1):=fun k E=>
   dN.mpr (by rw[dT]at E;omega)
  calc ∑k∈Icc (10*v+1) P,dl P k
      <= ∑k∈Icc (10*v+1) P,((3:O)/5)^k:=dG y
    _<=∑k∈range (P+1),((3:O)/5)^k:=dC e fun _ _ _=>_P
    _=(((3:O)/5)^(P+1)-1)/((3:O)/5-1):=fO (_N :((3:O)/5)≠1) (P+1)
    _<=4:=by have Hi:0<=((3:O)/5)^(P+1):=_P;have:(((3:O)/5)^(P+1)-1)/((3:O)/5-1)=(5/2:O)*(1-((3:O)/5)^(P+1)):=_R;rw[this];linarith
    _<=4*B:=by linarith
 have J:∑a∈cV P,L a/(a:O)<=U*B:=by
  rw[X];have hB:range (P+1)⊆({0}:Finset ℕ)∪Icc 1 v∪Icc (v+1) (10*v)∪Icc (10*v+1) P:=by
   intro k E;rw[dN]at E;by_cases h0:k=0
   ·exact e0 _ (e0 _ (e0 _ (eg.mpr h0)))
   ·by_cases u:k<=v
    ·exact e0 _ (e0 _ (eu _ (dT.mpr ⟨by omega,u⟩)))
    ·by_cases R:k<=10*v
     ·exact e0 _ (eu _ (dT.mpr ⟨by omega,R⟩))
     ·exact eu _ (dT.mpr ⟨by omega,_O⟩)
  have A:∀k,0<=dl P k:=fun k=>ea fun a _=>ed (bK a) (dK a);have hR:∑k∈range (P+1),dl P k <=dl P 0+∑k∈Icc 1 v,dl P k+∑k∈Icc (v+1) (10*v),dl P k +∑k∈Icc (10*v+1) P,dl P k:=(by have u:=dC hB (fun k _ _=>A k);have Hj:=fb (s₁:=({0}:Finset ℕ)∪Icc 1 v∪Icc (v+1) (10*v)) (s₂:=Icc (10*v+1) P) (f:=dl P);have Hk:=fb (s₁:=({0}:Finset ℕ)∪Icc 1 v) (s₂:=Icc (v+1) (10*v)) (f:=dl P);have H8:=fb (s₁:=({0}:Finset ℕ)) (s₂:=Icc 1 v) (f:=dl P);have Hl:0<=∑k∈(({0}:Finset ℕ)∪Icc 1 v∪Icc (v+1) (10*v))∩Icc (10*v+1) P,dl P k:=ea fun k _=>A k;have Hm:0<=∑k∈(({0}:Finset ℕ)∪Icc 1 v)∩Icc (v+1) (10*v),dl P k:=ea fun k _=>A k;have Hn:0<=∑k∈({0}:Finset ℕ)∩Icc 1 v,dl P k:=ea fun k _=>A k;rw[jA]at H8;linarith);have Ho:B+100*m*B+100*m*B+4*B<=U*B:=(by dsimp only[U];nlinarith[show 0<=m*B by positivity]);linarith
 have hC:B<=exp 1*(2*log 2)^((3:O)/2) *((log (P:O))^(2 - α)/(log (log (P:O)))^((3:O)/2)):=by
  have h5:=a6 v;have hg:((v:O)*sqrt (v:O))*((v:O)/exp 1)^v<=((v+1).factorial:O):=by
   rw[e6,g3];have H9:sqrt (v:O)<=sqrt (2*π*(v:O)):=sqrt_le_sqrt (by nlinarith[lh,show (0:O)<=(v:O) by positivity])
   have hM:(v:O)<=((v+1:ℕ):O):=_M (Nat.le_succ v)
   calc (v:O)*sqrt (v:O)*((v:O)/exp 1)^v
       <= ((v+1:ℕ):O)*(sqrt (2*π*(v:O))*((v:O)/exp 1)^v):=by rw[f0];exact en hM (dE H9 _P) _P _P
     _<=((v+1:ℕ):O)*(v.factorial:O):=dA h5 _P
  have hh:(((v+1:ℕ):O)/(v:O))^v<=exp 1:=by
   have hz:((v+1:ℕ):O)/(v:O)=1+1/(v:O):=(by push_cast;field_simp [(_P :(v:O)≠0)]);rw[hz]
   calc (1+1/(v:O))^v<=(exp (1/(v:O)))^v:=
         m9 _P (_l (fB (1/(v:O)))) v
     _=exp ((v:O)*(1/(v:O))):=(gg _ _).symm
     _=exp 1:=by congr 1;field_simp [(_P :(v:O)≠0)]
  have hS:2*log 2*exp 1=(2:O)^((2:O) - α):=(by have hT:log 2*(2 - α)=log 2+1+log (log 2):=(by dsimp only[α];field_simp [c.ne'];ring);rw[fQ (_N :(0:O)< 2),hT,gX,gX,eX _N,eX c];ring);have K:0< 2 - α:=(by dsimp only[α];have u:1-(log 2)⁻¹<=log (log 2):=fl c;have He:(log 2)⁻¹< 2:=(by rw[mz c _N];linarith[a3]);have Hp:log (log 2)< 0:=log_neg c a4;have Hf:0< (1+log (log 2))/log 2:=(jI c).mpr _L;linarith);have M:(2*log 2*exp 1)^v<=(log (P:O))^(2 - α):=by
   have Ha:(2:O)^v<=log (P:O):=by have u:=me.mpr hv;rw[eX w,gg,eX _N]at u;exact u
   calc (2*log 2*exp 1)^v=((2:O)^(2 - α))^v:=by rw[hS]
     _=((2:O)^v)^(2 - α):=by rw[<- eK ((2:O)^(2 - α)),<- gE _N,e8 (2 - α),gE _N,eK]
     _<=(log (P:O))^(2 - α):=fx _P Ha K.le
  have h4:log (log (P:O))/(2*log 2)<=(v:O):=(by rw[mc _P];have:((v+1:ℕ):O)<=2*(v:O):=_M (_O :v+1<=2*v);nlinarith);have hV:(log (log (P:O)))^((3:O)/2)/(2*log 2)^((3:O)/2)<=(v:O)*sqrt (v:O):=by have hW:(v:O)*sqrt (v:O)=(v:O)^((3:O)/2):=(by rw[ik,<- Real.rpow_one_add' _P _N];norm_num);rw[hW,<- div_rpow i.le _P];exact fx _P h4 _N
  calc B=(2*((v+1:ℕ):O)*log 2)^v/((v+1).factorial:O):=rfl
    _<=(2*((v+1:ℕ):O)*log 2)^v/(((v:O)*sqrt (v:O))*((v:O)/exp 1)^v):=dL _P _P hg
    _=(((v+1:ℕ):O)/(v:O))^v*((2*log 2*exp 1)^v/((v:O)*sqrt (v:O))):=by rw[ij,ij,eP,eP,eP,eP];field_simp [(_P :(v:O)≠0),(_P :sqrt (v:O)≠0),(ez 1).ne']
    _<=exp 1*((log (P:O))^(2 - α)/((log (log (P:O)))^((3:O)/2)/(2*log 2)^((3:O)/2))):=en hh (mj _P M _P hV) _P (ez 1).le
    _=exp 1*(2*log 2)^((3:O)/2) *((log (P:O))^(2 - α)/(log (log (P:O)))^((3:O)/2)):=by field_simp [(_P :(log (log (P:O)))^((3:O)/2)≠0),(_P :(2*log 2)^((3:O)/2)≠0)]
 have N:(log (P:O))^(2 - α)/(log (P:O))^2=(log (P:O))^(-α):=by rw[show (2:O) - α=-α+2 by ring,gF w,rpow_two,mul_div_cancel_right₀ _ _P]
 calc d8 P<=ht/(log (P:O))^2*∑a∈cV P,L a/(a:O):=Hb P hE
   _<=ht/(log (P:O))^2*(U*B):=dA J _P
   _<=ht/(log (P:O))^2*(U*(exp 1*(2*log 2)^((3:O)/2) *((log (P:O))^(2 - α)/(log (log (P:O)))^((3:O)/2)))):=dA (dA hC _P) _P
   _=G*(((log (P:O))^(2 - α)/(log (P:O))^2)/(log (log (P:O)))^((3:O)/2)):=by dsimp only[G];ring
   _=G*(log (P:O))^(-α)/(log (log (P:O)))^((3:O)/2):=by rw[N];ring
set_option maxHeartbeats 800000 in
theorem ford_upper_bound :
 let α : O:=1-(1+log (log 2))/log 2
 let w (j:ℕ):=((j:O)+1)^(-α)/(log ((j:O)+2))^((3:O)/2)
 ∃C:O,0< C/\∀ᶠ x:ℕ in atTop,∀j ≤ Nat.log 2 x/2,((c6 x j).card:O)<=C*((x:O)*w j):=by
 intro α w;obtain⟨H,h7,hp⟩:=di;obtain⟨J,A,P0,hh,hS⟩:=du;have d:0< log 2:=_l a3;have e:0< α/\α< 1:=by dsimp only[α];have hf:log (log 2)< log 2-1:=k7 d a4.ne;have B:(1+log (log 2))/log 2< 1:=(lF d).mpr _L;have N:1-(log 2)⁻¹<=log (log 2):=fl d;have hr:(log 2)⁻¹< 2:=(by rw[mz d _N];linarith[a3]);have h3:0< (1+log (log 2))/log 2:=(jI d).mpr _L;exact⟨by linarith,_L⟩
 obtain⟨b,K,h8⟩:∃b:ℕ,2000<=b/\P0<=2^(b/2):=⟨max 2000 (2*P0+2),eo _ _,by
   have B:P0<=max 2000 (2*P0+2)/2:=_O;exact (gC (n:=P0)).le.trans (dH _N B)⟩
 let l:O:=H*(16+J*(4:O)^α*(2:O)^((3:O)/2));let c:O:=((b:O)+1)*(log ((b:O)+2))^((3:O)/2);have T:0< log ((b:O)+2):=et (_l (dK (α:=O) b));refine⟨max l c,e9 _P (eo _ _),?_⟩;filter_upwards [lO 1] with x hx j hj;have hk:2*j<=Nat.log 2 x:=_O;have h:0< log ((j:O)+2):=et (_l (dK (α:=O) j));have hg:0< w j:=by dsimp only[w];positivity
 by_cases S:b<=j
 ·have i:2000<=j:=K.trans S;let M:O:=J*(4:O)^α*(2:O)^((3:O)/2)*w j;have h9:∀t∈Icc (2^(j/2)) x,d8 t<=M:=by
   intro t ht;have D:2^(j/2)<=t:=(dT.mp ht).1;have U:P0<=t:=h8.trans ((dH _N _O).trans D);have hl:=hS t U;have o:((j:O)+1)/4<=log (t:O):=by have B:(2:O)^(j/2)<=(t:O):=_M D;have N:=dM _P B;rw[fm]at N;have h3:(j:O)<=2*((j/2:ℕ):O)+1:=_M (_O :j<=2*(j/2)+1);have P:(2000:O)<=(j:O):=_M i;have W:((j:O)-1)/2<=((j/2:ℕ):O):=_L;have h4:((j:O)+1)/4<=((j:O)-1)/2*0.69:=_L;have h5:((j:O)-1)/2*0.69<=((j/2:ℕ):O)*log 2:=en W (_l kz) _N (dK _);linarith
   have X:0< log (t:O):=_l (show (0:O)< ((j:O)+1)/4 by positivity)
   have Q:log ((j:O)+2)/2<=log (log (t:O)):=(by have B:(j:O)+2<=(((j:O)+1)/4)^2:=(by have P:(2000:O)<=(j:O):=_M i;nlinarith);have N:=dM _P (B.trans (m9 _P o 2));rw[fm]at N;push_cast at N;linarith);have E:(log (t:O))^(-α)<=(4:O)^α*((j:O)+1)^(-α):=(by have B:(log (t:O))^(-α)<=(((j:O)+1)/4)^(-α):=rpow_le_rpow_of_nonpos _P o (_l e.1);have N:(((j:O)+1)/4)^(-α)=(4:O)^α*((j:O)+1)^(-α):=(by rw[div_rpow _P _N,lD (_N :(0:O)<=4),div_inv_eq_mul,e8]);exact B.trans_eq N);have Z:(log ((j:O)+2))^((3:O)/2)/(2:O)^((3:O)/2)<=(log (log (t:O)))^((3:O)/2):=by rw[<- div_rpow h.le _N];exact fx _P Q _N
   calc d8 t<=J*(log (t:O))^(-α)/(log (log (t:O)))^((3:O)/2):=hl
     _<=J*((4:O)^α*((j:O)+1)^(-α))/((log ((j:O)+2))^((3:O)/2)/(2:O)^((3:O)/2)):=mj _P (dA E A.le) _P Z
     _=M:=by dsimp only[M,w];field_simp [(_P :(log ((j:O)+2))^((3:O)/2)≠0),(_P :(2:O)^((3:O)/2)≠0)]
  have F:=hp x j M i hk (by dsimp only[M];positivity) h9;have q:1/(log ((2^j:ℕ):O))^2<=16*w j:=by
   have v:((j:O)+1)/4<=log ((2^j:ℕ):O):=(by rw[gx,g7,fm];have P:(2000:O)<=(j:O):=_M i;nlinarith[a3]);have u:0< log ((2^j:ℕ):O):=_l (show (0:O)< ((j:O)+1)/4 by positivity)
   have hs:((j:O)+1)^2/16<=(log ((2^j:ℕ):O))^2:=(by have:=m9 _P v 2;linarith);have B:1/(log ((2^j:ℕ):O))^2<=16/((j:O)+1)^2:=(by rw[mb (jB u) _P];linarith);have N:1/((j:O)+1)^2<=w j:=by
    dsimp only[w];rw[mb _P _P,gz];have R:(1:O)<=(j:O)+1:=_l (dK (α:=O) j);have y:((j:O)+1)^(-1:O)<=((j:O)+1)^(-α):=eT R (_l e.2);have m:(log ((j:O)+2))^((3:O)/2)<=(j:O)+1:=by
     have hm:log ((j:O)+2)<=sqrt ((j:O)+2):=by
      have hq:log (((j:O)+2)^((1:O)/4))<=((j:O)+2)^((1:O)/4):=(eY _P).trans _L;rw[kR _P]at hq;have h4:log ((j:O)+2)<=4*((j:O)+2)^((1:O)/4):=_L;have hc:4*((j:O)+2)^((1:O)/4)<=((j:O)+2)^((1:O)/2):=by
       have hd:(256:O)<=(j:O)+2:=(by have P:(2000:O)<=(j:O):=_M i;linarith);have hn:(4:O)<=((j:O)+2)^((1:O)/4):=by
        have B:=fx _N hd (_N :(0:O)<=1/4);have N:(256:O)^((1:O)/4)=4:=by
         rw[show (256:O)=(4:O)^(4:ℕ) by norm_num,<- eK,<- gE _N]
         norm_num
        linarith
       calc 4*((j:O)+2)^((1:O)/4)<=((j:O)+2)^((1:O)/4)*((j:O)+2)^((1:O)/4):=
             dE hn _P
         _=((j:O)+2)^((1:O)/2):=by rw[<- gF _P];norm_num
      rw[ik];exact h4.trans hc
     calc (log ((j:O)+2))^((3:O)/2)
         <= (sqrt ((j:O)+2))^((3:O)/2):=fx h.le hm _N
       _=((j:O)+2)^((3:O)/4):=by rw[ik,<- gE _P];norm_num
       _<=((j:O)+1)^(1:O):=by
           have ho:((j:O)+2)^(3:ℕ)<=((j:O)+1)^(4:ℕ):=by
             have P:(2000:O)<=(j:O):=_M i;have ha:((j:O)+2)^2<=2*((j:O)+1)^2:=_Q;have hb:(j:O)+2<=((j:O)+1)^2/2:=_Q
             calc ((j:O)+2)^3=((j:O)+2)^2*((j:O)+2):=by ring
               _<=(2*((j:O)+1)^2)*(((j:O)+1)^2/2):=en ha hb _P _P
               _=((j:O)+1)^4:=_R
           have h4:=fx _P ho (_N :(0:O)<=1/4);rw[<- eK ((j:O)+2),<- gE _P,<- eK ((j:O)+1),<- gE _P]at h4;rw[show ((3:ℕ):O)*((1:O)/4)=3/4 by norm_num,show ((4:ℕ):O)*((1:O)/4)=1 by norm_num]at h4
           exact h4
       _=(j:O)+1:=rpow_one _
    calc (log ((j:O)+2))^((3:O)/2)<=(j:O)+1:=m
      _=((j:O)+1)^(-1:O)*((j:O)+1)^2:=by rw[rpow_neg_one];field_simp [(_P :(j:O)+1≠0)]
      _<=((j:O)+1)^(-α)*((j:O)+1)^2:=dE y _P
   have hu:16/((j:O)+1)^2=16*(1/((j:O)+1)^2):=_R;linarith
  calc ((c6 x j).card:O)
      <= H*(x:O)*(1/(log ((2^j:ℕ):O))^2+M):=F
    _<=H*(x:O)*(16*w j+J*(4:O)^α*(2:O)^((3:O)/2)*w j):=dA (fd q eR) _P
    _=l*((x:O)*w j):=by dsimp only[l];ring
    _<=max l c*((x:O)*w j):=dE (eo _ _) _P
 ·push Not at S
  have z:((c6 x j).card:O)<=(x:O):=by
   have he:(c6 x j).card<=x:=by
    calc (c6 x j).card<=(Icc 1 x).card:=er (fj _ _)
      _=x:=by simp
   exact_mod_cast he
  have h0:1/c<=w j:=by
   dsimp only[c,w];rw[mb _P _P,gz];have h6:(j:O)+1<=(b:O)+1:=_M (_O :j+1<=b+1);have m:(log ((j:O)+2))^((3:O)/2)<=(log ((b:O)+2))^((3:O)/2):=fx h.le (dM _P (_M (_O :j+2<=b+2))) _N;have G:1<=((b:O)+1)*((j:O)+1)^(-α):=by
    have B:((j:O)+1)^(-1:O)<=((j:O)+1)^(-α):=eT (_l (dK (α:=O) j)) (_l e.2)
    calc (1:O)=((j:O)+1)*((j:O)+1)^(-1:O):=by
          rw[rpow_neg_one];field_simp [(_P :(j:O)+1≠0)]
      _<=((b:O)+1)*((j:O)+1)^(-α):=en h6 B _P _P
   calc (log ((j:O)+2))^((3:O)/2)
       <= 1*(log ((b:O)+2))^((3:O)/2):=by rw[gz];exact m
     _<=(((b:O)+1)*((j:O)+1)^(-α))*(log ((b:O)+2))^((3:O)/2):=dE G _P
     _=((j:O)+1)^(-α)*(((b:O)+1)*(log ((b:O)+2))^((3:O)/2)):=_R
  calc ((c6 x j).card:O)<=(x:O):=z
    _=c*((x:O)*(1/c)):=by field_simp [(_P :c≠0)]
    _<=max l c*((x:O)*w j):=en (ep _ _) (dA h0 (dK x)) _P _P
end
end Ford448
theorem OMA.solution:OMA.R_Erdos448_erdos_448_variants_ford_R1.H1:=by
 obtain⟨c,hc,hlo⟩:=Ford448.ford_lower_bound
 obtain⟨C,hC,hhi⟩:=Ford448.ford_upper_bound
 refine⟨c,C,hc,hC,?_⟩
 filter_upwards[hlo,hhi]with x hxlo hxhi j hj
 exact⟨hxlo j hj,hxhi j hj⟩
