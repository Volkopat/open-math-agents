import OMAStatements.S_mse_1364979

/-!
# Exponential growth of the generalized polygamma at imaginary orders

For s = 1 + ix, differentiate the defining expression and factor out ζ(s)/Γ(-ix).
The Hadamard product for ξ gives a lower bound on Re(ζ′/ζ)(s) with leading
term −(log x)/2. The digamma in the other summand has real part log x + O(1).
Consequently the factor multiplying 1/Γ(-ix) has upper and lower polynomial
bounds in x. Euler's reflection formula gives the exponential rate of Γ(-ix).

Credit: @Ico-NLE. The final arguments are in namespace PolygammaEstimate.
The following Apache-2.0 excerpts from open-math-agents (4d83d485d13e) supply
the analytic background. They have been trimmed and combined into one file.

* Xi factorization from RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1.R1.H2,
  based on Robin1984 and PrimeNumberTheoremAnd.
* Digamma series and vertical Stirling bound from RiemannHypothesis.li_criterion.R1.H2,
  adapted from the GammaFacts.Series and GammaFacts.StirlingVert modules of
  https://github.com/anthropics/zeta-23-lean/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
* Bounds on ζ, 1/ζ and ζ′ from Erdos454.erdos_454.R1.H1, based on PrimeNumberTheoremAnd.
-/
/- Copyright (c) 2026 Matteo Cipollina, Jonas Whidden, and PrimeNumberTheoremAnd authors.
Adapted under Apache-2.0 from kimihiro64/PrimeNumberTheoremAnd (f8f58c749d6c) and
kimihiro64/Robin1984 (e3697139babf): xi zeros and weighted theta tail bounds. -/
section
section
open scoped BigOperators
namespace Real
lemma YW {r:ℝ} (hr : 0 ≤ r) (qa : r ≤ 1/2) (m:ℕ) : r^(m+1)/(1 - r) ≤ 2*r^(m+1):=by
  have qc : 0 ≤ r^(m+1):=pow_nonneg hr _
  have qb : (1/2:ℝ) ≤ 1 - r:=by linarith
  calc
    r^(m+1)/(1 - r) ≤ r^(m+1)/(1/2:ℝ):=by
      exact div_le_div_of_nonneg_left qc (by positivity) qb
    _ = 2*r^(m+1):=by ring
end Real
namespace Complex
open scoped BigOperators in
lemma VI {z:ℂ} (hz : ‖z‖ < 1) : -log (1 - z) = ∑' n:ℕ,z^(n+1)/(n+1):=by
 have h:=hasSum_taylorSeries_neg_log hz
 rw [← h.tsum_eq,h.summable.tsum_eq_zero_add]
 simp only [pow_zero,Nat.cast_zero,div_zero,zero_add,Nat.cast_add,Nat.cast_one]
noncomputable
def W8 (m:ℕ) (z:ℂ):ℂ :=
 -logTaylor (m+1) (-z)
@[simp]
lemma Wy (z:ℂ) : W8 0 z=0:=by
 simp [W8,logTaylor_succ,logTaylor_zero]
@[simp]
lemma Wd (m:ℕ) : W8 m 0=0:=by
 simp [W8,logTaylor_at_zero]
lemma Wx (n:ℕ) (z:ℂ) : logTaylor (n+1) (-z)=logTaylor n (-z) - z^n/n:=by
 rw [logTaylor_succ,Pi.add_apply]
 have qa : (-1:ℂ)^(n+1)*(-z)^n = -z^n:=by
  have qb : (-z)^n=(((-1:ℂ)*z)^n):=by simp
  rw [qb,mul_pow,← mul_assoc,← pow_add]
  have qc : (-1:ℂ)^(n+1+n)=(-1:ℂ):=by
   rw [show n+1+n=2*n+1 by omega,pow_add,pow_mul]
   norm_num
  rw [qc]
  ring
 rw [show (-1:ℂ)^(n+1)*(-z)^n/n = -(z^n/n) by
  rw [qa]
  ring]
 abel
lemma Vk (m:ℕ) (z:ℂ) : logTaylor (m+1) (-z) = -∑ k ∈ Finset.range m,z^(k+1)/(k+1):=by
  induction m with
  | zero =>
      simp [logTaylor_succ,logTaylor_zero]
  | succ m hm =>
      rw [Wx,hm,Finset.sum_range_succ]
      have qa : ((m+1:ℕ):ℂ)=(1+(m:ℂ)):=by
        simp [Nat.cast_add,Nat.cast_one,add_comm]
      rw [qa]
      ring_nf
lemma Wk (m:ℕ) (z:ℂ) : W8 m z = ∑ k ∈ Finset.range m,z^(k+1)/(k+1):=by
 simpa [W8] using congrArg Neg.neg (Vk m z)
lemma VC (m:ℕ) (z:ℂ) : HasDerivAt (W8 m) (∑ j ∈ Finset.range m,z^j) z:=by
  cases m with
  | zero =>
      have qa : W8 0=fun _ : ℂ ↦ (0:ℂ):=by
        funext w
        exact Wy w
      simpa [qa] using (hasDerivAt_const z (c:=(0:ℂ)))
  | succ m =>
      have qb :
          (∑ j ∈ Finset.range (m+1),z^j) =
            ∑ j ∈ Finset.range (m+1),(-1)^j*(-z)^j:=by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1:ℂ)^j*(-z)^j=(-1:ℂ)^j*(((-1:ℂ)*z)^j):=by simp
          _ = ((-1:ℂ)^j*(-1:ℂ)^j)*z^j:=by rw [mul_pow]; ring
          _ = z^j:=by
                rw [← pow_add,show j+j=2*j by omega,pow_mul]
                norm_num
      rw [qb]
      simpa [W8] using!
        (((hasDerivAt_logTaylor (m+1) (-z)).comp z (hasDerivAt_neg z)).neg)
lemma Yw (m:ℕ) : Differentiable ℂ (fun z:ℂ => W8 m z):=by
 intro z
 exact (VC m z).differentiableAt
noncomputable
def un (m:ℕ) (z:ℂ):ℂ :=
 ∑' k,z^(m+1+k)/(m+1+k)
lemma WN {z:ℂ} (hz : ‖z‖ < 1) (m:ℕ) : Summable (fun k => z^(m+1+k)/((m+1+k):ℂ)):=by
  have qa : Summable (fun k:ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g:=fun k => ‖z‖ ^ k) qa ?_
  intro k
  rw [norm_div,norm_pow]
  have h1 : (1:ℝ) ≤ (m+1+k:ℝ):=by
    have : (0:ℝ) ≤ (m+k:ℝ):=by positivity
    nlinarith
  have qb : ‖(↑m+1 + ↑k:ℂ)‖ = (m+1+k:ℝ):=by
    simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
      (Complex.norm_natCast (m+1+k))
  rw [qb]
  calc
    ‖z‖ ^ (m+1+k)/(m+1+k:ℝ) ≤ ‖z‖ ^ (m+1+k):=by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m+1) * ‖z‖ ^ k:=by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k:=by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k:=one_mul _
lemma WY {z:ℂ} (hz : ‖z‖ < 1) (m:ℕ) : ‖un m z‖ ≤ ‖z‖ ^ (m+1)/(1 - ‖z‖):=by
  dsimp only [un]
  have qb : Summable (fun k => ‖z‖ ^ (m+1+k)):=by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m+1))
  have qa : Summable (fun k => ‖z^(m+1+k)/((m+1+k):ℂ)‖):=by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ qb
    intro k
    rw [norm_div,norm_pow]
    have qd : ‖(↑m+1 + ↑k:ℂ)‖ = (m+1+k:ℝ):=by
      simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
        (Complex.norm_natCast (m+1+k))
    rw [qd]
    have hm : 1 ≤ (m+1+k:ℝ):=by
      have : (0:ℝ) ≤ (m+k:ℝ):=by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k,z^(m+1+k)/((m+1+k):ℂ)‖
        ≤ ∑' k,‖z^(m+1+k)/((m+1+k):ℂ)‖ :=
          norm_tsum_le_tsum_norm qa
    _ ≤ ∑' k,‖z‖ ^ (m+1+k):=by
          refine qa.tsum_le_tsum ?_ qb
          intro k
          rw [norm_div,norm_pow]
          have hm : 1 ≤ (m+1+k:ℝ):=by
            have : (0:ℝ) ≤ (m+k:ℝ):=by positivity
            nlinarith
          have qd : ‖(↑m+1 + ↑k:ℂ)‖ = (m+1+k:ℝ):=by
            simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
              (Complex.norm_natCast (m+1+k))
          rw [qd]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m+1)/(1 - ‖z‖):=by
          have qe :
              (fun k => ‖z‖ ^ (m+1+k))=fun k => ‖z‖ ^ (m+1) * ‖z‖ ^ k:=by
            ext k
            rw [pow_add]
          rw [qe,tsum_mul_left]
          have qc:=hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [qc.tsum_eq,div_eq_mul_inv]
lemma ZA {z:ℂ} (hz : ‖z‖ < 1) (qa : ‖z‖ ≤ 1/2) (m:ℕ) :
  ‖un m z‖ ≤ 2 * ‖z‖ ^ (m+1) :=
 (WY hz m).trans (Real.YW (norm_nonneg z) qa m)
lemma yl (m:ℕ) (z:ℂ) : ‖W8 m z‖ ≤ (m:ℝ)*max 1 (‖z‖ ^ m):=by
  have qh :
      ‖W8 m z‖ ≤ ∑ k ∈ Finset.range m,‖z^(k+1)/(k+1)‖ := by
    rw [Wk]
    exact norm_sum_le _ _
  have qe : ∀ k ∈ Finset.range m,‖z^(k+1)/(k+1)‖ ≤ max 1 (‖z‖ ^ m):=by
    intro k hk
    rw [norm_div,norm_pow]
    have hk1 : (1:ℝ) ≤ (k:ℝ)+1:=by
      have qa : (1:ℕ) ≤ k+1:=Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast qa
    have qd : ‖((k:ℂ)+1)‖ = (k:ℝ)+1:=by
      simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
        (Complex.norm_natCast (k+1))
    have qf : k+1 ≤ m:=Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have qb : ‖z‖ ^ (k+1) ≤ max 1 (‖z‖ ^ m):=by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1:ℝ)
      · have : ‖z‖ ^ (k+1) ≤ 1:=by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have qi : (1:ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k+1) ≤ ‖z‖ ^ m:=pow_le_pow_right₀ qi qf
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k+1) / ‖((k:ℂ)+1)‖ = ‖z‖ ^ (k+1)/((k:ℝ)+1):=by simp [qd]
      _ ≤ ‖z‖ ^ (k+1):=by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m):=qb
  have qc :
      (∑ k ∈ Finset.range m,‖z^(k+1)/(k+1)‖) ≤
        ∑ _k ∈ Finset.range m,max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => qe k hk)
  have qg : ∑ _k ∈ Finset.range m,max 1 (‖z‖ ^ m)=(m:ℝ)*max 1 (‖z‖ ^ m):=by
    simp [Finset.sum_const]
  exact qh.trans (qc.trans_eq qg)
lemma yD {z:ℂ} (hz : ‖z‖ < 1) (m:ℕ) : -log (1 - z)=W8 m z+un m z:=by
 let f:ℕ → ℂ:=fun k ↦ z^(k+1)/((k:ℂ)+1)
 have qa : Summable f:=by
  simpa [f,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
   (WN hz 0)
 have qb:=qa.sum_add_tsum_nat_add m
 rw [VI hz,Wk,← qb]
 congr 1
 dsimp only [un]
 refine tsum_congr fun k ↦ ?_
 simp only [f,Nat.cast_add]
 ring_nf
end Complex
end
end
section
section
noncomputable section
namespace Complex
variable {z : ℂ}
theorem W3 (z:ℂ) : -‖z‖ ≤ z.re :=
 neg_le_of_abs_le (abs_re_le_norm z)
lemma Yr (z:ℂ) : ‖z - 1‖ ≤ 1 + ‖z‖ := by
 have qa : ‖(1:ℂ)‖ = (1:ℝ):=by simpa using Complex.norm_natCast 1
 simpa [qa,add_comm] using norm_sub_le z (1:ℂ)
lemma wP (u:ℂ) (n:ℕ) (hu : (1:ℝ) ≤ ‖u‖) : ‖(u^n)⁻¹‖ ≤ 1:=by
  have hge : (1:ℝ) ≤ ‖u^n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u^n)⁻¹‖ = ‖(1:ℂ)/u^n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u^n‖ := by
        have qa : ‖(1:ℂ)‖ = (1:ℝ):=by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div,qa]
    _ ≤ 1:=by simpa [one_div] using inv_le_one_of_one_le₀ hge
end Complex
end
end
end
section
section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def WE (m:ℕ) (z:ℂ):ℂ :=
 (1 - z)*exp (W8 m z)
lemma Wf (m:ℕ) (z:ℂ) : WE m z=(1 - z)*exp (W8 m z):=by
 simp [WE]
@[simp]
lemma Vf (m:ℕ) : WE m 0=1:=by
 simp [WE,Wd]
lemma Yn (m:ℕ) (z:ℂ) : WE m z=0 ↔ z=1:=by
  constructor
  · intro hz
    rw [WE] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [WE]
lemma Yk (m:ℕ) (z:ℂ) : WE m z ≠ 0 ↔ z ≠ 1:=by
 simpa [ne_eq] using (not_congr (Yn (m:=m) (z:=z)))
lemma wL (m:ℕ) {z:ℂ} (hz : z ≠ 1) :
  WE m z ≠ 0 :=
 (Yk (m:=m) (z:=z)).2 hz
lemma ZD (m:ℕ) : Differentiable ℂ (fun z:ℂ => WE m z):=by
 simpa [WE] using!
  ((differentiable_const (c:=(1:ℂ))).sub differentiable_id).mul
   (differentiable_exp.comp (Yw m))
theorem yQ (m:ℕ) {a:ℂ} (ha : a ≠ 0) : analyticOrderAt (fun z:ℂ => WE m (z/a)) a=(1 : ℕ∞):=by
 set F:ℂ → ℂ:=fun z => WE m (z/a)
 have hF : AnalyticAt ℂ F a:=by
  have qe : Differentiable ℂ (fun z:ℂ => z/a):=by
   simp [div_eq_mul_inv]
  have qc : Differentiable ℂ F:=(ZD m).comp qe
  exact Differentiable.analyticAt (f:=F) qc a
 let g:ℂ → ℂ:=fun z => (-a⁻¹)*Complex.exp (W8 m (z/a))
 have hg : AnalyticAt ℂ g a:=by
  have qe : Differentiable ℂ (fun z:ℂ => z/a):=by
   simp [div_eq_mul_inv]
  have qf : Differentiable ℂ (fun z:ℂ => W8 m (z/a)) :=
   (Yw m).comp qe
  have qg : Differentiable ℂ (fun z:ℂ => Complex.exp (W8 m (z/a))) :=
   (Complex.differentiable_exp).comp qf
  have qa : Differentiable ℂ g:=by
   simpa [g] using qg.const_mul (-a⁻¹ : ℂ)
  exact Differentiable.analyticAt (f:=g) qa a
 have hg0 : g a ≠ 0:=by
  have qb : (-a⁻¹ : ℂ) ≠ 0:=by simp [ha]
  have qd : Complex.exp (W8 m (a/a)) ≠ 0 :=
   Complex.exp_ne_zero (W8 m (a/a))
  simpa [g] using mul_ne_zero qb qd
 refine (hF.analyticOrderAt_eq_natCast (n:=1)).2 ?_
 refine ⟨g,hg,hg0,?_⟩
 refine Filter.Eventually.of_forall ?_
 intro z
 have qh : (1 - z/a)=(z - a)*(-a⁻¹):=by
  have h1 : (1:ℂ)=a*a⁻¹ := by simp [ha]
  simp [div_eq_mul_inv,h1]
  ring
 simp only [F,g,pow_one,smul_eq_mul]
 rw [Wf]
 simp [qh,mul_assoc]
lemma Zo (m:ℕ) {z:ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) : WE m z=exp (-un m z):=by
  unfold WE
  have qa : 1 - z ≠ 0:=sub_ne_zero.mpr hz1.symm
  rw [← exp_log qa,← Complex.exp_add]
  have qc : log (1 - z)+W8 m z = -un m z:=by
    have qb:=yD hz m
    calc
      log (1 - z)+W8 m z
          = log (1 - z)+(W8 m z+un m z) - un m z:=by ring
      _ = log (1 - z)+(-log (1 - z)) - un m z:=by rw [qb]
      _ = -un m z:=by ring
  simp [qc]
theorem wB {m:ℕ} {z:ℂ} (hz : ‖z‖ ≤ 1/2) : ‖WE m z - 1‖ ≤ 4 * ‖z‖ ^ (m+1):=by
  by_cases hm : m=0
  · subst hm
    have qe : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1:=by
      have h : (1 - z) - 1 = -z:=by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1:=by simp
        _ ≤ 4 * ‖z‖ ^ 1:=by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [WE] using qe
  · have qf : ‖z‖ < 1:=lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z=1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have qh : WE m z=exp (-un m z) :=
      Zo m qf hz1
    rw [qh]
    have qb:=ZA qf hz m
    have qc : ‖-un m z‖ ≤ 1:=by
      simp only [norm_neg]
      have : ‖un m z‖ ≤ 1:=by
        have qd : 0 < m:=Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m+1:=by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 qd)
        have qi : (‖z‖ ^ (m+1)) ≤ (‖z‖ ^ 2):=by
          have qj : ‖z‖ ≤ 1:=by nlinarith [hz]
          have qk : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one qk qj h2
        have ql : 2 * ‖z‖ ^ (m+1) ≤ 2 * ‖z‖ ^ 2:=by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1:=by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have qg : ‖z‖ ^ 2 ≤ (1/2:ℝ)^2:=pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (qb.trans ql).trans hsq
      linarith
    have qa : ‖exp (-un m z) - 1‖ ≤ 2 * ‖-un m z‖ :=
      Complex.norm_exp_sub_one_le qc
    simp only [norm_neg] at qa
    calc
      ‖exp (-un m z) - 1‖ ≤ 2 * ‖un m z‖ := qa
      _ ≤ 2*(2 * ‖z‖ ^ (m+1)):=by gcongr
      _ = 4 * ‖z‖ ^ (m+1):=by ring
lemma zP (m:ℕ) (z:ℂ) : Real.log ‖1 - z‖ - ‖W8 m z‖ ≤ Real.log ‖WE m z‖ := by
  by_cases hz1 : z=(1:ℂ)
  · subst hz1
    simp [WE]
  set S : ℂ:=W8 m z
  have hS : WE m z=(1 - z)*Complex.exp S:=by
    simp [WE,S]
  have qa : 0 < ‖(1:ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have qb :
      Real.log ‖WE m z‖ = Real.log ‖1 - z‖ + S.re:=by
    have hne : ‖(1:ℂ) - z‖ ≠ 0:=ne_of_gt qa
    calc
      Real.log ‖WE m z‖
          = Real.log (‖(1:ℂ) - z‖ * ‖Complex.exp S‖):=by
              simp [hS]
      _ = Real.log ‖(1:ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1:ℂ) - z‖ + S.re:=by
            simp [Complex.norm_exp,Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re:=by simp [sub_eq_add_neg,add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.W3 S
  have : Real.log ‖WE m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [qb,hre]
  simpa [S] using this
lemma y7 {m:ℕ} {z:ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) : (-2:ℝ) * ‖z‖ ^ (m+1) ≤ Real.log ‖WE m z‖ := by
  have qa : ‖z‖ < (1:ℝ):=lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1:ℂ):=by
    intro h
    have : (1:ℝ) ≤ (1/2:ℝ):=by
      simpa [h] using hz
    norm_num at this
  have hEq : WE m z=Complex.exp (-un m z) :=
    Zo m qa hz1
  have qc :
      Real.log ‖WE m z‖ = (-un m z).re:=by
    simp [hEq,Complex.norm_exp,Real.log_exp]
  have hre : (-un m z).re ≥ -‖un m z‖ := by
    simpa [norm_neg] using Complex.W3 (-un m z)
  have qb:=ZA qa hz m
  have : (-un m z).re ≥ (-2:ℝ) * ‖z‖ ^ (m+1):=by
    calc
      (-un m z).re ≥ -‖un m z‖ := hre
      _ ≥ (-2:ℝ) * ‖z‖ ^ (m+1):=by
            nlinarith [qb]
  simpa [qc,mul_assoc,mul_left_comm,mul_comm] using this
end Complex
end
end
end
section
section
noncomputable section
open Filter Topology
namespace Complex
theorem wU {a z:ℂ} (ha : a ≠ 0) (hz : z ≠ a) : logDeriv (fun w:ℂ => WE 1 (w/a)) z=1/(z - a)+1/a:=by
 have hE :
   (fun w:ℂ => WE 1 (w/a)) =
    fun w:ℂ => (1 - w/a)*exp (w/a):=by
  ext w
  simp [Wf,Wk]
 have hf : (1 - z/a) ≠ 0:=by
  intro hzero
  have qd : z/a=1:=by
   exact (sub_eq_zero.mp hzero).symm
  exact hz ((div_eq_one_iff_eq ha).1 qd)
 rw [hE,logDeriv_mul z hf (exp_ne_zero (z/a)) (by fun_prop) (by fun_prop)]
 have qc : logDeriv (fun w:ℂ => 1 - w/a) z=1/(z - a):=by
  rw [logDeriv_apply]
  have qa : deriv (fun w:ℂ => 1 - w/a) z = -(1/a):=by
   simp [one_div]
  rw [qa]
  have haz : -z+a ≠ 0:=by
   simpa [sub_eq_add_neg,add_comm] using sub_ne_zero.mpr (Ne.symm hz)
  field_simp [ha,sub_ne_zero.mpr hz,haz]
  have qe : a - z ≠ 0:=sub_ne_zero.mpr (Ne.symm hz)
  have hza : z - a = -(a - z):=by ring
  rw [hza]
  field_simp [qe]
 have qb : logDeriv (fun w:ℂ => exp (w/a)) z=1/a:=by
  rw [logDeriv_apply]
  have qa : deriv (fun w:ℂ => exp (w/a)) z =
    exp (z/a)*(1/a):=by
   simp [one_div]
  rw [qa]
  field_simp [exp_ne_zero (z/a)]
 rw [qc,qb]
end Complex
end
end
end
section
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜} {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma wg (f : 𝕜 → E) {U K : Set 𝕜} (hK : IsCompact K) (hKU : K ⊆ U) : (K ∩ (MeromorphicOn.divisor f U).support).Finite:=by
 classical
 set D : Function.locallyFinsuppWithin U ℤ:=MeromorphicOn.divisor f U
 have qc :
   ∀ x ∈ K,∃ V : Set 𝕜,V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support):=by
  intro x hxK
  rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V,hV,hfin⟩
  exact ⟨V,hV,hfin⟩
 choose V hVnhds hVfin using qc
 rcases hK.elim_nhds_subcover' (U:=fun x hx => V x hx) (hU:=fun x hx => hVnhds x hx) with
  ⟨t,ht⟩
 have qd :
   K ∩ D.support ⊆ ⋃ x ∈ t,(V (x : 𝕜) x.2 ∩ D.support):=by
  intro y hy
  rcases hy with ⟨hyK,hyS⟩
  have qa : y ∈ ⋃ x ∈ t,V (x : 𝕜) x.2:=ht hyK
  rcases Set.mem_iUnion.1 qa with ⟨x,hycov'⟩
  rcases Set.mem_iUnion.1 hycov' with ⟨hxT,hyV⟩
  refine Set.mem_iUnion.2 ⟨x,Set.mem_iUnion.2 ?_⟩
  exact ⟨hxT,⟨hyV,hyS⟩⟩
 have qb : Set.Finite (⋃ x ∈ t,(V (x : 𝕜) x.2 ∩ D.support)):=by
  classical
  refine (t.finite_toSet).biUnion ?_
  intro x hx
  simpa using (hVfin (x : 𝕜) x.2)
 exact qb.subset qd
end MeromorphicOn
end
end
section
section
open Set
namespace Complex.Hadamard
def WH (f:ℂ → ℂ) (U : Set ℂ) : Type :=
 Σ z:ℂ,Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev Wz (f:ℂ → ℂ) (U : Set ℂ) : Type :=
 {p : WH f U // p.1 ≠ 0}
abbrev Wc {f:ℂ → ℂ} {U : Set ℂ} (p : Wz f U):ℂ :=
 p.1.1
@[simp]
lemma Yd {f:ℂ → ℂ} {U : Set ℂ} (p : Wz f U) :
  Wc p ≠ 0:=p.2
@[simp]
lemma y4 {f:ℂ → ℂ} {U : Set ℂ} (p : Wz f U) : MeromorphicOn.divisor f U (Wc p) ≠ 0:=by
 have hn :
   Int.toNat (MeromorphicOn.divisor f U (Wc p)) ≠ 0:=by
  intro h0
  have q0 : Fin 0:=by
   simpa [Wc,h0] using p.1.2
  exact Fin.elim0 q0
 intro hdiv
 have : Int.toNat (MeromorphicOn.divisor f U (Wc p))=0:=by
  simp [hdiv]
 exact hn this
noncomputable def VJ (m:ℕ) (f:ℂ → ℂ) (U : Set ℂ) (z:ℂ):ℂ :=
 ∏' p : Wz f U,WE m (z/Wc p)
@[simp]
lemma Yy (m:ℕ) (f:ℂ → ℂ) (U : Set ℂ) : VJ m f U 0=1:=by
 simp [VJ]
end Complex.Hadamard
end
end
section
section
namespace Complex
section UniformMul
theorem _root_.TendstoUniformlyOn.WL {ι : Type*} {p : Filter ι} {K : Set ℂ} {F : ι → ℂ → ℂ} {f:ℂ → ℂ} {h:ℂ → ℂ} (hF : TendstoUniformlyOn F f p K) (hh : ∃ C,∀ z ∈ K,‖h z‖ ≤ C) : TendstoUniformlyOn (fun n z => h z*F n z) (fun z => h z*f z) p K:=by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε,hεpos,hεu⟩
  rcases hh with ⟨C,hC⟩
  set C' : ℝ:=max C 1
  have qa : 0 < C':=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K,‖h z‖ ≤ C':=fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p:ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C',div_pos hεpos qa,fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p,∀ z:ℂ,z ∈ K → dist (f z) (F n z) < ε / C':=hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C':=by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C'*(ε / C'):=mul_lt_mul_of_pos_left hn' qa
  have qb :
      ‖h z*f z - h z*F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z*f z - h z*F n z‖ = ‖h z*(f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have qc : dist (h z*f z) (h z*F n z) < ε := by
    rw [dist_eq_norm,qb]
    have qd : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C'*(ε / C'):=hlt
        _ = ε := by field_simp [qa.ne']
    exact qd
  exact hεu qc
end UniformMul
end Complex
end
end
section
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma vl {f:ℂ → ℂ} {U : Set ℂ} (B:ℝ) (hBU : Metric.closedBall (0:ℂ) B ⊆ U) : Finite {p : Wz f U // ‖Wc p‖ ≤ B}:=by
 set D : Function.locallyFinsuppWithin U ℤ:=MeromorphicOn.divisor f U
 have hK : IsCompact (Metric.closedBall (0:ℂ) B):=isCompact_closedBall _ _
 have qc : ((Metric.closedBall (0:ℂ) B) ∩ D.support).Finite :=
  MeromorphicOn.wg (f:=f) (U:=U)
   (K:=Metric.closedBall (0:ℂ) B) hK hBU
 set pts : Set ℂ:=((Metric.closedBall (0:ℂ) B) ∩ D.support) \ {0}
 have qg : pts.Finite:=qc.sdiff
 letI : Fintype pts:=qg.fintype
 let T : Type := Σ z : pts,Fin (Int.toNat (D z.1))
 haveI : Finite T:=by infer_instance
 let F :
   {p : Wz f U // ‖Wc p‖ ≤ B} → T:=fun p =>
  ⟨⟨Wc p.1,by
    have qd : Wc p.1 ∈ Metric.closedBall (0:ℂ) B:=by
     simpa [Metric.mem_closedBall,dist_zero_right] using p.2
    have qb : Wc p.1 ∈ D.support:=by
     have qa :
       Int.toNat (MeromorphicOn.divisor f U (Wc p.1)) ≠ 0:=by
      intro h0
      have qe :
        Fin (Int.toNat (MeromorphicOn.divisor f U (Wc p.1))):=by
       simpa [D] using p.1.1.2
      have : Fin 0:=by simpa [h0] using qe
      exact Fin.elim0 this
     have qf : D (Wc p.1) ≠ 0:=by
      intro hD0
      apply qa
      simp [D,hD0]
     simp [D,Function.locallyFinsuppWithin.support,Function.support]
    have qh : Wc p.1 ≠ 0:=Yd p.1
    exact ⟨⟨qd,qb⟩,by simp [Set.mem_singleton_iff]⟩⟩,
   p.1.1.2⟩
 refine Finite.of_injective F ?_
 intro p q hpq
 apply Subtype.ext
 apply Subtype.ext
 have h':=(Sigma.mk.inj_iff.1 hpq)
 have hz : Wc p.1=Wc q.1:=congrArg Subtype.val h'.1
 apply (Sigma.mk.inj_iff).2
 refine ⟨hz,?_⟩
 exact h'.2
lemma ZB {f:ℂ → ℂ} {U : Set ℂ} (B:ℝ) (hBU : Metric.closedBall (0:ℂ) B ⊆ U) : ({p : Wz f U | ‖Wc p‖ ≤ B} : Set _).Finite:=by
 let s : Set (Wz f U):={p | ‖Wc p‖ ≤ B}
 haveI : Finite (↥s) :=
  vl (f:=f) (U:=U) B hBU
 exact Set.toFinite s
lemma y8 {z a:ℂ} {R:ℝ} (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2*R:ℝ) < ‖a‖) : ‖z/a‖ ≤ (1/2:ℝ):=by
  have qa : 0 < (2*R:ℝ):=by nlinarith [hR]
  have qf : ‖a‖⁻¹ < (2*R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt qa ha
  have qb : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have qc : R * ‖a‖⁻¹ < R*(2*R)⁻¹ :=
    mul_lt_mul_of_pos_left qf hR
  have qd : R*(2*R)⁻¹ = (1/2:ℝ):=by
    have qg : (R:ℝ) ≠ 0:=hR.ne'
    rw [show R*(2*R)⁻¹ = R/(2*R) by simp [div_eq_mul_inv]]
    field_simp [qg]
  have qe : ‖z/a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z/a‖ = ‖z‖ * ‖a‖⁻¹ := qe
      _ ≤ R * ‖a‖⁻¹ := qb
      _ < R*(2*R)⁻¹ := qc
      _ = (1/2:ℝ):=qd
theorem zj {f:ℂ → ℂ} {z:ℂ} (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (2:ℕ))) (hz : ∀ p : Wz f (Set.univ : Set ℂ),z ≠ Wc p) : Summable (fun p : Wz f (Set.univ : Set ℂ) => 1/(z - Wc p)+1/Wc p):=by
  let R : ℝ:=max ‖z‖ 1
  have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  have qi : ‖z‖ ≤ R:=le_max_left _ _
  let u : Wz f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2*R)*(‖Wc p‖⁻¹ ^ (2:ℕ))
  have hu : Summable u:=h_sum.mul_left (2*R)
  refine hu.of_norm_bounded_eventually ?_
  have qf :
      ∀ᶠ p : Wz f (Set.univ : Set ℂ) in Filter.cofinite,
        (2*R:ℝ) < ‖Wc p‖ := by
    have qj :
        ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤
          2*R} : Set _).Finite:=by
      have : Metric.closedBall (0:ℂ) (2*R) ⊆ (Set.univ : Set ℂ):=by simp
      exact ZB
        (f:=f) (U:=(Set.univ : Set ℂ)) (B:=2*R) this
    have:=qj.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖Wc p‖ ≤ 2*R:=by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [qf] with p hp
  let a : ℂ:=Wc p
  have ha0 : a ≠ 0:=Yd p
  have qk : z - a ≠ 0:=sub_ne_zero.mpr (hz p)
  have qg : 1/(z - a)+1/a=z/(a*(z - a)):=by
    field_simp [ha0,qk]
    ring
  have ql : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have qm : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h:=norm_add_le z (a - z)
      simpa [a,sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using h
    simpa [norm_sub_rev] using qm
  have qc : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [ql,qi,hp]
  have qh : ‖1/(z - a)+1/a‖ ≤ (2*R)*(‖a‖⁻¹ ^ (2:ℕ)):=by
    rw [qg,norm_div,norm_mul]
    have qb : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have qa : 0 < ‖z - a‖ := norm_pos_iff.mpr qk
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [qb.ne',qa.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹):=by
              gcongr
              have qd : 0 < ‖a‖ / 2:=by positivity
              have qn : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le qd qc
              have qe : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [qb.ne']
              simpa [qe] using qn
      _ = (2*R)*(‖a‖⁻¹ ^ (2:ℕ)):=by ring
  simpa [u,a] using qh
theorem z9 (m:ℕ) (f:ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : HasProdUniformlyOn (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) => WE m (z/Wc p)) (VJ m f (Set.univ : Set ℂ)) K:=by
 rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0,hR0⟩
 set R : ℝ:=max R0 1
 have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
 have qb : ∀ z ∈ K,‖z‖ ≤ R:=fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
 let g : Wz f (Set.univ : Set ℂ) → ℂ → ℂ :=
  fun p z => WE m (z/Wc p) - 1
 let u : Wz f (Set.univ : Set ℂ) → ℝ :=
  fun p => (4*R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1))
 have hu : Summable u:=h_sum.mul_left (4*R^(m+1))
 have qg :
   ∀ᶠ p : Wz f (Set.univ : Set ℂ) in Filter.cofinite,
    (2*R:ℝ) < ‖Wc p‖ := by
  have qj :
    ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ 2*R} :
      Set _).Finite:=by
   have : Metric.closedBall (0:ℂ) (2*R) ⊆ (Set.univ : Set ℂ):=by simp
   exact ZB (f:=f) (U:=(Set.univ : Set ℂ)) (B:=2*R) this
  have:=qj.eventually_cofinite_notMem
  filter_upwards [this] with p hp
  have : ¬ ‖Wc p‖ ≤ 2*R:=by simpa using hp
  exact lt_of_not_ge this
 have qc :
   ∀ᶠ p in Filter.cofinite,∀ z ∈ K,‖g p z‖ ≤ u p:=by
  filter_upwards [qg] with p hp z hzK
  have qk : ‖z‖ ≤ R:=qb z hzK
  have qd : ‖z/Wc p‖ ≤ (1/2:ℝ):=by
   exact y8 hRpos qk hp
  have hE :
    ‖WE m (z/Wc p) - 1‖ ≤
     4 * ‖z/Wc p‖ ^ (m+1) :=
   wB (m:=m) (z:=z/Wc p) qd
  have qe :
    ‖z/Wc p‖ ^ (m+1) ≤
     (R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1)):=by
   have : ‖z/Wc p‖ = ‖z‖ * ‖Wc p‖⁻¹ := by
    simp [div_eq_mul_inv]
   rw [this]
   have : (‖z‖ * ‖Wc p‖⁻¹)^(m+1) =
     ‖z‖ ^ (m+1)*(‖Wc p‖⁻¹ ^ (m+1)):=by
    simp [mul_pow]
   rw [this]
   have qa : ‖z‖ ^ (m+1) ≤ R^(m+1) :=
    pow_le_pow_left₀ (norm_nonneg z) qk (m+1)
   gcongr
  dsimp [g,u]
  nlinarith [hE,qe]
 have ql : ∀ p,ContinuousOn (g p) K:=by
  intro p
  have qf : Continuous (fun z:ℂ => WE m z) :=
   (ZD m).continuous
  have qm : Continuous fun z:ℂ => z/Wc p:=by
   simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
  have qh : Continuous fun z:ℂ => WE m (z/Wc p) :=
   qf.comp qm
  simpa only [g] using qh.continuousOn.fun_sub continuous_const.continuousOn
 have qi :
   HasProdUniformlyOn (fun p z ↦ 1+g p z) (fun z ↦ ∏' p,(1+g p z)) K:=by
  simpa using
   Summable.hasProdUniformlyOn_one_add (f:=g) (u:=u) (K:=K) hK hu qc ql
 simpa [g,VJ,sub_eq_add_neg,add_assoc,add_left_comm,add_comm]
  using! qi
theorem zB (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : HasProdLocallyUniformlyOn (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) => WE m (z/Wc p)) (VJ m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ):=by
 refine hasProdLocallyUniformlyOn_of_forall_compact
   (f:=fun p z => WE m (z/Wc p))
   (g:=VJ m f (Set.univ : Set ℂ))
   (s:=(Set.univ : Set ℂ)) isOpen_univ ?_
 intro K hKU hK
 simpa using
  (z9 (m:=m) (f:=f) (K:=K) hK h_sum)
theorem yt (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : DifferentiableOn ℂ (VJ m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ):=by
 have qb :
   TendstoLocallyUniformlyOn
    (fun (s : Finset (Wz f (Set.univ : Set ℂ))) (z:ℂ) =>
     ∏ p ∈ s,WE m (z/Wc p))
    (VJ m f (Set.univ : Set ℂ))
    Filter.atTop (Set.univ : Set ℂ):=by
  simpa [HasProdLocallyUniformlyOn] using
   (zB (m:=m) (f:=f) h_sum)
 have hF :
   ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in Filter.atTop,
    DifferentiableOn ℂ
     (fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p))
     (Set.univ : Set ℂ):=by
  refine Filter.Eventually.of_forall ?_
  intro s
  have qa :
    Differentiable ℂ
     (fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p)):=by
   let F : Wz f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => WE m (z/Wc p)
   have hF' : ∀ p ∈ s,Differentiable ℂ (F p):=by
    intro p hp
    have qc : Differentiable ℂ (fun z:ℂ => z/Wc p):=by
     have : Differentiable ℂ (fun z:ℂ => z*((Wc p)⁻¹)) :=
      (differentiable_id : Differentiable ℂ (fun z:ℂ => z)).mul_const
       ((Wc p)⁻¹)
     simp [div_eq_mul_inv]
    exact (ZD m).comp qc
   simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f:=F) (u:=s) hF')
  simpa using qa.differentiableOn
 haveI : (Filter.atTop : Filter (Finset (Wz f (Set.univ : Set ℂ)))).NeBot :=
  Filter.atTop_neBot
 exact qb.differentiableOn hF isOpen_univ
theorem yu
  (m:ℕ) (f:ℂ → ℂ)
  (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
   ‖Wc p‖⁻¹ ^ (m+1))) (z:ℂ) :
  DifferentiableAt ℂ (VJ m f (Set.univ : Set ℂ)) z :=
 ((yt m f h_sum) z (by simp)).differentiableAt
  (by simp)
theorem yy {f:ℂ → ℂ} {z:ℂ} (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (2:ℕ))) (hz : ∀ p : Wz f (Set.univ : Set ℂ),z ≠ Wc p) (qa : VJ 1 f (Set.univ : Set ℂ) z ≠ 0) : logDeriv (VJ 1 f (Set.univ : Set ℂ)) z = ∑' p : Wz f (Set.univ : Set ℂ),(1/(z - Wc p)+1/Wc p):=by
  let Φ : Wz f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => WE 1 (w/Wc p)
  have hf : ∀ p,Φ p z ≠ 0:=by
    intro p
    have hp0 : Wc p ≠ 0:=Yd p
    refine wL 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p,DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ):=by
    intro p
    have qd : Differentiable ℂ (fun w:ℂ => w/Wc p):=by
      have : Differentiable ℂ (fun w:ℂ => w*((Wc p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w:ℂ => w)).mul_const
          ((Wc p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((ZD 1).comp qd).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z:=by
    have hm :
        Summable (fun p : Wz f (Set.univ : Set ℂ) =>
          1/(z - Wc p)+1/Wc p) :=
      zj h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : Wc p ≠ 0:=Yd p
    simpa [Φ] using
      (Complex.wU
        (a:=Wc p) (z:=z) hp0 (hz p)).symm
  have qb : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ):=by
    have qc:=zB
      (m:=1) (f:=f) h_sum
    simpa [Φ,VJ] using qc.multipliableLocallyUniformlyOn
  have qe : (∏' p,Φ p z) ≠ 0:=by
    simpa [Φ,VJ] using qa
  have qf : logDeriv (∏' p,Φ p ·) z = ∑' p,logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s:=(Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' qb qe
  calc
    logDeriv (VJ 1 f (Set.univ : Set ℂ)) z
        = ∑' p,logDeriv (Φ p) z:=by
          simpa [Φ,VJ] using! qf
    _ = ∑' p : Wz f (Set.univ : Set ℂ),
          (1/(z - Wc p)+1/Wc p):=by
          refine tsum_congr fun p => ?_
          have hp0 : Wc p ≠ 0:=Yd p
          simpa [Φ] using
            Complex.wU
              (a:=Wc p) (z:=z) hp0 (hz p)
end Complex.Hadamard
end
end
section
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma vZ {f:ℂ → ℂ} (hf : Differentiable ℂ f) (z:ℂ) : MeromorphicOn.divisor f (Set.univ : Set ℂ) z=(analyticOrderNatAt f z:ℤ):=by
  have qa : MeromorphicOn f (Set.univ : Set ℂ):=by
    intro w hw
    exact (Differentiable.analyticAt (f:=f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply qa (by simp : z ∈ (Set.univ : Set ℂ)),analyticOrderNatAt]
  have han : AnalyticAt ℂ f z:=Differentiable.analyticAt (f:=f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq,h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq,h]
theorem Z0 (f:ℂ → ℂ) (z₀ : ℂ) : ({p : Wz f (Set.univ : Set ℂ) | Wc p=z₀} : Set _).Finite:=by
 have qa :
   ({p : Wz f (Set.univ : Set ℂ) | Wc p=z₀} : Set _)
    ⊆ ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ ‖z₀‖} :
     Set _):=by
  intro p hp
  have : Wc p=z₀ := hp
  simp [this]
 have qb :
   ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ ‖z₀‖} :
    Set _).Finite:=by
  have : Metric.closedBall (0:ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ):=by simp
  simpa using (ZB (f:=f) (U:=(Set.univ : Set ℂ))
   (B := ‖z₀‖) this)
 exact qb.subset qa
def Z9 (f:ℂ → ℂ) (z₀ : ℂ) :
  Finset (Wz f (Set.univ : Set ℂ)) :=
 (Z0 (f:=f) z₀).toFinset
@[simp]
lemma Zl (f:ℂ → ℂ) (z₀ : ℂ) (p : Wz f (Set.univ : Set ℂ)) : p ∈ Z9 (f:=f) z₀ ↔ Wc p=z₀ := by
 simp [Z9]
theorem ww (f:ℂ → ℂ) (z₀ : ℂ) : ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),Z9 (f:=f) z₀ ⊆ s:=by
 refine (Filter.eventually_atTop.2 ?_)
 refine ⟨Z9 (f:=f) z₀,?_⟩
 intro s hs
 exact hs
lemma zN (f:ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (Z9 (f:=f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀):=by
  let S : Set (Wz f (Set.univ : Set ℂ)):={p | Wc p=z₀}
  have hS : S.Finite:=Z0 (f:=f) z₀
  set n : ℕ:=Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have qc : Nat.card S=n:=by
    classical
    haveI : Fintype S:=hS.fintype
    let e : S ≃ Fin n :=
      { toFun:=by
          intro x
          rcases x with ⟨p,hp⟩
          rcases p with ⟨⟨z,q⟩,hz⟩
          have qd : z=z₀ := by simpa [Wc] using! hp
          subst qd
          simpa [n] using q
        invFun:=by
          intro q
          refine ⟨⟨⟨z₀,?_⟩,hz₀⟩,?_⟩
          · simpa [n] using q
          · simp [S,Wc]
        left_inv:=by
          rintro ⟨p,hp⟩
          rcases p with ⟨⟨z,q⟩,hz⟩
          have qd : z=z₀ := by simpa [Wc] using! hp
          subst qd
          (ext; rfl)
        right_inv:=by
          intro q
          rfl }
    have h:=Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have qb : S.ncard=n:=by
    simpa [Nat.card_coe_set_eq] using qc
  have hto : hS.toFinset=Z9 (f:=f) z₀ := by
    rfl
  have qa : S.ncard=(Z9 (f:=f) z₀).card:=by
    have h' : S.ncard=hS.toFinset.card:=Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact qa.symm.trans qb
lemma zt {f:ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : (Z9 (f:=f) z₀).card=analyticOrderNatAt f z₀ := by
 have qb :
   MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
  vZ (f:=f) hf z₀
 have qa : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
  analyticOrderNatAt f z₀ := by
  simp [qb]
 exact (zN (f:=f) (z₀ := z₀) hz₀).trans qa
lemma z3 {f:ℂ → ℂ} (z₀ : ℂ) (p : Wz f (Set.univ : Set ℂ)) : p ∉ Z9 (f:=f) z₀ ↔ Wc p ≠ z₀ := by
 simp [Zl]
end Complex.Hadamard
end
end
end
section
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def VE (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) : ℂ:=by
 classical
 exact if p ∈ Z9 (f:=f) z₀ then (1:ℂ)
  else WE m (z/Wc p)
@[simp]
theorem wb
  (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ)
  (p : Wz f (Set.univ : Set ℂ)) (z:ℂ)
  (hp : p ∈ Z9 (f:=f) z₀) :
  VE m f z₀ p z=1:=by
 classical
 simp [VE,hp]
@[simp]
theorem zw
  (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ)
  (p : Wz f (Set.univ : Set ℂ)) (z:ℂ)
  (hp : p ∉ Z9 (f:=f) z₀) :
  VE m f z₀ p z =
   WE m (z/Wc p):=by
 classical
 simp [VE,hp]
lemma YP (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) : VE m f z₀ p z=if Wc p=z₀ then (1:ℂ) else WE m (z/Wc p):=by
  classical
  by_cases h : Wc p=z₀
  · have hp : p ∈ Z9 (f:=f) z₀ := by
      simpa [Zl] using h
    simp [wb,hp,h]
  · have hp : p ∉ Z9 (f:=f) z₀ := by
      intro hmem
      exact h ((Zl f z₀ p).1 hmem)
    simp [zw,hp,h]
noncomputable def V3 (m:ℕ) (f:ℂ → ℂ)
  (s : Finset (Wz f (Set.univ : Set ℂ))) (z:ℂ):ℂ :=
 ∏ p ∈ s,WE m (z/Wc p)
theorem zQ (m:ℕ) {f:ℂ → ℂ} (p : Wz f (Set.univ : Set ℂ)) : Differentiable ℂ (fun z:ℂ => WE m (z/Wc p)):=by
 have qa : Differentiable ℂ (fun z:ℂ => z/Wc p):=by
  simp [div_eq_mul_inv]
 exact (ZD m).comp qa
theorem wf (m:ℕ) (f:ℂ → ℂ) (s : Finset (Wz f (Set.univ : Set ℂ))) : Differentiable ℂ (V3 m f s):=by
 let Φ : Wz f (Set.univ : Set ℂ) → ℂ → ℂ :=
  fun p z => WE m (z/Wc p)
 have hΦ : ∀ p ∈ s,Differentiable ℂ (Φ p):=by
  intro p _hp
  exact zQ m p
 simpa [V3,Φ] using!
  (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u:=s) hΦ)
theorem ZJ (m:ℕ) (f:ℂ → ℂ)
  (s : Finset (Wz f (Set.univ : Set ℂ))) (z₀ : ℂ) :
  AnalyticAt ℂ (V3 m f s) z₀ :=
 (wf m f s).analyticAt z₀
noncomputable def ZT
  (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ)
  (s : Finset (Wz f (Set.univ : Set ℂ))) (z:ℂ):ℂ :=
 ∏ p ∈ s,VE m f z₀ p z
@[simp]
lemma wt (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (s : Finset (Wz f (Set.univ : Set ℂ))) (z:ℂ) : ZT m f z₀ s z = ∏ p ∈ s,if Wc p=z₀ then (1:ℂ) else WE m (z/Wc p):=by
 simp [ZT,VE,
  Zl]
theorem yh (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (s : Finset (Wz f (Set.univ : Set ℂ))) : Differentiable ℂ (ZT m f z₀ s):=by
  let Φ : Wz f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => VE m f z₀ p z
  have hΦ : ∀ p ∈ s,Differentiable ℂ (Φ p):=by
    intro p _hp
    by_cases hpF : p ∈ Z9 (f:=f) z₀
    · have hΦp : Φ p=fun _ => (1:ℂ):=by
        ext z
        simp only [Φ,wb m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_const (1:ℂ)
    · have hΦp : Φ p=fun z => WE m (z/Wc p):=by
        ext z
        simp only [Φ,zw m f z₀ p z hpF]
      rw [hΦp]
      exact zQ m p
  have hEq : (fun z:ℂ => ∏ p ∈ s,Φ p z) =
      ZT m f z₀ s:=by
    ext z
    simp [Φ,ZT]
  have : Differentiable ℂ (fun z:ℂ => ∏ p ∈ s,Φ p z):=by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u:=s) hΦ)
  simpa [hEq] using this
noncomputable def Zd
  (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (z:ℂ):ℂ :=
 ∏' p : Wz f (Set.univ : Set ℂ),VE m f z₀ p z
theorem zp (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : HasProdUniformlyOn (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) => VE m f z₀ p z) (Zd m f z₀) K:=by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0,hR0⟩
  set R : ℝ:=max R0 1
  have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  have qe : ∀ z ∈ K,‖z‖ ≤ R:=fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let qq : Wz f (Set.univ : Set ℂ) → ℂ → ℂ:=fun p z =>
    VE m f z₀ p z
  let g : Wz f (Set.univ : Set ℂ) → ℂ → ℂ:=fun p z => qq p z - 1
  let u : Wz f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4*R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1))
  have hu : Summable u:=h_sum.mul_left (4*R^(m+1))
  have ql :
      ∀ᶠ p : Wz f (Set.univ : Set ℂ) in Filter.cofinite,
        (2*R:ℝ) < ‖Wc p‖ := by
    have qr :
        ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ 2*R} :
          Set _).Finite:=by
      have : Metric.closedBall (0:ℂ) (2*R) ⊆ (Set.univ : Set ℂ):=by simp
      exact ZB (f:=f) (U:=(Set.univ : Set ℂ)) (B:=2*R) this
    have:=qr.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖Wc p‖ ≤ 2*R:=by simpa using hp
    exact lt_of_not_ge this
  have qf :
      ∀ᶠ p in Filter.cofinite,∀ z ∈ K,‖g p z‖ ≤ u p:=by
    filter_upwards [ql] with p hp z hzK
    by_cases hpF : p ∈ Z9 (f:=f) z₀
    · have qs : Wc p=z₀ :=
        (Zl (f:=f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p:=by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m+1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m+1)
      simp [g,qq,VE,qs,hu0,sub_eq_add_neg]
    · have qt : ‖z‖ ≤ R:=qe z hzK
      have qg : ‖z/Wc p‖ ≤ (1/2:ℝ):=by
        have qb : 0 < (2*R:ℝ):=by nlinarith [hRpos]
        have qu : ‖Wc p‖⁻¹ < (2*R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt qb hp)
        have qc : ‖z‖ * ‖Wc p‖⁻¹ ≤ R * ‖Wc p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right qt ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have qd : R * ‖Wc p‖⁻¹ < R*(2*R)⁻¹ :=
          mul_lt_mul_of_pos_left qu hRpos
        have hlt : ‖z‖ * ‖Wc p‖⁻¹ < R*(2*R)⁻¹ :=
          lt_of_le_of_lt qc qd
        have qh : R*(2*R)⁻¹ = (1/2:ℝ):=by
          have qv : (R:ℝ) ≠ 0:=hRpos.ne'
          have : R*(2*R)⁻¹ = R/(2*R):=by simp [div_eq_mul_inv]
          rw [this]
          field_simp [qv]
        have qm : ‖z/Wc p‖ = ‖z‖ * ‖Wc p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have qw : ‖z/Wc p‖ < (1/2:ℝ):=by
          calc
            ‖z/Wc p‖ = ‖z‖ * ‖Wc p‖⁻¹ := qm
            _ < R*(2*R)⁻¹ := hlt
            _ = (1/2:ℝ):=qh
        exact le_of_lt qw
      have hE : ‖WE m (z/Wc p) - 1‖ ≤
            4 * ‖z/Wc p‖ ^ (m+1) :=
        wB (m:=m) (z:=z/Wc p) qg
      have qi : ‖z/Wc p‖ ^ (m+1) ≤
            (R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1)):=by
        have : ‖z/Wc p‖ = ‖z‖ * ‖Wc p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖Wc p‖⁻¹)^(m+1) =
            ‖z‖ ^ (m+1)*(‖Wc p‖⁻¹ ^ (m+1)):=by
          simp [mul_pow]
        rw [this]
        have qa : ‖z‖ ^ (m+1) ≤ R^(m+1) :=
          pow_le_pow_left₀ (norm_nonneg z) qt (m+1)
        gcongr
      dsimp [g,qq,u]
      simp [VE,hpF] at *
      nlinarith [hE,qi]
  have qx : ∀ p,ContinuousOn (g p) K:=by
    intro p
    by_cases hpF : p ∈ Z9 (f:=f) z₀
    · have qs : Wc p=z₀ :=
        (Zl (f:=f) (z₀ := z₀) p).1 hpF
      simpa [g,qq,VE,qs,sub_eq_add_neg,add_assoc,add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0:ℂ)) K)
    · have qj : Wc p ≠ z₀ :=
        (z3 (f:=f) z₀ p).1 hpF
      have qk : Continuous (fun z:ℂ => WE m z) :=
        (ZD m).continuous
      have qy : Continuous fun z:ℂ => z/Wc p:=by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have qn : Continuous fun z:ℂ => WE m (z/Wc p) :=
        qk.comp qy
      have : ContinuousOn (fun z:ℂ => WE m (z/Wc p) - 1) K :=
        (qn.continuousOn.sub continuous_const.continuousOn)
      simpa [g,qq,VE,Zl,qj] using this
  have qo :
      HasProdUniformlyOn (fun p z ↦ 1+g p z) (fun z ↦ ∏' p,(1+g p z)) K:=by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f:=g) (u:=u) (K:=K) hK hu qf qx
  have qp :
      HasProdUniformlyOn (fun p z ↦ qq p z) (fun z ↦ ∏' p,qq p z) K:=by
    simpa [g,sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using qo
  refine qp.congr_right ?_
  intro z hz
  simp [qq,Zd,VE]
theorem zd (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : HasProdLocallyUniformlyOn (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) => VE m f z₀ p z) (Zd m f z₀) (Set.univ : Set ℂ):=by
 refine hasProdLocallyUniformlyOn_of_forall_compact
   (f:=fun p z => VE m f z₀ p z)
   (g:=Zd m f z₀) (s:=(Set.univ : Set ℂ))
   isOpen_univ ?_
 intro K hKU hK
 simpa using
  (zp (m:=m) (f:=f) (z₀ := z₀)
   (K:=K) hK h_sum)
theorem zg (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : TendstoLocallyUniformlyOn (fun s : Finset (Wz f (Set.univ : Set ℂ)) => ZT m f z₀ s) (Zd m f z₀) Filter.atTop (Set.univ : Set ℂ):=by
 have qa :
   HasProdLocallyUniformlyOn
    (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) =>
     VE m f z₀ p z)
    (Zd m f z₀)
    (Set.univ : Set ℂ) :=
  zd (m:=m) (f:=f)
   (z₀ := z₀) h_sum
 have h :
   TendstoLocallyUniformlyOn
    (fun (s : Finset (Wz f (Set.univ : Set ℂ))) (z:ℂ) =>
     ∏ p ∈ s,
      if Wc p=z₀ then (1:ℂ)
      else WE m (z/Wc p))
    (Zd m f z₀)
    Filter.atTop
    (Set.univ : Set ℂ):=by
  simpa [HasProdLocallyUniformlyOn,VE,Zl]
   using qa
 refine h.congr (G:=fun s z => ZT m f z₀ s z) ?_
 intro s z hz
 simp [wt]
theorem zu (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : DifferentiableOn ℂ (Zd m f z₀) (Set.univ : Set ℂ):=by
 have qa :
   TendstoLocallyUniformlyOn
    (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
     ZT m f z₀ s)
    (Zd m f z₀)
    Filter.atTop
    (Set.univ : Set ℂ) :=
  zg (m:=m) (f:=f)
   (z₀ := z₀) h_sum
 have hF :
   ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in Filter.atTop,
    DifferentiableOn ℂ (ZT m f z₀ s) (Set.univ : Set ℂ):=by
  refine Filter.Eventually.of_forall ?_
  intro s
  exact (yh m f z₀ s).differentiableOn
 haveI : (Filter.atTop : Filter (Finset (Wz f (Set.univ : Set ℂ)))).NeBot :=
  Filter.atTop_neBot
 exact qa.differentiableOn hF isOpen_univ
lemma zv
    (m:ℕ) (f:ℂ → ℂ) (z₀ z:ℂ)
    (s : Finset (Wz f (Set.univ : Set ℂ)))
    (hs : Z9 (f:=f) z₀ ⊆ s) :
    V3 m f s z =
      V3 m f (Z9 (f:=f) z₀) z *
        ZT m f z₀ s z:=by
  classical
  let qd : Finset (Wz f (Set.univ : Set ℂ)) :=
    Z9 (f:=f) z₀
  let P : Wz f (Set.univ : Set ℂ) → Prop:=fun p => p ∈ qd
  let qg : Wz f (Set.univ : Set ℂ) → ℂ :=
    fun p => WE m (z/Wc p)
  have qa : s.filter P=qd:=by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp,hp⟩
  have qc :
      (∏ p ∈ s with P p,qg p)*(∏ p ∈ s with ¬ P p,qg p) = ∏ p ∈ s,qg p:=by
    simpa [qg] using
      (Finset.prod_filter_mul_prod_filter_not (s:=s) (p:=P) (f:=qg))
  have hP : (∏ p ∈ s with P p,qg p)=V3 m f qd z:=by
    have hg : ∀ x ∈ s \ qd,(if x ∈ qd then qg x else (1:ℂ))=1:=by
      intro x hx
      have qe : x ∉ qd:=(Finset.mem_sdiff.mp hx).2
      simp [qe]
    have hfg :
        ∀ x ∈ qd,qg x=(if x ∈ qd then qg x else (1:ℂ)):=by
      intro x hx
      simp [hx]
    have qh:=(Finset.prod_subset_one_on_sdiff (s₁ := qd) (s₂ := s)
        (f:=qg) (g:=fun x => if x ∈ qd then qg x else (1:ℂ)) hs hg hfg)
    simpa [V3,qg,P,qd,Finset.prod_filter] using qh.symm
  have qf : (∏ p ∈ s with ¬ P p,qg p)=ZT m f z₀ s z:=by
    simp [ZT,VE,qg,P,qd,
      Finset.prod_filter,Zl]
  have qb : ∏ p ∈ s,qg p=(∏ p ∈ s with P p,qg p)*(∏ p ∈ s with ¬ P p,qg p) :=
    qc.symm
  calc
    V3 m f s z
        = ∏ p ∈ s,qg p:=by simp [V3,qg]
    _ = (∏ p ∈ s with P p,qg p)*(∏ p ∈ s with ¬ P p,qg p):=qb
    _ = V3 m f qd z*ZT m f z₀ s z:=by
      simp [hP,qf,qd]
end Complex.Hadamard
end
end
section
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem zf (m:ℕ) (f:ℂ → ℂ) (s : Finset (Wz f (Set.univ : Set ℂ))) (z₀ : ℂ) : analyticOrderAt (fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p)) z₀ = ((s.filter (fun p => Wc p=z₀)).card : ℕ∞):=by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : Wc p=z₀
    · have hp0 : Wc p ≠ 0:=p.property
      have qb :
          AnalyticAt ℂ (fun z:ℂ => WE m (z/Wc p)) z₀ := by
        exact (zQ m p).analyticAt z₀
      have qa : AnalyticAt ℂ (fun z:ℂ => ∏ q ∈ s,WE m
          (z/Wc q)) z₀ := by
        simpa [V3] using! ZJ m f s z₀
      let fac:ℂ → ℂ:=fun z:ℂ => WE m (z/Wc p)
      let qh:ℂ → ℂ:=fun z:ℂ => ∏ q ∈ s,WE m (z/Wc q)
      have qi :
          analyticOrderAt (fac*qh) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt qh z₀ := by
        simpa [fac,qh] using (analyticOrderAt_mul (z₀ := z₀) qb qa)
      have qe :
          (Finset.filter (fun q => Wc q=z₀) (insert p s)).card =
            (Finset.filter (fun q => Wc q=z₀) s).card+1:=by
        simp [hEq,hp,Finset.filter_insert]
      have qj : analyticOrderAt fac z₀ = (1 : ℕ∞):=by
        simpa [fac,hEq] using
          (yQ (m:=m) (a:=Wc p) hp0)
      have qf : analyticOrderAt qh z₀ = ((s.filter
          (fun q => Wc q=z₀)).card : ℕ∞):=by
        simpa [qh] using hs
      have qc :
          (fun z:ℂ => ∏ q ∈ insert p s,WE m (z/Wc q))
            =ᶠ[𝓝 z₀] (fac*qh):=by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac,qh,Finset.prod_insert,hp,Pi.mul_apply]
      calc
        analyticOrderAt (fun z:ℂ => ∏ q ∈ insert p s,WE m
            (z/Wc q)) z₀ = analyticOrderAt (fac*qh) z₀ := by
              simpa using (analyticOrderAt_congr qc)
        _ = analyticOrderAt fac z₀ + analyticOrderAt qh z₀ := qi
        _ = (1 : ℕ∞)+((s.filter (fun q => Wc q=z₀)).card : ℕ∞):=by
              simp [qj,qf]
        _ = (((insert p s).filter (fun q => Wc q=z₀)).card : ℕ∞):=by
              simp [qe,Nat.add_comm]
    · have qb :
          AnalyticAt ℂ (fun z:ℂ => WE m (z/Wc p)) z₀ := by
        exact (zQ m p).analyticAt z₀
      have qg : analyticOrderAt (fun z:ℂ => WE m
          (z/Wc p)) z₀ = 0:=by
        have hp0 : Wc p ≠ 0:=p.property
        have qk : WE m (z₀ / Wc p) ≠ 0:=by
          have : (z₀ / Wc p) ≠ 1:=by
            intro h1
            have : z₀ = Wc p:=by
              have : z₀ = (z₀ / Wc p)*(Wc p):=by
                simp [div_eq_mul_inv]
              simpa [h1,div_eq_mul_inv,hp0] using this
            exact hEq (this.symm)
          exact (Yk m (z₀ / Wc p)).2 this
        simpa using (qb.analyticOrderAt_eq_zero).2 (by simpa using qk)
      have qe :
          (Finset.filter (fun q => Wc q=z₀) (insert p s)).card =
            (Finset.filter (fun q => Wc q=z₀) s).card:=by
        simp [hEq,Finset.filter_insert]
      have qa : AnalyticAt ℂ (fun z:ℂ => ∏ q ∈ s,WE m
          (z/Wc q)) z₀ := by
        simpa [V3] using! ZJ m f s z₀
      let fac:ℂ → ℂ:=fun z:ℂ => WE m (z/Wc p)
      let qh:ℂ → ℂ:=fun z:ℂ => ∏ q ∈ s,WE m (z/Wc q)
      have qi :
          analyticOrderAt (fac*qh) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt qh z₀ := by
        simpa [fac,qh] using (analyticOrderAt_mul (z₀ := z₀) qb qa)
      have qc :
          (fun z:ℂ => ∏ q ∈ insert p s,WE m (z/Wc q))
            =ᶠ[𝓝 z₀] (fac*qh):=by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac,qh,Finset.prod_insert,hp,Pi.mul_apply]
      calc
        analyticOrderAt (fun z:ℂ => ∏ q ∈ insert p s,WE m
        (z/Wc q)) z₀
            = analyticOrderAt (fac*qh) z₀ := by
              simpa using (analyticOrderAt_congr qc)
        _ = analyticOrderAt qh z₀ := by
              calc
                analyticOrderAt (fac*qh) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt qh z₀ := qi
                _ = analyticOrderAt qh z₀ := by
                      have qd : analyticOrderAt fac z₀ = 0:=by
                        simpa [fac] using qg
                      simp [qd]
        _ = ((s.filter (fun q => Wc q=z₀)).card : ℕ∞):=by
              simpa [qh] using hs
        _ = (((insert p s).filter (fun q => Wc q=z₀)).card : ℕ∞):=by
              simpa using congrArg (fun n:ℕ => (n : ℕ∞)) qe.symm
theorem zC
    (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (Wz f (Set.univ : Set ℂ)))
    (hs : Z9 (f:=f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p))
        z₀ = ((Z9 (f:=f) z₀).card : ℕ∞):=by
  have h :=
    zf
      (m:=m) (f:=f) (s:=s) (z₀ := z₀)
  have qa :
      s.filter (fun p => Wc p=z₀) =
        Z9 (f:=f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : Wc p=z₀ := (Finset.mem_filter.mp hp').2
      simpa [Zl] using hpv
    · intro hp_fiber
      have hpv : Wc p=z₀ :=
        (Zl (f:=f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s:=hs (by simpa [Zl] using hpv)
      exact Finset.mem_filter.2 ⟨hps,hpv⟩
  simpa [qa] using h
theorem zh
  (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ)
  (s : Finset (Wz f (Set.univ : Set ℂ)))
  (hs : Z9 (f:=f) z₀ ⊆ s) :
  ∃ g:ℂ → ℂ,
   AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
    (fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p))
     =ᶠ[𝓝 z₀]
     fun z:ℂ => (z - z₀)^(Z9 (f:=f) z₀).card • g z:=by
 let F:ℂ → ℂ:=fun z:ℂ => ∏ p ∈ s,WE m (z/Wc p)
 have qa : AnalyticAt ℂ F z₀ := by
  simpa [F,V3] using! ZJ m f s z₀
 have qb :
   analyticOrderAt F z₀ =
    ((Z9 (f:=f) z₀).card : ℕ∞):=by
  simpa [F] using
   (zC (m:=m)
   (f:=f) (z₀ := z₀) (s:=s) hs)
 refine (qa.analyticOrderAt_eq_natCast (n:=(Z9
  (f:=f) z₀).card)).1 ?_
 simp [qb]
end Complex.Hadamard
end
end
end
section
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem zL (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : TendstoLocallyUniformlyOn (fun s : Finset (Wz f (Set.univ : Set ℂ)) => V3 m f s) (VJ m f (Set.univ : Set ℂ)) Filter.atTop (Set.univ : Set ℂ):=by
 have qa :
   HasProdLocallyUniformlyOn
    (fun (p : Wz f (Set.univ : Set ℂ)) (z:ℂ) =>
     WE m (z/Wc p))
    (VJ m f (Set.univ : Set ℂ))
    (Set.univ : Set ℂ) :=
  zB (m:=m) (f:=f) h_sum
 simpa [HasProdLocallyUniformlyOn,V3] using! qa
theorem zJ (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z₀ : ℂ) (k:ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K,z ≠ z₀) : TendstoUniformlyOn (fun s z => (V3 m f s z)/(z - z₀)^k) (fun z => (VJ m f (Set.univ : Set ℂ) z)/(z - z₀)^k) (Filter.atTop : Filter (Finset (Wz f (Set.univ : Set ℂ)))) K:=by
 have qe :
   TendstoLocallyUniformlyOn
    (fun s : Finset (Wz f (Set.univ : Set ℂ)) => V3 m f s)
    (VJ m f (Set.univ : Set ℂ))
    Filter.atTop
    K :=
  (zL (m:=m) (f:=f) h_sum).mono
   (by intro z hz; simp)
 have qb :
   TendstoUniformlyOn
    (fun s : Finset (Wz f (Set.univ : Set ℂ)) => V3 m f s)
    (VJ m f (Set.univ : Set ℂ))
    Filter.atTop
    K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 qe
 let h:ℂ → ℂ:=fun z => ((z - z₀)^k)⁻¹
 have hh : ∃ C,∀ z ∈ K,‖h z‖ ≤ C:=by
  have qc : ContinuousOn h K:=by
   have qf : ContinuousOn (fun z:ℂ => (z - z₀)^k) K:=by
    fun_prop
   refine qf.inv₀ ?_
   intro z hz
   have hz0 : z - z₀ ≠ 0:=sub_ne_zero.mpr (hKz z hz)
   exact pow_ne_zero k hz0
  have qd : IsCompact (h '' K):=hK.image_of_continuousOn qc
  rcases (isBounded_iff_forall_norm_le.1 qd.isBounded) with ⟨C,hC⟩
  refine ⟨C,?_⟩
  intro z hz
  exact hC (h z) ⟨z,hz,rfl⟩
 have qa :=
  (TendstoUniformlyOn.WL (p:=(Filter.atTop : Filter (Finset (Wz f
  (Set.univ : Set ℂ)))))
    (K:=K)
    (F:=fun s z => V3 m f s z)
    (f:=fun z => VJ m f (Set.univ : Set ℂ) z)
    (h:=h)
    qb hh)
 simpa [h,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using qa
theorem zk (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z₀ : ℂ) (k:ℕ) : TendstoLocallyUniformlyOn (fun s z => (V3 m f s z)/(z - z₀)^k) (fun z => (VJ m f (Set.univ : Set ℂ) z)/(z - z₀)^k) (Filter.atTop : Filter (Finset (Wz f (Set.univ : Set ℂ)))) ((Set.univ : Set ℂ) \ {z₀}):=by
 have qa : IsOpen ((Set.univ : Set ℂ) \ {z₀}):=by
  have qb : ((Set.univ : Set ℂ) \ {z₀})=({z₀} : Set ℂ)ᶜ := by
   ext z
   simp
  simp [qb]
 refine (tendstoLocallyUniformlyOn_iff_forall_isCompact qa).2 ?_
 intro K hKsub hK
 have hKz : ∀ z ∈ K,z ≠ z₀ := by
  intro z hzK
  have : z ∈ (Set.univ : Set ℂ) \ {z₀}:=hKsub hzK
  exact by simpa [Set.mem_sdiff,Set.mem_singleton_iff] using this.2
 exact zJ
  (m:=m) (f:=f) h_sum (z₀ := z₀) (k:=k) (hK:=hK) hKz
open Filter
theorem zZ
    (m:ℕ) (f:ℂ → ℂ)
    (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ (m+1)))
    (z₀ : ℂ) :
    ∃ ε > 0,∃ u:ℂ → ℂ,AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z:ℂ,z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (VJ m f (Set.univ : Set ℂ) z) /
              (z - z₀)^(Z9 (f:=f) z₀).card =
            (Zd m f z₀ z)*u z:=by
  let qb : Finset (Wz f (Set.univ : Set ℂ)) :=
    Z9 (f:=f) z₀
  have qf : ∃ u:ℂ → ℂ,AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z:ℂ => V3 m f qb z) =ᶠ[𝓝 z₀]
            fun z:ℂ => (z - z₀)^qb.card • u z:=by
    simpa [qb,V3] using
      (zh (m:=m) (f:=f) (z₀ := z₀)
        (s:=qb) (by rfl : qb ⊆ qb))
  rcases qf with ⟨u,huA,hu0,huEq⟩
  have qg : {z:ℂ | V3 m f qb z =
      (z - z₀)^qb.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 qg with ⟨ε,hε,hball⟩
  refine ⟨ε,hε,u,huA,hu0,?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (V3 m f s z)/(z - z₀)^qb.card)
        (fun z => (VJ m f (Set.univ : Set ℂ) z)/(z - z₀)^qb.card)
        (Filter.atTop : Filter (Finset (Wz f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    zk
      (m:=m) (f:=f) (h_sum:=h_sum) (z₀ := z₀) (k:=qb.card)
  have qc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
          ZT m f z₀ s)
        (Zd m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    zg (m:=m) (f:=f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}):=by
    refine ⟨by simp,?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
          (V3 m f s z)/(z - z₀)^qb.card) (Filter.atTop : Filter _)
        (𝓝 ((VJ m f (Set.univ : Set ℂ) z)/(z - z₀)^qb.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
          ZT m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (Zd m f z₀ z)) :=
    qc.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
          (ZT m f z₀ s z)*u z) (Filter.atTop : Filter _)
        (𝓝 ((Zd m f z₀ z)*u z)) :=
    (hG0.mul tendsto_const_nhds)
  have qh : ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      qb ⊆ s:=ww (f:=f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (V3 m f s z)/(z - z₀)^qb.card
          = (ZT m f z₀ s z)*u z:=by
    filter_upwards [qh] with s hs
    have qa :
        V3 m f s z =
          V3 m f qb z*ZT m f z₀ s z:=by
      simpa [qb] using
        (zv (m:=m) (f:=f) (z₀ := z₀)
          (z:=z) (s:=s) hs)
    have qd :
        V3 m f qb z=(z - z₀)^qb.card • u z:=by
      exact hball hz
    have qe : (z - z₀)^qb.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ:=(z - z₀)^qb.card
    have ha : a ≠ 0:=by simpa [a] using qe
    set c : ℂ:=ZT m f z₀ s z with hc
    rw [qa,qd,smul_eq_mul]
    calc
      ((a*u z)*c)/a
          = (a*(u z*c))/a:=by simp [mul_assoc]
      _ = u z*c:=by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z*c) ha)
      _ = c*u z:=by ac_rfl
      _ = (ZT m f z₀ s z)*u z:=by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (Wz f (Set.univ : Set ℂ)) =>
          (V3 m f s z)/(z - z₀)^qb.card)
        (Filter.atTop : Filter _)
        (𝓝 ((Zd m f z₀ z)*u z)):=by
    have heq' :
        ∀ᶠ s : Finset (Wz f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (ZT m f z₀ s z)*u z
            = (V3 m f s z)/(z - z₀)^qb.card:=by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'
theorem zl
    (m:ℕ) (f:ℂ → ℂ)
    (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ (m+1)))
    (z₀ : ℂ) : ∃ r > 0,BddAbove (norm ∘ (fun z:ℂ =>
      (VJ m f (Set.univ : Set ℂ) z) /
        (z - z₀)^(Z9 (f:=f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})):=by
  rcases zZ (m:=m) (f:=f) (h_sum:=h_sum)
    (z₀ := z₀) with ⟨ε,hε,u,huA,hu0,hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have qg : {z:ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1:ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball,dist_eq_norm,Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 qg with ⟨r0,hr0pos,hr0sub⟩
  set r : ℝ:=min (ε / 2) r0
  have hrpos : 0 < r:=lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have qb : ∀ z ∈ Metric.ball z₀ r,‖u z‖ ≤ ‖u z₀‖ + 1:=by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0:=by
      have : r ≤ r0:=min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have qe : ‖u z - u z₀‖ < 1:=hr0sub hz0
    have qh : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg,add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans qh (by nlinarith [le_of_lt qe])
    nlinarith [this]
  have qc :
      DifferentiableOn ℂ (Zd m f z₀) (Set.univ : Set ℂ) :=
    zu (m:=m) (f:=f) (z₀ := z₀) h_sum
  have qd : ContinuousOn (Zd m f z₀) (Metric.closedBall z₀ r) :=
    (qc.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r):=isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn qd).isBounded) with ⟨C,hC⟩
  refine ⟨r,hrpos,⟨C*(‖u z₀‖ + 1),?_⟩⟩
  rintro _ ⟨z,hzset,rfl⟩
  rcases hzset with ⟨hzr,hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have qf : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (VJ m f (Set.univ : Set ℂ) z) /
          (z - z₀)^(Z9 (f:=f) z₀).card
        = Zd m f z₀ z*u z :=
    hEq z hz_in_ε qf
  have hCz : ‖Zd m f z₀ z‖ ≤ C:=by
    have hzK : z ∈ Metric.closedBall z₀ r:=Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z,hzK,rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1:=qb z hzr
  have qa : 0 ≤ C:=le_trans (norm_nonneg _) hCz
  have qi : ‖Zd m f z₀ z*u z‖ ≤ C*(‖u z₀‖ + 1):=by
    calc
      ‖Zd m f z₀ z*u z‖
          = ‖Zd m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C*(‖u z₀‖ + 1):=by
            exact mul_le_mul hCz huZ (norm_nonneg _) qa
  simpa [Function.comp,hq] using qi
theorem yx (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : Zd m f z₀ z₀ ≠ 0:=by
  let Φ : Wz f (Set.univ : Set ℂ) → ℂ :=
    fun p => if Wc p=z₀ then (1:ℂ)
      else WE m (z₀ / Wc p)
  let a : Wz f (Set.univ : Set ℂ) → ℂ:=fun p => Φ p - 1
  have hΦ_ne : ∀ p,Φ p ≠ 0:=by
    intro p
    by_cases hp : Wc p=z₀
    · simp [Φ,hp]
    · have qp : Wc p ≠ z₀ := hp
      have hz : z₀ / Wc p ≠ (1:ℂ):=by
        intro h
        by_cases hp0 : Wc p=0
        · have : z₀ / Wc p=(0:ℂ):=by simp [hp0]
          have h01:=h
          rw [this] at h01
          exact (show False from (by simpa using (show (0:ℂ) ≠ (1:ℂ) from by simp) h01))
        · have : z₀ = Wc p:=(div_eq_one_iff_eq hp0).1 h
          exact qp this.symm
      have hE : WE m (z₀ / Wc p) ≠ 0:=by
        intro h0
        have : z₀ / Wc p=(1:ℂ) :=
          (Yn (m:=m) (z:=z₀ / Wc p)).1 h0
        exact hz this
      simp [Φ,hp,hE]
  have qg : ‖z₀‖ ≤ max ‖z₀‖ 1:=le_max_left _ _
  set R : ℝ:=max ‖z₀‖ 1
  have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  let u : Wz f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4*R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1))
  have hu : Summable u:=h_sum.mul_left (4*R^(m+1))
  have qm :
      ∀ᶠ p : Wz f (Set.univ : Set ℂ) in Filter.cofinite,
        (2*R:ℝ) < ‖Wc p‖ := by
    have qq : ({p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤
        2*R} : Set _).Finite:=by
      have : Metric.closedBall (0:ℂ) (2*R) ⊆ (Set.univ : Set ℂ):=by simp
      exact ZB (f:=f) (U:=(Set.univ : Set ℂ)) (B:=2*R) this
    have:=qq.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖Wc p‖ ≤ 2*R:=by simpa using hp
    exact lt_of_not_ge this
  have qh :
      ∀ᶠ p in Filter.cofinite,‖a p‖ ≤ u p:=by
    filter_upwards [qm] with p hp
    have qi : 0 < ‖Wc p‖ := lt_trans (by nlinarith [hRpos]) hp
    have qj : ‖z₀ / Wc p‖ ≤ (1/2:ℝ):=by
      have qd : 0 < (2*R:ℝ):=by nlinarith [hRpos]
      have qr : ‖Wc p‖⁻¹ < (2*R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt qd hp)
      have qe : ‖z₀‖ * ‖Wc p‖⁻¹ ≤ R * ‖Wc p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact qg
      have qf : R * ‖Wc p‖⁻¹ < R*(2*R)⁻¹ :=
        mul_lt_mul_of_pos_left qr hRpos
      have hlt : ‖z₀‖ * ‖Wc p‖⁻¹ < R*(2*R)⁻¹ :=
        lt_of_le_of_lt qe qf
      have qk : R*(2*R)⁻¹ = (1/2:ℝ):=by
        have qs : (R:ℝ) ≠ 0:=hRpos.ne'
        have : R*(2*R)⁻¹ = R/(2*R):=by simp [div_eq_mul_inv]
        rw [this]
        field_simp [qs]
      have qn : ‖z₀ / Wc p‖ = ‖z₀‖ * ‖Wc p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have qt : ‖z₀ / Wc p‖ < (1/2:ℝ):=by
        calc
          ‖z₀ / Wc p‖ = ‖z₀‖ * ‖Wc p‖⁻¹ := qn
          _ < R*(2*R)⁻¹ := hlt
          _ = (1/2:ℝ):=qk
      exact le_of_lt qt
    have hE :
        ‖WE m (z₀ / Wc p) - 1‖ ≤
          4 * ‖z₀ / Wc p‖ ^ (m+1) :=
      wB (m:=m) (z:=z₀ / Wc p) qj
    have ql :
        ‖z₀ / Wc p‖ ^ (m+1) ≤
          (R^(m+1))*(‖Wc p‖⁻¹ ^ (m+1)):=by
      have : ‖z₀ / Wc p‖ = ‖z₀‖ * ‖Wc p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖Wc p‖⁻¹)^(m+1) =
          ‖z₀‖ ^ (m+1)*(‖Wc p‖⁻¹ ^ (m+1)):=by
        simp [mul_pow]
      rw [this]
      have qc : ‖z₀‖ ^ (m+1) ≤ R^(m+1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) qg (m+1)
      gcongr
    have qo : Wc p ≠ z₀ := by
      intro h
      have : ‖Wc p‖ ≤ R:=by
        simp [h,R]
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖WE m (z₀ / Wc p) - 1‖ := by
      simp [a,Φ,qo,sub_eq_add_neg]
    calc
      ‖a p‖ = ‖WE m (z₀ / Wc p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / Wc p‖ ^ (m+1):=by
            simpa [sub_eq_add_neg,add_comm] using hE
      _ ≤ 4*(R^(m+1)*(‖Wc p‖⁻¹ ^ (m+1))):=by
            gcongr
      _ = u p:=by
            simp [u,mul_assoc,mul_comm]
  have qa : Summable (fun p => ‖a p‖):=by
    refine (Summable.of_norm_bounded_eventually (E:=ℝ) (f:=fun p => ‖a p‖) (g:=u) hu ?_)
    filter_upwards [qh] with p hp
    simpa [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (a p))] using hp
  have qb :
      (∏' p : Wz f (Set.univ : Set ℂ),(1+a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R:=ℂ) (f:=a) (hf:=fun p => by
      simpa [a,Φ,add_sub_cancel] using hΦ_ne p) qa
  have : (∏' p : Wz f (Set.univ : Set ℂ),(1+a p)) =
      Zd m f z₀ z₀ := by
    simp [a,Φ,Zd,YP]
  exact by
    intro h0
    exact qb (by simpa [this] using h0)
end Complex.Hadamard
end
end
section
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem zS (m:ℕ) (f:ℂ → ℂ) (z₀ : ℂ) (k:ℕ) (s : Finset (Wz f (Set.univ : Set ℂ))) : DifferentiableOn ℂ (fun z:ℂ => (V3 m f s z)/(z - z₀)^k) ((Set.univ : Set ℂ) \ {z₀}):=by
  have qa : DifferentiableOn ℂ (V3 m f s) (Set.univ : Set ℂ):=by
    exact (wf m f s).differentiableOn
  have qb : DifferentiableOn ℂ (fun z:ℂ => (z - z₀)^k) ((Set.univ : Set ℂ) \ {z₀}):=by
    have : Differentiable ℂ (fun z:ℂ => (z - z₀)^k):=by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k=0
  · subst hk
    simpa [pow_zero] using! (qa.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}),(fun z:ℂ => (z - z₀)^k) z ≠ 0:=by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff,Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have qc :
        DifferentiableOn ℂ (fun z:ℂ => ((z - z₀)^k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      qb.inv hne
    simpa [div_eq_mul_inv] using! (qa.mono (by intro z hz; exact hz.1)).mul qc
theorem zM (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z₀ : ℂ) (k:ℕ) : DifferentiableOn ℂ (fun z:ℂ => (VJ m f (Set.univ : Set ℂ) z)/(z - z₀)^k) ((Set.univ : Set ℂ) \ {z₀}):=by
 have qa : IsOpen ((Set.univ : Set ℂ) \ {z₀}):=by
  have qc : ((Set.univ : Set ℂ) \ {z₀})=({z₀} : Set ℂ)ᶜ := by
   ext z; simp
  simp [qc]
 have qb :=
  zk
   (m:=m) (f:=f) h_sum (z₀ := z₀) (k:=k)
 refine qb.differentiableOn ?_ qa
 refine Filter.Eventually.of_forall ?_
 intro s
 exact zS (m:=m) (f:=f) (z₀ := z₀) (k:=k) s
theorem ze
  (m:ℕ) (f:ℂ → ℂ)
  (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
   ‖Wc p‖⁻¹ ^ (m+1)))
  (z₀ : ℂ) : ∃ r > 0,DifferentiableOn ℂ (Function.update
     (fun z:ℂ => (VJ m f (Set.univ : Set ℂ) z) /
      (z - z₀)^(Z9 (f:=f) z₀).card) z₀
     (limUnder (𝓝[≠] z₀) (fun z:ℂ => (VJ m f (Set.univ : Set ℂ) z) /
        (z - z₀)^(Z9 (f:=f) z₀).card)))
    (Metric.ball z₀ r):=by
 rcases zl (m:=m) (f:=f)
   (h_sum:=h_sum) (z₀ := z₀) with ⟨r,hrpos,hbdd⟩
 refine ⟨r,hrpos,?_⟩
 have qa : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
 have qb : DifferentiableOn ℂ (fun z:ℂ =>
    (VJ m f (Set.univ : Set ℂ) z) /
     (z - z₀)^(Z9 (f:=f) z₀).card)
   ((Metric.ball z₀ r) \ {z₀}):=by
  have qc :=
   zM
    (m:=m) (f:=f) h_sum (z₀ := z₀)
    (k:=(Z9 (f:=f) z₀).card)
  refine qc.mono ?_
  intro z hz
  exact ⟨by simp,hz.2⟩
 have hb : BddAbove (norm ∘ (fun z:ℂ => (VJ m f (Set.univ : Set ℂ) z) /
   (z - z₀)^(Z9 (f:=f) z₀).card) ''
  ((Metric.ball z₀ r) \ {z₀})):=hbdd
 simpa using
  (Complex.differentiableOn_update_limUnder_of_bddAbove (f:=fun z:ℂ =>
    (VJ m f (Set.univ : Set ℂ) z) /
     (z - z₀)^(Z9 (f:=f) z₀).card)
   (s:=Metric.ball z₀ r) (c:=z₀) qa qb hb)
theorem zm
  (m:ℕ) (f:ℂ → ℂ)
  (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
   ‖Wc p‖⁻¹ ^ (m+1)))
  (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z:ℂ =>
     (VJ m f (Set.univ : Set ℂ) z) /
    (z - z₀)^(Z9 (f:=f) z₀).card) z₀
    (limUnder (𝓝[≠] z₀) (fun z:ℂ => (VJ m f (Set.univ : Set ℂ) z) /
       (z - z₀)^(Z9 (f:=f) z₀).card)))
   z₀ := by
 rcases
   ze
    (m:=m) (f:=f) h_sum (z₀ := z₀) with ⟨r,hrpos,hdiff⟩
 let g:ℂ → ℂ :=
  Function.update
   (fun z:ℂ =>
    (VJ m f (Set.univ : Set ℂ) z) /
     (z - z₀)^(Z9 (f:=f) z₀).card)
   z₀
   (limUnder (𝓝[≠] z₀) fun z:ℂ =>
    (VJ m f (Set.univ : Set ℂ) z) /
     (z - z₀)^(Z9 (f:=f) z₀).card)
 have qb : ContinuousAt g z₀ :=
  (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
 have hd :
   ∀ᶠ z in 𝓝[≠] z₀,DifferentiableAt ℂ g z:=by
  have qa : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
   refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
   refine ⟨Metric.ball z₀ r,Metric.ball_mem_nhds z₀ hrpos,?_⟩
   intro z hz
   exact hz.1
  filter_upwards [qa] with z hz
  exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
 simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd qb
theorem zT
    (m:ℕ) (f:ℂ → ℂ)
    (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ (m+1)))
    (z₀ : ℂ) :
    ∃ q:ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z:ℂ =>
            (VJ m f (Set.univ : Set ℂ) z) /
              (z - z₀)^(Z9 (f:=f) z₀).card) ∧
        ∀ z:ℂ,z ≠ z₀ →
          q z =
            (VJ m f (Set.univ : Set ℂ) z) /
              (z - z₀)^(Z9 (f:=f) z₀).card:=by
  let q:ℂ → ℂ :=
    Function.update
      (fun z:ℂ =>
        (VJ m f (Set.univ : Set ℂ) z) /
          (z - z₀)^(Z9 (f:=f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z:ℂ =>
        (VJ m f (Set.univ : Set ℂ) z) /
          (z - z₀)^(Z9 (f:=f) z₀).card)
  refine ⟨q,?_,?_,?_⟩
  · simpa [q] using
      zm
        (m:=m) (f:=f) (h_sum:=h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q,Function.update_of_ne hz]
theorem zs (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z₀ : ℂ) : analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z₀ = (Z9 (f:=f) z₀).card:=by
  set k : ℕ:=(Z9 (f:=f) z₀).card
  let F:ℂ → ℂ:=VJ m f (Set.univ : Set ℂ)
  let q0:ℂ → ℂ:=fun z => F z/(z - z₀)^k
  rcases zT
      (m:=m) (f:=f) (h_sum:=h_sum) (z₀ := z₀) with
    ⟨q,hqA,hq_self,hq_ne⟩
  have qa : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    yt (m:=m) (f:=f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z:=qa z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      zZ (m:=m) (f:=f) (h_sum:=h_sum)
      (z₀ := z₀)
    with ⟨ε,hε,u,huA,hu0,hEq⟩
  let g:ℂ → ℂ:=fun z => (Zd m f z₀ z)*u z
  have qb : DifferentiableOn ℂ (Zd m f z₀)
      (Set.univ : Set ℂ) :=
    zu (m:=m) (f:=f) (z₀ := z₀) h_sum
  have qc : ContinuousAt (Zd m f z₀) z₀ :=
    (qb z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have qh : ContinuousAt g z₀ := (qc.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0:=by
    have qi : Zd m f z₀ z₀ ≠ 0 :=
      yx (m:=m) (f:=f) (z₀ := z₀) h_sum
    exact mul_ne_zero qi hu0
  have qe : ∀ᶠ z in 𝓝[≠] z₀,z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀,z ≠ z₀ := by
    filter_upwards [qe] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have qm : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)):=by
    have qn : ∀ᶠ z in 𝓝[≠] z₀,z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g:=by
      filter_upwards [qn,hne] with z hz hzne
      have hq:=hEq z hz hzne
      simpa [q0,F,k,g,smul_eq_mul] using hq
    exact (qh.continuousWithinAt.tendsto.congr' heq.symm)
  have qq : limUnder (𝓝[≠] z₀) q0=g z₀ := qm.limUnder_eq
  have hq0 : q z₀ ≠ 0:=by
    have qd : q z₀ = limUnder (𝓝[≠] z₀) q0:=by
      simpa [q0,F,k] using hq_self
    have : q z₀ = g z₀ := qd.trans qq
    exact this.symm ▸ hg0
  have heq_punct : (fun z:ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z:ℂ => (z - z₀)^k • q z:=by
    filter_upwards [hne] with z hz
    have qo : (z - z₀)^k ≠ 0:=pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z=q0 z:=by simpa [q0,F,k] using hq_ne z hz
    have qr : (z - z₀)^k*q0 z=F z:=by
      calc
        (z - z₀)^k*q0 z
            = (((z - z₀)^k)*F z)/((z - z₀)^k):=by
                simp [q0,div_eq_mul_inv,mul_assoc]
        _ = F z:=by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) qo)
    have : F z=(z - z₀)^k*q z:=by
      calc
        F z=(z - z₀)^k*q0 z:=qr.symm
        _ = (z - z₀)^k*q z:=by simp [hq]
    simpa [smul_eq_mul] using this
  have qj : ContinuousAt F z₀ :=
    (qa z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have qk : ContinuousAt q z₀ := hqA.continuousAt
  have qf : F z₀ = (z₀ - z₀)^k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)):=qj.continuousWithinAt.tendsto
    have qs :
        Tendsto (fun z:ℂ => (z - z₀)^k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀)^k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z:ℂ => (z - z₀)^k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀)^k • q z₀)) :=
      qs.mul (qk.continuousWithinAt.tendsto)
    have qt : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀)^k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 qt
  have qu : ∀ᶠ z in 𝓝 z₀,F z=(z - z₀)^k • q z:=by
    have ql : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have qg : ∀ᶠ z in 𝓝 z₀,z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem ql (fun _ hz => hz)
    filter_upwards [qg] with z _hz
    by_cases hz0 : z=z₀
    · subst hz0
      simpa using qf
    · have qo : (z - z₀)^k ≠ 0:=pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z=q0 z:=by simpa [q0,F,k] using hq_ne z hz0
      have qr : (z - z₀)^k*q0 z=F z:=by
        calc
          (z - z₀)^k*q0 z
              = (((z - z₀)^k)*F z)/((z - z₀)^k):=by
                  simp [q0,div_eq_mul_inv,mul_assoc]
          _ = F z:=by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) qo)
      have : F z=(z - z₀)^k*q z:=by
        calc
          F z=(z - z₀)^k*q0 z:=qr.symm
          _ = (z - z₀)^k*q z:=by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n:=k)).2 ⟨q,hqA,hq0,qu⟩
  have qp : analyticOrderNatAt F z₀ = k:=by
    simp [analyticOrderNatAt,hk']
  simpa [F,k] using qp
theorem zb (m:ℕ) {f:ℂ → ℂ} (hf : Differentiable ℂ f) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z₀ = analyticOrderNatAt f z₀ := by
 have hcp :
   analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z₀ =
    (Z9 (f:=f) z₀).card :=
  zs (m:=m) (f:=f) (h_sum:=h_sum)
   (z₀ := z₀)
 have qa :
   (Z9 (f:=f) z₀).card=analyticOrderNatAt f z₀ :=
  zt (hf:=hf) (z₀ := z₀) hz₀
 simpa [qa] using hcp
end Complex.Hadamard
end
end
section
section
namespace Complex.Hadamard
open scoped Topology
open Set
lemma ve {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) : ∀ z:ℂ,analyticOrderAt f z ≠ ⊤ := by
 rcases hnot with ⟨z1,hz1⟩
 have qb : AnalyticOnNhd ℂ f (Set.univ : Set ℂ):=by
  intro z hz
  exact (Differentiable.analyticAt (f:=f) hf z)
 have qa : analyticOrderAt f z1 ≠ ⊤ := by
  have : analyticOrderAt f z1=0 :=
   (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
  simp [this]
 intro z
 exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf:=qb)
  (U:=(Set.univ : Set ℂ)) (x:=z1) (y:=z) (by simpa using isPreconnected_univ)
  (by simp) (by simp) qa
lemma vu {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) {B r:ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (qd : ∀ p : Wz f (Set.univ : Set ℂ),‖Wc p‖ ≤ B → r ≠ ‖Wc p‖) : ∀ u:ℂ,‖u‖ = r → f u ≠ 0:=by
 intro u hur
 have hu0 : u ≠ 0:=by
  intro hu0
  subst hu0
  have : (0:ℝ)=r:=by simpa using hur
  exact (ne_of_gt hrpos) this.symm
 intro hfu0
 have qc : analyticOrderAt f u ≠ ⊤ :=
  ve (f:=f) hf hnot u
 have qb : analyticOrderNatAt f u ≠ 0:=by
  intro h0
  have hEN : (analyticOrderNatAt f u : ENat)=0:=by simp [h0]
  have qh : analyticOrderAt f u=0:=by
   have qe : (analyticOrderNatAt f u : ENat)=analyticOrderAt f u :=
    Nat.cast_analyticOrderNatAt (f:=f) (z₀ := u) qc
   simpa [qe] using hEN
  have han : AnalyticAt ℂ f u:=Differentiable.analyticAt (f:=f) hf u
  exact ((han.analyticOrderAt_eq_zero).1 qh) hfu0
 have qa : 0 < (Z9 (f:=f) u).card:=by
  have qf :=
   zt (hf:=hf) (z₀ := u) hu0
  have : 0 < analyticOrderNatAt f u:=Nat.pos_of_ne_zero qb
  simpa [qf] using this
 rcases Finset.card_pos.mp qa with ⟨p,hp⟩
 have qg : Wc p=u :=
  (Zl (f:=f) (z₀ := u) p).1 hp
 have hpB : ‖Wc p‖ ≤ B:=by
  have : ‖Wc p‖ = r:=by simp [qg,hur]
  simpa [this] using hBr
 have : r ≠ ‖Wc p‖ := qd p hpB
 exact this (by simp [qg,hur])
theorem zE (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z₀ : ℂ) : analyticOrderAt (VJ m f (Set.univ : Set ℂ)) z₀ = ((Z9 (f:=f) z₀).card : ℕ∞):=by
 let F:ℂ → ℂ:=VJ m f (Set.univ : Set ℂ)
 have qf :
   analyticOrderNatAt F z₀ = (Z9 (f:=f) z₀).card:=by
  simpa [F] using
   (zs
    (m:=m) (f:=f) (h_sum:=h_sum) (z₀ := z₀))
 have qb : DifferentiableOn ℂ F (Set.univ : Set ℂ):=by
  simpa [F] using yt (m:=m) (f:=f) h_sum
 have qd : Differentiable ℂ F:=by
  intro z
  exact (qb z (by simp)).differentiableAt (by simp)
 have qc : analyticOrderAt F z₀ ≠ ⊤ :=
  ve (hf:=qd)
   ⟨0,by simp [F,Yy]⟩ z₀
 have qe : (analyticOrderNatAt F z₀ : ℕ∞)=analyticOrderAt F z₀ :=
  Nat.cast_analyticOrderNatAt (f:=F) (z₀ := z₀) qc
 have qa :
   (analyticOrderNatAt F z₀ : ℕ∞) =
    ((Z9 (f:=f) z₀).card : ℕ∞):=by
  simp [qf]
 simpa [F,qe] using qa
theorem yE (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) {z:ℂ} (hz : ∀ p : Wz f (Set.univ : Set ℂ),z ≠ Wc p) : VJ m f (Set.univ : Set ℂ) z ≠ 0:=by
  let F:ℂ → ℂ:=VJ m f (Set.univ : Set ℂ)
  have qa : Z9 (f:=f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((Zl (f:=f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have qb :
      analyticOrderAt F z=(0 : ℕ∞):=by
    have h :=
      zE
        (m:=m) (f:=f) (h_sum:=h_sum) (z₀ := z)
    simpa [F,qa] using h
  have han : AnalyticAt ℂ F z:=by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((yt m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 qb
theorem zn
  {f:ℂ → ℂ} {z:ℂ}
  (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
   ‖Wc p‖⁻¹ ^ (2:ℕ)))
  (hz : ∀ p : Wz f (Set.univ : Set ℂ),z ≠ Wc p) :
  logDeriv (VJ 1 f (Set.univ : Set ℂ)) z =
   ∑' p : Wz f (Set.univ : Set ℂ),
    (1/(z - Wc p)+1/Wc p) :=
 yy h_sum hz
  (yE 1 f h_sum hz)
end Hadamard
end Complex
end
end
section
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def W9 (m:ℕ) (f:ℂ → ℂ) (z:ℂ):ℂ :=
 z^(analyticOrderNatAt f 0)*VJ m f (Set.univ : Set ℂ) z
theorem yI (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : Differentiable ℂ (VJ m f (Set.univ : Set ℂ)):=by
 intro z
 have qa :
   DifferentiableOn ℂ (VJ m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
  yt (m:=m) (f:=f) h_sum
 exact (qa z (by simp)).differentiableAt (by simp)
theorem vw (m:ℕ) (f:ℂ → ℂ)
  (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
   ‖Wc p‖⁻¹ ^ (m+1))) (z:ℂ) :
  AnalyticAt ℂ (VJ m f (Set.univ : Set ℂ)) z :=
 (yI m f h_sum).analyticAt z
theorem Yz (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : Differentiable ℂ (W9 m f):=by
 have qa : Differentiable ℂ (VJ m f (Set.univ : Set ℂ)):=by
  exact yI m f h_sum
 simpa [W9] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul qa
theorem Vl {m:ℕ} {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) {z:ℂ} (hz : f z ≠ 0) : W9 m f z ≠ 0:=by
  have qe : ∀ w:ℂ,analyticOrderAt f w ≠ ⊤ :=
    ve (hf:=hf) hnot
  have qi : AnalyticAt ℂ f z:=hf.analyticAt z
  have qh : analyticOrderNatAt f z=0:=by
    have : analyticOrderAt f z=0:=(qi.analyticOrderAt_eq_zero).2 hz
    have qj : (analyticOrderNatAt f z : ℕ∞)=analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f:=f) (z₀ := z) (qe z)
    have : (analyticOrderNatAt f z : ℕ∞)=0:=by simp [qj,this]
    exact_mod_cast this
  have qf : AnalyticAt ℂ (VJ m f (Set.univ : Set ℂ)) z:=by
    exact vw m f h_sum z
  by_cases hz0 : z=0
  · subst hz0
    have qk : analyticOrderNatAt f 0=0:=by simpa using qh
    simp [W9,qk,Yy]
  · have hp : z^(analyticOrderNatAt f 0) ≠ 0:=pow_ne_zero _ hz0
    have qc :
        analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z=0:=by
      simpa [qh] using
        (zb (m:=m) (hf:=hf)
          (h_sum:=h_sum) (z₀ := z) hz0)
    have qg : VJ m f (Set.univ : Set ℂ) z ≠ 0:=by
      have qb :
          Differentiable ℂ (VJ m f (Set.univ : Set ℂ)):=by
        exact yI m f h_sum
      have qa :
          analyticOrderAt (VJ m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        ve (hf:=qb)
          ⟨0,by simp [Yy]⟩ z
      have qd :
          (analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (VJ m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f:=VJ m f (Set.univ : Set ℂ)) (z₀ := z) qa
      have : analyticOrderAt (VJ m f (Set.univ : Set ℂ)) z=0:=by
        have :
            (analyticOrderNatAt
              (VJ m f (Set.univ : Set ℂ)) z : ℕ∞)=0:=by
          exact_mod_cast qc
        simp [qd] at this
        simpa using this
      exact (qf.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp qg
lemma yd (m:ℕ) (f:ℂ → ℂ) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) 0=0:=by
 have qb :
   Differentiable ℂ (VJ m f (Set.univ : Set ℂ)):=by
  exact yI m f h_sum
 have qa :
   analyticOrderAt (VJ m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
  ve (hf:=qb)
   ⟨0,by simp [Yy]⟩ 0
 have qc : AnalyticAt ℂ (VJ m f (Set.univ : Set ℂ)) 0 :=
  qb.analyticAt 0
 have qd : VJ m f (Set.univ : Set ℂ) 0 ≠ 0:=by
  simp [Yy]
 have : analyticOrderAt (VJ m f (Set.univ : Set ℂ)) 0=0 :=
  (qc.analyticOrderAt_eq_zero).2 qd
 have qe :
   (analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
    analyticOrderAt (VJ m f (Set.univ : Set ℂ)) 0 :=
  Nat.cast_analyticOrderNatAt
   (f:=VJ m f (Set.univ : Set ℂ)) (z₀ := (0:ℂ)) qa
 have :
   (analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
    0:=by
  simp [qe,this]
 exact_mod_cast this
theorem wx (m:ℕ) {f:ℂ → ℂ} (hf : Differentiable ℂ f) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (z:ℂ) : analyticOrderNatAt (W9 m f) z=analyticOrderNatAt f z:=by
  by_cases hz0 : z=0
  · subst hz0
    have qh : AnalyticAt ℂ (fun z:ℂ => z^analyticOrderNatAt f 0) 0:=by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have qc :
        analyticOrderAt (fun z:ℂ => z^analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      ve
        (hf:=(differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1,by simp⟩ 0
    have qf : AnalyticAt ℂ (VJ m f (Set.univ : Set ℂ)) 0:=by
      exact vw m f h_sum 0
    have qg :
        analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) 0=0 :=
      yd (m:=m) (f:=f) h_sum
    have ql : analyticOrderNatAt (fun z:ℂ => z) 0=1:=by
      have qd : Differentiable ℂ (fun z:ℂ => z):=differentiable_id
      have qm :
          (MeromorphicOn.divisor (fun z:ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z:ℂ => z) 0:ℤ):=by
        simpa using
          (vZ
            (f:=fun z:ℂ => z) qd 0)
      have qi : (MeromorphicOn.divisor (fun z:ℂ => z) (Set.univ : Set ℂ)) 0=1:=by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0:ℂ))
            (U:=(Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z:ℂ => z) 0:ℤ)=1:=by
        simpa [qm] using qi
      exact_mod_cast this
    have qj :
        analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0:=by
      have qn : AnalyticAt ℂ (fun z:ℂ => z) 0:=by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id:ℂ → ℂ) 0)
      simpa [ql] using! (analyticOrderNatAt_pow (hf:=qn) (n:=analyticOrderNatAt f 0))
    have qo :
        analyticOrderNatAt (W9 m f) 0 =
          analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) 0:=by
      have qa :
          analyticOrderAt (VJ m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        ve
          (hf:=yI m f h_sum)
          ⟨0,by simp [Yy]⟩ 0
      simpa [W9] using!
        analyticOrderNatAt_mul (hf:=qh) (hg:=qf)
          (hf':=qc) (hg':=qa)
    simp [qo,qj,qg]
  · have qh : AnalyticAt ℂ (fun z:ℂ => z^analyticOrderNatAt f 0) z:=by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have qc :
        analyticOrderAt (fun z:ℂ => z^analyticOrderNatAt f 0) z ≠ ⊤ :=
      ve
        (hf:=(differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1,by simp⟩ z
    have qj : analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) z=0:=by
      have hz' : (fun z:ℂ => z^analyticOrderNatAt f 0) z ≠ 0:=by
        simp [hz0]
      have : analyticOrderAt (fun z:ℂ => z^analyticOrderNatAt f 0) z=0 :=
        ((qh).analyticOrderAt_eq_zero).2 hz'
      have qk : (analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z:ℂ => z^analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f:=fun z:ℂ => z^analyticOrderNatAt f 0) (z₀ := z) qc
      have : (analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) z : ℕ∞)=0:=by
        simp [qk,this]
      exact_mod_cast this
    have qe :
        analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      zb
        (m:=m) (hf:=hf) (h_sum:=h_sum) (z₀ := z) hz0
    have qf : AnalyticAt ℂ (VJ m f (Set.univ : Set ℂ)) z:=by
      exact vw m f h_sum z
    have qb :
        analyticOrderAt (VJ m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      ve
        (hf:=yI m f h_sum)
        ⟨0,by simp [Yy]⟩ z
    have qo :
        analyticOrderNatAt (W9 m f) z =
          analyticOrderNatAt (fun z:ℂ => z^analyticOrderNatAt f 0) z +
            analyticOrderNatAt (VJ m f (Set.univ : Set ℂ)) z:=by
      simpa [W9] using!
        analyticOrderNatAt_mul (hf:=qh) (hg:=qf)
          (hf':=qc) (hg':=qb)
    simp [qo,qj,qe]
theorem Vm (m:ℕ) {f:ℂ → ℂ} (hf : Differentiable ℂ f) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : MeromorphicOn.divisor (W9 m f) (Set.univ : Set ℂ)=MeromorphicOn.divisor f (Set.univ : Set ℂ):=by
 ext z
 have qa : Differentiable ℂ (W9 m f) :=
  Yz (m:=m) f h_sum
 have qb : Differentiable ℂ f:=hf
 have qc :
   (MeromorphicOn.divisor (W9 m f) (Set.univ : Set ℂ)) z =
    (analyticOrderNatAt (W9 m f) z:ℤ):=by
  simpa using (vZ (f:=W9 m f) qa z)
 have hfz :
   (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
    (analyticOrderNatAt f z:ℤ):=by
  simpa using (vZ (f:=f) qb z)
 simp [qc,hfz,wx (m:=m) (hf:=hf) (h_sum:=h_sum) z]
theorem ZI (m:ℕ) {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : MeromorphicOn.divisor (fun z:ℂ => f z/W9 m f z) (Set.univ : Set ℂ)=0:=by
  have ql : MeromorphicOn f (Set.univ : Set ℂ):=by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have qd : Differentiable ℂ (W9 m f) :=
    Yz (m:=m) f h_sum
  have qi : MeromorphicOn (W9 m f) (Set.univ : Set ℂ):=by
    intro z hz
    exact (qd.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1,hz1⟩
  have qo : W9 m f z1 ≠ 0 :=
    Vl (m:=m) (f:=f) hf ⟨z1,hz1⟩ h_sum hz1
  have qc : ∀ z ∈ (Set.univ : Set ℂ),meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have qf : meromorphicOrderAt f z1 ≠ ⊤ := by
      have qr : MeromorphicAt f z1:=ql z1 (by simp)
      have qp : ContinuousAt f z1:=(hf.differentiableAt).continuousAt
      have qk : ∀ᶠ w in 𝓝 z1,f w ≠ 0 :=
        (qp.ne_iff_eventually_ne continuousAt_const).1 hz1
      have qg : ∀ᶠ w in 𝓝[≠] z1,f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qk
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf:=qr)).2 qg
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf:=ql)
      (x:=z1) (hU:=isPreconnected_univ) (h₁x:=by simp) (hy:=by simp) qf
  have qa :
      ∀ z ∈ (Set.univ : Set ℂ),meromorphicOrderAt (W9 m f) z ≠ ⊤ := by
    intro z hzU
    have qf : meromorphicOrderAt (W9 m f) z1 ≠ ⊤ := by
      have qm : MeromorphicAt (W9 m f) z1:=qi z1 (by simp)
      have qp : ContinuousAt (W9 m f) z1 :=
        (qd.differentiableAt).continuousAt
      have qk : ∀ᶠ w in 𝓝 z1,W9 m f w ≠ 0 :=
        (qp.ne_iff_eventually_ne continuousAt_const).1 qo
      have qg : ∀ᶠ w in 𝓝[≠] z1,W9 m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qk
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf:=qm)).2 qg
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf:=qi)
      (x:=z1) (hU:=isPreconnected_univ) (h₁x:=by simp) (hy:=by simp) qf
  have qb :
      ∀ z ∈ (Set.univ : Set ℂ),
        meromorphicOrderAt (fun z:ℂ => (W9 m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have qj :
        MeromorphicOn (fun z:ℂ => (W9 m f z)⁻¹) (Set.univ : Set ℂ) :=
      qi.inv
    have qf :
        meromorphicOrderAt (fun z:ℂ => (W9 m f z)⁻¹) z1 ≠ ⊤ := by
      have qn : MeromorphicAt (fun z:ℂ => (W9 m f z)⁻¹) z1 :=
        qj z1 (by simp)
      have qe : ContinuousAt (W9 m f) z1 :=
        (qd.differentiableAt).continuousAt
      have qp : ContinuousAt (fun z:ℂ => (W9 m f z)⁻¹) z1 :=
        qe.inv₀ qo
      have qq : (fun z:ℂ => (W9 m f z)⁻¹) z1 ≠ 0:=by
        simpa using inv_ne_zero qo
      have qk :
          ∀ᶠ w in 𝓝 z1,(fun z:ℂ => (W9 m f z)⁻¹) w ≠ 0 :=
        (qp.ne_iff_eventually_ne continuousAt_const).1 qq
      have qg :
          ∀ᶠ w in 𝓝[≠] z1,(fun z:ℂ => (W9 m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qk
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf:=qn)).2 qg
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf:=qj)
      (x:=z1) (hU:=isPreconnected_univ) (h₁x:=by simp) (hy:=by simp) qf
  have qh : MeromorphicOn.divisor (W9 m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    Vm (m:=m) (hf:=hf) (h_sum:=h_sum)
  calc
    MeromorphicOn.divisor (fun z:ℂ => f z/W9 m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor
            (fun z:ℂ => f z*(W9 m f z)⁻¹) (Set.univ : Set ℂ):=by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z:ℂ => (W9 m f z)⁻¹) (Set.univ : Set ℂ):=by
          simpa using (MeromorphicOn.divisor_fun_mul (U:=(Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (W9 m f z)⁻¹) ql (qi.inv)
            qc qb)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) -
          MeromorphicOn.divisor (W9 m f) (Set.univ : Set ℂ):=by
          simp [sub_eq_add_neg]
    _ = 0:=by
          simp [qh]
theorem vN (m:ℕ) {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) : ∃ H:ℂ → ℂ,Differentiable ℂ H ∧ (∀ z,H z ≠ 0) ∧ ∀ z:ℂ,f z=H z*z^(analyticOrderNatAt f 0)*VJ m f (Set.univ : Set ℂ) z:=by
  let qo:ℂ → ℂ:=W9 m f
  let q:ℂ → ℂ:=fun z => f z/qo z
  have qb : Differentiable ℂ qo :=
    Yz (m:=m) f h_sum
  have qe : MeromorphicOn q (Set.univ : Set ℂ):=by
    intro z hzU
    have qz : MeromorphicAt f z:=(hf.analyticAt z).meromorphicAt
    have qi : MeromorphicAt qo z:=(qb.analyticAt z).meromorphicAt
    simpa [q,qo,div_eq_mul_inv] using! (qz.mul qi.inv)
  let H:ℂ → ℂ:=toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have qp : MeromorphicOn.divisor H (Set.univ : Set ℂ)=0:=by
    have qq : MeromorphicOn.divisor q (Set.univ : Set ℂ)=0 :=
      ZI (m:=m) (f:=f) (hf:=hf)
        (hnot:=hnot) (h_sum:=h_sum)
    simpa [H,qq] using
      (MeromorphicOn.divisor_of_toMeromorphicNFOn
        (f:=q) (U:=(Set.univ : Set ℂ)) qe)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ):=by
    have :
        (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤
          MeromorphicOn.divisor H (Set.univ : Set ℂ):=by
      simp [qp]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f:=hNF)).1 (by simp [qp])
  have qd : Differentiable ℂ H:=by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1,hz1⟩
  have qr : qo z1 ≠ 0 :=
    Vl (m:=m) (f:=f) hf ⟨z1,hz1⟩ h_sum hz1
  have qA : AnalyticAt ℂ q z1:=by
    have qj : AnalyticAt ℂ qo z1:=qb.analyticAt z1
    exact (hf.analyticAt z1).div qj qr
  have qs : MeromorphicNFAt q z1:=qA.meromorphicNFAt
  have qt : toMeromorphicNFAt q z1=q:=(toMeromorphicNFAt_eq_self (f:=q) (x:=z1)).2 qs
  have hH1 : H z1=q z1:=by
    have hx : z1 ∈ (Set.univ : Set ℂ):=by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1=toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f:=q) (U:=(Set.univ : Set ℂ)) qe hx)
    simpa [H,qt] using this
  have qk : H z1 ≠ 0:=by
    have : q z1 ≠ 0:=div_ne_zero hz1 qr
    simpa [hH1] using this
  have qc : ∀ z:ℂ,analyticOrderAt H z ≠ ⊤ := by
    exact ve (hf:=qd) ⟨z1,qk⟩
  have qa : ∀ z:ℂ,analyticOrderNatAt H z=0:=by
    intro z
    have qu :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z=(analyticOrderNatAt H z:ℤ):=by
      simpa using (vZ (f:=H) qd z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z=0:=by
      simp [qp]
    have : (analyticOrderNatAt H z:ℤ)=0:=by simpa [qu] using this
    exact_mod_cast this
  have qv : ∀ z:ℂ,H z ≠ 0:=by
    intro z
    have qw : (analyticOrderNatAt H z : ℕ∞)=analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f:=H) (z₀ := z) (qc z)
    have : analyticOrderAt H z=0:=by
      have : (analyticOrderNatAt H z : ℕ∞)=0:=by exact_mod_cast (qa z)
      simpa [qw] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ):=fun z hzU => hf.analyticAt z
  have qx : AnalyticOnNhd ℂ qo (Set.univ : Set ℂ):=fun z hzU => qb.analyticAt z
  have ql : AnalyticOnNhd ℂ (fun z => H z*qo z) (Set.univ : Set ℂ) :=
    (hA.mul qx)
  have qm : f =ᶠ[𝓝 z1] fun z => H z*qo z:=by
    have qf : ∀ᶠ z in 𝓝 z1,qo z ≠ 0 :=
      (qb.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 qr
    have qg : H =ᶠ[𝓝 z1] q:=by
      have hx : z1 ∈ (Set.univ : Set ℂ):=by simp
      have qB :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1:=by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f:=q)
          (U:=(Set.univ : Set ℂ)) qe hx)
      simpa [H,qt] using qB
    filter_upwards [qf,qg] with z hzden hHz
    have qh : q z*qo z=f z:=by
      dsimp [q]
      field_simp [hzden]
    calc
      f z=q z*qo z:=qh.symm
      _ = H z*qo z:=by simp [hHz]
  have qy : f=fun z => H z*qo z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf:=hfA) (hg:=ql) qm
  refine ⟨H,qd,qv,?_⟩
  intro z
  have qn : f z=H z*qo z:=congrArg (fun g => g z) qy
  simpa [qo,W9,mul_assoc,mul_left_comm,mul_comm] using qn
end Complex.Hadamard
end
end
section
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
lemma vz {D : locallyFinsupp E ℤ} {r:ℝ} {z : E} (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
 have qa : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
 simpa [mem_closedBall,dist_zero_right] using qa
lemma wK {D : locallyFinsupp E ℤ} {r:ℝ} {z : E} (hz : ‖z‖ ≤ |r|) : toClosedBall r D z=D z:=by
 have qa : z ∈ closedBall (0 : E) |r| := by
  simpa [mem_closedBall,dist_zero_right] using hz
 simpa using toClosedBall_eval_within (f:=D) qa
lemma zA {D : locallyFinsupp E ℤ} {r:ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) : z ∈ (toClosedBall r D).support:=by
 rw [Function.mem_support]
 rw [wK hzR]
 rwa [Function.mem_support] at hzD
lemma vE {D : locallyFinsupp E ℤ} {r:ℝ} {z : E} (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support:=by
 have qa : ‖z‖ ≤ |r| := vz hz
 rw [Function.mem_support] at hz ⊢
 rw [wK qa] at hz
 exact hz
noncomputable def WV {E : Type*} [NormedAddCommGroup E] [ProperSpace E] (D : locallyFinsupp E ℤ) (R:ℝ) : ℝ:=by
 classical
 exact
  (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
   (fun z => z ≠ (0 : E))).sum fun z => (D z:ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
theorem zc {R:ℝ} {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) : logCounting (divisor f ⊤) R=circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have qa : Meromorphic f:=fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f:=f) qa hR
end Function.locallyFinsuppWithin
end
end
section
section
namespace Real
theorem Z8 {x:ℝ} (hx : 0 ≤ x) : log (1+exp x) ≤ x+log 2:=by
  have qa : (1:ℝ) ≤ exp x:=by
    simpa using (one_le_exp_iff.2 hx)
  have qb : 1+exp x ≤ 2*exp x:=by linarith
  have qc : log (1+exp x) ≤ log (2*exp x) :=
    log_le_log (by positivity) qb
  calc
    log (1+exp x) ≤ log (2*exp x):=qc
    _ = log 2+x:=by simp [log_mul,add_comm]
    _ = x+log 2:=by ring
theorem wh {x y:ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) (hxy : y ≤ exp x) : log (1+y) ≤ x+log 2:=by
 have qa : 0 < (1:ℝ)+y:=by linarith
 have hle : (1:ℝ)+y ≤ 1+exp x:=by linarith
 exact (log_le_log qa hle).trans (Z8 hx)
theorem Vt {x y:ℝ} (hy : 0 ≤ y) (hxy : log (1+y) ≤ x) : y ≤ exp x:=by
 have qa : 0 < (1:ℝ)+y:=by linarith
 have qb : 1+y ≤ exp x:=(log_le_iff_le_exp qa).1 hxy
 linarith
theorem Wg (x:ℝ) : -log⁺ x⁻¹ ≤ log x:=by
 linarith [posLog_sub_posLog_inv (x:=x),posLog_nonneg (x:=x)]
end Real
end
end
section
section
namespace Real
theorem uh (x:ℝ) : x ≤ exp x :=
 le_trans (by linarith : x ≤ x+1) (add_one_le_exp x)
end Real
end
end
section
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
theorem YC (w : E) : Real.log ‖w‖ ≤ Real.log (1 + ‖w‖):=by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have qa : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log qa (by linarith [norm_nonneg w])
variable {F : Type*} [NormedAddCommGroup F]
theorem wR {z : F} {r:ℝ} (hz : ‖z‖ ≤ r) : 0 ≤ Real.log (r * ‖z‖⁻¹):=by
  by_cases hz0 : z=0
  · simp [hz0]
  · have qa : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1:ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1:ℝ) ≤ r / ‖z‖ := (one_le_div qa).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this
theorem yk {z : F} {R:ℝ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ R) : Real.log 2 ≤ Real.log ((2*R) * ‖z‖⁻¹):=by
 have qa : 0 < ‖z‖ := norm_pos_iff.2 hz0
 have qb : (1:ℝ) ≤ R / ‖z‖ := (one_le_div qa).2 hz
 have qc : (2:ℝ) ≤ (2*R) * ‖z‖⁻¹ := by
  have : (2:ℝ) ≤ 2*(R / ‖z‖):=by nlinarith
  simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using this
 exact Real.log_le_log (by norm_num) qc
theorem wI {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x,1 ≤ r x) (hρτ : ρ ≤ τ) (qa : ∀ x,‖f x‖ ≤ Real.exp (C*(r x) ^ ρ)) : ∀ x,‖f x‖ ≤ Real.exp (C*(r x) ^ τ):=by
 intro x
 refine (qa x).trans (Real.exp_le_exp.2 ?_)
 exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) hρτ) hC
theorem w5 {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x,1 ≤ r x) (hρτ : ρ ≤ τ) (qa : ∀ x,Real.log (1 + ‖f x‖) ≤ C*(r x) ^ ρ) : ∀ x,‖f x‖ ≤ Real.exp (C*(r x) ^ τ):=by
 intro x
 have qb : (r x) ^ ρ ≤ (r x) ^ τ :=
  Real.rpow_le_rpow_of_exponent_le (hr x) hρτ
 have hlogτ : Real.log (1 + ‖f x‖) ≤ C*(r x) ^ τ :=
  (qa x).trans (mul_le_mul_of_nonneg_left qb hC)
 exact Real.Vt (norm_nonneg (f x)) hlogτ
theorem wQ {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ) (hr : ∀ x,1 ≤ r x) (qb : ∀ x,‖f x‖ ≤ Real.exp (C*(r x) ^ τ)) : ∃ C' > 0,∀ x,Real.log (1 + ‖f x‖) ≤ C'*(r x) ^ τ := by
 refine ⟨C+Real.log 2,by
  have qc : 0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
  linarith,?_⟩
 intro x
 have hX : (1:ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
 have hB : 0 ≤ C*(r x) ^ τ :=
  mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
 have qd :
   Real.log (1 + ‖f x‖) ≤ C*(r x) ^ τ + Real.log 2 :=
  Real.wh (norm_nonneg _) hB (qb x)
 have qa : 0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
 nlinarith [qd,hX,qa]
theorem vh {f : α → E} {r : α → ℝ} {τ : ℝ} {n:ℕ} (hr : ∀ x,1 ≤ r x) (hτn : τ < (n:ℝ)) (qa : ∃ C > 0,∀ x,‖f x‖ ≤ Real.exp (C*(r x) ^ τ)) : ∃ C > 0,∀ x,‖f x‖ ≤ Real.exp (C*(r x)^n):=by
 rcases qa with ⟨C,hCpos,hC⟩
 have qb :
   ∀ x,‖f x‖ ≤ Real.exp (C*(r x)^(n:ℝ)) :=
  wI
   (f:=f) (r:=r) hCpos.le hr (le_of_lt hτn) hC
 refine ⟨C,hCpos,?_⟩
 intro x
 have qc : (r x)^(n:ℝ)=(r x)^n:=Real.rpow_natCast (r x) n
 simpa [qc] using qb x
theorem Vy {b r:ℝ} (hb : 0 < b) (hr : 1 ≤ r) : r^2 ≤ exp ((4/b)*r^b):=by
  have hrpos : 0 < r:=zero_lt_one.trans_le hr
  have qa : 0 ≤ (2/b:ℝ):=by positivity
  have qb : 0 ≤ (4/b:ℝ):=by positivity
  have qc : log r ≤ (2/b)*r^(b/2):=by
    have qd : (b/2)*log r ≤ exp ((b/2)*log r):=uh _
    calc
      log r=(2/b)*((b/2)*log r):=by
        field_simp [ne_of_gt hb]
      _ ≤ (2/b)*exp ((b/2)*log r) :=
        mul_le_mul_of_nonneg_left qd qa
      _ = (2/b)*r^(b/2):=by
        simp [rpow_def_of_pos hrpos,mul_comm]
  have qe : r^(b/2) ≤ r^b :=
    rpow_le_rpow_of_exponent_le hr (by linarith)
  have qf : log (r^2) ≤ (4/b)*r^b:=by
    calc
      log (r^2)=2*log r:=by
        simp [log_pow]
      _ ≤ 2*((2/b)*r^(b/2)) :=
        mul_le_mul_of_nonneg_left qc (by norm_num)
      _ = (4/b)*r^(b/2):=by ring
      _ ≤ (4/b)*r^b :=
        mul_le_mul_of_nonneg_left qe qb
  have qg : 0 < r^2:=by positivity
  rw [← exp_log qg]
  exact exp_le_exp.2 qf
theorem yg {x r:ℝ} (hx : 0 ≤ x) (hr : r ≤ 2*max x 1) :  1+r ≤ 3*(1+x):=by
 have qa : max x 1 ≤ 1+x:=max_le_iff.2 ⟨by linarith,by linarith⟩
 nlinarith
theorem vQ {A B x y τ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ : 0 ≤ τ) (hxy : x ≤ B*y) : Real.exp (A*x ^ τ) ≤ Real.exp ((A*B ^ τ)*y ^ τ):=by
 refine Real.exp_le_exp.2 ?_
 have qb : x ^ τ ≤ (B*y) ^ τ := Real.rpow_le_rpow hx hxy hτ
 have qa : (B*y) ^ τ = B ^ τ * y ^ τ := by
  simpa using (Real.mul_rpow (x:=B) (y:=y) (z := τ) hB hy)
 simpa [mul_assoc] using mul_le_mul_of_nonneg_left (qb.trans_eq qa) hA
theorem z7 {ρ : ℝ} (hρ : 0 ≤ ρ) : ∃ τ : ℝ,ρ < τ ∧ τ < (Nat.floor ρ + 1:ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
 set m : ℕ:=Nat.floor ρ
 set τ : ℝ:=(ρ + (m+1:ℝ))/2
 have hm : ρ < (m+1:ℝ):=by simpa [m] using Nat.lt_floor_add_one (a := ρ)
 have hτ : ρ < τ := by dsimp [τ]; linarith
 have hτ_lt : τ < (m+1:ℝ):=by dsimp [τ]; linarith
 have hτ_nonneg : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
 have hfloorτ : Nat.floor τ = m:=by
  have hm_le_τ : (m:ℝ) ≤ τ := le_trans (Nat.floor_le hρ) (le_of_lt hτ)
  have hτ_lt_m1 : τ < (m:ℝ)+1:=by simpa [add_assoc,add_comm,add_left_comm] using hτ_lt
  exact (Nat.floor_eq_iff hτ_nonneg).2 ⟨hm_le_τ,hτ_lt_m1⟩
 exact ⟨τ,hτ,by simpa [m] using hτ_lt,hτ_nonneg,by simpa [m] using hfloorτ⟩
open Metric Complex
theorem yJ {f:ℂ → ℂ} {C ρ R:ℝ} (hC : ∀ z:ℂ,log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) {z:ℂ} (hz : z ∈ sphere (0:ℂ) |R|) : log ‖f z‖ ≤ C*(1 + |R|) ^ ρ := by
 have qa : ‖z‖ = |R| := by
  simpa [mem_sphere,dist_zero_right] using hz
 simpa [qa] using le_trans (YC (f z)) (hC z)
end Real
end
end
section
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
theorem wm {f:ℂ → ℂ} {ρ C:ℝ} (hf : Differentiable ℂ f) (hC : ∀ z:ℂ,log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) {R:ℝ} (hR0 : 0 < R) : logCounting (divisor f (Set.univ : Set ℂ)) R ≤ C*(1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0:=ne_of_gt hR0
  have hEq :=
    zc (f:=f) hf hR
  have qc : MeromorphicOn f (sphere (0:ℂ) |R|):=by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have qd : CircleIntegrable (fun z:ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm qc
  have qa : ∀ z ∈ sphere (0:ℂ) |R|,
      log ‖f z‖ ≤ C*(1 + |R|) ^ ρ := by
    intro z hz
    exact yJ hC hz
  have qb :
      circleAverage (fun z:ℂ => log ‖f z‖) 0 R ≤ C*(1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c:=(0:ℂ)) (R:=R)
      (f:=fun z => log ‖f z‖) qd qa
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z:ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z:ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C*(1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [qb]
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
theorem yW {D : locallyFinsupp E ℤ} (qj : 0 ≤ D) {R:ℝ} (hR : 1 ≤ R) : (log 2)*WV D R ≤ logCounting D (2*R):=by
  classical
  have hR0 : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hR
  set r : ℝ:=2*R
  have hrpos : 0 < r:=by dsimp [r]; nlinarith
  let Dr:=toClosedBall r D
  have ql : Set.Finite Dr.support:=Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E:=ql.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E:=SR.filter fun z => z ≠ (0 : E)
  have qo : S ⊆ F:=by
    intro z hzS
    have qi : z ∈ SR:=(Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support:=by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        qi
    have qb : ‖z‖ ≤ R:=by
      have:=vz hzR
      simpa [abs_of_pos hR0] using this
    have qc : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r:=le_trans qb (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support:=vE hzR
    have : z ∈ Dr.support:=by
      simpa [Dr] using
        zA (D:=D) (r:=r) hzD qc
    exact ql.mem_toFinset.2 this
  have qd :
      logCounting D r
        = (F.sum fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹))+(D 0:ℝ)*log r:=by
    have qs : Function.support (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)) ⊆ F:=by
      intro z hz
      have : Dr z ≠ 0:=by
        by_contra h0
        simp [Function.mem_support,h0] at hz
      have : z ∈ Dr.support:=by simpa [Function.mem_support] using this
      exact ql.mem_toFinset.2 this
    simp [logCounting,Dr,r,
      finsum_eq_sum_of_support_subset (f:=fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)) (s:=F) qs]
  have qm :
      (log 2)*(S.sum fun z => (D z:ℝ))
        ≤ F.sum (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)):=by
    have qe : ∀ z ∈ F,0 ≤ (Dr z:ℝ)*log (r * ‖z‖⁻¹):=by
      intro z hzF
      have qp : z ∈ Dr.support:=ql.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z:=by
        have qv : 0 ≤ D z:=qj z
        have qw : Dr z=D z :=
          wK (vz qp)
        simpa [qw] using qv
      have qx : 0 ≤ log (r * ‖z‖⁻¹):=by
        have qy : ‖z‖ ≤ r:=by
          have qt:=vz qp
          simpa [abs_of_pos hrpos] using qt
        exact wR qy
      exact mul_nonneg (by exact_mod_cast hDz) qx
    have qq :
        S.sum (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg qo (by
        intro z hzF _; exact qe z hzF)
    have qk : ∀ z ∈ S,(log 2)*(D z:ℝ) ≤ (Dr z:ℝ)*log (r * ‖z‖⁻¹):=by
      intro z hzS
      have hz0 : z ≠ (0 : E):=(Finset.mem_filter.1 hzS).2
      have qb : ‖z‖ ≤ R:=by
        have qi : z ∈ SR:=(Finset.mem_filter.1 hzS).1
        have qr : z ∈ (toClosedBall R D).support:=by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            qi
        have qt:=vz qr
        simpa [abs_of_pos hR0] using qt
      have qn : log 2 ≤ log (r * ‖z‖⁻¹):=by
        simpa [r] using yk hz0 qb
      have qg : 0 ≤ D z:=qj z
      have qf : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r:=le_trans qb (by dsimp [r]; nlinarith)
        simpa [mem_closedBall,dist_zero_right,abs_of_pos hrpos] using this
      have qw : Dr z=D z:=by
        have qh : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall,dist_zero_right] using qf
        simpa [Dr] using wK (D:=D) (r:=r) (z:=z) qh
      have : (log 2)*(D z:ℝ) ≤ (log (r * ‖z‖⁻¹))*(D z:ℝ) :=
        mul_le_mul_of_nonneg_right qn (by exact_mod_cast qg)
      simpa [qw,mul_assoc,mul_left_comm,mul_comm] using this
    calc
      (log 2)*(S.sum fun z => (D z:ℝ))
          = S.sum (fun z => (log 2)*(D z:ℝ)):=by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => qk z hz
      _ ≤ F.sum (fun z => (Dr z:ℝ)*log (r * ‖z‖⁻¹)):=qq
  have qa : 0 ≤ (D 0:ℝ)*log r:=by
    have hD0 : 0 ≤ D 0:=qj 0
    have qu : 0 ≤ log r:=log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) qu
  have : (log 2)*(S.sum fun z => (D z:ℝ)) ≤ logCounting D r:=by
    rw [qd]
    nlinarith [qm,qa]
  simpa [WV,r,S,SR] using this
theorem vq {f:ℂ → ℂ} {ρ C:ℝ} (hf : Differentiable ℂ f) (hC : ∀ z:ℂ,log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) {R:ℝ} (hR : 1 ≤ R) : WV (divisor f (Set.univ : Set ℂ)) R ≤ (C*(1 + |2*R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|)/log 2:=by
 have hR0 : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hR
 have qa : 0 < log 2:=log_pos (by norm_num : (1:ℝ) < 2)
 have qc :
   (log 2)*WV (divisor f (Set.univ : Set ℂ)) R
    ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2*R) :=
  yW
   (D:=divisor f (Set.univ : Set ℂ))
   (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
 have qd :
   logCounting (divisor f (Set.univ : Set ℂ)) (2*R)
    ≤ C*(1 + |2*R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have qe : 0 < 2*R:=by nlinarith [hR0]
  simpa using wm (f:=f) (ρ := ρ) (C:=C) hf hC
   (R:=2*R) qe
 have qf :
   (log 2)*WV (divisor f (Set.univ : Set ℂ)) R
    ≤ C*(1 + |2*R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
  qc.trans qd
 have qb :
   WV (divisor f (Set.univ : Set ℂ)) R*log 2
    ≤ C*(1 + |2*R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  simpa [mul_assoc,mul_left_comm,mul_comm] using qf
 exact (le_div_iff₀ qa).2 qb
end Function.locallyFinsuppWithin
end
end
section
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f:ℂ → E} (hf : Differentiable ℂ f) :
  0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
 MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
end
section
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
lemma VY {x:ℝ} (hx : 1 ≤ x) : (2:ℝ)^(⌊Real.logb 2 x⌋₊ : ℝ) ≤ x:=by
 have hx0 : 0 < x:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hx
 have qa : 0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (b:=(2:ℝ)) (by norm_num : (1:ℝ) < 2) hx
 have qb : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x:=by
  simpa using (Nat.floor_le qa)
 exact (Real.le_logb_iff_rpow_le (b:=(2:ℝ))
  (x:=(⌊Real.logb 2 x⌋₊ : ℝ)) (y:=x)
  (by norm_num : (1:ℝ) < 2) hx0).1 qb
lemma Yi {x:ℝ} (hx : 1 ≤ x) : x < (2:ℝ)^((⌊Real.logb 2 x⌋₊ : ℝ)+1):=by
 have hx0 : 0 < x:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hx
 have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ)+1:=by
  simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
 exact (Real.logb_lt_iff_lt_rpow (b:=(2:ℝ)) (x:=x)
  (y:=(⌊Real.logb 2 x⌋₊ : ℝ)+1)
  (by norm_num : (1:ℝ) < 2) hx0).1 hlt
lemma VP {r0 x:ℝ} {k:ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x) (hk : ⌊Real.logb 2 (x/r0)⌋₊ = k) : r0*(2:ℝ)^(k:ℝ) ≤ x:=by
 have qa : r0 ≠ 0:=ne_of_gt hr0
 have hx1 : (1:ℝ) ≤ x/r0:=by
  have : r0/r0 ≤ x/r0:=div_le_div_of_nonneg_right hx hr0.le
  simpa [qa] using this
 have hle : (2:ℝ)^(k:ℝ) ≤ x/r0:=by
  have:=Real.VY (x:=x/r0) hx1
  simpa [hk] using this
 have:=mul_le_mul_of_nonneg_left hle hr0.le
 have qb : r0*(x/r0)=x:=by
  field_simp [qa]
 simpa [mul_assoc,qb] using this
lemma VL {r0 x:ℝ} {k:ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x) (hk : ⌊Real.logb 2 (x/r0)⌋₊ = k) : x ≤ r0*(2:ℝ)^((k:ℝ)+1):=by
 have qa : r0 ≠ 0:=ne_of_gt hr0
 have hx1 : (1:ℝ) ≤ x/r0:=by
  have : r0/r0 ≤ x/r0:=div_le_div_of_nonneg_right hx hr0.le
  simpa [qa] using this
 have hlt : x/r0 < (2:ℝ)^((k:ℝ)+1):=by
  have:=Real.Yi (x:=x/r0) hx1
  simpa [hk] using this
 have:=mul_lt_mul_of_pos_left hlt hr0
 have qb : r0*(x/r0)=x:=by
  field_simp [qa]
 exact le_of_lt (by simpa [mul_assoc,qb] using this)
lemma Wb (A:ℝ) : ∃ k0:ℕ,∀ n ≥ k0,A ≤ (2:ℝ)^n:=by
 have qa : Tendsto (fun n:ℕ => (2:ℝ)^n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (r:=(2:ℝ)) (by norm_num : (1:ℝ) < 2)
 exact eventually_atTop.1 ((tendsto_atTop.1 qa) A)
lemma yR {r0:ℝ} {k0 kk:ℕ} (hr0 : 0 < r0) (hk0 : ∀ n ≥ k0,(1/r0:ℝ) ≤ (2:ℝ)^n) (hkk : k0 ≤ kk+1) : (1:ℝ) ≤ r0*(2:ℝ)^((kk:ℝ)+1):=by
  have qc : r0 ≠ 0:=ne_of_gt hr0
  have qb : (1/r0:ℝ) ≤ (2:ℝ)^(kk+1):=hk0 (kk+1) hkk
  have qa : (1/r0:ℝ) ≤ (2:ℝ)^((kk:ℝ)+1):=by
    have qd : (2:ℝ)^((kk:ℝ)+1)=(2:ℝ)^(kk+1):=by
      calc
        (2:ℝ)^((kk:ℝ)+1)=(2:ℝ)^((kk+1:ℕ):ℝ):=by
          simp [Nat.cast_add,Nat.cast_one]
        _ = (2:ℝ)^(kk+1):=by
          simpa using (Real.rpow_natCast (2:ℝ) (kk+1))
    simpa [qd] using qb
  have : (r0*(1/r0):ℝ) ≤ r0*(2:ℝ)^((kk:ℝ)+1) :=
    mul_le_mul_of_nonneg_left qa hr0.le
  simpa [one_div,qc,mul_assoc] using this
lemma vr {r0 ρ : ℝ} (k:ℕ) (hr0 : 0 < r0) (hρ : 0 ≤ ρ) : (1 + |2*(r0*(2:ℝ)^((k:ℝ)+1))|) ^ ρ ≤ (1+4*r0) ^ ρ * ((2:ℝ) ^ ρ)^k:=by
  let Rk : ℝ:=r0*(2:ℝ)^((k:ℝ)+1)
  have qf : |2*Rk| = 4*r0*(2:ℝ)^(k:ℝ):=by
    have qc : 0 ≤ (2:ℝ)*Rk:=by
      have : 0 ≤ Rk:=by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have qg : (2:ℝ)*Rk=4*r0*(2:ℝ)^(k:ℝ):=by
      dsimp [Rk]
      calc
        (2:ℝ)*(r0*(2:ℝ)^((k:ℝ)+1))
            = (2*r0)*(2:ℝ)^((k:ℝ)+1):=by ring
        _ = (2*r0)*((2:ℝ)^(k:ℝ)*(2:ℝ)^(1:ℝ)):=by
              simp [Real.rpow_add,mul_assoc]
        _ = (2*r0)*((2:ℝ)^(k:ℝ)*2):=by simp [Real.rpow_one]
        _ = 4*r0*(2:ℝ)^(k:ℝ):=by ring
    calc
      |2*Rk| = 2*Rk:=abs_of_nonneg qc
      _ = 4*r0*(2:ℝ)^(k:ℝ):=qg
  have qe :
      (1 + |2*Rk|) ≤ (1+4*r0)*(2:ℝ)^(k:ℝ):=by
    have h1 : (1:ℝ) ≤ (2:ℝ)^(k:ℝ):=by
      have : (1:ℝ) ≤ (2:ℝ)^(k:ℕ):=by
        simpa using (one_le_pow₀ (by norm_num : (1:ℝ) ≤ (2:ℝ)))
      simpa [Real.rpow_natCast] using this
    have qh :
        1 + |2*Rk| ≤ (2:ℝ)^(k:ℝ)+(4*r0)*(2:ℝ)^(k:ℝ):=by
      rw [qf]
      simpa [add_assoc,add_left_comm,add_comm,mul_assoc,mul_left_comm,mul_comm] using
        (add_le_add_right h1 ((4*r0)*(2:ℝ)^(k:ℝ)))
    have qi :
        (2:ℝ)^(k:ℝ)+(4*r0)*(2:ℝ)^(k:ℝ)
          = (1+4*r0)*(2:ℝ)^(k:ℝ):=by
      ring
    exact qh.trans (le_of_eq qi)
  have qa : 0 ≤ (1 + |2*Rk|):=by linarith [abs_nonneg (2*Rk)]
  have :
      (1 + |2*Rk|) ^ ρ ≤ ((1+4*r0)*(2:ℝ)^(k:ℝ)) ^ ρ :=
    Real.rpow_le_rpow qa qe hρ
  have qd :
      ((1+4*r0)*(2:ℝ)^(k:ℝ)) ^ ρ
        = (1+4*r0) ^ ρ * ((2:ℝ)^(k:ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1+4*r0):=by nlinarith [hr0.le]
    have h2 : 0 ≤ (2:ℝ)^(k:ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have qj : ((2:ℝ)^(k:ℝ)) ^ ρ = ((2:ℝ) ^ ρ)^k:=by
    have qb : (0:ℝ) ≤ 2:=by norm_num
    calc
      ((2:ℝ)^(k:ℝ)) ^ ρ = (2:ℝ)^((k:ℝ) * ρ):=by
        simp [Real.rpow_mul]
      _ = ((2:ℝ) ^ ρ)^(k:ℝ):=by
        simpa [mul_comm] using
          (Real.rpow_mul (x:=(2:ℝ)) (y := ρ) (z:=(k:ℝ)) qb)
      _ = ((2:ℝ) ^ ρ)^k:=by
        simp [Real.rpow_natCast]
  calc
    (1 + |2*(r0*(2:ℝ)^((k:ℝ)+1))|) ^ ρ
        = (1 + |2*Rk|) ^ ρ := by rfl
    _ ≤ ((1+4*r0)*(2:ℝ)^(k:ℝ)) ^ ρ := this
    _ = (1+4*r0) ^ ρ * ((2:ℝ)^(k:ℝ)) ^ ρ := qd
    _ = (1+4*r0) ^ ρ * ((2:ℝ) ^ ρ)^k:=by
      simpa [mul_assoc] using congrArg (fun t => (1+4*r0) ^ ρ * t) qj
lemma vm {α : Type*} [Fintype α] {a : α → ℝ} {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (qa : ∀ x,0 ≤ a x) (qb : ∀ x,R ≤ a x) : (∑' x : α,(a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ)*(R⁻¹ ^ τ):=by
 have qc :
   (∑ x : α,(a x)⁻¹ ^ τ) ≤ ∑ _x : α,R⁻¹ ^ τ := by
  refine Finset.sum_le_sum ?_
  intro x _hx
  have qd : (a x)⁻¹ ≤ R⁻¹ := by
   simpa using (inv_anti₀ hR (qb x))
  exact Real.rpow_le_rpow (inv_nonneg.2 (qa x)) qd hτ.le
 simpa [tsum_fintype,Finset.sum_const,nsmul_eq_mul,mul_comm] using qc
lemma Vp (r0 τ : ℝ) (k:ℕ) (hr0 : 0 ≤ r0) : (r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ = (r0⁻¹ : ℝ) ^ τ * ((2:ℝ)^(-τ))^k:=by
  have qa : 0 ≤ (2:ℝ)^(k:ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
  calc
    (r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ =
        (r0*(2:ℝ)^(k:ℝ))^(-τ):=by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0*(2:ℝ)^(k:ℝ)) τ).symm
    _ = r0^(-τ)*(((2:ℝ)^(k:ℝ))^(-τ)):=by
      simpa using (Real.mul_rpow hr0 qa (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2:ℝ)^(-τ))^k:=by
      have qc : r0^(-τ)=(r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2:ℝ)^(k:ℝ))^(-τ)=((2:ℝ)^(-τ))^k:=by
        have qb : (0:ℝ) ≤ (2:ℝ):=by norm_num
        calc
          ((2:ℝ)^(k:ℝ))^(-τ)=(2:ℝ)^((k:ℝ)*(-τ)):=by
            exact (Real.rpow_mul (x:=(2:ℝ)) (y:=(k:ℝ)) (z := -τ)
              qb).symm
          _ = (2:ℝ)^((-τ)*(k:ℝ)):=by ring_nf
          _ = ((2:ℝ)^(-τ))^(k:ℝ):=by
            exact Real.rpow_mul (x:=(2:ℝ)) (y := -τ) (z:=(k:ℝ)) qb
          _ = ((2:ℝ)^(-τ))^k:=by
            simp [Real.rpow_natCast]
      calc
        r0^(-τ)*(((2:ℝ)^(k:ℝ))^(-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2:ℝ)^(k:ℝ))^(-τ)):=by
              rw [qc]
        _ = (r0⁻¹ : ℝ) ^ τ * ((2:ℝ)^(-τ))^k:=by
              rw [h2']
lemma VG (ρ τ : ℝ) : (2:ℝ)^(ρ - τ)=(2:ℝ) ^ ρ * (2:ℝ)^(-τ):=by
  have qa : (0:ℝ) < (2:ℝ):=by norm_num
  calc
    (2:ℝ)^(ρ - τ)=(2:ℝ)^(ρ + (-τ)):=by ring_nf
    _ = (2:ℝ) ^ ρ * (2:ℝ)^(-τ):=by
      simp [Real.rpow_add qa]
lemma YK (ρ τ : ℝ) (k:ℕ) : ((2:ℝ)^(ρ - τ))^k=((2:ℝ) ^ ρ)^k*(((2:ℝ)^(-τ))^k):=by
 simp [VG,mul_pow]
lemma Y9 (C L M r0 ρ τ : ℝ) (k:ℕ) (hr0 : 0 ≤ r0) : ((C/L)*(M*((2:ℝ) ^ ρ)^k))*((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)=(((C/L)*M)*(r0⁻¹ : ℝ) ^ τ)*((2:ℝ)^(ρ - τ))^k:=by
 have qa :
   (r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ =
    (r0⁻¹ : ℝ) ^ τ * (((2:ℝ)^(-τ))^k) :=
  Vp r0 τ k hr0
 rw [qa,YK]
 ac_rfl
lemma YN (C L r0 τ : ℝ) (k:ℕ) (hr0 : 0 ≤ r0) : (C/L)*((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ) ≤ (((C/L)+1)*(r0⁻¹ : ℝ) ^ τ)*((2:ℝ)^(-τ))^k:=by
 rw [Vp r0 τ k hr0]
 have qc : C/L ≤ C/L+1:=by linarith
 have qa : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
  Real.rpow_nonneg (inv_nonneg.2 hr0) _
 have qd :
   (C/L)*((r0⁻¹ : ℝ) ^ τ)
    ≤ ((C/L)+1)*((r0⁻¹ : ℝ) ^ τ) :=
  mul_le_mul_of_nonneg_right qc qa
 have qb : 0 ≤ ((2:ℝ)^(-τ))^k :=
  pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)) _
 have:=mul_le_mul_of_nonneg_right qd qb
 simpa [mul_assoc,mul_left_comm,mul_comm] using this
lemma vF {C L M X T Ctrail r0 ρ τ : ℝ} {k:ℕ} (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0) (hX : X ≤ M*((2:ℝ) ^ ρ)^k) (hT : T ≤ ((C*X+Ctrail)/L)*((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)) : T ≤ (((C/L)*M)*(r0⁻¹ : ℝ) ^ τ)*((2:ℝ)^(ρ - τ))^k+(((Ctrail/L)+1)*(r0⁻¹ : ℝ) ^ τ)*((2:ℝ)^(-τ))^k:=by
 have qf : C*X ≤ C*(M*((2:ℝ) ^ ρ)^k) :=
  mul_le_mul_of_nonneg_left hX hC
 have qg : C*X+Ctrail ≤ C*(M*((2:ℝ) ^ ρ)^k)+Ctrail :=
  add_le_add qf le_rfl
 have qh :
   (C*X+Ctrail)/L ≤ (C*(M*((2:ℝ) ^ ρ)^k)+Ctrail)/L :=
  div_le_div_of_nonneg_right qg hL.le
 have qb : 0 ≤ (2:ℝ)^(k:ℝ) :=
  le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (k:ℝ))
 have qc : 0 ≤ r0*(2:ℝ)^(k:ℝ) :=
  mul_nonneg hr0 qb
 have qa : 0 ≤ ((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ) :=
  Real.rpow_nonneg (inv_nonneg.2 qc) τ
 have qe :=
  mul_le_mul_of_nonneg_right qh qa
 have qd :
   ((C*(M*((2:ℝ) ^ ρ)^k)+Ctrail)/L) *
     ((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)
    =
    ((C/L)*(M*((2:ℝ) ^ ρ)^k)) *
      ((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)
     + ((Ctrail/L)*((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)):=by
  let Y : ℝ:=(r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ
  have :
    ((C*(M*((2:ℝ) ^ ρ)^k)+Ctrail)/L)*Y
     = ((C/L)*(M*((2:ℝ) ^ ρ)^k))*Y
      + ((Ctrail/L)*Y):=by
   ring
  simpa [Y]
 have qi :
   T ≤ ((C/L)*(M*((2:ℝ) ^ ρ)^k)) *
      ((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)
     + ((Ctrail/L)*((r0*(2:ℝ)^(k:ℝ))⁻¹ ^ τ)) :=
  hT.trans (qe.trans_eq qd)
 have hA:=le_of_eq (Y9 C L M r0 ρ τ k hr0)
 have hB:=YN Ctrail L r0 τ k hr0
 exact qi.trans (by
  simpa [mul_assoc,mul_left_comm,mul_comm] using add_le_add hA hB)
lemma VN (A B q qσ : ℝ) (k k0:ℕ) : A*q^(k+k0)+B*qσ ^ (k+k0)=(A*q^k0)*q^k+(B*qσ ^ k0)*qσ ^ k:=by
 rw [pow_add,pow_add]
 ac_rfl
end Real
end
end
end
section
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
noncomputable def VS (f:ℂ → ℂ) (R:ℝ):ℝ :=
 Function.locallyFinsuppWithin.WV (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
lemma wF {f:ℂ → ℂ} {ρ C:ℝ} (hf : Differentiable ℂ f) (hC : ∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) {R:ℝ} (hR : 1 ≤ R) : VS f R ≤ (C*(1 + |2*R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)/Real.log 2:=by
 simpa [VS] using
  (Function.locallyFinsuppWithin.vq
   (f:=f) (ρ := ρ) (C:=C) hf hC hR)
lemma vt {f:ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) : ∃ r0:ℝ,0 < r0 ∧ ∀ p : Wz f (Set.univ : Set ℂ),r0 ≤ ‖Wc p‖ := by
  classical
  set U : Set ℂ:=(Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ:=MeromorphicOn.divisor f U
  have qa : 0 ≤ D:=by
    simpa [D,U] using (Differentiable.divisor_nonneg (f:=f) hf)
  have qm : ∀ p : Wz f U,f (Wc p)=0:=by
    intro p
    set z : ℂ:=Wc p
    have qd : meromorphicOrderAt f z ≠ ⊤ := by
      have qe : AnalyticAt ℂ f z:=hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        ve (f:=f) (hf:=hf) hnot (z:=z)
      intro htop
      have hm : meromorphicOrderAt f z=(analyticOrderAt f z).map (↑) :=
        qe.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ):=by
            simp [h]
          exact this (by simpa [hm] using htop)
    have qt : MeromorphicOn f U:=by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have qu : MeromorphicOn.divisor f U z=(meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f:=f) (U:=U) (z:=z) qt (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0:=by
      have qn : z ∈ (MeromorphicOn.divisor f U).support:=by
        simp [z]
      simpa [Function.mem_support] using qn
    have qo : (0:ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have qv : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z:=by
          simpa [D,U,z] using qa z
        simpa [qu] using this
      have qw : (meromorphicOrderAt f z).untop₀ ≠ 0:=by
        simpa [qu] using hDz
      exact lt_of_le_of_ne qv (by simpa [eq_comm] using qw)
    have qx : (0 : WithTop ℤ) < meromorphicOrderAt f z:=by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 qo
      simpa [WithTop.coe_untop₀_of_ne_top qd] using this
    have qf : Tendsto f (𝓝[≠] z) (𝓝 (0:ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f:=f) (x:=z) qx
    have qg : ContinuousAt f z:=(hf z).continuousAt
    have qh : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (qg.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique qh qf
  by_cases h0 : f 0=0
  · have hD0 : D 0 ≠ 0:=by
      have qi : MeromorphicAt f (0:ℂ):=(hf.analyticAt 0).meromorphicAt
      have qc : meromorphicOrderAt f (0:ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0:ℂ) ≠ ⊤ :=
          ve (f:=f) (hf:=hf) hnot (z:=0)
        intro htop
        have hm : meromorphicOrderAt f (0:ℂ)=(analyticOrderAt f (0:ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0:ℂ) with
        | top => exact hA0 h
        | coe n =>
            have : (analyticOrderAt f (0:ℂ)).map (↑) ≠ (⊤ : WithTop ℤ):=by
              simp [h]
            exact this (by simpa [hm] using htop)
      have qf : Tendsto f (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)):=by
        have qj : ContinuousAt f (0:ℂ):=(hf 0).continuousAt
        have : Tendsto f (𝓝 (0:ℂ)) (𝓝 (0:ℂ)):=by simpa [h0] using qj.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
      have qp : (0 : WithTop ℤ) < meromorphicOrderAt f (0:ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos qi).1 qf
      have qk : (0:ℤ) < (meromorphicOrderAt f (0:ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0:ℂ)).untop₀ : WithTop ℤ):=by
          simpa [WithTop.coe_untop₀_of_ne_top qc] using qp
        simpa using (WithTop.coe_lt_coe.1 this)
      have qq : D 0=(meromorphicOrderAt f (0:ℂ)).untop₀ := by
        have qt : MeromorphicOn f U:=by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D,U] using
          (MeromorphicOn.divisor_apply (f:=f) (U:=U) (z:=(0:ℂ))
            qt (by aesop))
      exact by
        have : (meromorphicOrderAt f (0:ℂ)).untop₀ ≠ 0:=ne_of_gt qk
        simpa [qq] using this
    have qr : (0:ℂ) ∈ D.support:=by
      simp [Function.mem_support,hD0]
    have qs : IsDiscrete D.support:=by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete qs qr with ⟨r0,hr0pos,hr0⟩
    refine ⟨r0,hr0pos,?_⟩
    intro p
    have hp : Wc p ∈ D.support:=by
      simp [D,y4 (f:=f) (U:=U) p]
    have qb : Wc p ∉ Metric.ball (0:ℂ) r0:=by
      intro hball
      have : Wc p ∈ Metric.ball (0:ℂ) r0 ∩ D.support := ⟨hball,hp⟩
      have : Wc p ∈ ({(0:ℂ)} : Set ℂ):=by simp [hr0] at this
      have : Wc p=0:=by simp [Set.mem_singleton_iff] at this
      exact (Yd p) this
    have : r0 ≤ ‖Wc p‖ := by
      have : ¬ ‖Wc p‖ < r0:=by
        intro hlt
        exact qb (by simpa [Metric.mem_ball,dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have qj : ContinuousAt f (0:ℂ):=(hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0:ℂ),f z ≠ 0:=qj.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0,hr0pos,hr0⟩
    refine ⟨r0,hr0pos,?_⟩
    intro p
    have : ¬ ‖Wc p‖ < r0:=by
      intro hlt
      have ql : Wc p ∈ Metric.ball (0:ℂ) r0:=by
        simpa [Metric.mem_ball,dist_zero_right] using hlt
      have : f (Wc p) ≠ 0:=hr0 ql
      exact this (qm p)
    exact le_of_not_gt this
open scoped BigOperators
lemma wq {f:ℂ → ℂ} (hf : Differentiable ℂ f) {R:ℝ} (hR : 0 < R) : (Nat.card {p : Wz f (Set.univ : Set ℂ) // ‖Wc p‖ ≤ R}:ℝ) ≤ VS f R:=by
  set U : Set ℂ:=(Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ:=MeromorphicOn.divisor f U
  haveI :
      Fintype {p : Wz f U // ‖Wc p‖ ≤ R}:=by
    have : Finite {p : Wz f U // ‖Wc p‖ ≤ R}:=by
      have : Metric.closedBall (0:ℂ) R ⊆ U:=by simp [U]
      simpa using (vl (f:=f) (U:=U) (B:=R) this)
    exact Fintype.ofFinite _
  have qf : 0 ≤ D:=by
    simpa [D,U] using (Differentiable.divisor_nonneg (f:=f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0:ℂ) |R|)).toFinset
  let S : Finset ℂ:=SR.filter fun z:ℂ => z ≠ 0
  let T : Type :=
    Σ z : S,Fin (Int.toNat (D z.1))
  let φ :
      {p : Wz f U // ‖Wc p‖ ≤ R} → T:=fun p =>
    let z0 : ℂ:=Wc p.1
    have qc : z0 ∈ SR:=by
      have qg : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R:=p.2
        simpa [abs_of_pos hR] using this
      have qa : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support:=by
        have qd : z0 ∈ D.support:=by
          simp [z0,D]
        exact Function.locallyFinsuppWithin.zA
          qd qg
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0:ℂ) |R|))).2 qa
    have qj : z0 ≠ 0:=Yd p.1
    have qh : z0 ∈ S:=Finset.mem_filter.2 ⟨qc,qj⟩
    ⟨⟨z0,qh⟩,by
        simpa [z0,Wc,D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1=(φ q).1:=hσ.1
    have hz : Wc p.1=Wc q.1:=by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have qi :
      Fintype.card {p : Wz f U // ‖Wc p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have qk :
      (Fintype.card T:ℝ) =
        (S.sum fun z:ℂ => (Int.toNat (D z):ℝ)):=by
    have ql :
        Fintype.card T = ∑ z : S,Int.toNat (D z.1):=by
      have h1 :
          Fintype.card T = ∑ z : S,Fintype.card (Fin (Int.toNat (D z.1))):=by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S,Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T:ℝ) = ∑ z : S,(Int.toNat (D z.1):ℝ):=by
      exact_mod_cast ql
    have hR' :
        (Fintype.card T:ℝ)=S.attach.sum (fun z : S => (Int.toNat (D z.1):ℝ)):=by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T:ℝ)=S.attach.sum (fun z : S => (Int.toNat (D z.1):ℝ)):=hR'
      _ = S.sum (fun z:ℂ => (Int.toNat (D z):ℝ)):=by
            simpa using (Finset.sum_attach (s:=S) (f:=fun z:ℂ => (Int.toNat (D z):ℝ)))
  have qe : ∀ z ∈ S,(Int.toNat (D z):ℝ) ≤ (D z:ℝ):=by
    intro z hz
    have qb : 0 ≤ D z:=by simpa [D] using qf z
    have qm : ((Int.toNat (D z):ℕ):ℤ)=D z:=by
      simpa using (Int.toNat_of_nonneg qb)
    have qn : (Int.toNat (D z):ℝ)=(D z:ℝ):=by
      exact_mod_cast qm
    exact le_of_eq qn
  calc
    (Nat.card {p : Wz f U // ‖Wc p‖ ≤ R}:ℝ)
        = (Fintype.card {p : Wz f U // ‖Wc p‖ ≤ R}:ℝ):=by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T:ℝ):=by exact_mod_cast qi
    _ = S.sum (fun z:ℂ => (Int.toNat (D z):ℝ)):=qk
    _ ≤ S.sum (fun z:ℂ => (D z:ℝ)):=by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact qe z hz
    _ = VS f R:=by
      rfl
lemma zU {f:ℂ → ℂ} (hf : Differentiable ℂ f) {s : Set (Wz f (Set.univ : Set ℂ))} [Fintype s] {R:ℝ} (hR : 0 < R) (hs : ∀ p : s,‖Wc p.1‖ ≤ R) : (Fintype.card s:ℝ) ≤ VS f R:=by
  let Aball : Type :=
    {p : Wz f (Set.univ : Set ℂ) // ‖Wc p‖ ≤ R}
  haveI : Fintype Aball:=by
    have : Finite Aball:=by
      have : Metric.closedBall (0:ℂ) R ⊆ (Set.univ : Set ℂ):=by simp
      simpa [Aball] using
        (vl (f:=f) (U:=(Set.univ : Set ℂ))
          (B:=R) this)
    exact Fintype.ofFinite _
  have qc : Function.Injective (fun p : s => (⟨p.1,hs p⟩ : Aball)):=by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have qa : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ qc
  have qb : (Nat.card Aball:ℝ) ≤ VS f R:=by
    simpa [Aball] using wq (f:=f) hf hR
  calc
    (Fintype.card s:ℝ) ≤ (Fintype.card Aball:ℝ):=by exact_mod_cast qa
    _ = (Nat.card Aball:ℝ):=by simp [Nat.card_eq_fintype_card]
    _ ≤ VS f R:=qb
lemma y3 {f:ℂ → ℂ} {r0:ℝ} (qa : 0 < r0) (hr0 : ∀ p : Wz f (Set.univ : Set ℂ),r0 ≤ ‖Wc p‖) {k:ℕ} {p : Wz f (Set.univ : Set ℂ)} (hp : ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊ = k) : ‖Wc p‖ ≤ r0*(2:ℝ)^((k:ℝ)+1):=by
 exact Real.VL (r0:=r0) (x := ‖Wc p‖)
  qa (hr0 p) hp
lemma y1 {f:ℂ → ℂ} {r0:ℝ} (qa : 0 < r0) (hr0 : ∀ p : Wz f (Set.univ : Set ℂ),r0 ≤ ‖Wc p‖) {k:ℕ} {p : Wz f (Set.univ : Set ℂ)} (hp : ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊ = k) : r0*(2:ℝ)^(k:ℝ) ≤ ‖Wc p‖ := by
 exact Real.VP (r0:=r0) (x := ‖Wc p‖)
  qa (hr0 p) hp
lemma wi {f:ℂ → ℂ} {r0:ℝ} (qa : 0 < r0) (hr0 : ∀ p : Wz f (Set.univ : Set ℂ),r0 ≤ ‖Wc p‖) (k:ℕ) : ({p : Wz f (Set.univ : Set ℂ) | ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊ = k} : Set _).Finite:=by
 have qb :
   {p : Wz f (Set.univ : Set ℂ) |
    ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊ = k} ⊆
    {p : Wz f (Set.univ : Set ℂ) |
     ‖Wc p‖ ≤ r0*(2:ℝ)^((k:ℝ)+1)}:=by
  intro p hp
  exact y3 qa hr0 hp
 have qc :
   ({p : Wz f (Set.univ : Set ℂ) |
    ‖Wc p‖ ≤ r0*(2:ℝ)^((k:ℝ)+1)} : Set _).Finite:=by
  have :
    Metric.closedBall (0:ℂ) (r0*(2:ℝ)^((k:ℝ)+1)) ⊆
     (Set.univ : Set ℂ):=by
   simp
  simpa using
   (ZB (f:=f) (U:=(Set.univ : Set ℂ))
    (B:=r0*(2:ℝ)^((k:ℝ)+1)) this)
 exact qc.subset qb
lemma za
  {f:ℂ → ℂ} {ρ τ r0 Cgrow:ℝ}
  (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
  (qd : 0 < Cgrow)
  (qm : ∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ Cgrow*(1 + ‖z‖) ^ ρ)
  (qn : 0 < r0)
  (hr0 : ∀ p : Wz f (Set.univ : Set ℂ),
   r0 ≤ ‖Wc p‖)
  (k:ℕ) (qf : 1 ≤ r0*(2:ℝ)^((k:ℝ)+1)) :
  let qp : Wz f (Set.univ : Set ℂ) → ℕ :=
   fun p => ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊
  let S : Set (Wz f (Set.univ : Set ℂ)):={p | qp p=k}
  let Ctrail:ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  let A : ℝ:=((Cgrow/Real.log 2)*(1+4*r0) ^ ρ)*(r0⁻¹) ^ τ
  let B : ℝ:=((Ctrail/Real.log 2)+1)*(r0⁻¹) ^ τ
  let q : ℝ:=(2:ℝ)^(ρ - τ)
  let qσ : ℝ:=(2:ℝ)^(-τ)
  (∑' p : S,‖Wc p.1‖⁻¹ ^ τ) ≤ A*q^k+B*qσ ^ k:=by
 classical
 intro qp S Ctrail A B q qσ
 let rk : ℝ:=r0*(2:ℝ)^(k:ℝ)
 let Rk : ℝ:=r0*(2:ℝ)^((k:ℝ)+1)
 have qk : 0 < rk:=mul_pos qn (Real.rpow_pos_of_pos (by norm_num) _)
 have qq : 0 ≤ rk:=le_of_lt qk
 haveI : Finite S:=by
  simpa [S,qp] using (wi
   (f:=f) qn hr0 k).to_subtype
 haveI : Fintype S:=Fintype.ofFinite S
 have qg : ∀ p : S,‖Wc p.1‖ ≤ Rk:=by
  intro p
  have hk' : qp p.1=k:=p.2
  simpa [Rk,qp] using
   y3 (f:=f) qn hr0 hk'
 have qh : ∀ p : S,rk ≤ ‖Wc p.1‖ := by
  intro p
  have hk' : qp p.1=k:=p.2
  simpa [rk,qp] using
   y1 (f:=f) qn hr0 hk'
 have qi :
   (∑' p : S,‖Wc p.1‖⁻¹ ^ τ)
    ≤ (Fintype.card S:ℝ)*(rk⁻¹ ^ τ):=by
  exact Real.vm
   (a:=fun p : S => ‖Wc p.1‖)
   qk hτpos (fun _ => norm_nonneg _) qh
 have qa :
   VS f Rk
    ≤ (Cgrow*(1 + |2*Rk|) ^ ρ + Ctrail)/(Real.log 2):=by
  simpa [Ctrail,Rk] using
   (wF (f:=f) (ρ := ρ) (C:=Cgrow) hf qm
    (R:=Rk) qf)
 have qc :
   (Fintype.card S:ℝ) ≤ VS f Rk:=by
  have ql : 0 < Rk:=lt_of_lt_of_le (by norm_num) qf
  exact zU (f:=f) hf ql qg
 have qo :
   (∑' p : S,‖Wc p.1‖⁻¹ ^ τ)
    ≤ ((Cgrow*(1 + |2*Rk|) ^ ρ + Ctrail)/(Real.log 2))*(rk⁻¹ ^ τ):=by
  have qb :
    (Fintype.card S:ℝ) ≤
     (Cgrow*(1 + |2*Rk|) ^ ρ + Ctrail)/(Real.log 2) :=
   le_trans qc qa
  exact le_trans qi <|
   mul_le_mul_of_nonneg_right qb (Real.rpow_nonneg (inv_nonneg.2 qq) τ)
 have qe :
   (1 + |2*Rk|) ^ ρ ≤ (1+4*r0) ^ ρ * ((2:ℝ) ^ ρ)^k:=by
  simpa [Rk] using
   Real.vr (r0:=r0) (ρ := ρ) k qn hρ
 have qj : 0 < Real.log 2:=Real.log_pos (by norm_num : (1:ℝ) < 2)
 simpa [A,B,q,qσ,rk,Ctrail,mul_assoc,mul_left_comm,mul_comm] using
  Real.vF
   (C:=Cgrow) (L:=Real.log 2) (M:=(1+4*r0) ^ ρ)
   (X:=(1 + |2*Rk|) ^ ρ)
   (T := ∑' p : S,‖Wc p.1‖⁻¹ ^ τ)
   (Ctrail:=Ctrail) (r0:=r0) (ρ := ρ) (τ := τ) (k:=k)
   qj qd.le qn.le qe
   (by simpa [rk] using qo)
theorem zR {f:ℂ → ℂ} {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (qg : ∃ C > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ τ):=by
  rcases qg with ⟨Cgrow,hCgrow_pos,hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases vt (f:=f) hf hnot with ⟨r0,hr0pos,hr0⟩
  have qk : (r0:ℝ) ≠ 0:=ne_of_gt hr0pos
  let qn : Wz f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖Wc p‖ / r0)⌋₊
  let S:ℕ → Set (Wz f (Set.univ : Set ℂ)) :=
    fun k => {p | qn p=k}
  have hS : ∀ p : Wz f (Set.univ : Set ℂ),∃! k:ℕ,p ∈ S k:=by
    intro p
    refine ⟨qn p,?_,?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have qh : 0 ≤ fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have qc : ∀ k:ℕ,Summable fun p : S k => ‖Wc p.1‖⁻¹ ^ τ := by
    intro k
    haveI : Finite (S k):=by
      simpa [S,qn] using (wi
        (f:=f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have qb :
      Summable fun k:ℕ => ∑' p : S k,‖Wc p.1‖⁻¹ ^ τ := by
    let q : ℝ:=(2:ℝ)^(ρ - τ)
    let qσ : ℝ:=(2:ℝ)^(-τ)
    have qe : 0 ≤ q:=le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
    have qf : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x:=(2:ℝ)) (by norm_num : (1:ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x:=(2:ℝ)) (by norm_num : (1:ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have qi : Summable (fun k:ℕ => q^k) :=
      summable_geometric_of_lt_one qe qf
    have hgeom_qσ : Summable (fun k:ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail:ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ:=((Cgrow/Real.log 2)*(1+4*r0) ^ ρ)*(r0⁻¹) ^ τ
    let B : ℝ:=((Ctrail/Real.log 2)+1)*(r0⁻¹) ^ τ
    rcases Real.Wb (1/r0) with ⟨k0,hk0⟩
    let A0 : ℝ:=A*q^k0
    let B0 : ℝ:=B*qσ ^ k0
    have qj : Summable (fun k:ℕ => A0*q^k+B0*qσ ^ k) :=
      (qi.mul_left A0).add (hgeom_qσ.mul_left B0)
    have qa :
        Summable fun k:ℕ => ∑' p : S (k+k0),‖Wc p.1‖⁻¹ ^ τ := by
      refine qj.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k+k0),0 ≤ ‖Wc p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ:=k+k0
          let Rk : ℝ:=r0*(2:ℝ)^((kk:ℝ)+1)
          have qd : (1:ℝ) ≤ Rk:=by
            have hkk : k0 ≤ kk+1:=by
              simp [kk,Nat.add_assoc,Nat.add_comm]
            simpa [Rk] using
              Real.yR hr0pos hk0 hkk
          have ql :
              (∑' p : S kk,‖Wc p.1‖⁻¹ ^ τ) ≤ A*q^kk+B*qσ ^ kk:=by
            simpa [S,qn,Ctrail,A,B,q,qσ] using
              za
                (f:=f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk qd
          have : A*q^kk+B*qσ ^ kk=A0*q^k+B0*qσ ^ k:=by
            simpa [A0,B0,kk] using Real.VN A B q qσ k k0
          simpa [kk] using (ql.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 qa
  have qm :=
    (summable_partition (f:=fun p : Wz f (Set.univ : Set ℂ) =>
        ‖Wc p‖⁻¹ ^ τ) qh (s:=S) hS)
  exact (qm.2 ⟨qc,qb⟩)
theorem zX {f:ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (qa : ∃ C > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (Nat.floor ρ + 1)):=by
 have hτ : ρ < (Nat.floor ρ + 1:ℝ):=by
  simpa [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
 have hs :=
  zR (f:=f) (ρ := ρ)
   (τ := (Nat.floor ρ + 1:ℝ)) hρ hτ hf hnot qa
 exact hs.congr fun p => by
  have qb : ((Nat.floor ρ : ℝ)+1)=((Nat.floor ρ + 1:ℕ):ℝ):=by
   norm_num
  rw [qb,Real.rpow_natCast]
end Complex.Hadamard
end
end
end
section
section
namespace Complex
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem yB {f:ℂ → F} {r C:ℝ} {z:ℂ} (hd : Differentiable ℂ f) (hrpos : 0 < r) (hz : z ∈ Metric.ball (0:ℂ) r) (qa : ∀ u:ℂ,‖u‖ = r → ‖f u‖ ≤ C) : ‖f z‖ ≤ C:=by
 let U : Set ℂ:=Metric.ball (0:ℂ) r
 have qc : ∀ u ∈ frontier U,‖f u‖ ≤ C:=by
  intro u hu
  have hur : ‖u‖ = r:=by
   have qb : frontier (Metric.ball (0:ℂ) r)=Metric.sphere (0:ℂ) r:=by
    simpa using (frontier_ball (x:=(0:ℂ)) (r:=r) (ne_of_gt hrpos))
   have : u ∈ Metric.sphere (0:ℂ) r:=by simpa [U,qb] using hu
   simpa [Metric.mem_sphere,dist_zero_right] using this
  exact qa u hur
 exact norm_le_of_forall_mem_frontier_norm_le (f:=f) (U:=U) Metric.isBounded_ball
  hd.diffContOnCl qc (subset_closure hz)
end Complex
end
end
section
section
namespace Complex
namespace CartanBound
open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal
private lemma VK {x:ℝ} (hx : 0 < x) (qk : x ≤ 1) : -Real.log x ≤ Real.sqrt (2/x):=by
 have hx0 : 0 ≤ x:=le_of_lt hx
 have ht : 0 ≤ -Real.log x:=by
  have : Real.log x ≤ 0:=Real.log_nonpos hx0 qk
  linarith
 have qa : ∀ {t:ℝ},0 ≤ t → t^2/2 ≤ Real.exp t:=by
  intro t ht
  let g:ℝ → ℝ:=fun u => Real.exp u - u^2/2
  have qd : ContinuousOn g (Set.Ici (0:ℝ)):=by
   have : Continuous g:=by fun_prop
   simpa using this.continuousOn
  have qe : DifferentiableOn ℝ g (interior (Set.Ici (0:ℝ))):=by
   intro u hu
   have : DifferentiableAt ℝ g u:=by fun_prop
   exact this.differentiableWithinAt
  have qb : ∀ u ∈ interior (Set.Ici (0:ℝ)),0 ≤ deriv g u:=by
   intro u hu
   have hu0 : 0 < u:=by simpa [interior_Ici] using hu
   have qg : deriv g u=Real.exp u - u:=by
    have ql : HasDerivAt Real.exp (Real.exp u) u:=Real.hasDerivAt_exp u
    have qh : HasDerivAt (fun z:ℝ => z^2) (2*u) u:=by
     simpa using! ((hasDerivAt_id u).pow 2)
    have qc : HasDerivAt (fun z:ℝ => z^2/2) u u:=by
     simpa using (qh.div_const (2:ℝ))
    have hG : HasDerivAt g (Real.exp u - u) u:=by
     simpa [g] using! ql.sub qc
    exact hG.deriv
   have qi : u ≤ Real.exp u:=by
    have h1 : u+1 ≤ Real.exp u:=Real.add_one_le_exp u
    exact (le_trans (le_add_of_nonneg_right (by norm_num)) h1)
   have : 0 ≤ Real.exp u - u:=sub_nonneg.2 qi
   simpa [qg] using this
  have qf : MonotoneOn g (Set.Ici (0:ℝ)) :=
   monotoneOn_of_deriv_nonneg (D:=Set.Ici (0:ℝ)) (hD:=convex_Ici 0)
    qd qe qb
  have hg0 : g 0=1:=by simp [g]
  have hle : g 0 ≤ g t:=qf (by simp) (by simpa [Set.mem_Ici] using ht) ht
  have : (1:ℝ) ≤ Real.exp t - t^2/2:=by simpa [g,hg0] using hle
  linarith
 have qj : (-Real.log x)^2/2 ≤ Real.exp (-Real.log x):=qa ht
 have qm : Real.exp (-Real.log x)=x⁻¹ := by simp [Real.exp_neg,Real.exp_log hx]
 have qn : (-Real.log x)^2 ≤ 2*Real.exp (-Real.log x):=by nlinarith [qj]
 have qo : (-Real.log x)^2 ≤ 2/x:=by simpa [qm,div_eq_mul_inv,mul_assoc] using qn
 have hy : 0 ≤ 2/x:=div_nonneg (by norm_num) (le_of_lt hx)
 exact (Real.le_sqrt ht hy).2 qo
lemma vS {t:ℝ} : Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|):=by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t=1:=by
        have : 1 - t=0:=by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have qb : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        VK (x := |1 - t|) qb ht
      have qc : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have qa : 0 ≤ Real.log (1 / |1 - t|):=by
        exact Real.log_nonneg ((one_le_div qb).2 ht)
      have qd : Real.posLog (1 / |1 - t|)=Real.log (1 / |1 - t|) :=
        max_eq_right qa
      calc
        Real.posLog (1 / |1 - t|)=Real.log (1 / |1 - t|):=qd
        _ = -Real.log |1 - t| := qc
        _ ≤ Real.sqrt (2 / |1 - t|):=hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have qe : Real.log (1 / |1 - t|) ≤ 0:=by
      have qb : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1:=(div_le_one qb).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have qd : Real.posLog (1 / |1 - t|)=0:=max_eq_left qe
    have qf : 0 ≤ Real.sqrt (2 / |1 - t|):=by
      exact Real.sqrt_nonneg _
    rw [qd]
    exact qf
noncomputable def φ (t:ℝ):ℝ :=
 log⁺ (1 / |1 - t|)
lemma W6 : Measurable φ := by
 unfold φ
 simpa [Real.posLog_def,Real.posLog] using
  (by fun_prop : Measurable fun t:ℝ => max 0 (Real.log (1 / |1 - t|)))
lemma Y8 {t:ℝ} (ht : t ≤ (1/2:ℝ)) : φ t ≤ Real.log 2:=by
 have qc : 0 ≤ (1 - t:ℝ):=by linarith
 have qf : (1/2:ℝ) ≤ |1 - t| := by
  have : (1/2:ℝ) ≤ (1 - t:ℝ):=by linarith
  simpa [abs_of_nonneg qc] using this
 have qe : (1 / |1 - t| : ℝ) ≤ 2:=by
  have qa : (0:ℝ) < (1/2:ℝ):=by norm_num
  have:=one_div_le_one_div_of_le qa qf
  simpa [one_div,div_eq_mul_inv] using this
 have qd : log⁺ (1 / |1 - t|) ≤ log⁺ (2:ℝ) :=
  Real.posLog_le_posLog (by positivity) qe
 have qg : (1:ℝ) ≤ |(2:ℝ)| := by
  simp
 have qb : (log⁺ (2:ℝ))=Real.log 2:=by
  simpa using (Real.posLog_eq_log qg)
 simpa [φ,qb] using qd
lemma w9 {t:ℝ} (ht : (1:ℝ) ≤ |1 - t|) : φ t=0:=by
 have qc : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
 have qb : (1 / |1 - t| : ℝ) ≤ 1:=(div_le_one qc).2 ht
 have qd : |(1 / |1 - t| : ℝ)| ≤ 1:=by
  have qa : 0 ≤ (1 / |1 - t| : ℝ):=by positivity
  simpa [abs_of_nonneg qa] using qb
 have : log⁺ (1 / |1 - t|)=0:=(Real.posLog_eq_zero_iff _).2 qd
 simpa [φ] using this
lemma ul (t:ℝ) : 0 ≤ φ t:=by
 simpa [φ] using (Real.posLog_nonneg (x:=(1 / |1 - t|)))
lemma uk (t:ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|):=by
 simpa [φ,Real.posLog] using
  vS (t:=t)
lemma v4 {A B:ℝ} (hAB : A ≤ B) {g:ℝ → ℝ} (hg : ∀ t,0 ≤ g t) (h : ∀ t ∈ Set.Icc A B,φ t ≤ g t) : (fun t:ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
 refine
  MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
  (s:=Set.uIoc A B)
   (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
 intro t ht
 have qa : t ∈ Set.Ioc A B:=by
  simpa [Set.uIoc_of_le hAB] using ht
 have qb : t ∈ Set.Icc A B := ⟨le_of_lt qa.1,qa.2⟩
 have hle : φ t ≤ g t:=h t qb
 have hφ0 : 0 ≤ φ t:=ul t
 have hg0 : 0 ≤ g t:=hg t
 simpa [Real.norm_eq_abs,abs_of_nonneg hφ0,abs_of_nonneg hg0] using hle
lemma ZO {u a:ℂ} {r:ℝ} (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) : Real.log ‖(1:ℂ) - u/a‖ ≥ -φ (r / ‖a‖):=by
  have qd : 0 < ‖a‖ := norm_pos_iff.2 ha
  have qb : ‖(1:ℂ) - u/a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1:ℂ) - u/a=(a - u)/a:=by
      field_simp [ha]
    calc
      ‖(1:ℂ) - u/a‖ = ‖(a - u)/a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have qf : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have qg : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right qf (le_of_lt qd)
  have qh : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r:=hur
    have ha0 : (‖a‖ : ℝ) ≠ 0:=qd.ne'
    have h1 : (1:ℝ) - (r / ‖a‖)=(‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div,abs_of_pos qd]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have qc : |1 - (r / ‖a‖)| ≤ ‖(1:ℂ) - u/a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [qh]
      exact qg
    rwa [qb]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖):ℝ) ≠ 0:=by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1:ℝ):=by linarith
        simpa using (div_eq_iff qd.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0:=by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have qe :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖):=by
    have:=Real.Wg (x := |1 - (r / ‖a‖)|)
    simpa [φ,one_div,inv_inv,abs_sub_comm,sub_eq_add_neg] using this
  have qa :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1:ℂ) - u/a‖ :=
    Real.log_le_log (by positivity) qc
  linarith [qa,qe]
noncomputable def K:ℝ :=
 ∫ (t:ℝ) in (1/4:ℝ)..(4:ℝ),Real.sqrt (2 / |1 - t|) ∂volume
lemma um : 0 ≤ K:=by
 have hle : (1/4:ℝ) ≤ (4:ℝ):=by norm_num
 have hnn : ∀ t ∈ Set.Icc (1/4:ℝ) (4:ℝ),0 ≤ Real.sqrt (2 / |1 - t|):=by
  intro _t _ht
  exact Real.sqrt_nonneg _
 simpa [K] using (intervalIntegral.integral_nonneg
  (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)
noncomputable def Cφ : ℝ :=
 Real.log 2+4*K+1
lemma uo : 0 < Cφ := by
 have qa : 0 < Real.log 2:=by
  simpa using Real.log_pos (by norm_num : (1:ℝ) < 2)
 have hK : 0 ≤ K:=um
 have : 0 < Real.log 2+4*K:=by nlinarith
 have : 0 < Real.log 2+4*K+1:=by linarith
 simpa [Cφ] using this
lemma ye : IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|)) volume (1/4:ℝ) (4:ℝ):=by
  let f:ℝ → ℝ:=fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0:ℝ) (3:ℝ):=by
    have qg :
        IntervalIntegrable (fun u:ℝ => u^(- (2⁻¹ : ℝ))) volume (0:ℝ) (3:ℝ):=by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=(3:ℝ))
          (r:=(- (2⁻¹ : ℝ))) (by linarith : (-1:ℝ) < - (2⁻¹ : ℝ)))
    have qd :
        IntervalIntegrable (fun u:ℝ => Real.sqrt 2*u^(- (2⁻¹ : ℝ))) volume (0:ℝ) (3:ℝ) :=
      qg.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u:ℝ => Real.sqrt 2*u^(- (2⁻¹ : ℝ))) (Set.uIoc (0:ℝ) (3:ℝ)):=by
      intro u hu
      have hu' : u ∈ Set.Ioc (0:ℝ) (3:ℝ):=by
        simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u:=hu'.1
      have qh : 0 ≤ u:=le_of_lt hu0
      have qi : |u| = u:=abs_of_nonneg qh
      have : f u=Real.sqrt (2/u):=by simp [f,qi]
      calc
        f u=Real.sqrt (2/u):=this
        _ = Real.sqrt 2/Real.sqrt u:=by simp
        _ = Real.sqrt 2*(Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2*(u^(2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2*u^(- (2⁻¹ : ℝ)):=by
              have h : (u^(2⁻¹ : ℝ))⁻¹ = u^(- (2⁻¹ : ℝ)):=by
                simpa using (Real.rpow_neg qh (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a:=(0:ℝ)) (b:=(3:ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f:=fun u:ℝ => Real.sqrt 2*u^(- (2⁻¹ : ℝ))) (g:=f) hEq.symm)
        qd
  have qj : IntervalIntegrable f volume (0:ℝ) (3/4:ℝ) :=
    hf0.mono_set (by
      intro u hu
      have qk : Set.uIcc (0:ℝ) (3/4:ℝ) ⊆ Set.uIcc (0:ℝ) (3:ℝ):=by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0:ℝ) ≤ (3/4:ℝ):=by nlinarith
          have h1 : (3/4:ℝ) ≤ (3:ℝ):=by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0,h1⟩)
      exact qk hu)
  have qe :
      IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|)) volume (1/4:ℝ) (1:ℝ):=by
    have ql :
        IntervalIntegrable (fun t:ℝ => f (1 - t)) volume (1:ℝ) ((1:ℝ) - (3/4:ℝ)):=by
      simpa using (qj.comp_sub_left (c:=(1:ℝ)))
    have qf :
        IntervalIntegrable (fun t:ℝ => f (1 - t)) volume ((1:ℝ) - (3/4:ℝ)) (1:ℝ) :=
      ql.symm
    have qk : ((1:ℝ) - (3/4:ℝ))=(1/4:ℝ):=by norm_num
    have qa : IntervalIntegrable (fun t:ℝ => f (1 - t)) volume (1/4:ℝ) (1:ℝ):=by
      simpa [qk] using qf
    simpa [f] using qa
  have qb :
      IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|)) volume (1:ℝ) (4:ℝ):=by
    have ql :
        IntervalIntegrable (fun t:ℝ => f (t - 1)) volume (1:ℝ) ((3:ℝ)+(1:ℝ)):=by
      simpa using (hf0.comp_sub_right (c:=(1:ℝ)))
    have qk : ((3:ℝ)+(1:ℝ))=(4:ℝ):=by norm_num
    have qf : IntervalIntegrable (fun t:ℝ => f (t - 1)) volume (1:ℝ) (4:ℝ):=by
      simpa [qk] using ql
    have qc :
        Set.EqOn (fun t:ℝ => f (t - 1)) (fun t:ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1:ℝ) (4:ℝ)):=by
      intro t _ht
      simp [f,abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a:=(1:ℝ)) (b:=(4:ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f:=fun t:ℝ => f (t - 1)) (g:=fun t:ℝ => Real.sqrt (2 / |1 - t|)) qc)
        qf
  exact qe.trans qb
lemma vX {A t:ℝ} (hA : A ≤ (1/4:ℝ)) (ht : t ∈ Set.Icc A (2*A)) : φ t ≤ Real.log 2:=by
 have qa : t ≤ (1/2:ℝ):=by
  exact ht.2.trans (by nlinarith [hA])
 exact Y8 qa
lemma V4 {t:ℝ} (ht : (2:ℝ) ≤ t) : φ t=0:=by
 have qa : (1:ℝ) ≤ |1 - t| := by
  have : (1:ℝ) ≤ t - 1:=by linarith
  have : (1:ℝ) ≤ |t - 1| := by
   simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
  simpa [abs_sub_comm] using this
 exact w9 qa
lemma wJ {A:ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1/4:ℝ)) : IntervalIntegrable φ volume A (2*A):=by
  have qb : A ≤ 2*A:=by nlinarith
  have qa : IntervalIntegrable (fun _ : ℝ => (Real.log 2:ℝ)) volume A (2*A) :=
    intervalIntegrable_const
  have qc :
      AEStronglyMeasurable (fun t:ℝ => φ t) (volume.restrict (Set.uIoc A (2*A))) :=
    (W6.aestronglyMeasurable : _)
  have qd :
      (fun t:ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2*A)))]
        fun _ => ‖(Real.log 2:ℝ)‖ := by
    refine v4 (A:=A) (B:=2*A) qb
      (g:=fun _ => (Real.log 2:ℝ)) (hg:=fun _ => ?_) ?_
    · simpa using (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    · intro t ht
      exact vX hA ht
  exact IntervalIntegrable.mono_fun qa qc qd
lemma wv {A:ℝ} (hA : (2:ℝ) ≤ A) : IntervalIntegrable φ volume A (2*A):=by
 have qa : A ≤ 2*A:=by nlinarith
 have hEq : Set.EqOn (fun t:ℝ => φ t) (fun _ => (0:ℝ)) (Set.uIoc A (2*A)):=by
  intro t ht
  have qb : t ∈ Set.Ioc A (2*A):=by
   simpa [Set.uIoc_of_le qa] using ht
  exact V4 (le_trans hA (le_of_lt qb.1))
 have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume A (2*A) :=
  intervalIntegrable_const
 exact (IntervalIntegrable.congr (a:=A) (b:=(2*A))
  (μ := (volume : MeasureTheory.Measure ℝ))
  (f:=fun _ => (0:ℝ)) (g:=fun t => φ t) (by
   intro t ht
   simpa using (hEq (x:=t) ht).symm)) hz
lemma zo {A:ℝ} (qb : (1/4:ℝ) ≤ A) (qc : A ≤ (2:ℝ)) : IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|)) volume A (2*A):=by
  have qa :
      IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|))
        (volume : MeasureTheory.Measure ℝ) (1/4:ℝ) (4:ℝ) :=
    ye
  refine qa.mono_set ?_
  refine Set.uIcc_subset_uIcc ?_ ?_
  · exact (Set.mem_uIcc).2 (Or.inl ⟨qb,by nlinarith [qc]⟩)
  · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [qb],by nlinarith [qc]⟩)
lemma wo {A:ℝ} (qa : (1/4:ℝ) ≤ A) (qb : A ≤ (2:ℝ)) : IntervalIntegrable φ volume A (2*A):=by
 have qc : A ≤ 2*A:=by nlinarith [qa]
 have qd :
   IntervalIntegrable (fun t:ℝ => Real.sqrt (2 / |1 - t|)) volume A (2*A) :=
  zo qa qb
 have qe :
   AEStronglyMeasurable (fun t:ℝ => φ t) (volume.restrict (Set.uIoc A (2*A))) :=
  (W6.aestronglyMeasurable : _)
 have qf :
   (fun t:ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2*A)))]
    fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
  refine v4 (A:=A) (B:=2*A) qc
   (g:=fun t => Real.sqrt (2 / |1 - t|)) (hg:=fun _ => Real.sqrt_nonneg _) ?_
  intro t _ht
  exact uk t
 exact IntervalIntegrable.mono_fun qd qe qf
lemma Ye {A:ℝ} (hA : 0 ≤ A) : IntervalIntegrable φ volume A (2*A):=by
  by_cases hA0 : A=0
  · subst hA0
    simp
  cases le_total A (1/4:ℝ) with
  | inl hsmall =>
      exact wJ hA hsmall
  | inr hge_quarter =>
      cases le_total (2:ℝ) A with
      | inl hbig =>
          exact wv hbig
      | inr hA_le_two =>
          exact wo hge_quarter hA_le_two
lemma Y3 {a R:ℝ} (ha : 0 < a) (hR : 0 ≤ R) : IntervalIntegrable (fun r:ℝ => φ (r/a)) volume R (2*R):=by
 have ha0 : a ≠ 0:=ne_of_gt ha
 have qa : 0 ≤ R/a:=by
  exact div_nonneg hR (le_of_lt ha)
 have hφ : IntervalIntegrable φ volume (R/a) (2*(R/a)) :=
  Ye (A:=(R/a)) qa
 have:=(hφ.comp_mul_right (c:=(a⁻¹ : ℝ)))
 have qb : a*(R*(a⁻¹ * 2))=(2*R):=by
  field_simp [ha0]
 simpa [div_eq_mul_inv,ha0,qb,mul_assoc,mul_left_comm,mul_comm] using this
lemma ua : Real.log 2 ≤ Cφ := by
 dsimp [Cφ]
 have hK : 0 ≤ K:=um
 linarith [hK]
lemma Vi : (4*K+1:ℝ) ≤ Cφ := by
 dsimp [Cφ]
 have qa : 0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
 linarith [qa]
lemma Yv {A:ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1/4:ℝ)) : (∫ (t:ℝ) in A..(2*A),φ t ∂volume) ≤ Cφ * A:=by
 have qc : A ≤ 2*A:=by nlinarith
 have hφ_int : IntervalIntegrable φ volume A (2*A) :=
  wJ hA0 hA
 have qb : IntervalIntegrable (fun _ : ℝ => (Real.log 2:ℝ)) volume A (2*A) :=
  intervalIntegrable_const
 have qa :
   (∫ (t:ℝ) in A..(2*A),φ t ∂volume)
    ≤ ∫ (t:ℝ) in A..(2*A),(Real.log 2:ℝ) ∂volume:=by
  refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
   qc hφ_int qb ?_
  intro t ht
  exact vX hA ht
 have qe :
   (∫ (t:ℝ) in A..(2*A),(Real.log 2:ℝ) ∂volume)=A*Real.log 2:=by
  simp [intervalIntegral.integral_const,sub_eq_add_neg,add_assoc,two_mul]
 have qd : A*Real.log 2 ≤ Cφ * A:=by
  have:=mul_le_mul_of_nonneg_left ua hA0
  simpa [mul_assoc,mul_left_comm,mul_comm] using this
 exact le_trans (by simpa [qe] using qa) qd
lemma YB {A:ℝ} (hA : (2:ℝ) ≤ A) : (∫ (t:ℝ) in A..(2*A),φ t ∂volume) ≤ Cφ * A:=by
 have qb : A ≤ 2*A:=by nlinarith
 have hφ0 : Set.EqOn (fun t:ℝ => φ t) (fun _ => (0:ℝ)) (Set.uIcc A (2*A)):=by
  intro t ht
  have ht' : t ∈ Set.Icc A (2*A):=by
   simpa [Set.uIcc_of_le qb] using ht
  exact V4 (le_trans hA ht'.1)
 have qc : (∫ (t:ℝ) in A..(2*A),φ t ∂volume)=0:=by
  simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
 have qa : (0:ℝ) ≤ Cφ * A:=mul_nonneg (le_of_lt uo) (by linarith)
 simpa [qc] using qa
lemma zG {A:ℝ} (qc : (1/4:ℝ) ≤ A) (qd : A ≤ (2:ℝ)) : (∫ (t:ℝ) in A..(2*A),Real.sqrt (2 / |1 - t|) ∂volume) ≤ K:=by
 let s (t:ℝ) : ℝ:=Real.sqrt (2 / |1 - t|)
 have qe : A ≤ 2*A:=by nlinarith [qc]
 have qa : (2*A:ℝ) ≤ 4:=by nlinarith [qd]
 have qb : IntervalIntegrable s volume (1/4:ℝ) (4:ℝ):=by
  simpa [s] using ye
 have qf :
   (∫ (t:ℝ) in A..(2*A),s t ∂volume)
    ≤ ∫ (t:ℝ) in (1/4:ℝ)..(4:ℝ),s t ∂volume:=by
  refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
   (c:=(1/4:ℝ)) (d:=(4:ℝ)) (a:=A) (b:=(2*A))
   qc qe qa ?_ qb
  exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
 simpa [K,s] using qf
lemma y2 {A:ℝ} (hA : (1/4:ℝ) ≤ A) : K ≤ (4*K+1)*A:=by
 have qa : 1 ≤ 4*A:=by nlinarith [hA]
 have hK : 0 ≤ K:=um
 nlinarith [hK,qa]
lemma Yg {A:ℝ} (qa : (1/4:ℝ) ≤ A) (qb : A ≤ (2:ℝ)) : (∫ (t:ℝ) in A..(2*A),φ t ∂volume) ≤ Cφ * A:=by
 let s (t:ℝ) : ℝ:=Real.sqrt (2 / |1 - t|)
 have qe : A ≤ 2*A:=by nlinarith [qa]
 have hφ_int : IntervalIntegrable φ volume A (2*A) :=
  wo qa qb
 have qf : IntervalIntegrable s volume A (2*A):=by
  simpa [s] using
   zo qa qb
 have qd :
   (∫ (t:ℝ) in A..(2*A),φ t ∂volume)
    ≤ ∫ (t:ℝ) in A..(2*A),s t ∂volume:=by
  refine intervalIntegral.integral_mono_on
   (μ := (volume : MeasureTheory.Measure ℝ)) qe hφ_int qf ?_
  intro t _ht
  exact uk t
 have qc : (∫ (t:ℝ) in A..(2*A),s t ∂volume) ≤ (4*K+1)*A:=by
  have hK : (∫ (t:ℝ) in A..(2*A),s t ∂volume) ≤ K:=by
   simpa [s] using zG qa qb
  exact le_trans hK (y2 qa)
 have qg : (4*K+1:ℝ)*A ≤ Cφ * A :=
  mul_le_mul_of_nonneg_right Vi (by nlinarith [qa])
 exact le_trans qd (le_trans qc qg)
lemma VT {A:ℝ} (hA : 0 ≤ A) : (∫ (t:ℝ) in A..(2*A),φ t ∂volume) ≤ Cφ * A:=by
  by_cases hA0 : A=0
  · subst hA0
    simp [Cφ,φ,K]
  cases le_total A (1/4:ℝ) with
  | inl hsmall =>
      exact Yv hA hsmall
  | inr hge_quarter =>
      cases le_total (2:ℝ) A with
      | inl hbig =>
          exact YB hbig
      | inr hA_le_two =>
          exact Yg hge_quarter hA_le_two
open scoped BigOperators
lemma Y0 {R:ℝ} (hR : 0 < R) : (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2*R)) ≠ 0:=by
 have qa : (0:ℝ) < 2*R - R:=by nlinarith [hR]
 simp [Real.volume_Ioc,ENNReal.ofReal_eq_zero,not_le_of_gt qa]
lemma vV (bad : Finset ℝ) {R:ℝ} (hR : 0 < R) : (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2*R) \ (bad : Set ℝ)) ≠ 0:=by
 have qa : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ)=0:=by
  simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
 have qb :
   (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2*R) \ (bad : Set ℝ))
    = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2*R)):=by
  simpa [Set.sdiff_eq,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using
   (MeasureTheory.measure_sdiff_null (s:=Set.Ioc R (2*R)) (t:=(bad : Set ℝ))
    qa)
 simpa [qb] using Y0 hR
lemma ya (bad : Finset ℝ) {R:ℝ} (hR : 0 < R) : (volume.restrict (Set.Ioc R (2*R))) (Set.Ioc R (2*R) \ (bad : Set ℝ)) ≠ 0:=by
 have qa : Set.Ioc R (2*R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2*R):=by
  intro r hr
  exact hr.1
 have qb :
   (Set.Ioc R (2*R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2*R)
    = (Set.Ioc R (2*R) \ (bad : Set ℝ)):=by
  exact Set.inter_eq_left.mpr qa
 simpa [MeasureTheory.Measure.restrict_apply,measurableSet_Ioc,qb] using
  vV bad hR
lemma YY {a R:ℝ} (ha : 0 < a) (hR : 0 ≤ R) : (∫ (r:ℝ) in R..(2*R),φ (r/a) ∂volume) ≤ Cφ * R:=by
 have ha0 : a ≠ 0:=ne_of_gt ha
 have qb :
   (∫ (r:ℝ) in R..(2*R),φ (r/a) ∂volume)
    = a*(∫ (t:ℝ) in (R/a)..(2*R/a),φ t ∂volume):=by
  simp [smul_eq_mul,mul_left_comm,mul_comm,div_eq_mul_inv,ha0]
 rw [qb]
 have hA : 0 ≤ R/a:=by
  exact div_nonneg hR ha.le
 have hle : (∫ (t:ℝ) in (R/a)..(2*(R/a)),φ t ∂volume) ≤ Cφ * (R/a) :=
  VT (A:=R/a) hA
 have hEq : (2*R/a)=2*(R/a):=by ring
 have qc :
   (∫ (t:ℝ) in (R/a)..(2*R/a),φ t ∂volume) ≤ Cφ * (R/a):=by
  simpa [hEq] using hle
 have qa : 0 ≤ a:=ha.le
 have:=mul_le_mul_of_nonneg_left qc qa
 have qd : a*(Cφ * (R/a))=Cφ * R:=by
  field_simp [ha0]
 simpa [qd,mul_assoc,mul_left_comm,mul_comm] using this
lemma w3 {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ) (ha : ∀ i ∈ s,0 < a i) {R:ℝ} (hR : 0 ≤ R) : IntervalIntegrable (∑ i ∈ s,fun r:ℝ => w i * φ (r/a i)) volume R (2*R):=by
 refine IntervalIntegrable.sum (μ := volume) (a:=R) (b:=2*R)
  (s:=s) (f:=fun i : ι => fun r:ℝ => w i * φ (r/a i)) ?_
 intro i hi
 have hφi : IntervalIntegrable (fun r:ℝ => φ (r/a i)) volume R (2*R) :=
  Y3 (a:=a i) (R:=R) (ha i hi) hR
 simpa [mul_assoc] using hφi.const_mul (w i)
lemma vR {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ) (hw : ∀ i ∈ s,0 ≤ w i) (ha : ∀ i ∈ s,0 < a i) {R:ℝ} (hR : 0 ≤ R) : (∫ r in R..(2*R),(∑ i ∈ s,fun r:ℝ => w i * φ (r/a i)) r ∂volume) ≤ Cφ * (∑ i ∈ s,w i)*R:=by
  have qc : ∀ i ∈ s,IntervalIntegrable (fun r:ℝ => w i * φ (r/a i))
      volume R (2*R):=by
    intro i hi
    have hφi : IntervalIntegrable (fun r:ℝ => φ (r/a i)) volume R (2*R) :=
      Y3 (a:=a i) (R:=R) (ha i hi) hR
    simpa [mul_assoc] using hφi.const_mul (w i)
  have qa :
      (∫ r in R..(2*R),(∑ i ∈ s,fun r:ℝ => w i * φ (r/a i)) r ∂volume)
        = ∑ i ∈ s,∫ r in R..(2*R),(fun r:ℝ => w i * φ (r/a i)) r
            ∂volume:=by
    simpa using
      (intervalIntegral.integral_finsetSum (μ := volume) (a:=R) (b:=2*R)
        (s:=s) (f:=fun i : ι => fun r:ℝ => w i * φ (r/a i)) qc)
  rw [qa]
  have qb :
      (∑ i ∈ s,∫ r in R..(2*R),(fun r:ℝ => w i * φ (r/a i)) r ∂volume)
        ≤ ∑ i ∈ s,w i*(Cφ * R):=by
    refine Finset.sum_le_sum ?_
    intro i hi
    have qd :
        (∫ r in R..(2*R),φ (r/a i) ∂volume) ≤ Cφ * R :=
      YY (a:=a i) (R:=R) (ha i hi) hR
    have:=mul_le_mul_of_nonneg_left qd (hw i hi)
    simpa [mul_assoc,mul_left_comm,mul_comm] using this
  refine le_trans qb ?_
  have : (∑ i ∈ s,w i*(Cφ * R))=Cφ * (∑ i ∈ s,w i)*R:=by
    calc
      (∑ i ∈ s,w i*(Cφ * R))=(∑ i ∈ s,w i)*(Cφ * R):=by
        simp [Finset.sum_mul]
      _ = Cφ * (∑ i ∈ s,w i)*R:=by
        ac_rfl
  exact le_of_eq this
lemma zD {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ) (hw : ∀ i ∈ s,0 ≤ w i) (ha : ∀ i ∈ s,0 < a i) (bad : Finset ℝ) {R:ℝ} (hR : 0 < R) : ∃ r ∈ Set.Ioc R (2*R),r ∉ bad ∧ (∑ i ∈ s,w i * φ (r/a i)) ≤ Cφ * (∑ i ∈ s,w i):=by
 by_contra hbad
 have qe :
   ∀ r ∈ Set.Ioc R (2*R),r ∉ bad →
    Cφ * (∑ i ∈ s,w i) < (∑ i ∈ s,w i * φ (r/a i)):=by
  intro r hr hrbad
  have : ¬(∑ i ∈ s,w i * φ (r/a i)) ≤ Cφ * (∑ i ∈ s,w i):=by
   intro hle
   exact hbad ⟨r,hr,hrbad,hle⟩
  exact lt_of_not_ge this
 let g:ℝ → ℝ := ∑ i ∈ s,fun r:ℝ => w i * φ (r/a i)
 have qi : IntervalIntegrable g volume R (2*R):=by
  simpa [g] using w3 s w a ha hR.le
 have qb :
   IntervalIntegrable (fun _r:ℝ => Cφ * (∑ i ∈ s,w i)) volume R (2*R) :=
  intervalIntegrable_const
 have qd :
   (volume.restrict (Set.Ioc R (2*R)))
    {r | Cφ * (∑ i ∈ s,w i) < g r} ≠ 0:=by
  have qm : Set.Ioc R (2*R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s,w i) < g r}:=by
   intro r hr
   have qj : r ∈ Set.Ioc R (2*R):=hr.1
   have hrbad : r ∉ bad:=by simpa using hr.2
   simpa [g] using qe r qj hrbad
  have hle :
    (volume.restrict (Set.Ioc R (2*R))) (Set.Ioc R (2*R) \ (bad : Set ℝ))
     ≤ (volume.restrict (Set.Ioc R (2*R))) {r | Cφ * (∑ i ∈ s,w i) < g r} :=
   MeasureTheory.measure_mono qm
  have qk :
    (volume.restrict (Set.Ioc R (2*R))) (Set.Ioc R (2*R) \ (bad : Set ℝ)) ≠ 0:=by
   exact ya bad hR
  intro hzero
  have : (volume.restrict (Set.Ioc R (2*R))) (Set.Ioc R (2*R) \ (bad : Set ℝ))=0 :=
   le_antisymm (le_trans hle (le_of_eq hzero)) (by positivity)
  exact qk this
 have qf :
   (∫ r in R..(2*R),(Cφ * (∑ i ∈ s,w i)) ∂volume)
    < ∫ r in R..(2*R),g r ∂volume:=by
  have hab : R ≤ 2*R:=by nlinarith [hR.le]
  refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero (μ := volume)
   (a:=R) (b:=2*R) (f:=fun _ => (Cφ * (∑ i ∈ s,w i))) (g:=g)
   hab qb qi ?_ qd
  have qn : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2*R))),r ∈ Set.Ioc R (2*R) :=
   MeasureTheory.ae_restrict_mem (by simp)
  have qg :
    ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2*R))),r ∉ (bad : Set ℝ):=by
   simpa using
    (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2*R)))))
  filter_upwards [qn,qg] with r qj hrNotBad
  have qc : r ∉ bad:=by simpa using hrNotBad
  exact le_of_lt (by simpa [g] using qe r qj qc)
 have qa :
   (∫ r in R..(2*R),(Cφ * (∑ i ∈ s,w i)) ∂volume)=Cφ * (∑ i ∈ s,w i)*R:=by
  simp [intervalIntegral.integral_const,sub_eq_add_neg,mul_comm]
  ring
 have ql :
   (∫ r in R..(2*R),g r ∂volume) ≤ Cφ * (∑ i ∈ s,w i)*R:=by
  simpa [g] using vR s w a hw ha hR.le
 have : ¬(Cφ * (∑ i ∈ s,w i)*R < Cφ * (∑ i ∈ s,w i)*R):=lt_irrefl _
 have qh : Cφ * (∑ i ∈ s,w i)*R < Cφ * (∑ i ∈ s,w i)*R:=by
  have:=qf
  simpa [qa] using (this.trans_le ql)
 exact this qh
end CartanBound
end Complex
end
end
section
section
noncomputable section
namespace Complex.Hadamard
open Complex Real
lemma wl {m:ℕ} {τ r:ℝ} {u a:ℂ} (hur : ‖u‖ = r) (hmτ : (m:ℝ) ≤ τ) : max 1 (‖u/a‖ ^ m) ≤ 1+(r / ‖a‖) ^ τ := by
  by_cases hx : ‖u/a‖ ≤ 1
  · have qa : ‖u/a‖ ^ m ≤ 1:=pow_le_one₀ (norm_nonneg (u/a)) hx
    have hr0 : 0 ≤ r:=by simpa [hur] using (norm_nonneg u)
    have qd : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have qc : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg qd τ
    have qf : (1:ℝ) ≤ 1+(r / ‖a‖) ^ τ := le_add_of_nonneg_right qc
    have qg : ‖u/a‖ ^ m ≤ 1+(r / ‖a‖) ^ τ := qa.trans qf
    exact (max_le_iff).2 ⟨qf,qg⟩
  · have hx1 : 1 < ‖u/a‖ := lt_of_not_ge hx
    have qh :
        (‖u/a‖ : ℝ)^(m:ℝ) ≤ (‖u/a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have qe : ‖u/a‖ ^ m ≤ (‖u/a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using qh
    have qb : max 1 (‖u/a‖ ^ m) ≤ 1 + ‖u/a‖ ^ m:=by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u/a‖ ^ m) ≤ 1+(‖u/a‖ : ℝ) ^ τ :=
      qb.trans (by nlinarith [qe])
    simpa [norm_div,hur] using this
lemma vI {m:ℕ} {τ r:ℝ} {u a:ℂ} (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) (hmτ : (m:ℝ) ≤ τ) : ‖(WE m (u/a))⁻¹‖ ≤ Real.exp (CartanBound.φ (r / ‖a‖)+(m:ℝ)*(1+(r / ‖a‖) ^ τ)):=by
 have qa :
   Real.log ‖(1:ℂ) - u/a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
  CartanBound.ZO (hur:=hur) (ha:=ha) (hr:=hr)
 have qc :=
  zP (m:=m) (z:=(u/a))
 have qd :
   Real.log ‖WE m (u/a)‖
    ≥ -CartanBound.φ (r / ‖a‖) - (m:ℝ)*max 1 (‖u/a‖ ^ m):=by
  have qe :=
   yl m (u/a)
  linarith [qc,qa,qe]
 have qf :
   max 1 (‖u/a‖ ^ m) ≤ 1+(r / ‖a‖) ^ τ :=
  wl (m:=m) (τ := τ) (r:=r) (u:=u) (a:=a) hur hmτ
 have qb :
   -Real.log ‖WE m (u/a)‖
    ≤ CartanBound.φ (r / ‖a‖)+(m:ℝ)*(1+(r / ‖a‖) ^ τ):=by
  have : -Real.log ‖WE m (u/a)‖
    ≤ CartanBound.φ (r / ‖a‖)+(m:ℝ)*max 1 (‖u/a‖ ^ m):=by
   linarith [qd]
  have hm0 : 0 ≤ (m:ℝ):=by exact_mod_cast (Nat.zero_le m)
  exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left qf hm0])
 have qg : 0 < ‖WE m (u/a)‖ := by
  have : WE m (u/a) ≠ 0:=by
   intro h0
   have : u/a=(1:ℂ):=(Yn m (u/a)).1 h0
   have : u=a:=(div_eq_one_iff_eq ha).1 this
   have : r = ‖a‖ := by simpa [this] using hur.symm
   exact (hr this).elim
  exact norm_pos_iff.2 this
 have hEq :
   ‖(WE m (u/a))⁻¹‖ =
    Real.exp (-Real.log ‖WE m (u/a)‖):=by
  simp [norm_inv,Real.exp_neg,Real.exp_log qg]
 have:=Real.exp_le_exp.2 qb
 simpa [hEq] using this
lemma wa {m:ℕ} {τ r:ℝ} {u a:ℂ} (hur : ‖u‖ = r) (ha : a ≠ 0) (hz : ‖u/a‖ ≤ (1/2:ℝ)) (hτ_le : τ ≤ (m+1:ℝ)) : ‖(WE m (u/a))⁻¹‖ ≤ Real.exp ((2:ℝ)*(r / ‖a‖) ^ τ):=by
  by_cases hu : u=0
  · subst hu
    have hr0 : r=0:=by simpa [hur] using (norm_zero : ‖(0:ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0:ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2:ℝ)*((0:ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have qe : (1:ℝ) ≤ Real.exp ((2:ℝ)*((0:ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using qe
  have qc :=
    y7 (m:=m) (z:=(u/a)) hz
  have qb : -Real.log ‖WE m (u/a)‖ ≤ (2:ℝ)*(r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖WE m (u/a)‖ ≤ (2:ℝ) * ‖u/a‖ ^ (m+1):=by
      linarith [qc]
    set x:ℝ := ‖u/a‖
    have hx1 : x ≤ 1:=le_trans (by simpa [x] using hz) (by norm_num)
    have qd : 0 < x:=by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m+1:ℕ):ℝ):=by
      simpa [Nat.cast_add,Nat.cast_one] using hτ_le
    have qa : x^((m+1:ℕ):ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge qd hx1 hτ_le'
    have qf : x^(m+1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using qa
    have h2x : (2:ℝ)*x^(m+1) ≤ (2:ℝ)*x ^ τ :=
      mul_le_mul_of_nonneg_left qf (by positivity)
    have h2 : (2:ℝ) * ‖u/a‖ ^ (m+1) ≤ (2:ℝ)*(‖u/a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have qg : 0 < ‖WE m (u/a)‖ := by
    have : WE m (u/a) ≠ 0:=by
      intro h0
      have : u/a=(1:ℂ):=(Yn m (u/a)).1 h0
      have : u=a:=(div_eq_one_iff_eq ha).1 this
      have : (‖u/a‖ : ℝ)=1:=by simpa [this] using (by simp [ha])
      linarith [hz,this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(WE m (u/a))⁻¹‖ =
        Real.exp (-Real.log ‖WE m (u/a)‖):=by
    simp [norm_inv,Real.exp_neg,Real.exp_log qg]
  have:=Real.exp_le_exp.2 qb
  simpa [hEq] using this
end Complex.Hadamard
end
end
end
section
section
noncomputable section
namespace Complex.Hadamard
open scoped BigOperators
open Filter Finset Real Topology
section CartanFiniteSum
variable {α : Type*}
private lemma VO [DecidableEq α] (s : Finset α) (u : α → ℝ) :
  Summable (fun a => if a ∈ s then u a else 0) :=
 summable_of_ne_finset_zero (s:=s) fun a ha => by simp [if_neg ha]
private lemma Wq [DecidableEq α] (s : Finset α) (u : α → ℝ) : (∑' a,if a ∈ s then u a else 0) = ∑ a ∈ s,u a:=by
 classical
 simpa [Finset.sum_ite] using
  (hasSum_sum_of_ne_finset_zero (s:=s) (f:=fun a => if a ∈ s then u a else 0)
   fun a ha => by simp [if_neg ha]).tsum_eq
private lemma ub (u₁ u₂ u₃ u₄ : α → ℝ) (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) : tsum (fun a => ((u₁ a+u₂ a)+u₃ a)+u₄ a)=tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a+u₂ a)+u₃ a)+u₄ a)
        = tsum (fun a => (u₁ a+u₂ a)+(u₃ a+u₄ a)):=by
          simp [add_comm,add_left_comm]
    _ = tsum (fun a => u₁ a+u₂ a)+tsum (fun a => u₃ a+u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂,Summable.tsum_add h₃ h₄]
        ring
end CartanFiniteSum
noncomputable def VZ (m:ℕ) (τ Sτ : ℝ):ℝ :=
 ((CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ + 3)*(Sτ + 1)
lemma YD {m:ℕ} {τ Sτ : ℝ} (hSτ : 0 ≤ Sτ) : 0 ≤ VZ m τ Sτ := by
 have hS : 0 ≤ Sτ + 1:=by linarith
 have hA : 0 ≤ (CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ + 3:=by
  have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.uo
  have hm0 : 0 ≤ (m:ℝ):=by exact_mod_cast (Nat.zero_le m)
  have h4τ : 0 ≤ (4:ℝ) ^ τ := by positivity
  nlinarith [hCφ,hm0,h4τ]
 simpa [VZ] using mul_nonneg hA hS
lemma wV {f:ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (p : Wz f (Set.univ : Set ℂ)) : (r / ‖Wc p‖) ^ τ = (r ^ τ)*((‖Wc p‖⁻¹ : ℝ) ^ τ):=by
 have hp : 0 ≤ (‖Wc p‖⁻¹ : ℝ):=by positivity
 simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
  (Real.mul_rpow (x:=r) (y:=(‖Wc p‖⁻¹ : ℝ)) (z := τ) hr hp)
lemma vv {f:ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) : (∑' p : Wz f (Set.univ : Set ℂ),(r / ‖Wc p‖) ^ τ)=(r ^ τ) * ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ := by
  calc
    (∑' p : Wz f (Set.univ : Set ℂ),
        (r / ‖Wc p‖) ^ τ)
        = ∑' p : Wz f (Set.univ : Set ℂ),
            (r ^ τ)*(‖Wc p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact wV (f:=f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : Wz f (Set.univ : Set ℂ),
          ‖Wc p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]
lemma yf {f:ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) : (∑' p : Wz f (Set.univ : Set ℂ),(2:ℝ)*(r / ‖Wc p‖) ^ τ) ≤ (2:ℝ)*((∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ)+1)*(1+r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
  have qa :
      (∑' p : Wz f (Set.univ : Set ℂ),
          (2:ℝ)*(r / ‖Wc p‖) ^ τ)
        = (2:ℝ)*(r ^ τ)*Sτ := by
    calc
      (∑' p : Wz f (Set.univ : Set ℂ),
          (2:ℝ)*(r / ‖Wc p‖) ^ τ)
          = (2:ℝ) * ∑' p : Wz f (Set.univ : Set ℂ),
              (r / ‖Wc p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2:ℝ)*((r ^ τ)*Sτ):=by
              rw [vv (f:=f) (τ := τ) hr]
      _ = (2:ℝ)*(r ^ τ)*Sτ := by ring
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1+r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : Sτ ≤ Sτ + 1:=by linarith
  have hle : (r ^ τ)*Sτ ≤ (1+r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [qa]
  have : (2:ℝ)*(r ^ τ)*Sτ ≤ (2:ℝ)*(Sτ + 1)*(1+r) ^ τ := by
    nlinarith [hle]
  simpa [Sτ,mul_assoc,mul_left_comm,mul_comm] using this
lemma vJ {f:ℂ → ℂ} {r τ : ℝ} (small : Finset (Wz f (Set.univ : Set ℂ))) (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) (hsumτ : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ τ)) : (∑ p ∈ small,(r / ‖Wc p‖) ^ τ) ≤ ((∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ)+1)*(1+r) ^ τ := by
 set Sτ : ℝ :=
  ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
 have qa :
   (∑ p ∈ small,(‖Wc p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
  have hnn : ∀ p : Wz f (Set.univ : Set ℂ),
    0 ≤ (‖Wc p‖⁻¹ : ℝ) ^ τ := by
   intro p
   positivity
  simpa [Sτ] using
   (Summable.sum_le_tsum (s:=small)
    (f:=fun p : Wz f (Set.univ : Set ℂ) =>
     (‖Wc p‖⁻¹ : ℝ) ^ τ)
    (fun p _ => hnn p) hsumτ)
 have qb :
   ∑ p ∈ small,(r / ‖Wc p‖) ^ τ =
    (r ^ τ) * ∑ p ∈ small,(‖Wc p‖⁻¹ : ℝ) ^ τ := by
  simp [wV (f:=f) (τ := τ) hr,Finset.mul_sum]
 have h1r : r ^ τ ≤ (1+r) ^ τ :=
  Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
 have hS : (∑ p ∈ small,(‖Wc p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1:=by
  linarith [qa]
 have hle :
   (r ^ τ)*(∑ p ∈ small,(‖Wc p‖⁻¹ : ℝ) ^ τ)
    ≤ (1+r) ^ τ * (Sτ + 1) :=
  mul_le_mul h1r hS (by positivity) (by positivity)
 simpa [Sτ,qb,mul_assoc,mul_left_comm,mul_comm] using hle
lemma Ym {x₁ x₂ x₃ x₄ A B C:ℝ} (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) : x₁ + x₂ + x₃ + x₄ ≤ A+2*B+C:=by
 nlinarith
lemma ZU {xφ x0 xm xt Cφ m q Y T:ℝ} (hφ : xφ ≤ Cφ * q*Y*T) (h0 : x0 ≤ m*q*Y*T) (hm : xm ≤ m*q*Y*T) (ht : xt ≤ (2:ℝ)*Y*T) : xφ + x0+xm+xt ≤ (Cφ + (2:ℝ)*m)*q*Y*T+(2:ℝ)*Y*T:=by
 have h :=
  Ym hφ h0 hm ht
 have qa :
   Cφ * (q*(Y*T))+2*(m*(q*(Y*T)))+2*(Y*T)
    = (Cφ + (2:ℝ)*m)*(q*(Y*T))+(2:ℝ)*(Y*T):=by
  ring
 simpa [mul_assoc,qa] using h
lemma Z1 (A Y T:ℝ) : A*Y*T+(2:ℝ)*Y*T=((A+2)*Y)*T:=by
 ring
lemma ZE {A S T:ℝ} (hS : 0 ≤ S+1) (hT : 0 ≤ T) : ((A+2)*(S+1))*T ≤ ((A+3)*(S+1))*T:=by
 have h : (A+2)*(S+1) ≤ (A+3)*(S+1):=by
  nlinarith
 exact mul_le_mul_of_nonneg_right h hT
lemma VR
    {f:ℂ → ℂ} {m:ℕ} {τ r:ℝ} (hr : 0 ≤ r)
    (small : Finset (Wz f (Set.univ : Set ℂ))) :
    letI : DecidableEq (Wz f (Set.univ : Set ℂ)):=Classical.decEq _
    let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
    let b : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
        else
          (2:ℝ)*(r/ap p) ^ τ
    ∀ p,0 ≤ b p:=by
  classical
  dsimp
  intro p
  let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun q => ‖Wc q‖
  have hap : ap p = ‖Wc p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ CartanBound.φ (r/ap p):=CartanBound.ul (t:=r/ap p)
    have hm0 : 0 ≤ (m:ℝ):=by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1+(r/ap p) ^ τ):=by positivity
    have : 0 ≤ CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ):=by
      nlinarith [hφ,hm0,h1]
    simpa [hap,hp,ap] using this
  · have qa : 0 ≤ r/ap p:=div_nonneg hr (by positivity)
    have qb : 0 ≤ (r/ap p) ^ τ := Real.rpow_nonneg qa τ
    have : 0 ≤ (2:ℝ)*(r/ap p) ^ τ := mul_nonneg (by norm_num) qb
    simpa [hap,hp,ap] using this
lemma Vw
    {f:ℂ → ℂ} {m:ℕ} {τ r:ℝ} (hr : 0 ≤ r)
    (small : Finset (Wz f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : Wz f (Set.univ : Set ℂ) =>
        ‖Wc p‖⁻¹ ^ τ)) :
    letI : DecidableEq (Wz f (Set.univ : Set ℂ)):=Classical.decEq _
    let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
    let b : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
        else
          (2:ℝ)*(r/ap p) ^ τ
    Summable b:=by
  classical
  dsimp
  let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun q => ‖Wc q‖
  let b : Wz f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
      else
        (2:ℝ)*(r/ap p) ^ τ
  have hb : Summable b:=by
    let b₁ : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
        else 0
    let b₂ : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2:ℝ)*(r/ap p) ^ τ
    have qa : b=fun p => b₁ p+b₂ p:=by
      funext p
      by_cases hp : p ∈ small <;> simp [b,b₁,b₂,hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        VO small
          (fun p => CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have qb :
          Summable (fun p =>
            (2:ℝ)*(r ^ τ)*(‖Wc p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2:ℝ)*(r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂,hp]
          · have : 0 ≤ (2:ℝ)*(r/ap p) ^ τ := by positivity
            simpa [b₂,hp] using this)
        (fun p => ?_) qb
      by_cases hp : p ∈ small
      · have : 0 ≤ (2:ℝ)*(r ^ τ)*(‖Wc p‖⁻¹ ^ τ):=by positivity
        simpa [b₂,hp] using this
      · have qc : (r/ap p) ^ τ = (r ^ τ)*(‖Wc p‖⁻¹ ^ τ):=by
          simpa [ap] using wV (f:=f) (τ := τ) hr p
        simp [b₂,hp,qc,mul_assoc,mul_left_comm,mul_comm]
    simpa [qa] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b,ap,hp]
lemma Wo {f:ℂ → ℂ} {τ R:ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ) (small : Finset (Wz f (Set.univ : Set ℂ))) (qe : ∀ p ∈ small,‖Wc p‖ ≤ 4*R) (hsumτ : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ τ)) : (small.card:ℝ) ≤ (4*R) ^ τ * ((∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ)+1):=by
 classical
 set Sτ : ℝ :=
  ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
 have qd : (∑ p ∈ small,‖Wc p‖⁻¹ ^ τ) ≤ Sτ := by
  have hnn :
    ∀ p : Wz f (Set.univ : Set ℂ),
     0 ≤ ‖Wc p‖⁻¹ ^ τ := by
   intro p
   exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  simpa [Sτ] using
   (Summable.sum_le_tsum (s:=small)
    (f:=fun p : Wz f (Set.univ : Set ℂ) =>
     ‖Wc p‖⁻¹ ^ τ)
    (fun p _ => hnn p) hsumτ)
 have qa :
   (small.card:ℝ) ≤ ∑ p ∈ small,(4*R) ^ τ * ‖Wc p‖⁻¹ ^ τ := by
  have qc : (small.card:ℝ) = ∑ p ∈ small,(1:ℝ):=by simp
  rw [qc]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have qf : ‖Wc p‖ ≤ 4*R:=qe p hp
  have hap : 0 < ‖Wc p‖ :=
   norm_pos_iff.2 (Yd p)
  have qg : (1:ℝ) ≤ (4*R) / ‖Wc p‖ := by
   exact (le_div_iff₀ hap).2 (by simpa [mul_one] using qf)
  have : (1:ℝ) ≤ ((4*R) / ‖Wc p‖) ^ τ :=
   Real.one_le_rpow qg hτ_nonneg
  have qj :
    ((4*R) / ‖Wc p‖) ^ τ =
     (4*R) ^ τ * (‖Wc p‖)⁻¹ ^ τ := by
   have h4 : 0 ≤ (4*R:ℝ):=by nlinarith [le_of_lt hRpos]
   have ha : 0 ≤ (‖Wc p‖ : ℝ)⁻¹ := by positivity
   simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
    (Real.mul_rpow (x:=(4*R:ℝ))
     (y:=(‖Wc p‖ : ℝ)⁻¹) (z := τ) h4 ha)
  have : (1:ℝ) ≤ (4*R) ^ τ * ‖Wc p‖⁻¹ ^ τ := by
   simpa [qj] using this
  exact this
 have qh :
   (small.card:ℝ) ≤ (4*R) ^ τ * (∑ p ∈ small,‖Wc p‖⁻¹ ^ τ):=by
  simpa [Finset.mul_sum] using qa
 have qb : (small.card:ℝ) ≤ (4*R) ^ τ * Sτ := by
  exact qh.trans (mul_le_mul_of_nonneg_left qd (by positivity))
 have qi : (4*R) ^ τ * Sτ ≤ (4*R) ^ τ * (Sτ + 1):=by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith
 have : (small.card:ℝ) ≤ (4*R) ^ τ * (Sτ + 1):=qb.trans qi
 simpa [Sτ,add_comm,add_left_comm,add_assoc,mul_assoc] using this
lemma Ww {τ R r:ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) : (4*R) ^ τ ≤ (4:ℝ) ^ τ * (1+r) ^ τ := by
 have qa : R ≤ 1+r:=by linarith [hR_le_r,le_of_lt hrpos]
 have qb : 0 ≤ (4*R:ℝ):=by nlinarith [le_of_lt hRpos]
 have : (4*R) ^ τ ≤ (4*(1+r)) ^ τ := by
  refine Real.rpow_le_rpow qb ?_ hτ_nonneg
  nlinarith [qa]
 have qc : (4*(1+r)) ^ τ = (4:ℝ) ^ τ * (1+r) ^ τ := by
  have h4 : 0 ≤ (4:ℝ):=by norm_num
  have h1 : 0 ≤ (1+r:ℝ):=by positivity
  simpa [mul_assoc] using
   (Real.mul_rpow (x:=(4:ℝ)) (y:=(1+r:ℝ)) (z := τ) h4 h1)
 simpa [qc] using this
open Classical in
theorem VX
    {f:ℂ → ℂ} {m:ℕ} {τ R r:ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (Wz f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ 4*R})
    (hsumτ :
      Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ τ))
    (hr_phi :
      let qE : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
      let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
      (∑ p ∈ qE,CartanBound.φ (r/a p)) ≤ CartanBound.Cφ * (qE.card:ℝ)) :
    let qE : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
    letI : DecidableEq (Wz f (Set.univ : Set ℂ)):=Classical.decEq _
    let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
    let b : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ qE then
          CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
        else
          (2:ℝ)*(r/ap p) ^ τ
    let Sτ : ℝ := ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
    let Cprod : ℝ:=VZ m τ Sτ
    ∀ s : Finset (Wz f (Set.univ : Set ℂ)),
      (∑ p ∈ s,b p) ≤ Cprod*(1+r) ^ τ := by
  classical
  intro qE ap b Sτ Cprod s
  have hr : 0 ≤ r:=le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have qh : ∀ p,p ∈ qE ↔ p ∈ smallSet:=by
    intro p
    simp [qE,hsmall_fin.mem_toFinset]
  have qn :
      (∑ p ∈ qE,CartanBound.φ (r/ap p)) ≤ CartanBound.Cφ * (qE.card:ℝ):=by
    simpa [qE,ap] using hr_phi
  have qk : ∀ p,0 ≤ b p:=by
    simpa [ap,b] using (VR (f:=f) (m:=m) (τ := τ) (r:=r) hr qE)
  have qe : Summable b:=by
    simpa [ap,b] using
      (Vw (f:=f) (m:=m) (τ := τ) (r:=r) hr qE hsumτ)
  have qf : ∀ p ∈ qE,‖Wc p‖ ≤ 4*R:=by
    intro p hp
    have : p ∈ smallSet:=(qh p).1 hp
    simpa [hsmallSet] using this
  have qo : (qE.card:ℝ) ≤ (4*R) ^ τ * (Sτ + 1):=by
    simpa [Sτ,mul_assoc,add_assoc,add_left_comm,add_comm] using
      (Wo (f:=f) (τ := τ) (R:=R) hRpos hτ_nonneg qE qf hsumτ)
  have qF : (4*R) ^ τ ≤ (4:ℝ) ^ τ * (1+r) ^ τ :=
    Ww (τ := τ) (R:=R) (r:=r) hRpos hrpos hR_le_r hτ_nonneg
  have ql : (qE.card:ℝ) ≤ (4:ℝ) ^ τ * (1+r) ^ τ * (Sτ + 1):=by
    have : (4*R) ^ τ * (Sτ + 1) ≤ (4:ℝ) ^ τ * (1+r) ^ τ * (Sτ + 1):=by
      exact mul_le_mul_of_nonneg_right qF (by linarith [hSτ_nonneg])
    exact le_trans qo this
  have qi :
      (∑' p : Wz f (Set.univ : Set ℂ),b p) ≤ Cprod*(1+r) ^ τ := by
    let bφ : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ qE then CartanBound.φ (r/ap p) else 0
    let b0 : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ qE then (m:ℝ) else 0
    let bmτ : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ qE then (m:ℝ)*(r/ap p) ^ τ else 0
    let bt : Wz f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2:ℝ)*(r/ap p) ^ τ
    have qd : ∀ p,b p ≤ bφ p+b0 p+bmτ p+bt p:=by
      intro p
      by_cases hp : p ∈ qE
      · have qG : 0 ≤ r/ap p:=div_nonneg hr (by positivity)
        have hx : 0 ≤ (r/ap p) ^ τ := Real.rpow_nonneg qG τ
        have qJ : 0 ≤ (2:ℝ)*(r/ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b,bφ,b0,bmτ,bt,hp]
        nlinarith
      · simp [b,bφ,b0,bmτ,bt,hp]
    have qm : Summable (fun p => bφ p+b0 p+bmτ p+bt p):=by
      have hbφ_summ : Summable bφ := by
        simpa [bφ] using VO qE (fun p => CartanBound.φ (r/ap p))
      have qp : Summable b0:=by
        simpa [b0] using VO qE (fun _ => (m:ℝ))
      have hbmτ_summ : Summable bmτ := by
        simpa [bmτ] using VO qE (fun p => (m:ℝ)*(r/ap p) ^ τ)
      have qq : Summable bt:=by
        have qz : Summable (fun p =>
            (2:ℝ)*(r ^ τ)*(‖Wc p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2:ℝ)*(r ^ τ))
        refine qz.congr ?_
        intro p
        simp [bt,ap,wV (f:=f) (τ := τ) hr p,
          mul_assoc,mul_left_comm,mul_comm]
      have h' : Summable (fun p => bφ p+b0 p+(bmτ p+bt p)) :=
        (hbφ_summ.add qp).add (hbmτ_summ.add qq)
      simpa [add_assoc] using h'
    have qr :
        (∑' p : Wz f (Set.univ : Set ℂ),b p)
          ≤ ∑' p : Wz f (Set.univ : Set ℂ),(bφ p+b0 p+bmτ p+bt p) :=
      (hasSum_le qd qe.hasSum qm.hasSum)
    have htsum_bφ :
        (∑' p : Wz f (Set.univ : Set ℂ),bφ p)
          = ∑ p ∈ qE,CartanBound.φ (r/ap p):=by
      classical
      simpa [bφ] using Wq qE (fun p => CartanBound.φ (r/ap p))
    have qs :
        (∑' p : Wz f (Set.univ : Set ℂ),b0 p)
          = (m:ℝ)*(qE.card:ℝ):=by
      classical
      have : (∑' p : Wz f (Set.univ : Set ℂ),b0 p) = ∑ p ∈ qE,(m:ℝ):=by
        simpa [b0] using Wq qE (fun _ => (m:ℝ))
      simp [this,Finset.sum_const,nsmul_eq_mul,mul_comm]
    have htsum_bmτ :
        (∑' p : Wz f (Set.univ : Set ℂ),bmτ p)
          = (m:ℝ) * ∑ p ∈ qE,(r/ap p) ^ τ := by
      classical
      have :
          (∑' p : Wz f (Set.univ : Set ℂ),bmτ p)
            = ∑ p ∈ qE,(m:ℝ)*(r/ap p) ^ τ := by
        simpa [bmτ] using Wq qE (fun p => (m:ℝ)*(r/ap p) ^ τ)
      simp [this,Finset.mul_sum]
    have qt :
        (∑' p : Wz f (Set.univ : Set ℂ),bt p)
          ≤ (2:ℝ)*(Sτ + 1)*(1+r) ^ τ := by
      simpa [bt,ap,Sτ] using
        yf (f:=f) (τ := τ) hr hτ_nonneg
    have qa :
        (∑ p ∈ qE,(r/ap p) ^ τ) ≤ (Sτ + 1)*(1+r) ^ τ := by
      simpa [ap,Sτ] using
        vJ (f:=f) (τ := τ) qE hr hτ_nonneg hsumτ
    have hm0 : 0 ≤ (m:ℝ):=by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.uo
    have hS : 0 ≤ Sτ + 1:=by linarith [hSτ_nonneg]
    have qc :
        (∑' p : Wz f (Set.univ : Set ℂ),(bφ p+b0 p+bmτ p+bt p))
          ≤ (((CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ + 2)*(Sτ + 1))
              * (1+r) ^ τ := by
      have hφ_le :
          (∑' p : Wz f (Set.univ : Set ℂ),bφ p)
            ≤ CartanBound.Cφ * (qE.card:ℝ):=by
        simpa [htsum_bφ] using qn
      have qA :
          (∑' p : Wz f (Set.univ : Set ℂ),b0 p)
            ≤ (m:ℝ)*(qE.card:ℝ):=by
        simp [qs]
      have hbmτ_le :
          (∑' p : Wz f (Set.univ : Set ℂ),bmτ p) ≤
            (m:ℝ)*(4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ := by
        have h0 :
            (∑' p : Wz f (Set.univ : Set ℂ),bmτ p)
              ≤ (m:ℝ)*((Sτ + 1)*(1+r) ^ τ):=by
          have qK:=mul_le_mul_of_nonneg_left qa hm0
          simpa [htsum_bmτ,mul_assoc,mul_left_comm,mul_comm] using qK
        have h1 : (1:ℝ) ≤ (4:ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have qB :
            (m:ℝ)*((Sτ + 1)*(1+r) ^ τ)
              ≤ (m:ℝ)*(4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ := by
          have qu : 0 ≤ (m:ℝ)*((Sτ + 1)*(1+r) ^ τ):=by
            have : 0 ≤ (Sτ + 1)*(1+r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc,mul_left_comm,mul_comm] using (mul_le_mul_of_nonneg_right h1 qu)
        exact h0.trans qB
      have qC :
          (∑' p : Wz f (Set.univ : Set ℂ),bt p)
            ≤ (2:ℝ)*(Sτ + 1)*(1+r) ^ τ := by
        simpa [mul_assoc,mul_left_comm,mul_comm] using qt
      have qD :
          (∑' p : Wz f (Set.univ : Set ℂ),(bφ p+b0 p+bmτ p+bt p))
            = (∑' p,bφ p)+(∑' p,b0 p)+(∑' p,bmτ p)+(∑' p,bt p):=by
        classical
        have hbφ_summ : Summable bφ := by
          simpa [bφ] using VO qE (fun p => CartanBound.φ (r/ap p))
        have qp : Summable b0:=by
          simpa [b0] using VO qE (fun _ => (m:ℝ))
        have hbmτ_summ : Summable bmτ := by
          simpa [bmτ] using VO qE (fun p => (m:ℝ)*(r/ap p) ^ τ)
        have qq : Summable bt:=by
          have qz :
              Summable
                (fun p : Wz f (Set.univ : Set ℂ) =>
                  (2:ℝ)*(r ^ τ)*((‖Wc p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2:ℝ)*(r ^ τ))
          refine qz.congr ?_
          intro p
          simp [bt,ap,wV (f:=f) (τ := τ) hr p,
            mul_assoc,mul_left_comm,mul_comm]
        exact ub bφ b0 bmτ bt hbφ_summ qp hbmτ_summ qq
      have qj :
          (qE.card:ℝ) ≤ (4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ := by
        simpa [mul_assoc,mul_left_comm,mul_comm] using ql
      have hφ_le' :
          (∑' p : Wz f (Set.univ : Set ℂ),bφ p) ≤
            CartanBound.Cφ * (4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ := by
        have : CartanBound.Cφ * (qE.card:ℝ) ≤
            CartanBound.Cφ * ((4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ) :=
          mul_le_mul_of_nonneg_left qj hCφ
        exact hφ_le.trans (by simpa [mul_assoc,mul_left_comm,mul_comm] using this)
      have qv :
          (∑' p : Wz f (Set.univ : Set ℂ),b0 p) ≤
            (m:ℝ)*(4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ := by
        have : (m:ℝ)*(qE.card:ℝ) ≤ (m:ℝ)*((4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ) :=
          mul_le_mul_of_nonneg_left qj hm0
        exact qA.trans (by simpa [mul_assoc,mul_left_comm,mul_comm] using this)
      have qb :
          (∑' p : Wz f (Set.univ : Set ℂ),(bφ p+b0 p+bmτ p+bt p))
            ≤ (CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ
              + (2:ℝ)*(Sτ + 1)*(1+r) ^ τ := by
        rw [qD]
        set Y : ℝ:=Sτ + 1 with hY
        set T : ℝ:=(1+r) ^ τ with hT
        have hφ_leY :
            (∑' p : Wz f (Set.univ : Set ℂ),bφ p)
              ≤ CartanBound.Cφ * (4:ℝ) ^ τ * Y*T:=by
          simpa [hY,hT,mul_assoc] using hφ_le'
        have qw :
            (∑' p : Wz f (Set.univ : Set ℂ),b0 p)
              ≤ (m:ℝ)*(4:ℝ) ^ τ * Y*T:=by
          simpa [hY,hT,mul_assoc] using qv
        have hbmτ_leY :
            (∑' p : Wz f (Set.univ : Set ℂ),bmτ p)
              ≤ (m:ℝ)*(4:ℝ) ^ τ * Y*T:=by
          simpa [hY,hT,mul_assoc] using hbmτ_le
        have qx :
            (∑' p : Wz f (Set.univ : Set ℂ),bt p) ≤ (2:ℝ)*Y*T:=by
          simpa [hY,hT,mul_assoc] using qC
        have qH :=
          ZU
            (q:=(4:ℝ) ^ τ) hφ_leY qw hbmτ_leY qx
        simpa [Y,T,add_assoc] using qH
      have qI :
          (CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ * (Sτ + 1)*(1+r) ^ τ
              + (2:ℝ)*(Sτ + 1)*(1+r) ^ τ
            = (((CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ + 2)*(Sτ + 1))*(1+r) ^ τ := by
        exact Z1
          ((CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ) (Sτ + 1) ((1+r) ^ τ)
      rw [← qI]
      exact qb
    have qy :
        (((CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ + 2)*(Sτ + 1))*(1+r) ^ τ
          ≤ Cprod*(1+r) ^ τ := by
      simpa [Cprod,VZ,mul_assoc,mul_left_comm,mul_comm] using
        ZE
          (A:=(CartanBound.Cφ + (2:ℝ)*m)*(4:ℝ) ^ τ)
          (S:=Sτ) (T:=(1+r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans qr qc) qy)
  have qg :
      (∑ p ∈ s,b p) ≤ (∑' p : Wz f (Set.univ : Set ℂ),b p):=by
    simpa using
      (Summable.sum_le_tsum (s:=s) (f:=b) (fun p _ => qk p) qe)
  exact qg.trans qi
end Complex.Hadamard
end
end
end
section
section
noncomputable section
open scoped BigOperators
open Filter Finset Real Topology
lemma Finset.WW {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ) (ha : ∀ x ∈ s,0 ≤ a x) (hab : ∀ x ∈ s,a x ≤ Real.exp (b x)) : (∏ x ∈ s,a x) ≤ Real.exp (∑ x ∈ s,b x):=by
  calc
    (∏ x ∈ s,a x) ≤ ∏ x ∈ s,Real.exp (b x):=Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s,b x):=by
      simpa using (Real.exp_sum (s:=s) (f:=b)).symm
lemma Vb {α : Type} {f : α → ℝ} {a:ℝ}
  (hf : HasProd f a (SummationFilter.unconditional α))
  {B:ℝ} (hB : ∀ s : Finset α,(∏ x ∈ s,f x) ≤ Real.exp B) :
  a ≤ Real.exp B :=
 hasProd_le_of_prod_le (L:=(SummationFilter.unconditional α)) hf hB
lemma Ve {α : Type} {fac : α → ℂ} {F:ℂ} (qb : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) : HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α):=by
 change
  Tendsto (fun s : Finset α => ∏ x ∈ s,(fac x)⁻¹)
   (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
 have qa :
   Tendsto (fun s : Finset α => ∏ x ∈ s,fac x)
    (SummationFilter.unconditional α).filter (𝓝 F):=by
  simpa [HasProd] using qb
 have qc :
   Tendsto (fun s : Finset α => (∏ x ∈ s,fac x)⁻¹)
    (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
  qa.inv₀ hF
 refine qc.congr' (Filter.Eventually.of_forall ?_)
 intro s
 simp [Finset.prod_inv_distrib]
lemma Z5 {α : Type} {fac : α → ℂ} {F:ℂ} (qb : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) : HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α):=by
 change
  Tendsto (fun s : Finset α => ∏ x ∈ s,‖(fac x)⁻¹‖)
   (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
 have qa:=(Ve qb hF).norm
 refine qa.congr' (Filter.Eventually.of_forall ?_)
 intro s
 simp [norm_inv,Finset.prod_inv_distrib]
lemma yF {α : Type} {fac : α → ℂ} {F:ℂ} (qd : HasProd fac F (SummationFilter.unconditional α)) (b : α → ℝ) (B:ℝ) (qa : ∀ x,‖(fac x)⁻¹‖ ≤ Real.exp (b x)) (qe : ∀ s : Finset α,(∑ x ∈ s,b x) ≤ B) : ‖F⁻¹‖ ≤ Real.exp B:=by
  by_cases hF : F=0
  · subst hF
    simpa using exp_nonneg B
  have qb :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    Z5 qd hF
  have qc : ∀ s : Finset α,(∏ x ∈ s,‖(fac x)⁻¹‖) ≤ Real.exp B:=by
    intro s
    have h0 : ∀ x ∈ s,0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s,‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s,b x):=by
      refine Finset.WW s (a:=fun x => ‖(fac x)⁻¹‖) (b:=b) h0 ?_
      intro x hx
      simpa using qa x
    have h2 : Real.exp (∑ x ∈ s,b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (qe s)
    exact h1.trans h2
  exact Vb qb qc
end
end
end
section
section
open Metric
namespace Complex
theorem Zq {f:ℂ → ℂ} {M r R:ℝ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) R)) (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0=0) (qc : ∀ w,‖w‖ ≤ R → (f w).re ≤ M) {z:ℂ} (hz : ‖z‖ ≤ r) : ‖f z‖ ≤ 2*M*r/(R - r):=by
  have hR : 0 < R:=lt_trans hr hlt
  have qa : z ∈ Metric.ball (0:ℂ) R:=by
    rw [Metric.mem_ball,dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0:ℂ) R):=by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0:ℂ) R:=ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have qb : Set.MapsTo f (Metric.ball (0:ℂ) R) {w | w.re ≤ M}:=by
    intro w hw
    simp only [Set.mem_setOf_eq]
    have hw' : ‖w‖ < R:=by simpa [Metric.mem_ball,dist_zero_right] using hw
    exact qc w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff qb hR qa hf0
  have hzR : ‖z‖ < R:=by
    rw [Metric.mem_ball,dist_zero_right] at qa
    exact qa
  have qd : ‖z‖ / (R - ‖z‖) ≤ r/(R - r):=by
    have qe : 0 < R - r:=sub_pos.mpr hlt
    have qf : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ qf qe]
    nlinarith [hz,norm_nonneg z]
  have hM' : 0 ≤ 2*M:=mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2*M * ‖z‖ / (R - ‖z‖):=hbc
    _ ≤ 2*M*(r/(R - r)):=by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left qd hM'
    _ = 2*M*r/(R - r):=by ring
end Complex
end
end
section
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
theorem vD {H:ℂ → ℂ} {n:ℕ} (hH : Differentiable ℂ H) (qk : ∀ z,H z ≠ 0) (h_bound : ∃ C > 0,∀ z,‖H z‖ ≤ Real.exp (C*(1 + ‖z‖)^n)) : ∃ P : Polynomial ℂ,P.natDegree ≤ n ∧ ∀ z,H z=Complex.exp (Polynomial.eval z P):=by
  classical
  rcases h_bound with ⟨C,hCpos,hC⟩
  let L:ℂ → ℂ:=fun z => deriv H z/H z
  have qs : Differentiable ℂ (deriv H):=by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L:=by
    simpa [L] using! (qs.div hH qk)
  let h:ℂ → ℂ:=fun z => Complex.wedgeIntegral (0:ℂ) z L
  have ql : ∀ z,HasDerivAt h (L z) z:=by
    intro z
    let r:ℝ := ‖z‖ + 1
    have hrpos : 0 < r:=by
      dsimp [r]; linarith [norm_nonneg z]
    have qt : z ∈ Metric.ball (0:ℂ) r:=by
      have : dist z (0:ℂ) < r:=by simp [r,dist_zero_right]
      simpa [Metric.mem_ball] using this
    have qm : Complex.IsConservativeOn L (Metric.ball (0:ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have qP : ContinuousOn L (Metric.ball (0:ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h,r] using qm.hasDerivAt_wedgeIntegral (f_cont:=qP) (hz:=qt)
  have hh : Differentiable ℂ h:=fun z => (ql z).differentiableAt
  have qn : ∀ z,deriv h z=L z:=fun z => (ql z).deriv
  let k:ℂ → ℂ:=fun z => h z+Complex.log (H 0)
  have hk : Differentiable ℂ k:=hh.add_const (Complex.log (H 0))
  have qF : ∀ z,H z=Complex.exp (k z):=by
    let F:ℂ → ℂ:=fun z => Complex.exp (k z)/H z
    have qo : ∀ z,deriv F z=0:=by
      intro z
      have qG : HasDerivAt H (deriv H z) z:=(hH z).hasDerivAt
      have qH : HasDerivAt k (L z) z:=by
        have qI : HasDerivAt h (L z) z:=ql z
        simpa [k,L] using qI.add_const (Complex.log (H 0))
      have q6 : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z)*L z) z :=
        (HasDerivAt.cexp qH)
      have q7:=(HasDerivAt.div q6 qG (qk z))
      have :
          deriv F z =
            ((Complex.exp (k z)*L z)*H z - Complex.exp (k z)*deriv H z)/(H z)^2:=by
        simpa [F] using! q7.deriv
      rw [this]
      have q8 :
          (Complex.exp (k z)*L z)*H z - Complex.exp (k z)*deriv H z=0:=by
        dsimp [L]
        field_simp [qk z]
        ring
      simp [q8]
    have qu : Differentiable ℂ F:=(hk.cexp).div hH qk
    have qp : ∀ z,F z=F 0:=by
      intro z
      exact is_const_of_deriv_eq_zero qu qo z 0
    have hF0 : F 0=1:=by
      have hh0 : h 0=0:=by simp [h,Complex.wedgeIntegral]
      have hk0 : k 0=Complex.log (H 0):=by simp [k,hh0]
      have hH0 : H 0 ≠ 0:=qk 0
      simp [F,hk0,Complex.exp_log hH0,hH0]
    intro z
    have : F z=1:=by simpa [hF0] using (qp z)
    have hHz : H z ≠ 0:=qk z
    have : Complex.exp (k z)/H z=1:=by simpa [F] using this
    have : Complex.exp (k z)=H z:=by
      field_simp [hHz] at this
      simpa using this
    exact this.symm
  have qg : ∀ z,(k z).re ≤ C*(1 + ‖z‖)^n:=by
    intro z
    have hHz : H z ≠ 0:=qk z
    have q9 : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have qv : Real.log ‖H z‖ ≤ C*(1 + ‖z‖)^n:=by
      have:=Real.log_le_log q9 (hC z)
      simpa [Real.log_exp] using this
    have qw : Real.log ‖H z‖ = (k z).re:=by
      have : ‖H z‖ = Real.exp (k z).re:=by
        simpa [qF z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re):=by simp [this]
        _ = (k z).re:=by simp
    simpa [qw] using qv
  have qa : ∀ m:ℕ,n < m → iteratedDeriv m k 0=0:=by
    intro m hm
    have hm' : 0 < (m - n:ℕ):=Nat.sub_pos_of_lt hm
    have ja : m - n ≠ 0:=(Nat.pos_iff_ne_zero.1 hm')
    let f:ℂ → ℂ:=fun z => k z - k 0
    have hf : Differentiable ℂ f:=hk.sub_const (k 0)
    have hf0 : f 0=0:=by simp [f]
    have qh : ∀ R:ℝ,0 < R →
        ∀ z,‖z‖ ≤ R → (f z).re ≤ C*(1+R)^n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C*(1 + ‖z‖)^n:=qg z
      have jb : (k z).re ≤ C*(1+R)^n:=by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1+R:=by linarith
        have jc : (1 + ‖z‖ : ℝ)^n ≤ (1+R)^n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left jc (le_of_lt hCpos))
      have jd : -(k 0).re ≤ ‖k 0‖ := by
        have je : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have jf : -(k 0).re ≤ |(k 0).re| := by simpa using (neg_le_abs (k 0).re)
        exact jf.trans je
      have : (f z).re ≤ C*(1+R)^n + ‖k 0‖ := by
        have : (f z).re=(k z).re - (k 0).re:=by simp [f,sub_eq_add_neg]
        nlinarith [this,jb,jd]
      exact this
    have qb : ∀ R:ℝ,0 < R →
        ∀ z,‖z‖ ≤ R/2 → ‖f z‖ ≤ 2*(C*(1+R)^n + ‖k 0‖ + 1):=by
      intro R hRpos z hz
      have qJ : 0 < R/2:=by nlinarith
      have hlt : R/2 < R:=by nlinarith
      have qQ : 0 < (C*(1+R)^n + ‖k 0‖ + 1):=by
        have : 0 ≤ C*(1+R)^n:=by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this,norm_nonneg (k 0)]
      have qx : AnalyticOnNhd ℂ f (Metric.closedBall 0 R):=by
        intro w _hw
        exact (hf.analyticAt w)
      have qR : ∀ w,‖w‖ ≤ R → (f w).re ≤ (C*(1+R)^n + ‖k 0‖ + 1):=by
        intro w hw
        have:=qh R hRpos w hw
        linarith
      have qS :=
        Zq (f:=f) (r:=R/2) (R:=R)
          (M:=(C*(1+R)^n + ‖k 0‖ + 1))
          qx qJ hlt qQ hf0 qR (z:=z) hz
      have qK :
          2*(C*(1+R)^n + ‖k 0‖ + 1)*(R/2)/(R - R/2)
            = 2*(C*(1+R)^n + ‖k 0‖ + 1):=by
        field_simp [hRpos.ne'] ; ring
      simpa [qK] using qS
    have qy : ∀ R:ℝ,0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial:ℝ)*(2*(C*(1+R)^n + ‖k 0‖ + 1))/(R/2)^m:=by
      intro R hRpos
      have qJ : 0 < R/2:=by nlinarith
      have qi : DiffContOnCl ℂ f (Metric.ball (0:ℂ) (R/2)):=hf.diffContOnCl
      have qe :
          ∀ z ∈ Metric.sphere (0:ℂ) (R/2),
            ‖f z‖ ≤ 2*(C*(1+R)^n + ‖k 0‖ + 1):=by
        intro z hz
        have hz' : ‖z‖ ≤ R/2:=by
          simpa [Metric.mem_sphere,dist_zero_right] using (le_of_eq hz)
        exact qb R hRpos z hz'
      simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n:=m) (c:=(0:ℂ))
          (R:=R/2) (C:=2*(C*(1+R)^n + ‖k 0‖ + 1))
          (hR:=qJ) qi qe)
    have qj : iteratedDeriv m f 0=0:=by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne
      let RHS:ℝ → ℝ:=fun R =>
        (m.factorial:ℝ)*(2*(C*(1+R)^n + ‖k 0‖ + 1))/(R/2)^m
      have qz : ∀ R:ℝ,0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R:=by
        intro R hRpos
        simpa [RHS] using qy R hRpos
      have qf : Tendsto RHS atTop (𝓝 0):=by
        let K:ℝ := ‖k 0‖ + 1
        have qT : 0 < m:=lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0:=ne_of_gt qT
        have qL : Tendsto (fun R:ℝ => R^n/(R/2)^m) atTop (𝓝 0):=by
          have qM :
              (fun R:ℝ => R^n/(R/2)^m)=fun R:ℝ => (2:ℝ)^m*(R^n/R^m):=by
            funext R
            simp [div_eq_mul_inv,mul_pow,mul_assoc,mul_comm]
          have qU : Tendsto (fun R:ℝ => R^n/R^m) atTop (𝓝 0):=by
            have hp : m - n ≠ 0:=(Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have qN : Tendsto (fun R:ℝ => (R^(m - n))⁻¹) atTop (𝓝 0):=by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n:=m - n) hp)
            have hEq : (fun R:ℝ => (R^(m - n))⁻¹) =ᶠ[atTop] fun R:ℝ => R^n/R^m:=by
              have jg : (fun R:ℝ => R^n/R^m) =ᶠ[atTop] fun R:ℝ => (R^(m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0:ℝ)] with R hR
                have hle : n ≤ m:=le_of_lt hm
                have qV : n+(m - n)=m:=Nat.add_sub_of_le hle
                have hn0 : R^n ≠ 0:=pow_ne_zero n hR
                calc
                  R^n/R^m=R^n/R^(n+(m - n)):=by simp [qV]
                  _ = R^n*((R^(m - n))⁻¹ * (R^n)⁻¹):=by
                        simp [pow_add,div_eq_mul_inv,mul_comm]
                  _ = (R^(m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact jg.symm
            exact Filter.Tendsto.congr' hEq qN
          have : Tendsto (fun R:ℝ => (2:ℝ)^m*(R^n/R^m)) atTop (𝓝 ((2:ℝ)^m*0)) :=
            tendsto_const_nhds.mul qU
          simpa [qM] using this
        have jh : Tendsto (fun R:ℝ => ((R/2)^m)⁻¹) atTop (𝓝 0):=by
          have ji : Tendsto (fun R:ℝ => R/2) atTop atTop :=
            (tendsto_id.atTop_div_const (r:=(2:ℝ)) (by norm_num : (0:ℝ) < 2))
          have jc : Tendsto (fun R:ℝ => (R/2)^m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n:=m) hm0).comp ji
          simpa using! jc.inv_tendsto_atTop
        have ji : Tendsto (fun R:ℝ => (1+R)/R) atTop (𝓝 (1:ℝ)):=by
          have qW : Tendsto (fun R:ℝ => (R:ℝ)⁻¹) atTop (𝓝 (0:ℝ)):=tendsto_inv_atTop_zero
          have jj : Tendsto (fun R:ℝ => (1:ℝ)+(R:ℝ)⁻¹) atTop (𝓝 (1:ℝ)):=by
            simpa using (tendsto_const_nhds.add qW)
          have hEq : (fun R:ℝ => (1+R)/R) =ᶠ[atTop] fun R:ℝ => (1:ℝ)+(R:ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0:ℝ)] with R hR
            field_simp [hR]; ring
          exact Filter.Tendsto.congr' hEq.symm jj
        have qq : Tendsto (fun R:ℝ => ((1+R)/R)^n) atTop (𝓝 (1:ℝ)):=by
          simpa using (ji.pow n)
        have qc :
            Tendsto (fun R:ℝ => (1+R)^n/(R/2)^m) atTop (𝓝 (0:ℝ)):=by
          have hEq :
              (fun R:ℝ => (1+R)^n/(R/2)^m)
                =ᶠ[atTop] fun R:ℝ => ((1+R)/R)^n*(R^n/(R/2)^m):=by
            filter_upwards [eventually_ne_atTop (0:ℝ)] with R hR
            have qX : (R^n:ℝ) ≠ 0:=pow_ne_zero n hR
            have qM :
                ((1+R)/R)^n*(R^n/(R/2)^m)=(1+R)^n/(R/2)^m:=by
              calc
                ((1+R)/R)^n*(R^n/(R/2)^m)
                    = ((1+R)^n/R^n)*(R^n/(R/2)^m):=by
                        simp [div_pow]
                _ = ((1+R)^n*R^n)/(R^n*(R/2)^m):=by
                        simp [div_mul_div_comm,mul_comm]
                _ = ((1+R)^n*R^n)/((R/2)^m*R^n):=by
                        simp [mul_comm]
                _ = (1+R)^n/(R/2)^m:=by
                        simpa [mul_assoc,mul_comm,mul_left_comm] using
                          (mul_div_mul_right (a:=(1+R)^n) (b:=(R/2)^m) qX)
            exact qM.symm
          have jk :
              Tendsto
                (fun R:ℝ => ((1+R)/R)^n*(R^n/(R/2)^m))
                atTop (𝓝 (0:ℝ)):=by
            simpa [mul_zero] using (qq.mul qL)
          exact Filter.Tendsto.congr' hEq.symm jk
        have h1 : Tendsto (fun R:ℝ => C*((1+R)^n/(R/2)^m)) atTop (𝓝 0):=by
          simpa using (tendsto_const_nhds.mul qc)
        have h2 : Tendsto (fun R:ℝ => K*((R/2)^m)⁻¹) atTop (𝓝 0):=by
          simpa using (tendsto_const_nhds.mul jh)
        have jl :
            Tendsto
              (fun R:ℝ => C*((1+R)^n/(R/2)^m)+K*((R/2)^m)⁻¹)
              atTop (𝓝 0):=by
          simpa using (h1.add h2)
        have jm :
            (fun R:ℝ => (C*(1+R)^n+K)/(R/2)^m)
              = fun R:ℝ => C*((1+R)^n/(R/2)^m)+K*((R/2)^m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv,mul_add,mul_assoc,mul_comm]
        have qY : Tendsto (fun R:ℝ => (C*(1+R)^n+K)/(R/2)^m) atTop (𝓝 0):=by
          simpa [jm] using jl
        have qK :
            Tendsto (fun _ : ℝ => (m.factorial:ℝ)*(2:ℝ)) atTop
              (𝓝 ((m.factorial:ℝ)*(2:ℝ))):=tendsto_const_nhds
        have jk : Tendsto (fun R:ℝ => ((m.factorial:ℝ)*(2:ℝ)) *
              ((C*(1+R)^n+K)/(R/2)^m)) atTop (𝓝 0):=by
          simpa [mul_assoc,mul_left_comm,mul_comm] using (qK.mul qY)
        have qA : RHS=fun R:ℝ => ((m.factorial:ℝ)*(2:ℝ)) *
              ((C*(1+R)^n+K)/(R/2)^m):=by
          funext R
          dsimp [RHS,K]
          ring_nf
        simpa [qA] using jk
      have qO : ∀ᶠ R in atTop,RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 qf).2 _ (half_pos ha)
      have qd : ∀ᶠ R in atTop,‖iteratedDeriv m f 0‖ ≤ RHS R:=by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with R hRpos
        exact qz R hRpos
      rcases (qd.and qO).exists with ⟨R,hle,hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ :=
        (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this
    have qT : 0 < m:=lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0:=ne_of_gt qT
    have jn : ContDiffAt ℂ (↑m) k (0:ℂ):=(hk.analyticAt 0).contDiffAt
    have jo : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0:ℂ):=contDiffAt_const
    have jp :
        iteratedDeriv m f 0 =
          iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0:=by
      simpa [f] using! (iteratedDeriv_sub (n:=m) (x:=(0:ℂ)) jn jo)
    have qB : iteratedDeriv m (fun _ : ℂ => k 0) 0=0:=by
      simp [iteratedDeriv_const,hm0]
    have qZ : iteratedDeriv m f 0=iteratedDeriv m k 0:=by
      simp [jp,qB]
    simpa [qZ] using qj
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n+1),Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)
  have q0 : P.natDegree ≤ n:=by
    have jq :
        P.natDegree ≤
          Finset.fold max 0
            (fun m:ℕ =>
              (Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n+1)):=by
      simpa [P,Function.comp] using
        (Polynomial.natDegree_sum_le (s:=Finset.range (n+1))
          (f:=fun m:ℕ =>
            Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)))
    have q1 :
        Finset.fold max 0
            (fun m:ℕ =>
              (Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n+1)) ≤ n:=by
      refine (Finset.fold_max_le (f:=fun m:ℕ =>
        (Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b:=0) (s:=Finset.range (n+1)) (c:=n)).2 ?_
      refine ⟨Nat.zero_le n,?_⟩
      intro m hm
      have jr :
          (Polynomial.monomial m ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have q2 : m ≤ n:=Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact jr.trans q2
    exact jq.trans q1
  have qC : ∀ z,k z=Polynomial.eval z P:=by
    intro z
    have qD:=Complex.taylorSeries_eq_of_entire' (c:=(0:ℂ)) (z:=z) hk
    have q3 : ∀ m:ℕ,m ∉ Finset.range (n+1) →
        ((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0*(z - 0)^m)=0:=by
      intro m hm'
      have js : n < m:=by
        have : n+1 ≤ m:=Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0=0:=qa m js
      simp [hz]
    have q4 :
        (∑' m:ℕ,(m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0*(z - 0)^m)
          = ∑ m ∈ Finset.range (n+1),(m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0*z^m:=by
      simpa [sub_zero] using (tsum_eq_sum (s:=Finset.range (n+1)) q3)
    have qE :
        k z = ∑ m ∈ Finset.range (n+1),(m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0*z^m:=by
      calc
        k z = ∑' m:ℕ,(m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0*(z - 0)^m:=by
          simpa using qD.symm
        _ = _ := q4
    have q5 :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n+1),z^m*((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0):=by
      classical
      change Polynomial.eval₂ (RingHom.id ℂ) z P=_
      let φ : Polynomial ℂ →+* ℂ:=Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P=_
      simp [P,φ,Polynomial.eval₂_monomial,mul_comm]
    have qr :
        k z = ∑ m ∈ Finset.range (n+1),z^m*((m.factorial:ℂ)⁻¹ * iteratedDeriv m k 0):=by
      simpa [mul_comm,mul_left_comm,mul_assoc] using qE
    simpa [q5] using qr
  refine ⟨P,q0,?_⟩
  intro z
  have : H z=Complex.exp (k z):=by simp [qF z]
  simp [this,qC z]
end Hadamard
end Complex
end
end
end
section
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
open Polynomial
private lemma V7 {n:ℕ} (hn : 0 < n) (w:ℂ) : ∃ z:ℂ,z^n=w:=by
  classical
  by_cases hw : w=0
  · subst hw
    refine ⟨0,?_⟩
    have hn0 : n ≠ 0:=Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w/n),?_⟩
    have hn0 : (n:ℂ) ≠ 0:=by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w/n))^n
          = Complex.exp ((n:ℂ)*(Complex.log w/n)):=by
              simpa using (Complex.exp_nat_mul (Complex.log w/n) n).symm
      _ = Complex.exp (Complex.log w):=by
            have : (n:ℂ)*(Complex.log w/n)=Complex.log w:=by
              field_simp [hn0]
            simp [this]
      _ = w:=by simpa using (Complex.exp_log hw)
private lemma WG (a:ℂ) (ha : a ≠ 0) : a*((starRingEnd ℂ) a/(‖a‖ : ℂ))=(‖a‖ : ℂ):=by
  have qa : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have qb : (‖a‖ : ℂ) ≠ 0:=by
    exact_mod_cast (ne_of_gt qa)
  have qd : a*(starRingEnd ℂ) a=(Complex.normSq a:ℂ) :=
    Complex.mul_conj a
  have qc : (Complex.normSq a:ℂ)=((‖a‖ ^ 2:ℝ):ℂ):=by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have qe : ((‖a‖ ^ 2:ℝ):ℂ)/(‖a‖ : ℂ)=(‖a‖ : ℂ):=by
    have : ((‖a‖ ^ 2:ℝ):ℂ)=(‖a‖ : ℂ)*(‖a‖ : ℂ):=by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2:ℝ):ℂ)/(‖a‖ : ℂ)
          = ((‖a‖ : ℂ)*(‖a‖ : ℂ))/(‖a‖ : ℂ):=by simp [this]
      _ = (‖a‖ : ℂ):=by
            field_simp [qb]
  calc
    a*((starRingEnd ℂ) a/(‖a‖ : ℂ))
        = (a*(starRingEnd ℂ) a)/(‖a‖ : ℂ):=by
            simp [div_eq_mul_inv,mul_assoc]
    _ = (Complex.normSq a:ℂ)/(‖a‖ : ℂ):=by simp [qd]
    _ = ((‖a‖ ^ 2:ℝ):ℂ)/(‖a‖ : ℂ):=by simp [qc]
    _ = (‖a‖ : ℂ):=qe
private lemma YG (P : Polynomial ℂ) (hn : 0 < P.natDegree) : ∃ R0:ℝ,0 < R0 ∧ ∀ R:ℝ,R0 ≤ R → ∃ z:ℂ,‖z‖ = R ∧ (‖P.leadingCoeff‖ / 2)*R^P.natDegree ≤ (P.eval z).re:=by
  classical
  set n : ℕ:=P.natDegree
  have hn0 : 0 < n:=hn
  have hP0 : P ≠ 0:=by
    intro h0
    simp [n,h0] at hn0
  have hLC : P.leadingCoeff ≠ 0:=Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ:=P.leadingCoeff
  have ha : a ≠ 0:=hLC
  have qc : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set wtarget : ℂ:=(starRingEnd ℂ) a/(‖a‖ : ℂ)
  have qa : ‖wtarget‖ = (1:ℝ):=by
    calc
      ‖wtarget‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [wtarget]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1:ℝ):=by
        field_simp [qc.ne']
  rcases V7 (n:=n) hn0 (w:=wtarget) with ⟨w,hw⟩
  have qn : ‖w‖ = (1:ℝ):=by
    have qI : (‖w‖ : ℝ)^n=1:=by
      have:=congrArg (fun z:ℂ => ‖z‖) hw
      simpa [norm_pow,qa] using this
    have qJ : n ≠ 0:=Nat.ne_of_gt hn0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) qJ).1 qI
  set S:ℝ := ∑ i ∈ Finset.range n,‖P.coeff i‖
  set R0 : ℝ:=max 1 (2*S / ‖a‖)
  refine ⟨R0,?_,?_⟩
  · have : (0:ℝ) < (1:ℝ):=by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have qs : (1:ℝ) ≤ R:=by
      exact le_trans (le_max_left _ _) hR
    have qf : 0 ≤ R:=le_trans (by norm_num) qs
    set z : ℂ:=(R:ℂ)*w
    have qo : ‖z‖ = R:=by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this,qn,abs_of_nonneg qf]
    have qt : P.eval z =
        (∑ i ∈ Finset.range n,P.coeff i*z^i)+P.coeff n*z^n:=by
      have qK : P.eval z = ∑ i ∈ Finset.range (n+1),P.coeff i*z^i:=by
        have : P.natDegree+1=n+1:=by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p:=P) z)
      have qu :
          (∑ i ∈ Finset.range (n+1),P.coeff i*z^i)
            = (∑ i ∈ Finset.range n,P.coeff i*z^i)+P.coeff n*z^n:=by
        simpa using (Finset.sum_range_succ (f:=fun i => P.coeff i*z^i) n)
      exact qK.trans qu
    have qb :
        ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ ≤ S*R^(n - 1):=by
      have h1 :
          ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖
            ≤ ∑ i ∈ Finset.range n,‖P.coeff i*z^i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i*z^i))
      have qA : ∀ i ∈ Finset.range n,‖P.coeff i*z^i‖ ≤ ‖P.coeff i‖ * R^(n - 1):=by
        intro i hi
        have qB : i < n:=Finset.mem_range.mp hi
        have qC : i ≤ n - 1:=Nat.le_pred_of_lt qB
        have qD : ‖z‖ ^ i ≤ R^(n - 1):=by
          have qE : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (by simpa [qo] using qs) qC
          simpa [qo] using qE
        calc
          ‖P.coeff i*z^i‖ = ‖P.coeff i‖ * ‖z‖ ^ i:=by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R^(n - 1):=by
            exact mul_le_mul_of_nonneg_left qD (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n,‖P.coeff i*z^i‖
            ≤ ∑ i ∈ Finset.range n,‖P.coeff i‖ * R^(n - 1):=by
        exact Finset.sum_le_sum (fun i hi => qA i hi)
      have h3 :
          (∑ i ∈ Finset.range n,‖P.coeff i‖ * R^(n - 1))
            = (∑ i ∈ Finset.range n,‖P.coeff i‖)*R^(n - 1):=by
        simp [Finset.sum_mul]
      have qp : (∑ i ∈ Finset.range n,‖P.coeff i‖) ≤ S:=by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖
            ≤ ∑ i ∈ Finset.range n,‖P.coeff i*z^i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n,‖P.coeff i‖ * R^(n - 1):=h2
        _ = (∑ i ∈ Finset.range n,‖P.coeff i‖)*R^(n - 1):=h3
        _ ≤ S*R^(n - 1):=by
              exact mul_le_mul_of_nonneg_right qp (pow_nonneg qf _)
    have qg : (P.coeff n*z^n).re = ‖a‖ * R^n:=by
      have qv : w^n=wtarget:=hw
      have qw : a*w^n=(‖a‖ : ℂ):=by
        have : a*w^n=a*wtarget:=by simp [qv]
        simpa [wtarget,a] using (this.trans (WG a ha))
      have qx : z^n=((R:ℂ)^n)*(w^n):=by
        simp [z,mul_pow,mul_comm]
      have qq : P.coeff n=a:=by simp [a,n,Polynomial.coeff_natDegree]
      have qL : ∀ m:ℕ,(((R:ℂ)^m).re)=R^m:=by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ,ih,mul_re]
      calc
        (P.coeff n*z^n).re
            = (a*z^n).re:=by simp [qq]
        _ = (a*(((R:ℂ)^n)*(w^n))).re:=by simp [qx]
        _ = (((R:ℂ)^n)*(a*(w^n))).re:=by
              ring_nf
        _ = (((R:ℂ)^n)*(‖a‖ : ℂ)).re:=by simp [qw]
        _ = (((R:ℂ)^n).re) * ‖a‖ := by
              simp [mul_re]
        _ = (R^n) * ‖a‖ := by simp [qL n]
        _ = ‖a‖ * R^n:=by ring
    refine ⟨z,qo,?_⟩
    have qh : (∑ i ∈ Finset.range n,P.coeff i*z^i).re
        ≥ -‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ := by
      have qM : |(∑ i ∈ Finset.range n,P.coeff i*z^i).re|
          ≤ ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ :=
        Complex.abs_re_le_norm _
      have:=neg_le_of_abs_le qM
      simpa using this
    have ql :
        (P.eval z).re ≥ (P.coeff n*z^n).re - ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ := by
      have : (P.eval z).re =
          (∑ i ∈ Finset.range n,P.coeff i*z^i).re+(P.coeff n*z^n).re:=by
        simp [qt,add_comm]
      linarith [this,qh]
    have qm : R0 ≤ R:=hR
    have qF : 2*S / ‖a‖ ≤ R:=le_trans (le_max_right _ _) qm
    have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) qs
    have qe : 0 ≤ R:=le_of_lt hRpos
    have qy : 1 ≤ n:=Nat.succ_le_of_lt hn0
    have qi : S*R^(n - 1) ≤ (‖a‖ / 2)*R^n:=by
      have qz : 0 < ‖a‖ := qc
      have qG : S ≤ (‖a‖ / 2)*R:=by
        have : 2*S ≤ ‖a‖ * R:=by
          have:=(mul_le_mul_of_nonneg_left qF (by linarith [qz.le] : (0:ℝ) ≤ ‖a‖))
          have hne : (‖a‖ : ℝ) ≠ 0:=ne_of_gt qz
          simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,hne] using this
        have : S ≤ (‖a‖ * R)/2:=by linarith
        simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using this
      have : S*R^(n - 1) ≤ (‖a‖ / 2)*R*R^(n - 1):=by
        have qd : 0 ≤ R^(n - 1):=pow_nonneg qe _
        exact mul_le_mul_of_nonneg_right qG qd
      have hRR : R*R^(n - 1)=R^n:=by
        have : n=(n - 1)+1:=by
          exact (Nat.sub_add_cancel qy).symm
        rw [this,pow_succ]
        ring_nf; grind
      simpa [mul_assoc,hRR] using this
    have qj :
        (‖a‖ / 2)*R^n ≤ (P.eval z).re:=by
      have qr : ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ ≤ (‖a‖ / 2)*R^n:=by
        exact qb.trans qi
      have qH : (P.coeff n*z^n).re = ‖a‖ * R^n:=by simpa [a] using qg
      have qk :
          (‖a‖ * R^n) - ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ ≤ (P.eval z).re:=by
        simpa [qH] using ql
      have qN :
          (‖a‖ * R^n) - (‖a‖ / 2)*R^n ≤
            (‖a‖ * R^n) - ‖∑ i ∈ Finset.range n,P.coeff i*z^i‖ :=
        sub_le_sub_left qr (‖a‖ * R^n)
      have qO : (‖a‖ * R^n) - (‖a‖ / 2)*R^n=(‖a‖ / 2)*R^n:=by ring
      have : (‖a‖ * R^n) - (‖a‖ / 2)*R^n ≤ (P.eval z).re :=
        qN.trans qk
      simpa [qO] using this
    simpa [a,n] using qj
theorem v9 {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ) (qh : ∃ C > 0,∀ z:ℂ,Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C*(1 + ‖z‖) ^ ρ) : P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree=0
  · simp [hdeg]
  · have qr : 0 < P.natDegree:=Nat.pos_of_ne_zero hdeg
    rcases YG (P:=P) qr with ⟨R0,hR0pos,hray⟩
    rcases qh with ⟨C,hCpos,hC⟩
    have ql : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0:=by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0:=(Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c:ℝ := ‖P.leadingCoeff‖ / 2
    have qs : 0 < c:=by
      have : (0:ℝ) < (2:ℝ):=by norm_num
      exact (div_pos ql this)
    have qa : (P.natDegree:ℝ) ≤ ρ := by
      by_contra hnlt
      have qt : ρ < (P.natDegree:ℝ):=lt_of_not_ge hnlt
      let δ : ℝ:=(P.natDegree:ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 qt
      let K0 : ℝ:=(C*(2:ℝ) ^ ρ)/c
      have hK0 : ∃ R1,∀ R ≥ R1,K0+1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ),K0+1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0+1)
        rcases (eventually_atTop.1 h) with ⟨R1,hR1⟩
        exact ⟨R1,hR1⟩
      rcases hK0 with ⟨R1,hR1⟩
      set R : ℝ:=max (max R0 1) R1
      have qd : R0 ≤ R:=le_trans (le_max_left _ _) (le_max_left _ _)
      have qm : (1:ℝ) ≤ R:=le_trans (le_max_right _ _) (le_max_left _ _)
      have qe : R1 ≤ R:=le_max_right _ _
      have qn : 0 < R:=lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) qm
      have hRδ : K0+1 ≤ R ^ δ := hR1 R qe
      rcases hray R qd with ⟨z,hz_norm,hz_re⟩
      have qb :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖):=by
        have qx : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have qi : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log qx hle
        have qj : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re:=by
          simp [Complex.norm_exp]
        simpa [qj] using qi
      have qc :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C*(1 + ‖z‖) ^ ρ :=
        hC z
      have qu : c*R^(P.natDegree:ℝ) ≤ C*(1+R) ^ ρ := by
        have qo : c*R^P.natDegree ≤ (P.eval z).re:=by
          simpa [c] using hz_re
        have qk : c*R^(P.natDegree:ℝ) ≤ (P.eval z).re:=by
          simpa [Real.rpow_natCast,c] using qo
        have : c*R^(P.natDegree:ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          qk.trans qb
        have : c*R^(P.natDegree:ℝ) ≤ C*(1 + ‖z‖) ^ ρ :=
          this.trans qc
        simpa [hz_norm] using this
      have qp : (1+R:ℝ) ≤ R*2:=by linarith
      have qv : (1+R:ℝ) ^ ρ ≤ (R*2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [qn.le]) qp hρ
      have hR2 : (R*2) ^ ρ = R ^ ρ * (2:ℝ) ^ ρ := by
        have qf : 0 ≤ R:=le_of_lt qn
        have qg : 0 ≤ (2:ℝ):=by norm_num
        simpa [mul_assoc] using (Real.mul_rpow qf qg (z := ρ))
      have qq : c*R^(P.natDegree:ℝ) ≤ C*(R ^ ρ * (2:ℝ) ^ ρ):=by
        have:=le_trans qu (mul_le_mul_of_nonneg_left qv (le_of_lt hCpos))
        simpa [hR2,mul_assoc,mul_left_comm,mul_comm] using this
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos qn _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0:=ne_of_gt hRρ_pos
      have qy :
          (c*R^(P.natDegree:ℝ))/(R ^ ρ) ≤ C*(2:ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right qq (le_of_lt hRρ_pos)
        have qz : (C*(R ^ ρ * (2:ℝ) ^ ρ))/(R ^ ρ)=C*(2:ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        simpa [qz,mul_assoc,mul_left_comm,mul_comm] using h
      have qw : R ^ δ = R^(P.natDegree:ℝ)/R ^ ρ := by
        simpa [δ] using (Real.rpow_sub qn (P.natDegree:ℝ) ρ)
      have hRδ_le : c*(R ^ δ) ≤ C*(2:ℝ) ^ ρ := by
        have qA : c*(R ^ δ)=(c*R^(P.natDegree:ℝ))/(R ^ ρ):=by
          simp [qw,div_eq_mul_inv,mul_left_comm,mul_comm]
        simpa [qA] using qy
      have hRδ_le' : R ^ δ ≤ K0:=by
        have : R ^ δ ≤ (C*(2:ℝ) ^ ρ)/c:=by
          refine (le_div_iff₀ qs).2 ?_
          simpa [mul_assoc,mul_left_comm,mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0+1 ≤ K0:=le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0:ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 qa
theorem y9 {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ) (qb : ∃ C > 0,∀ z:ℂ,‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C*(1 + ‖z‖) ^ τ)) : P.natDegree ≤ Nat.floor τ := by
 rcases qb with ⟨C,hCpos,hC⟩
 have qa :
   ∃ C > 0,∀ z:ℂ,
    Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C*(1 + ‖z‖) ^ τ :=
  Real.wQ
   (f:=fun z:ℂ => Complex.exp (Polynomial.eval z P))
   (r:=fun z:ℂ => 1 + ‖z‖) hCpos hτ
   (fun z => by linarith [norm_nonneg z]) hC
 exact v9 (ρ := τ) hτ P qa
end Hadamard
end Complex
end
end
end
section
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma v0
  {f:ℂ → ℂ} (qd : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0)
  {B r:ℝ} (hrpos : 0 < r) (qe : r ≤ B)
  (smallSet : Set (Wz f (Set.univ : Set ℂ))) (hsmall_fin : smallSet.Finite)
  (hsmallSet :
   smallSet = {p : Wz f (Set.univ : Set ℂ) | ‖Wc p‖ ≤ B})
  (qb :
   let qh : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
   let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
   r ∉ qh.image a) :
  ∀ u:ℂ,‖u‖ = r → f u ≠ 0:=by
 classical
 let qh : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
 let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
 let bad : Finset ℝ:=qh.image a
 have qa : r ∉ bad:=by
  simpa [bad,qh,a] using qb
 have qf :
   ∀ p : Wz f (Set.univ : Set ℂ),
    ‖Wc p‖ ≤ B → r ≠ ‖Wc p‖ := by
  intro p hpB hEq
  have qc : p ∈ qh:=by
   have qg : p ∈ smallSet:=by
    simpa [hsmallSet] using hpB
   simpa [qh] using (hsmall_fin.mem_toFinset.2 qg)
  have : r ∈ bad:=Finset.mem_image.2 ⟨p,qc,by simpa [a] using hEq.symm⟩
  exact (qa this).elim
 exact vu (f:=f) qd hnot
  (B:=B) (r:=r) hrpos qe qf
theorem zI
    {f:ℂ → ℂ} {ρ τ : ℝ} {m:ℕ}
    (hmρ : (m:ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m+1:ℝ))
    (hτ_nonneg : 0 ≤ τ)
    (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ (m+1)))
    (hsumτ : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ τ)) :
    let Sτ : ℝ :=
      ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
    let Cprod : ℝ:=VZ m τ Sτ
    ∀ {R r:ℝ},0 < R → 1 ≤ R → R ≤ r → r ≤ 2*R →
      ∀ (smallSet : Set (Wz f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : Wz f (Set.univ : Set ℂ) |
              ‖Wc p‖ ≤ 4*R} →
        (let qg : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
         let a : Wz f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖Wc p‖
         r ∉ qg.image a) →
        (let qg : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
         let a : Wz f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖Wc p‖
         (∑ p ∈ qg,(1:ℝ)*CartanBound.φ (r/a p)) ≤
          CartanBound.Cφ * (qg.card:ℝ)) →
        ∀ u:ℂ,‖u‖ = r →
          ‖(u^analyticOrderNatAt f 0 *
              VJ m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cprod*(1+r) ^ τ):=by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let qg : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
  let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
  let bad : Finset ℝ:=qg.image a
  have qb : r ∉ bad:=by
    simpa [bad,qg,a] using hr_not_bad
  have hr1 : (1:ℝ) ≤ r:=le_trans hRle hR_le_r
  have qa : ‖(u^analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.wP u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : Wz f (Set.univ : Set ℂ) → ℂ :=
    fun p => WE m (u/Wc p)
  have qm :
      HasProdLocallyUniformlyOn
        (fun (p : Wz f (Set.univ : Set ℂ)) (w:ℂ) =>
          WE m (w/Wc p))
        (VJ m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    zB (m:=m) (f:=f) h_sum
  have qh :
      HasProd fac (VJ m f (Set.univ : Set ℂ) u) :=
    qm.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
  haveI : DecidablePred (fun p : Wz f (Set.univ : Set ℂ) => p ∈ qg) :=
    Classical.decPred _
  let b : Wz f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ qg then
        CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)
      else
        (2:ℝ)*(r/ap p) ^ τ
  have qi : ∀ p,‖(fac p)⁻¹‖ ≤ Real.exp (b p):=by
    intro p
    by_cases hp : p ∈ qg
    · have qd : r ≠ ap p:=by
        intro hEq
        have : r ∈ bad:=by
          refine Finset.mem_image.2 ⟨p,hp,?_⟩
          simp [ap,a,hEq]
        exact (qb this).elim
      have qj : Wc p ≠ 0:=Yd p
      have hmτ : (m:ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
      have qk :
          ‖(WE m (u/Wc p))⁻¹‖
            ≤ Real.exp (CartanBound.φ (r/ap p)+(m:ℝ)*(1+(r/ap p) ^ τ)):=by
        simpa [ap] using
          (vI (m:=m) (τ := τ) (r:=r)
              (u:=u) (a:=Wc p)
              (hur:=hur) (ha:=qj) (hr:=by simpa [ap] using qd) hmτ)
      simpa [fac,b,hp] using qk
    · have qe : (4*R:ℝ) < ap p:=by
        have : ¬ap p ≤ 4*R:=by
          intro hle
          have : p ∈ qg:=by
            have qf : p ∈ smallSet:=by
              simpa [hsmallSet,ap] using hle
            simpa [qg] using (hsmall_fin.mem_toFinset.2 qf)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u/Wc p‖ ≤ (1/2:ℝ) :=
        y8 (z:=u) (a:=Wc p)
          (R:=2*R) (by nlinarith [hRpos]) (by rw [hur]; exact hr_le_2R)
          (by nlinarith [qe])
      have hτ_le : τ ≤ (m+1:ℝ):=le_of_lt hτ_lt
      have qn :
          ‖(WE m (u/Wc p))⁻¹‖ ≤
            Real.exp ((2:ℝ)*(r/ap p) ^ τ):=by
        simpa [ap] using
          (wa (m:=m) (τ := τ) (r:=r)
              (u:=u) (a:=Wc p)
              (hur:=hur) (ha:=Yd p) (hz:=hz') hτ_le)
      simpa [fac,b,hp] using qn
  have ql :
      ∀ s : Finset (Wz f (Set.univ : Set ℂ)),
        (∑ p ∈ s,b p) ≤ Cprod*(1+r) ^ τ := by
    intro s
    simpa [qg,ap,b,Sτ,Cprod,a,hsmallSet] using
      (Complex.Hadamard.VX (f:=f) (m:=m) (τ := τ) (R:=R) (r:=r)
        (hRpos:=hRpos) (hrpos:=lt_of_lt_of_le hRpos hR_le_r)
        (hR_le_r:=hR_le_r) (hτ_nonneg:=hτ_nonneg)
        (smallSet:=smallSet) (hsmall_fin:=hsmall_fin) (hsmallSet:=hsmallSet)
        (hsumτ := hsumτ)
        (hr_phi:=by
          simpa [qg,a,one_mul] using hr_phi)
        s)
  have qc :
      ‖(VJ m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (Cprod*(1+r) ^ τ):=by
    refine yF
      (α := Wz f (Set.univ : Set ℂ)) (fac:=fac)
      (F:=VJ m f (Set.univ : Set ℂ) u)
      qh (b:=b) (B:=Cprod*(1+r) ^ τ) ?_ ?_
    · exact qi
    · intro s
      exact ql s
  have qo :
      ‖(u^analyticOrderNatAt f 0 *
          VJ m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u^analyticOrderNatAt f 0)⁻¹‖ *
        ‖(VJ m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev,mul_comm]
  rw [qo]
  have :
      ‖(u^analyticOrderNatAt f 0)⁻¹‖ *
          ‖(VJ m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1*Real.exp (Cprod*(1+r) ^ τ) :=
    mul_le_mul qa qc (by positivity) (by positivity)
  simpa using this
theorem yw
    {f H:ℂ → ℂ} {ρ τ : ℝ} {m:ℕ} {Cf:ℝ}
    (hmρ : (m:ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m+1:ℝ))
    (hτ_nonneg : 0 ≤ τ) (qd : Differentiable ℂ f)
    (hnot : ∃ z:ℂ,f z ≠ 0)
    (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ (m+1)))
    (hsumτ : Summable (fun p : Wz f (Set.univ : Set ℂ) =>
      ‖Wc p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z:ℂ,‖f z‖ ≤ Real.exp (Cf*(1 + ‖z‖) ^ τ))
    (qe : ∀ z:ℂ,
      f z =
        H z*z^analyticOrderNatAt f 0 *
          VJ m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
    let Cprod : ℝ:=VZ m τ Sτ
    ∀ {R r:ℝ},0 < R → 1 ≤ R → R ≤ r → r ≤ 2*R → 0 < r →
      ∀ (smallSet : Set (Wz f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : Wz f (Set.univ : Set ℂ) |
              ‖Wc p‖ ≤ 4*R} →
        (let qj : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
         let a : Wz f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖Wc p‖
         r ∉ qj.image a) →
        (let qj : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
         let a : Wz f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖Wc p‖
         (∑ p ∈ qj,(1:ℝ)*CartanBound.φ (r/a p)) ≤
          CartanBound.Cφ * (qj.card:ℝ)) →
        ∀ u:ℂ,‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf+Cprod+10)*(1+r) ^ τ):=by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R hrpos smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let qj : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
  let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
  let bad : Finset ℝ:=qj.image a
  have qa : r ∉ bad:=by
    simpa [bad,qj,a] using hr_not_bad
  have qf :
      f u =
        H u*(u^analyticOrderNatAt f 0 *
          VJ m f (Set.univ : Set ℂ) u):=by
    simpa [mul_assoc,mul_left_comm,mul_comm] using (qe u)
  have qh : f u ≠ 0:=by
    have qb : r ≤ 4*R:=by nlinarith [hr_le_2R,hRpos]
    exact v0 (f:=f) qd hnot
      (B:=4*R) (r:=r) hrpos qb smallSet hsmall_fin hsmallSet
      (by simpa [qj,a] using hr_not_bad) u hur
  have qg :
      (u^analyticOrderNatAt f 0 *
        VJ m f (Set.univ : Set ℂ) u) ≠ 0:=by
    intro hden0
    have : f u=0:=by simpa [hden0] using qf
    exact qh this
  have hHu :
      H u =
        f u/(u^analyticOrderNatAt f 0 *
          VJ m f (Set.univ : Set ℂ) u):=by
    exact eq_div_of_mul_eq qg (Eq.symm qf)
  have qk : ‖f u‖ ≤ Real.exp (Cf*(1+r) ^ τ):=by
    simpa [hur] using hf_boundτ u
  have qc :
      ‖(u^analyticOrderNatAt f 0 *
          VJ m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cprod*(1+r) ^ τ):=by
    simpa [Sτ,Cprod] using
      (zI
        (f:=f) (ρ := ρ) (τ := τ) (m:=m)
        hmρ hτ hτ_lt hτ_nonneg h_sum hsumτ
        (R:=R) (r:=r) hRpos hRle hR_le_r hr_le_2R
        smallSet hsmall_fin hsmallSet
        (by simpa [qj,a] using hr_not_bad)
        (by simpa [qj,a,one_mul] using hr_phi)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u^analyticOrderNatAt f 0 *
            VJ m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u^analyticOrderNatAt f 0 *
              VJ m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv,norm_inv,this]
  have ql :
      ‖f u‖ *
          ‖(u^analyticOrderNatAt f 0 *
            VJ m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf*(1+r) ^ τ)*Real.exp (Cprod*(1+r) ^ τ) :=
    mul_le_mul qk qc (by positivity) (by positivity)
  have qm :
      Real.exp (Cf*(1+r) ^ τ)*Real.exp (Cprod*(1+r) ^ τ)
        = Real.exp ((Cf+Cprod)*(1+r) ^ τ):=by
    simp [Real.exp_add,add_mul,add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf+Cprod)*(1+r) ^ τ) :=
    (this.trans ql).trans_eq qm
  have qi :
      Real.exp ((Cf+Cprod)*(1+r) ^ τ) ≤
        Real.exp ((Cf+Cprod+10)*(1+r) ^ τ):=by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1+r) ^ τ := by positivity
    nlinarith
  exact this.trans qi
theorem yL {f H:ℂ → ℂ} {ρ τ : ℝ} {m:ℕ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m+1:ℝ)) (hτ_nonneg : 0 ≤ τ) (qd : Differentiable ℂ f) (qb : Differentiable ℂ H) (hnot : ∃ z:ℂ,f z ≠ 0) (h_sum : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (m+1))) (qe : ∃ C > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) (qf : ∀ z:ℂ,f z=H z*z^analyticOrderNatAt f 0*VJ m f (Set.univ : Set ℂ) z) : ∃ C > 0,∀ z:ℂ,‖H z‖ ≤ Real.exp (C*(1 + ‖z‖) ^ τ):=by
 rcases qe with ⟨Cf,hCfpos,hCf⟩
 have hsumτ :
   Summable (fun p : Wz f (Set.univ : Set ℂ) =>
    ‖Wc p‖⁻¹ ^ τ) :=
  zR (f:=f) (ρ := ρ) (τ := τ)
   hρ hτ qd hnot ⟨Cf,hCfpos,hCf⟩
 let Sτ : ℝ := ∑' p : Wz f (Set.univ : Set ℂ),‖Wc p‖⁻¹ ^ τ
 have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg fun _ =>
  Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
 let Cprod : ℝ:=VZ m τ Sτ
 have qa : 0 ≤ Cprod:=by
  simpa [Cprod] using YD (m:=m) (τ := τ) hSτ_nonneg
 have hf_boundτ : ∀ z:ℂ,‖f z‖ ≤ Real.exp (Cf*(1 + ‖z‖) ^ τ) :=
  Real.w5
   (f:=f) (r:=fun z:ℂ => 1 + ‖z‖) (C:=Cf) (ρ := ρ) (τ := τ)
   hCfpos.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
 refine ⟨(Cf+Cprod+10)*(3:ℝ) ^ τ,by
  have h3τ : 0 < (3:ℝ) ^ τ := by positivity
  nlinarith [hCfpos,qa,h3τ],?_⟩
 intro z
 let R : ℝ:=max ‖z‖ 1
 have hRpos : 0 < R:=lt_of_lt_of_le (by norm_num) (le_max_right _ _)
 have qn : (1:ℝ) ≤ R:=le_max_right _ _
 let smallSet : Set (Wz f (Set.univ : Set ℂ)) :=
  {p | ‖Wc p‖ ≤ 4*R}
 have hsmall_fin : smallSet.Finite:=by
  have : Metric.closedBall (0:ℂ) (4*R) ⊆ (Set.univ : Set ℂ):=by simp
  simpa [smallSet] using
   (ZB (f:=f) (U:=(Set.univ : Set ℂ))
    (B:=4*R) this)
 let qk : Finset (Wz f (Set.univ : Set ℂ)):=hsmall_fin.toFinset
 let a : Wz f (Set.univ : Set ℂ) → ℝ:=fun p => ‖Wc p‖
 have qj : ∀ p ∈ qk,0 < a p:=by
  intro p hp
  exact norm_pos_iff.2 (Yd p)
 let bad : Finset ℝ:=qk.image a
 rcases CartanBound.zD
   (s:=qk) (w:=fun _ => (1:ℝ)) (a:=a)
   (hw:=by intro _ _; norm_num) (ha:=qj) (bad:=bad) (R:=R) hRpos with
  ⟨r,hr_mem,hr_not_bad,hr_phi⟩
 have hR_le_r : R ≤ r:=le_of_lt hr_mem.1
 have qc : r ≤ 2*R:=hr_mem.2
 have hrpos : 0 < r:=lt_of_lt_of_le hRpos hR_le_r
 have qg :
   ∀ u:ℂ,‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf+Cprod+10)*(1+r) ^ τ):=by
  simpa [Sτ,Cprod] using
   (yw
    (f:=f) (H:=H) (ρ := ρ) (τ := τ) (m:=m) (Cf:=Cf)
    hmρ hτ hτ_lt hτ_nonneg qd hnot h_sum hsumτ hf_boundτ qf
    (R:=R) (r:=r) hRpos qn hR_le_r qc hrpos
    smallSet hsmall_fin (by rfl)
    (by simpa [qk,a,bad] using hr_not_bad)
    (by simpa [qk,a,one_mul,Finset.sum_const,nsmul_eq_mul] using hr_phi))
 have qh : z ∈ Metric.ball (0:ℂ) r:=by
  rw [Metric.mem_ball,dist_zero_right]
  exact lt_of_le_of_lt (le_max_left _ _) hr_mem.1
 have ql :
   ‖H z‖ ≤ Real.exp ((Cf+Cprod+10)*(1+r) ^ τ):=by
  exact Complex.yB qb hrpos qh qg
 have qi : 1+r ≤ 3*(1 + ‖z‖):=by
  exact Real.yg (norm_nonneg z)
   (by simpa [R] using qc)
 have qm :
   Real.exp ((Cf+Cprod+10)*(1+r) ^ τ)
    ≤ Real.exp (((Cf+Cprod+10)*(3:ℝ) ^ τ)*(1 + ‖z‖) ^ τ):=by
  have hnn : 0 ≤ (Cf+Cprod+10):=by nlinarith [le_of_lt hCfpos,qa]
  exact Real.vQ hnn (by norm_num)
   (by linarith [le_of_lt hrpos]) (by positivity) hτ_nonneg qi
 simpa [mul_assoc] using ql.trans qm
theorem ZC {f:ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (qc : Differentiable ℂ f) (hnot : ∃ z:ℂ,f z ≠ 0) (qd : ∃ C > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C*(1 + ‖z‖) ^ ρ) : ∃ (P : Polynomial ℂ),P.degree ≤ Nat.floor ρ ∧ ∀ z:ℂ,f z=Complex.exp (Polynomial.eval z P)*z^(analyticOrderNatAt f 0)*VJ (Nat.floor ρ) f (Set.univ : Set ℂ) z:=by
  set m : ℕ:=Nat.floor ρ
  have h_sum :
      Summable (fun p : Wz f (Set.univ : Set ℂ) =>
        ‖Wc p‖⁻¹ ^ (m+1)):=by
    simpa [m] using
      (zX (f:=f) (ρ := ρ)
        hρ qc hnot qd)
  rcases vN (m:=m) (f:=f) qc hnot h_sum with
    ⟨H,hH_entire,hH_ne,hfactor⟩
  rcases Real.z7 hρ with
    ⟨τ,hτ,hτ_lt,hτ_nonneg,hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m:=by
    simpa [m] using hfloorτ'
  have hτ_lt_m : τ < (m+1:ℝ):=by
    simpa [m] using hτ_lt
  have hτ_lt_nat : τ < ((m+1:ℕ):ℝ):=by
    simpa [Nat.cast_add,Nat.cast_one] using hτ_lt_m
  have hmρ : (m:ℝ) ≤ ρ := by
    have:=Nat.floor_le hρ
    simpa [m] using this
  have qa :
      ∃ C > 0,∀ z:ℂ,‖H z‖ ≤ Real.exp (C*(1 + ‖z‖) ^ τ) :=
    yL (f:=f) (H:=H) (ρ := ρ) (τ := τ)
      (m:=m) hρ hmρ hτ hτ_lt hτ_nonneg qc hH_entire hnot h_sum qd hfactor
  have qb :
      ∃ C > 0,∀ z:ℂ,‖H z‖ ≤ Real.exp (C*(1 + ‖z‖)^(m+1)):=by
    exact Real.vh
      (f:=H) (r:=fun z:ℂ => 1 + ‖z‖)
      (fun z => by linarith [norm_nonneg z]) hτ_lt_nat qa
  rcases vD (H:=H) (n:=m+1)
      hH_entire hH_ne qb with
    ⟨P,hPn,hHP⟩
  have qf : P.natDegree ≤ m:=by
    have qe :
        ∃ C > 0,∀ z:ℂ,
          ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C*(1 + ‖z‖) ^ τ):=by
      rcases qa with ⟨C,hCpos,hC⟩
      exact ⟨C,hCpos,fun z => by simpa [hHP z] using (hC z)⟩
    have:=y9 hτ_nonneg P qe
    simpa [hfloorτ] using this
  refine ⟨P,?_,?_⟩
  · have : P.degree ≤ m:=Polynomial.degree_le_of_natDegree_le qf
    simpa [m] using this
  · intro z
    have hH' : H z=Complex.exp (Polynomial.eval z P):=by simpa using (hHP z)
    simpa [hH',mul_assoc,mul_left_comm,mul_comm,m] using (hfactor z)
end Complex.Hadamard
end
end
end
section
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
def Ws (ρ : ℝ) (f:ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ ε : ℝ,0 < ε →
 ∃ C > 0,∀ z:ℂ,‖f z‖ ≤ Real.exp (C*(1 + ‖z‖)^(ρ + ε))
namespace Ws
theorem differentiable {ρ : ℝ} {f:ℂ → ℂ} (h : Ws ρ f) :
  Differentiable ℂ f :=
 h.1
theorem exists_bound {ρ ε : ℝ} {f:ℂ → ℂ} (h : Ws ρ f)
  (hε : 0 < ε) :
  ∃ C > 0,∀ z:ℂ,‖f z‖ ≤ Real.exp (C*(1 + ‖z‖)^(ρ + ε)) :=
 h.2 ε hε
theorem WF {ρ τ : ℝ} {f:ℂ → ℂ} (h : Ws ρ f) (hτ : ρ < τ) (hτ_nonneg : 0 ≤ τ) : ∃ C' > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C'*(1 + ‖z‖) ^ τ := by
 rcases h.exists_bound (sub_pos.2 hτ) with ⟨C,hCpos,hC⟩
 have qa : ∀ z:ℂ,‖f z‖ ≤ Real.exp (C*(1 + ‖z‖) ^ τ):=by
  intro z
  simpa [sub_add_cancel] using (hC z)
 exact Real.wQ (f:=f)
  (r:=fun z:ℂ => 1 + ‖z‖) hCpos hτ_nonneg
  (fun z => by linarith [norm_nonneg z]) qa
theorem vA {ρ : ℝ} {f:ℂ → ℂ} (h : Ws ρ f) (hρ : 0 ≤ ρ) (hnot : ∃ z:ℂ,f z ≠ 0) : Summable (fun p : Wz f (Set.univ : Set ℂ) => ‖Wc p‖⁻¹ ^ (Nat.floor ρ + 1)):=by
 rcases Real.z7 hρ with
  ⟨τ,hτ,_hτ_lt,hτ_nonneg,hfloorτ⟩
 have hgrowthτ :
   ∃ C' > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C'*(1 + ‖z‖) ^ τ :=
  h.WF hτ hτ_nonneg
 have qa :=
  zX
   (f:=f) (ρ := τ) hτ_nonneg h.differentiable hnot hgrowthτ
 simpa [hfloorτ] using qa
end Ws
theorem ZQ {f:ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hnot : ∃ z:ℂ,f z ≠ 0) (qb : Ws ρ f) : ∃ (P : Polynomial ℂ),P.degree ≤ Nat.floor ρ ∧ ∀ z:ℂ,f z=Complex.exp (Polynomial.eval z P)*z^(analyticOrderNatAt f 0)*VJ (Nat.floor ρ) f (Set.univ : Set ℂ) z:=by
  classical
  let qa : Differentiable ℂ f:=qb.differentiable
  set m : ℕ:=Nat.floor ρ
  rcases Real.z7 hρ with
    ⟨τ,hτ,hτ_lt,hτ_nonneg,hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m:=by
    simpa [m] using hfloorτ'
  have hgrowthτ :
      ∃ C' > 0,∀ z:ℂ,Real.log (1 + ‖f z‖) ≤ C'*(1 + ‖z‖) ^ τ :=
    qb.WF hτ hτ_nonneg
  rcases ZC (f:=f) (ρ := τ) hτ_nonneg
      qa hnot hgrowthτ with
    ⟨P,hdeg,hfac⟩
  refine ⟨P,?_,?_⟩
  · simpa [m,hfloorτ] using hdeg
  · intro z
    simpa [m,hfloorτ] using hfac z
end Complex.Hadamard
end
end
end
section
section
namespace Polynomial
theorem WC (P : ℂ[X]) (z:ℂ) : logDeriv (fun w:ℂ => Complex.exp (Polynomial.eval w P)) z=Polynomial.eval z P.derivative:=by
 have qa :
   deriv (fun w:ℂ => Complex.exp (Polynomial.eval w P)) z =
    Complex.exp (Polynomial.eval z P)*Polynomial.eval z P.derivative:=by
  simpa [Function.comp_def,mul_comm] using
   ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
 rw [logDeriv_apply,qa]
 field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]
theorem yO {P : Polynomial ℂ} (hP : P.degree ≤ 1) : P.derivative.degree ≤ 0:=by
 rw [Polynomial.degree_le_iff_coeff_zero]
 intro m hm
 rw [Polynomial.coeff_derivative]
 have qb : 0 < m:=by exact_mod_cast hm
 have hlt : (1 : WithBot ℕ) < (m+1:ℕ):=by
  norm_cast
  exact Nat.succ_lt_succ qb
 have qa:=(Polynomial.degree_le_iff_coeff_zero P 1).mp hP (m+1) hlt
 simp [qa]
theorem zr {P : Polynomial ℂ} (hP : P.degree ≤ 1) (z:ℂ) : Polynomial.eval z P.derivative=Polynomial.eval 0 P.derivative:=by
 have qa :
   P.derivative.degree ≤ 0 :=
  yO hP
 rw [Polynomial.eq_C_of_degree_le_zero qa]
 simp
end Polynomial
end
end
section
section
noncomputable section
open Complex
namespace Complex
noncomputable def uj (s:ℂ):ℂ :=
 (s*(s - 1)*completedRiemannZeta₀ s+1)/2
theorem W4 : uj 0=1/2:=by
 simp [uj]
theorem Wm : ∃ s:ℂ,uj s ≠ 0:=by
 refine ⟨0,?_⟩
 simp [W4]
theorem VB : Differentiable ℂ uj:=by
 exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const (1:ℂ)))).mul
  differentiable_completedZeta₀).add (differentiable_const (1:ℂ))).div_const 2
theorem v2 {s:ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) : uj s=s*(s - 1)*completedRiemannZeta s/2:=by
 rw [uj,completedRiemannZeta_eq]
 have qa : 1 - s ≠ 0:=sub_ne_zero.mpr (Ne.symm hs1)
 field_simp [hs0,qa]
 ring
theorem WA (s:ℂ) : uj (1 - s)=uj s:=by
 rw [uj,uj,completedRiemannZeta₀_one_sub]
 ring
end Complex
end
end
end
section
section
namespace Complex
lemma ZR {f:ℂ → ℂ} {R:ℝ} (qa : ContinuousOn f (Metric.closedBall (0:ℂ) R)) : ∃ M:ℝ,0 ≤ M ∧ ∀ z:ℂ,‖z‖ ≤ R → ‖f z‖ ≤ M:=by
 have qb : IsCompact (Metric.closedBall (0:ℂ) R):=isCompact_closedBall 0 R
 obtain ⟨M,hM⟩ := qb.exists_bound_of_continuousOn qa
 refine ⟨max M 0,le_max_right _ _,fun z hz => ?_⟩
 exact (hM z (Metric.mem_closedBall.mpr (by simpa using hz))).trans (le_max_left _ _)
theorem vC {z₀ : ℂ} {a:ℝ} (ha : a < z₀.re) : ∃ δ > 0,∀ (x y:ℂ),dist x z₀ < δ → dist y x < δ → a ≤ y.re:=by
 set δ : ℝ:=(z₀.re - a)/2 with hδdef
 have qh : 0 < z₀.re - a:=sub_pos.mpr ha
 have hδpos : 0 < δ := by simpa [hδdef] using half_pos qh
 refine ⟨δ,hδpos,?_⟩
 intro x y hx hy
 have qi : dist y z₀ ≤ dist y x+dist x z₀ := dist_triangle y x z₀
 have qf : dist y x+dist x z₀ < δ + δ := add_lt_add hy hx
 have qd : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt qi qf
 have qb : δ + δ = z₀.re - a:=by simp [hδdef,add_halves]
 have qa : ‖y - z₀‖ < z₀.re - a:=by simpa [qb] using qd
 have qe : a < z₀.re - ‖y - z₀‖ := by
  have qg : a + ‖y - z₀‖ < z₀.re:=by
   simpa [add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using
    (add_lt_add_left qa a)
  simpa [lt_sub_iff_add_lt] using qg
 have qc : -‖y - z₀‖ ≤ (y - z₀).re:=(abs_le.mp (abs_re_le_norm (y - z₀))).1
 have qj : z₀.re - ‖y - z₀‖ ≤ y.re:=by
  have h' : z₀.re+(-‖y - z₀‖) ≤ z₀.re+(y - z₀).re:=add_le_add_right qc z₀.re
  have h'' : z₀.re+(y - z₀).re=y.re:=by
   simp [sub_eq_add_neg]
  simpa [sub_eq_add_neg,h''] using h'
 exact le_of_lt (lt_of_lt_of_le qe qj)
end Complex
end
end
section
open Real Complex Set MeasureTheory
section
noncomputable section
namespace Real
namespace Gamma
theorem WD {x:ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) : Gamma x ≤ 1:=by
  have qb:=Real.convexOn_Gamma
  have h1 : Gamma 1=1:=Gamma_one
  have h2 : Gamma 2=1:=Gamma_two
  let t:=2 - x
  have qa : 0 ≤ t:=by linarith
  have qc : x=t*1+(1 - t)*2:=by field_simp [t]; ring
  have:=qb.2 (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 2)
    qa (by linarith : 0 ≤ 1 - t) (by ring : t+(1 - t)=1)
  rw [smul_eq_mul,smul_eq_mul] at this
  calc
    Gamma x=Gamma (t*1+(1 - t)*2):=by rw [qc]
    _ ≤ t*Gamma 1+(1 - t)*Gamma 2:=this
    _ = 1:=by rw [h1,h2]; ring
end Gamma
end Real
namespace Complex
namespace Gamma
theorem WK {z:ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re:=by
  rw [Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  have qa : ∀ t ∈ Set.Ioi (0:ℝ),
      ‖((-t).exp:ℂ)*(t:ℂ)^(z - 1)‖ = Real.exp (-t)*t^(z.re - 1):=by
    intro t ht
    have qb : ‖(t:ℂ)^(z - 1)‖ = t^(z.re - 1):=by
      simpa using norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [norm_exp,qb]
  calc
    ‖GammaIntegral z‖
        ≤ ∫ t in Set.Ioi (0:ℝ),‖((-t).exp:ℂ)*(t:ℂ)^(z - 1)‖ := by
          unfold GammaIntegral
          exact norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0:ℝ),Real.exp (-t)*t^(z.re - 1):=by
          exact setIntegral_congr_fun measurableSet_Ioi qa
theorem norm_le_one {z:ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) : ‖Gamma z‖ ≤ 1:=by
  have qa : 0 < z.re:=by linarith
  calc
    ‖Gamma z‖ ≤ Real.Gamma z.re:=WK qa
    _ ≤ 1:=Real.Gamma.WD hlo hhi
end Gamma
end Complex
end
end
end
section
section
open Complex
open scoped Topology BigOperators
namespace Stirling.GammaAux
lemma WQ {s:ℂ} {a:ℝ} (qa : 0 < a) (qb : a < s.re) : ‖s - a‖ ≤ ‖s‖ := by
  have qc : (s.re - a)^2 ≤ s.re^2:=by nlinarith
  have h1 : Complex.normSq (s - a) ≤ Complex.normSq s:=by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,
               Complex.sub_im,Complex.ofReal_im,sub_zero]
    linarith [sq_nonneg s.im]
  calc
    ‖s - a‖ = Real.sqrt (Complex.normSq (s - a)):=by
      rw [Complex.normSq_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq s):=Real.sqrt_le_sqrt h1
    _ = ‖s‖ := by
      rw [Complex.normSq_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
lemma ud {s:ℂ} {k:ℕ} (hk : (k:ℝ)+1 < s.re) : ‖s - 1 - k‖ ≤ ‖s‖ := by
 have qa : (0:ℝ) < 1+k:=by linarith
 have qb : (1:ℝ)+k < s.re:=by linarith
 simpa [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using
  WQ (s:=s) (a:=(1+k:ℝ)) qa qb
lemma WM {s:ℂ} {m:ℕ} (h : ∀ k < m,(k:ℝ)+1 < s.re) : ‖∏ k ∈ Finset.range m,(s - 1 - k)‖ ≤ ‖s‖ ^ m:=by
  calc ‖∏ k ∈ Finset.range m,(s - 1 - k)‖
      = ∏ k ∈ Finset.range m,‖s - 1 - k‖ := norm_prod _ _
    _ ≤ ∏ _k ∈ Finset.range m,‖s‖ := by
        apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
        intro k hk; exact ud (h k (Finset.mem_range.mp hk))
    _ = ‖s‖ ^ m:=by rw [Finset.prod_const,Finset.card_range]
lemma uc {s:ℂ} {n:ℕ} (hs : ∀ k < n,s - 1 - k ≠ 0) : Complex.Gamma s=Complex.Gamma (s - n) * ∏ k ∈ Finset.range n,(s - 1 - k):=by
  induction n with
  | zero => simp
  | succ m ih =>
    have qb : ∀ k < m,s - 1 - k ≠ 0:=fun k hk => hs k (Nat.lt_succ_of_lt hk)
    have qc : s - 1 - m ≠ 0:=hs m (Nat.lt_succ_self m)
    have qd : Complex.Gamma (s - m)=(s - m - 1)*Complex.Gamma (s - m - 1):=by
      have qf : s - ↑m - 1 ≠ 0:=by convert qc using 1; ring
      have:=Complex.Gamma_add_one (s - m - 1) qf
      simp only [sub_add_cancel] at this
      exact this
    have qe : s - ↑(m+1)=s - m - 1:=by simp only [Nat.cast_add,Nat.cast_one]; ring
    have qa : (s - m - 1) * ∏ k ∈ Finset.range m,(s - 1 - k) =
        ∏ k ∈ Finset.range (m+1),(s - 1 - k):=by
      rw [Finset.prod_range_succ]; ring
    calc
      Complex.Gamma s
          = Complex.Gamma (s - m) * ∏ k ∈ Finset.range m,(s - 1 - k):=ih qb
      _ = (s - m - 1)*Complex.Gamma (s - m - 1)
            * ∏ k ∈ Finset.range m,(s - 1 - k):=by
          rw [qd]
      _ = Complex.Gamma (s - m - 1) *
            ((s - m - 1) * ∏ k ∈ Finset.range m,(s - 1 - k)):=by
          ring
      _ = Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range (m+1),(s - 1 - k):=by
          rw [qa]
      _ = Complex.Gamma (s - ↑(m+1)) * ∏ k ∈ Finset.range (m+1),(s - 1 - k):=by
          rw [← qe]
end Stirling.GammaAux
end
end
section
section
noncomputable section
open Complex Real Set Metric
namespace Real.Stirling
lemma VV {x:ℝ} (hx : 1 ≤ x) : Real.log 2 ≤ Real.log (1+x):=by
 have h₂ : (0:ℝ) < 2:=by norm_num
 have hle : (2:ℝ) ≤ 1+x:=by linarith
 exact Real.log_le_log h₂ hle
lemma Y1 {x:ℝ} (hx : 1 ≤ x) : Real.log 2 ≤ x*Real.log (1+x):=by
 have qa : 0 < Real.log 2:=Real.log_pos (by norm_num : (1:ℝ) < 2)
 have qb:=VV hx
 have qc : x*Real.log 2 ≤ x*Real.log (1+x) :=
  mul_le_mul_of_nonneg_left qb (by linarith)
 have qd : Real.log 2 ≤ x*Real.log 2:=by
  simpa [one_mul] using mul_le_mul_of_nonneg_right hx qa.le
 exact le_trans qd qc
lemma w8 {x:ℝ} (hx : 1 ≤ x) : Real.log 3 ≤ (Real.log 3/Real.log 2)*Real.log (1+x):=by
 have qb : 0 < Real.log 2:=Real.log_pos (by norm_num : (1:ℝ) < 2)
 have qd : Real.log 2 ≠ 0:=ne_of_gt qb
 have qc : 0 < Real.log 3:=Real.log_pos (by norm_num : (1:ℝ) < 3)
 have qa : 0 ≤ Real.log 3/Real.log 2:=div_nonneg qc.le qb.le
 have qe :
   (Real.log 3/Real.log 2)*Real.log 2 ≤
    (Real.log 3/Real.log 2)*Real.log (1+x) :=
  mul_le_mul_of_nonneg_left (VV hx) qa
 simpa [div_mul_cancel₀ _ qd] using qe
noncomputable def VM:ℝ :=
 (3/2:ℝ)*(Real.log 3/Real.log 2+1)
lemma YE : 0 < VM:=by
 have qd : 0 < (3/2:ℝ):=by norm_num
 have qe : 0 < Real.log 3/Real.log 2+1:=by
  have qb : 0 < Real.log 2:=Real.log_pos (by norm_num : (1:ℝ) < 2)
  have qc : 0 < Real.log 3:=Real.log_pos (by norm_num : (1:ℝ) < 3)
  have qa : 0 ≤ Real.log 3/Real.log 2 :=
   div_nonneg qc.le qb.le
  linarith
 simpa [VM] using mul_pos qd qe
end Real.Stirling
namespace Complex.Gamma
open Real
lemma Yp {s:ℂ} (hs : 1 ≤ ‖s‖) : ‖s+1‖ ≤ 2 * ‖s‖ := by
 have h1 : ‖s+1‖ ≤ ‖s‖ + 1:=by simpa using norm_add_le s (1:ℂ)
 nlinarith [h1,hs]
lemma vc {s:ℂ} (hs : 1 ≤ ‖s‖) : ‖s/2+1‖ ≤ (3/2) * ‖s‖ := by
 have h1 : ‖s/2+1‖ ≤ ‖s/2‖ + 1:=by simpa using norm_add_le (s/2) (1:ℂ)
 have h1' : ‖s/2+1‖ ≤ ‖s‖ / 2+1:=by simpa using h1
 nlinarith [h1',hs]
lemma YI {s:ℂ} (hs : 1 ≤ ‖s‖) : Real.log (1 + ‖s+1‖) ≤ Real.log 2+Real.log (1 + ‖s‖):=by
 have qb : 0 < (1 + ‖s+1‖ : ℝ):=by linarith [norm_nonneg (s+1)]
 have hle : (1 + ‖s+1‖ : ℝ) ≤ 2*(1 + ‖s‖):=by
  have hn : ‖s+1‖ ≤ ‖s‖ + 1:=by simpa using norm_add_le s (1:ℂ)
  nlinarith [hn,hs]
 have qa : Real.log (1 + ‖s+1‖) ≤ Real.log (2*(1 + ‖s‖)) :=
  Real.log_le_log qb (by linarith)
 have qc : Real.log (2*(1 + ‖s‖))=Real.log 2+Real.log (1 + ‖s‖):=by
  have h2 : (2:ℝ) ≠ 0:=by norm_num
  have h1 : (1 + ‖s‖ : ℝ) ≠ 0:=by linarith [norm_nonneg s]
  simpa [mul_assoc] using Real.log_mul h2 h1
 simpa [qc] using qa
lemma ws {s:ℂ} (hs : 1 ≤ ‖s‖) : Real.log (1 + ‖s/2+1‖) ≤ Real.log 3+Real.log (1 + ‖s‖):=by
 have qb : 0 < (1 + ‖s/2+1‖ : ℝ):=by linarith [norm_nonneg (s/2+1)]
 have hle : (1 + ‖s/2+1‖ : ℝ) ≤ 3*(1 + ‖s‖):=by
  nlinarith [vc hs]
 have qa : Real.log (1 + ‖s/2+1‖) ≤ Real.log (3*(1 + ‖s‖)) :=
  Real.log_le_log qb (by linarith)
 have qc : Real.log (3*(1 + ‖s‖))=Real.log 3+Real.log (1 + ‖s‖):=by
  have h3 : (3:ℝ) ≠ 0:=by norm_num
  have h1 : (1 + ‖s‖ : ℝ) ≠ 0:=by linarith [norm_nonneg s]
  simpa [mul_assoc] using Real.log_mul h3 h1
 simpa [qc] using qa
lemma Zy {s:ℂ} (hs : 1 ≤ ‖s‖) : ‖s+1‖ * Real.log (1 + ‖s+1‖) ≤ 4*(‖s‖ * Real.log (1 + ‖s‖)):=by
  have qc:=Real.Stirling.VV hs
  have qa : Real.log (1 + ‖s+1‖) ≤ 2*Real.log (1 + ‖s‖):=by
    nlinarith [YI hs,qc]
  have qb : 0 ≤ Real.log (1 + ‖s+1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s+1)])
  calc
    ‖s+1‖ * Real.log (1 + ‖s+1‖)
        ≤ (2 * ‖s‖)*Real.log (1 + ‖s+1‖) :=
          mul_le_mul_of_nonneg_right (Yp hs) qb
    _ ≤ (2 * ‖s‖)*(2*Real.log (1 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left qa (by positivity)
    _ = 4*(‖s‖ * Real.log (1 + ‖s‖)):=by ring
lemma Yh {s:ℂ} (hs : 1 ≤ ‖s‖) : ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖) ≤ Real.Stirling.VM*(‖s‖ * Real.log (1 + ‖s‖)):=by
  have qa : 0 ≤ Real.log (1 + ‖s/2+1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s/2+1)])
  have qb :
      Real.log (1 + ‖s/2+1‖) ≤
        (Real.log 3/Real.log 2+1)*Real.log (1 + ‖s‖):=by
    nlinarith [ws hs,
      Real.Stirling.w8 hs]
  calc
    ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)
        ≤ ((3/2:ℝ) * ‖s‖)*Real.log (1 + ‖s/2+1‖) :=
          mul_le_mul_of_nonneg_right (vc hs) qa
    _ ≤ Real.Stirling.VM*(‖s‖ * Real.log (1 + ‖s‖)):=by
      have qc :
          ((3/2:ℝ) * ‖s‖)*Real.log (1 + ‖s/2+1‖) ≤
            ((3/2:ℝ) * ‖s‖)*((Real.log 3/Real.log 2+1)*Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left qb (by positivity)
      have hEq :
          ((3/2:ℝ) * ‖s‖)*((Real.log 3/Real.log 2+1)*Real.log (1 + ‖s‖)) =
            Real.Stirling.VM*(‖s‖ * Real.log (1 + ‖s‖)):=by
        simp [Real.Stirling.VM,mul_assoc,mul_left_comm,mul_comm]
      exact le_trans qc (by simp [hEq])
lemma vg {z:ℂ} (hz : z ≠ 0) (qd : (1/2:ℝ) ≤ ‖z‖) : ‖Gamma z‖ ≤ 2 * ‖Gamma (z+1)‖ := by
  have qe:=Gamma_add_one z hz
  have qa : ‖Gamma (z+1)‖ = ‖z‖ * ‖Gamma z‖ := by
    calc
      ‖Gamma (z+1)‖ = ‖z*Gamma z‖ := by simp [qe]
      _ = ‖z‖ * ‖Gamma z‖ := by simp
  have qc : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) qd
  have qf : ‖z‖ ≠ 0:=ne_of_gt qc
  have qg : 1 / ‖z‖ ≤ (2:ℝ):=by
    have qb : (0:ℝ) < (1/2:ℝ):=by norm_num
    simpa using one_div_le_one_div_of_le qb qd
  have : ‖Gamma z‖ = ‖Gamma (z+1)‖ / ‖z‖ := by
    calc
      ‖Gamma z‖ = (‖z‖ * ‖Gamma z‖) / ‖z‖ := by field_simp [qf]
      _ = ‖Gamma (z+1)‖ / ‖z‖ := by simp [qa]
  rw [this,div_eq_mul_inv]
  have :
      (‖Gamma (z+1)‖ : ℝ)*(1 / ‖z‖) ≤ ‖Gamma (z+1)‖ * 2 :=
    mul_le_mul_of_nonneg_left qg (norm_nonneg _)
  simpa [mul_assoc,mul_left_comm,mul_comm] using this
theorem Wh : ∃ C:ℝ,0 < C ∧ ∀ s:ℂ,1 ≤ s.re → ‖Gamma s‖ ≤ C*(1 + ‖s‖)^(‖s‖ + 1):=by
  refine ⟨1,by norm_num,?_⟩
  intro s hs_re
  classical
  by_cases hs_small : s.re < 2
  ·
    have hΓ : ‖Gamma s‖ ≤ 1:=Complex.Gamma.norm_le_one hs_re
      (le_of_lt hs_small)
    have qu : (1:ℝ) ≤ (1 + ‖s‖)^(‖s‖ + 1):=by
      have qr : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have qv : (0:ℝ) ≤ ‖s‖ + 1:=by linarith [norm_nonneg s]
      have h:=Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) qr qv
      simpa [Real.one_rpow] using h
    simpa [one_mul] using le_trans hΓ qu
  ·
    have qi : 2 ≤ s.re:=le_of_not_gt hs_small
    let m:ℕ := ⌊s.re⌋₊ - 1
    have qb : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor (by exact_mod_cast qi)
    have qe : (⌊s.re⌋₊ : ℝ) ≤ s.re:=Nat.floor_le (by linarith : (0:ℝ) ≤ s.re)
    have qf : s.re < (⌊s.re⌋₊ : ℝ)+1:=by
      simpa using (Nat.lt_floor_add_one s.re)
    have qs : (m:ℝ)=(⌊s.re⌋₊ : ℝ) - 1:=by
      have : (1:ℕ) ≤ ⌊s.re⌋₊ := by omega
      simp [m,Nat.cast_sub this,Nat.cast_one]
    have qp : 0 < m:=by simp [m]; omega
    have qm : 1 ≤ (s - (m:ℂ)).re:=by
      simp [sub_re,qs]
      linarith [qe]
    have qn : (s - (m:ℂ)).re < 2:=by
      simp [sub_re,qs]
      linarith [qf]
    have qj : ∀ k < m,(k:ℝ)+1 < s.re:=by
      intro k hk
      calc (k:ℝ)+1 ≤ (m:ℝ):=by exact_mod_cast (Nat.lt_iff_add_one_le.mp hk)
        _ = (⌊s.re⌋₊ : ℝ) - 1:=qs
        _ < (⌊s.re⌋₊ : ℝ):=by linarith
        _ ≤ s.re:=qe
    have WM :
        ‖∏ k ∈ Finset.range m,(s - 1 - (k:ℂ))‖ ≤ ‖s‖ ^ m:=by
      simpa using Stirling.GammaAux.WM (s:=s) (m:=m) qj
    have uc :
        Gamma s=Gamma (s - (m:ℂ)) * ∏ k ∈ Finset.range m,(s - 1 - (k:ℂ)):=by
      have qg : ∀ k < m,s - 1 - (k:ℂ) ≠ 0:=by
        intro k hk hk0
        have : (s - 1 - (k:ℂ)).re=0:=by simp [hk0]
        have hk' : (k:ℝ)+1 < s.re:=qj k hk
        simp [Complex.sub_re] at this
        linarith
      simpa using Stirling.GammaAux.uc (s:=s) (n:=m) qg
    have qa : ‖Gamma (s - (m:ℂ))‖ ≤ 1 :=
      Complex.Gamma.norm_le_one qm (le_of_lt qn)
    have hΓ_le_pow : ‖Gamma s‖ ≤ ‖s‖ ^ m:=by
      calc
        ‖Gamma s‖ =
            ‖Gamma (s - (m:ℂ)) * ∏ k ∈ Finset.range m,(s - 1 - (k:ℂ))‖ := by
              simp [uc]
        _ =
            ‖Gamma (s - (m:ℂ))‖ *
              ‖∏ k ∈ Finset.range m,(s - 1 - (k:ℂ))‖ := by
              simp
        _ ≤ 1 * ‖s‖ ^ m :=
            mul_le_mul qa WM (norm_nonneg _) (by norm_num)
        _ = ‖s‖ ^ m:=by ring
    have qh : (m:ℝ) ≤ ‖s‖ := by
      have qc : m ≤ ⌊s.re⌋₊ := Nat.sub_le _ _
      have qk : (m:ℝ) ≤ s.re:=by
        have qd : (⌊s.re⌋₊ : ℝ) ≤ s.re :=
          Nat.floor_le (by linarith : (0:ℝ) ≤ s.re)
        exact le_trans (by exact_mod_cast qc) qd
      exact le_trans qk (Complex.re_le_norm s)
    have qo : ‖s‖ ^ m ≤ (1 + ‖s‖)^(‖s‖ + 1):=by
      have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
      have hm0 : (0:ℝ) ≤ (m:ℝ):=by exact_mod_cast (Nat.cast_nonneg m)
      have ql : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have h1 : (‖s‖ : ℝ)^m=(‖s‖ : ℝ)^(m:ℝ):=by
        simp [Real.rpow_natCast]
      have h2 : (‖s‖ : ℝ)^(m:ℝ) ≤ (1 + ‖s‖)^(m:ℝ) :=
        Real.rpow_le_rpow hx0 ql hm0
      have qq : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have qt : (m:ℝ) ≤ ‖s‖ + 1:=by linarith [qh]
      have h3 : (1 + ‖s‖)^(m:ℝ) ≤ (1 + ‖s‖)^(‖s‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le qq qt
      calc
        ‖s‖ ^ m=(‖s‖ : ℝ)^(m:ℝ):=h1
        _ ≤ (1 + ‖s‖)^(m:ℝ):=h2
        _ ≤ (1 + ‖s‖)^(‖s‖ + 1):=h3
    have : ‖Gamma s‖ ≤ (1 + ‖s‖)^(‖s‖ + 1):=le_trans hΓ_le_pow qo
    simpa [one_mul] using this
theorem Vd : ∃ C:ℝ,0 < C ∧ ∀ s:ℂ,0 ≤ s.re → 1 ≤ ‖s‖ → ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
  classical
  rcases Wh with ⟨C₁,hC₁_pos,hC₁⟩
  have qi : 0 < Real.log 2:=by
    have : (1:ℝ) < 2:=by norm_num
    exact Real.log_pos this
  have qm : Real.log 2 ≠ 0:=ne_of_gt qi
  let K:ℝ := |Real.log C₁| + 1
  have qu : 0 < K:=by
    have : 0 ≤ |Real.log C₁| := abs_nonneg _
    linarith [K]
  have hC₁_exp : C₁ ≤ Real.exp K:=by
    have qJ : Real.log C₁ ≤ |Real.log C₁| + 1:=by
      have : Real.log C₁ ≤ |Real.log C₁| := le_abs_self _
      linarith
    have h:=Real.exp_le_exp.mpr qJ
    simpa [K,Real.exp_log hC₁_pos] using h
  let Cbase : ℝ:=K/Real.log 2+2
  have qg : 0 < Cbase:=by
    have qa : 0 ≤ K/Real.log 2:=div_nonneg qu.le qi.le
    linarith [Cbase,qa]
  let C : ℝ:=4*Cbase
  refine ⟨C,by nlinarith [qg],?_⟩
  have qe :
      ∀ z:ℂ,1 ≤ z.re →
        ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)):=by
    intro z hz_re
    have qp : (1:ℝ) ≤ ‖z‖ := le_trans hz_re (Complex.re_le_norm z)
    have qv : 0 < (1 + ‖z‖ : ℝ):=by linarith [norm_nonneg z]
    have qj : 0 ≤ Real.log (1 + ‖z‖):=Real.log_nonneg (by linarith [norm_nonneg z])
    have qb : Real.log 2 ≤ Real.log (1 + ‖z‖) :=
      Real.Stirling.VV qp
    have qn : Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖):=by
      have qw : ‖z‖ * Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left qb (by linarith)
      have qz : Real.log 2 ≤ ‖z‖ * Real.log 2:=by
        have:=mul_le_mul_of_nonneg_right qp qi.le
        simpa [one_mul] using this
      exact le_trans qz qw
    have qc : 0 ≤ K/Real.log 2:=div_nonneg qu.le qi.le
    have qq :
        (K/Real.log 2)*Real.log 2 ≤ (K/Real.log 2)*(‖z‖ * Real.log (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left qn qc
    have qA : K ≤ (K/Real.log 2)*(‖z‖ * Real.log (1 + ‖z‖)):=by
      have : (K/Real.log 2)*Real.log 2=K:=by field_simp [qm]
      simpa [this] using qq
    have qK :
        Real.log (1 + ‖z‖)*(‖z‖ + 1) ≤
          2*(‖z‖ * Real.log (1 + ‖z‖)):=by
      have qB : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith [qp]
      have qL :
          Real.log (1 + ‖z‖)*(‖z‖ + 1) ≤
            Real.log (1 + ‖z‖)*(2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left qB qj
      simpa [mul_assoc,mul_left_comm,mul_comm,two_mul] using qL
    have qC : ‖Gamma z‖ ≤ C₁ * (1 + ‖z‖)^(‖z‖ + 1):=hC₁ z hz_re
    have qd : 0 ≤ (1 + ‖z‖)^(‖z‖ + 1) :=
      Real.rpow_nonneg (by linarith [norm_nonneg z]) _
    have qL :
        C₁ * (1 + ‖z‖)^(‖z‖ + 1) ≤
          Real.exp K*(1 + ‖z‖)^(‖z‖ + 1) :=
      mul_le_mul_of_nonneg_right hC₁_exp qd
    have qD :
        (1 + ‖z‖)^(‖z‖ + 1) =
          Real.exp (Real.log (1 + ‖z‖)*(‖z‖ + 1)):=by
      simp [Real.rpow_def_of_pos qv,mul_comm]
    have qE :
        C₁ * (1 + ‖z‖)^(‖z‖ + 1) ≤
          Real.exp (K+Real.log (1 + ‖z‖)*(‖z‖ + 1)):=by
      calc
        C₁ * (1 + ‖z‖)^(‖z‖ + 1)
            ≤ Real.exp K*(1 + ‖z‖)^(‖z‖ + 1):=qL
        _ = Real.exp K*Real.exp (Real.log (1 + ‖z‖)*(‖z‖ + 1)):=by simp [qD]
        _ = Real.exp (K+Real.log (1 + ‖z‖)*(‖z‖ + 1)):=by
              simp [Real.exp_add]
    have qF :
        Real.exp (K+Real.log (1 + ‖z‖)*(‖z‖ + 1))
          ≤ Real.exp (Cbase*(‖z‖ * Real.log (1 + ‖z‖))):=by
      apply Real.exp_le_exp.mpr
      have qM :
          K+Real.log (1 + ‖z‖)*(‖z‖ + 1)
            ≤ (K/Real.log 2+2)*(‖z‖ * Real.log (1 + ‖z‖)):=by
        have qr : K ≤ (K/Real.log 2)*(‖z‖ * Real.log (1 + ‖z‖)):=by
          simpa [mul_assoc] using qA
        have qs :
            Real.log (1 + ‖z‖)*(‖z‖ + 1) ≤ 2*(‖z‖ * Real.log (1 + ‖z‖)):=qK
        have :
            K+Real.log (1 + ‖z‖)*(‖z‖ + 1) ≤
              (K/Real.log 2)*(‖z‖ * Real.log (1 + ‖z‖)) +
                2*(‖z‖ * Real.log (1 + ‖z‖)):=by
          nlinarith [qr,qs]
        simpa [Cbase,add_mul,mul_add,two_mul,mul_assoc,mul_left_comm,mul_comm] using this
      simpa [Cbase,mul_assoc] using qM
    have qG :
        Real.exp (Cbase*(‖z‖ * Real.log (1 + ‖z‖)))
          = Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)):=by ring_nf
    have : ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) :=
      le_trans qC (le_trans qE (le_trans qF (by simp [qG] )))
    simpa [mul_assoc] using this
  intro s hs_re hs_norm
  have hs0 : s ≠ 0:=(norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  by_cases hs_ge_one : 1 ≤ s.re
  · have h1:=qe s hs_ge_one
    have qf : 0 ≤ ‖s‖ * Real.log (1 + ‖s‖):=by
      have : 0 ≤ Real.log (1 + ‖s‖):=Real.log_nonneg (by linarith [norm_nonneg s])
      exact mul_nonneg (norm_nonneg _) this
    have qH : Cbase*(‖s‖ * Real.log (1 + ‖s‖)) ≤ C*(‖s‖ * Real.log (1 + ‖s‖)):=by
      have : Cbase ≤ C:=by simp [C,le_mul_of_one_le_left,qg.le]
      exact mul_le_mul_of_nonneg_right this qf
    have h2 : Real.exp (Cbase * ‖s‖ * Real.log (1 + ‖s‖))
        ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
      apply Real.exp_le_exp.mpr
      have qI : Cbase * ‖s‖ * Real.log (1 + ‖s‖)=Cbase*(‖s‖ * Real.log (1 + ‖s‖)):=by ring
      have qx : C * ‖s‖ * Real.log (1 + ‖s‖)=C*(‖s‖ * Real.log (1 + ‖s‖)):=by ring
      simpa [qI,qx] using qH
    exact le_trans h1 h2
  · have qk : s.re < 1:=lt_of_not_ge hs_ge_one
    have qo : ‖Gamma s‖ = ‖Gamma (s+1)‖ / ‖s‖ := by
      have h:=Complex.Gamma_add_one s hs0
      have hn : ‖Gamma (s+1)‖ = ‖s‖ * ‖Gamma s‖ := by
        calc
          ‖Gamma (s+1)‖ = ‖s*Gamma s‖ := by simp [h]
          _ = ‖s‖ * ‖Gamma s‖ := by simp
      have qh : ‖s‖ ≠ 0:=(norm_ne_zero_iff).2 hs0
      calc
        ‖Gamma s‖ = (‖s‖ * ‖Gamma s‖) / ‖s‖ := by field_simp [qh]
        _ = ‖Gamma (s+1)‖ / ‖s‖ := by simp [hn]
    have qN : ‖Gamma s‖ ≤ ‖Gamma (s+1)‖ := by
      rw [qo]
      exact div_le_self (norm_nonneg _) hs_norm
    have hs1 : (1:ℝ) ≤ (s+1).re:=by
      simp [Complex.add_re]
      linarith [hs_re]
    have hG1 : ‖Gamma (s+1)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
      have h0:=qe (s+1) hs1
      have qy:=Zy hs_norm
      have ql : 0 ≤ Cbase:=le_of_lt qg
      have qt :
          Cbase*(‖s+1‖ * Real.log (1 + ‖s+1‖)) ≤ C*(‖s‖ * Real.log (1 + ‖s‖)):=by
        calc
          Cbase*(‖s+1‖ * Real.log (1 + ‖s+1‖))
              ≤ Cbase*(4*(‖s‖ * Real.log (1 + ‖s‖))):=by
                    exact mul_le_mul_of_nonneg_left qy ql
          _ = C*(‖s‖ * Real.log (1 + ‖s‖)):=by simp [C,mul_assoc,mul_left_comm,mul_comm]
      have h0' :
          Cbase * ‖s+1‖ * Real.log (1 + ‖s+1‖) =
            Cbase*(‖s+1‖ * Real.log (1 + ‖s+1‖)):=by
        ring
      have h1' :
          C * ‖s‖ * Real.log (1 + ‖s‖) =
            C*(‖s‖ * Real.log (1 + ‖s‖)):=by
        ring
      exact le_trans h0 (by
        apply Real.exp_le_exp.mpr
        simpa [h0',h1'] using qt)
    exact le_trans qN hG1
theorem V5 : ∃ C:ℝ,0 < C ∧ ∀ s:ℂ,0 ≤ s.re → 1 ≤ ‖s‖ → ‖Gamma (s/2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
  classical
  rcases Vd with ⟨C₀,hC₀_pos,hC₀⟩
  let A : ℝ:=Real.Stirling.VM
  have qi:=Real.Stirling.YE
  let C : ℝ:=1+C₀ * A
  refine ⟨C,by nlinarith [hC₀_pos,qi],?_⟩
  intro s hs_re hs_norm
  have hs0 : s ≠ 0:=(norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  have qd : s/2 ≠ 0:=div_ne_zero hs0 (by norm_num : (2:ℂ) ≠ 0)
  have qj : (1/2:ℝ) ≤ ‖s/2‖ := by
    simpa using (show (1/2:ℝ) ≤ ‖s‖ / 2 by nlinarith)
  have qo:=vg qd qj
  have qk : 0 ≤ (s/2+1).re:=by simp [Complex.add_re]; linarith
  have qe : (1:ℝ) ≤ ‖s/2+1‖ := by
    have : (1:ℝ) ≤ (s/2+1).re:=by simp [Complex.add_re]; linarith
    exact le_trans this (Complex.re_le_norm (s/2+1))
  have hΓz :
      ‖Gamma (s/2+1)‖ ≤
        Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)) :=
    hC₀ (s/2+1) qk qe
  have qf :
      ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖) ≤ A*(‖s‖ * Real.log (1 + ‖s‖)):=by
    simpa [A] using Yh hs_norm
  have qa:=Real.Stirling.Y1 hs_norm
  have ql :
      ‖Gamma (s/2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
    have qp :
        ‖Gamma (s/2)‖ ≤
          2*Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)) :=
      le_trans qo (mul_le_mul_of_nonneg_left hΓz (by norm_num))
    have qm :
        2*Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖))
          = Real.exp (Real.log 2+C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)):=by
      have qq : Real.exp (Real.log 2)=(2:ℝ):=by
        have : (0:ℝ) < 2:=by norm_num
        simp [Real.exp_log this]
      calc
        2*Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖))
            = Real.exp (Real.log 2) *
                Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)):=by
                simp [qq,mul_assoc]
        _ = Real.exp (Real.log 2+C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)):=by
              simp [Real.exp_add]
    refine le_trans qp (by
      have qg :
          Real.log 2+C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)
            ≤ C*(‖s‖ * Real.log (1 + ‖s‖)):=by
        have qb : 0 ≤ C₀ := le_of_lt hC₀_pos
        have qh :
            C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖) ≤
              (C₀ * A)*(‖s‖ * Real.log (1 + ‖s‖)):=by
          have:=mul_le_mul_of_nonneg_left qf qb
          simpa [mul_assoc,mul_left_comm,mul_comm] using this
        have qc : Real.log 2 ≤ 1*(‖s‖ * Real.log (1 + ‖s‖)):=by
          simpa using qa
        nlinarith [qh,qc,C]
      have qn :
          Real.exp (Real.log 2+C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖))
            ≤ Real.exp (C*(‖s‖ * Real.log (1 + ‖s‖))) :=
        Real.exp_le_exp.mpr qg
      have :
          2*Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖))
            ≤ Real.exp (C*(‖s‖ * Real.log (1 + ‖s‖))):=by
        calc
          2*Real.exp (C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖))
              = Real.exp (Real.log 2+C₀ * ‖s/2+1‖ * Real.log (1 + ‖s/2+1‖)):=qm
          _ ≤ Real.exp (C*(‖s‖ * Real.log (1 + ‖s‖))):=qn
      simpa [mul_assoc] using this)
  simpa [mul_assoc] using ql
end Complex.Gamma
namespace Complex.Gammaℝ.Stirling
open Real
lemma Yt {s:ℂ} (hs : 0 ≤ s.re) : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1:=by
  have qb : (0:ℝ) < Real.pi:=Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos qb]
  have qd : (-s/2).re = -s.re/2:=by simp [Complex.neg_re]
  rw [qd]
  have qc : -s.re/2 ≤ 0:=by linarith
  have qa : (1:ℝ) < Real.pi:=by
    calc (1:ℝ) < 3:=by norm_num
      _ < Real.pi:=Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt qa) qc
theorem WP : ∃ C:ℝ,0 < C ∧ ∀ s:ℂ,0 ≤ s.re → 1 ≤ ‖s‖ → ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)):=by
  obtain ⟨C₁,hC₁_pos,hC₁⟩ := Complex.Gamma.V5
  refine ⟨C₁ + 2,by linarith,?_⟩
  intro s hs_re hs_norm
  have qd : Complex.Gammaℝ s=(Real.pi:ℂ)^(-s/2)*Complex.Gamma (s/2):=by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s/2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1:=Yt hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi:ℂ)^(-s/2)‖ * ‖Complex.Gamma (s/2)‖ := by
    rw [qd]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi:ℂ)^(-s/2)‖ * ‖Complex.Gamma (s/2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)):=by
    calc ‖(Real.pi:ℂ)^(-s/2)‖ * ‖Complex.Gamma (s/2)‖
        ≤ 1 * ‖Complex.Gamma (s/2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s/2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)):=hΓ
  have qb : 0 ≤ Real.log (1 + ‖s‖):=Real.log_nonneg (by linarith [norm_nonneg s])
  have qa : 0 ≤ ‖s‖ := norm_nonneg _
  have qc : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖):=by
    apply mul_le_mul_of_nonneg_right _ qb
    apply mul_le_mul_of_nonneg_right _ qa
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr qc)
end Complex.Gammaℝ.Stirling
end
end
end
section
section
namespace Real
theorem vd {ε : ℝ} (hε : 0 < ε) {u:ℝ} (hu : 1 < u) : Real.log u*u^(-1 - ε) ≤ (2 / ε)*u^(-1 - ε / 2):=by
  have hu0 : 0 < u:=lt_trans zero_lt_one hu
  have hεne : ε ≠ 0:=ne_of_gt hε
  have qa : 0 < 2 / ε := by
    simpa [one_div,div_eq_mul_inv] using mul_pos (by norm_num : (0:ℝ) < 2) (inv_pos.mpr hε)
  have qe : (ε / 2)*Real.log u ≤ Real.exp ((ε / 2)*Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2)*Real.log u))
  have qb : Real.log u ≤ (2 / ε)*Real.exp ((ε / 2)*Real.log u):=by
    calc
      Real.log u=(2 / ε)*((ε / 2)*Real.log u):=by field_simp [hεne]
      _ ≤ (2 / ε)*Real.exp ((ε / 2)*Real.log u) :=
        mul_le_mul_of_nonneg_left qe (le_of_lt qa)
  have qc : Real.exp ((ε / 2)*Real.log u)=u^(ε / 2):=by
    simp [Real.rpow_def_of_pos hu0,mul_comm]
  have qf : Real.log u*u^(-1 - ε) ≤ ((2 / ε)*u^(ε / 2))*u^(-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [qc] using qb)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have qd : u^(ε / 2)*u^(-1 - ε)=u^(-1 - ε / 2):=by
    rw [← Real.rpow_add hu0,show ε / 2+(-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u*u^(-1 - ε)
        ≤ ((2 / ε)*u^(ε / 2))*u^(-1 - ε):=qf
    _ = (2 / ε)*u^(-1 - ε / 2):=by rw [mul_assoc,qd]
end Real
namespace Complex
theorem Vu (z:ℂ) {p:ℝ} (hp : 0 ≤ p) : (1:ℝ) ≤ (1 + ‖z‖)^p :=
 Real.one_le_rpow (by linarith [norm_nonneg z]) hp
end Complex
end
end
section
section
open scoped BigOperators Topology
open Complex Filter Real Set
namespace Nat.Primes
end Nat.Primes
section RiemannZetaEulerProduct
end RiemannZetaEulerProduct
theorem wj (s:ℂ) (hs : s ≠ 0) (n:ℕ) : 1/(n:ℂ)^s=if n=0 then 0 else (n:ℂ)^(-s):=by
  by_cases h : n=0
  · simp [h,Complex.zero_cpow hs]
  · simp [h,one_div,Complex.cpow_neg]
end
end
section
section
namespace Complex
theorem yn (a:ℝ) (p:ℂ) (hp : a < p.re) : IsPathConnected ({z:ℂ | a < z.re} \ ({p} : Set ℂ)):=by
  classical
  let S1 : Set ℂ:={z:ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ:={z:ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ:={z:ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ:={z:ℂ | p.re < z.re}
  have qf : Convex ℝ S1:=by
    have h1 : Convex ℝ {z:ℂ | a < z.re}:=convex_halfSpace_re_gt (r:=a)
    have h2 : Convex ℝ {z:ℂ | z.im < p.im}:=convex_halfSpace_im_lt (r:=p.im)
    simpa [S1,Set.setOf_and] using h1.inter h2
  have qg : Convex ℝ S2:=by
    have h1 : Convex ℝ {z:ℂ | a < z.re}:=convex_halfSpace_re_gt (r:=a)
    have h2 : Convex ℝ {z:ℂ | z.re < p.re}:=convex_halfSpace_re_lt (r:=p.re)
    simpa [S2,Set.setOf_and] using h1.inter h2
  have qh : Convex ℝ S3:=by
    have h1 : Convex ℝ {z:ℂ | a < z.re}:=convex_halfSpace_re_gt (r:=a)
    have h2 : Convex ℝ {z:ℂ | p.im < z.im}:=convex_halfSpace_im_gt (r:=p.im)
    simpa [S3,Set.setOf_and] using h1.inter h2
  have qi : Convex ℝ S4:=by
    simpa [S4] using (convex_halfSpace_re_gt (r:=p.re))
  have ql : S1.Nonempty:=by
    refine ⟨((max a p.re)+1:ℝ)+(p.im - 1)*Complex.I,?_⟩
    have h1 : a < (max a p.re)+1:=by
      have : a ≤ max a p.re:=le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im:=by linarith
    simpa [S1,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
      using And.intro h1 h2
  have qm : S2.Nonempty:=by
    refine ⟨((a+p.re)/2:ℝ)+(p.im:ℝ)*Complex.I,?_⟩
    have h1 : a < (a+p.re)/2:=by linarith
    have h2 : (a+p.re)/2 < p.re:=by linarith
    simpa [S2,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
      using And.intro h1 h2
  have qn : S3.Nonempty:=by
    refine ⟨((max a p.re)+1:ℝ)+(p.im+1)*Complex.I,?_⟩
    have h1 : a < (max a p.re)+1:=by
      have : a ≤ max a p.re:=le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im+1):=by linarith
    simpa [S3,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
      using And.intro h1 h2
  have qo : S4.Nonempty:=by
    refine ⟨(p.re+1:ℝ)+(0:ℝ)*Complex.I,?_⟩
    have : p.re < p.re+1:=by linarith
    simp [S4,Complex.add_re]
  have qp : IsPathConnected S1:=(qf.isPathConnected ql)
  have qq : IsPathConnected S2:=(qg.isPathConnected qm)
  have qr : IsPathConnected S3:=(qh.isPathConnected qn)
  have qs : IsPathConnected S4:=(qi.isPathConnected qo)
  let A : Set ℂ:=S1 ∪ S2
  let B : Set ℂ:=S3 ∪ S4
  have qa : (S1 ∩ S2).Nonempty:=by
    refine ⟨((a+p.re)/2:ℝ)+(p.im - (1/2))*Complex.I,?_⟩
    have h1a : a < (a+p.re)/2:=by linarith
    have h1b : (p.im - (1/2)) < p.im:=by linarith
    have h2a : a < (a+p.re)/2:=by linarith
    have h2b : (a+p.re)/2 < p.re:=by linarith
    constructor
    · simpa [S1,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
        using And.intro h2a h2b
  have qv : IsPathConnected A :=
    IsPathConnected.union (U:=S1) (V:=S2) qp qq (by
      rcases qa with ⟨z,hz⟩; exact ⟨z,hz⟩)
  have qb : (S3 ∩ S4).Nonempty:=by
    refine ⟨(p.re+1:ℝ)+(p.im+1)*Complex.I,?_⟩
    have h3a : a < p.re+1:=lt_trans hp (by linarith)
    have h3b : p.im < p.im+1:=by linarith
    have h4 : p.re < p.re+1:=by linarith
    constructor
    · simpa [S3,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4,Complex.add_re,Complex.mul_re]
  have qw : IsPathConnected B :=
    IsPathConnected.union (U:=S3) (V:=S4) qr qs (by
      rcases qb with ⟨z,hz⟩; exact ⟨z,hz⟩)
  have qj : (A ∩ B).Nonempty:=by
    refine ⟨(p.re+1:ℝ)+(p.im - 1)*Complex.I,?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re+1:=lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im:=by linarith
      simpa [S1,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re+1:=by linarith
      simp [S4,Complex.add_re,Complex.mul_re]
  have qc : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U:=A) (V:=B) qv qw (by
      rcases qj with ⟨z,hz⟩; exact ⟨z,hz⟩)
  have qk : ({z:ℂ | a < z.re} \ ({p} : Set ℂ))=A ∪ B:=by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH,hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH,hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH,himlt⟩)
        · have qt : z=p:=by
            have qd : (z.re:ℂ)+(z.im:ℝ)*Complex.I=z:=by simp
            have qe : (p.re:ℂ)+(p.im:ℝ)*Complex.I=p:=by simp
            have : (z.re:ℂ)+(z.im:ℝ)*Complex.I=(p.re:ℂ)+(p.im:ℝ)*Complex.I:=by
              simp [heq,himeq]
            simpa [qd,qe] using this
          have : z ∈ ({p} : Set ℂ):=by simp [Set.mem_singleton_iff,qt]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH,himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re:=by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have qu : z ≠ p:=by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im=p.im:=by simp [h]
            have : z.im < z.im:=by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re=p.re:=by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im=z.im:=by simp [h]
            have : z.im < z.im:=by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re=z.re:=by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact qu (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [qk] using qc
end Complex
end
end
section
section
namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ) (hf : AEStronglyMeasurable f (μ.restrict s)) (h : ∀ᵐ x ∂μ.restrict s,‖f x‖ ≤ g x) : IntegrableOn f s μ := by
 exact Integrable.mono' hg hf h
end MeasureTheory
end
end
section
section
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology
theorem intervalIntegral.wT {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (f:ℝ → E) (g:ℝ → ℝ) (c:ℝ)
  (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
  (qa : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c),‖f u‖ ≤ g u)
  (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
  Tendsto (fun N:ℕ => ∫ u in c..N,f u) atTop (𝓝 (∫ u in Ioi c,f u)) :=
 intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm qa)
  tendsto_natCast_atTop_atTop
theorem ZL {s:ℂ} (hs : 0 < s.re) : ∫ u in Ioi (1:ℝ),u^(-s.re - 1)=1/s.re:=by
  have ha : (-s.re - 1) < -1:=by linarith
  have hc : 0 < (1:ℝ):=zero_lt_one
  have h:=integral_Ioi_rpow_of_lt (a:=(-s.re - 1)) ha (c:=(1:ℝ)) hc
  have h' : ∫ u in Ioi (1:ℝ),u^(-s.re - 1) = - (1:ℝ)^(-s.re)/(-s.re):=by
    simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h
  calc
    ∫ u in Ioi (1:ℝ),u^(-s.re - 1)
        = - (1:ℝ)^(-s.re)/(-s.re):=h'
    _ = - (1:ℝ)/(-s.re):=by simp [Real.one_rpow]
    _ = 1/s.re:=by simp
end
end
section
section
namespace Int
variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]
theorem WR (a : R) : |fract a| ≤ 1:=by
 rw [abs_fract]
 exact (fract_lt_one a).le
end Int
end
end
section
section
namespace Complex
theorem VD {r:ℂ} {a b:ℝ} (ha : 0 < a) :
  ContinuousOn (fun u:ℝ => (u:ℂ)^r) (Set.Icc a b) :=
 (continuous_ofReal.continuousOn.cpow continuousOn_const
  (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl
theorem Wa (s:ℂ) {x:ℝ} (hx : 0 < x) : deriv (fun (t:ℝ) => (t:ℂ)^(-s)) x = -s*(x:ℂ)^(-s - 1):=by
  by_cases hs : s=0
  · simp [hs,deriv_const,cpow_zero,sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)
theorem wX (s:ℂ) {a b:ℝ} (ha : 0 < a) :
  ContinuousOn (deriv (fun (t:ℝ) => (t:ℂ)^(-s))) (Set.Icc a b) :=
  ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s:ℂ)) (Set.Icc a b)).mul
   (VD (r := -s - 1) ha)).congr fun _ ht =>
  Wa s (lt_of_lt_of_le ha ht.1)
theorem Zu (s:ℂ) {u:ℝ} (hu : 0 < u) : (u:ℂ)*(u:ℂ)^(-s - 1)=(u:ℂ)^(-s):=by
  have hx : (u:ℂ) ≠ 0:=ofReal_ne_zero.mpr hu.ne'
  calc
    (u:ℂ)*(u:ℂ)^(-s - 1)=(u:ℂ)^(1:ℂ)*(u:ℂ)^(-s - 1):=by simp [cpow_one]
    _ = (u:ℂ)^(-s):=by rw [← cpow_add _ _ hx]; ring_nf
theorem we (N:ℕ) (s:ℂ) (hN : N ≠ 0) : (N:ℂ)*(N:ℂ)^(-s)=(N:ℂ)^(1 - s):=by
  have hN' : (N:ℂ) ≠ 0:=Nat.cast_ne_zero.mpr hN
  calc
    (N:ℂ)*(N:ℂ)^(-s)=(N:ℂ)^(1:ℂ)*(N:ℂ)^(-s):=by simp [cpow_one]
    _ = (N:ℂ)^(1 - s):=by rw [← cpow_add _ _ hN']; ring_nf
theorem HasDerivAt.Zi (a:ℂ) {u:ℝ} (hu : 0 < u) (z:ℂ) : HasDerivAt (fun w => a*(u:ℂ)^(-w - 1)) (-a*(Complex.log u)*(u:ℂ)^(-z - 1)) z:=by
 set huC : (u:ℂ) ≠ 0:=ofReal_ne_zero.mpr hu.ne'
 have hf : HasDerivAt (fun w => -w - 1) (-1) z:=by
  simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using
   (hasDerivAt_id z).neg.sub_const (1:ℂ)
 have qb : HasDerivAt (fun w => (u:ℂ)^(-w - 1))
   ((u:ℂ)^(-z - 1)*Complex.log (u:ℂ)*(-1)) z :=
  HasDerivAt.const_cpow (c:=(u:ℂ)) hf (Or.inl huC)
 have qa : HasDerivAt (fun w => (u:ℂ)^(-w - 1))
   (-(Complex.log (u:ℂ))*(u:ℂ)^(-z - 1)) z:=by
  simpa [mul_comm,mul_left_comm,mul_assoc] using qb
 have qc : (Real.log u:ℂ)=Complex.log (u:ℂ):=by
  simpa using (ofReal_log (x:=u) (hx:=le_of_lt hu))
 simpa [qc,mul_comm,mul_left_comm,mul_assoc] using qa.const_mul a
end Complex
end
end
section
section
open Set MeasureTheory
namespace intervalIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {μ : Measure ℝ}
theorem Vj {a b:ℝ} (hab : a ≤ b) (h : ∀ u ∈ Ioc a b,f u=g u) : ∫ u in a..b,f u ∂μ = ∫ u in a..b,g u ∂μ := by
  refine integral_congr_ae' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) <;>
    intro u hu
  · exact h u hu
  · have qa : Ioc b a = ∅ := Ioc_eq_empty hab.not_gt
    exact (qa ▸ hu).elim
end intervalIntegral
end
end
section
section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex
noncomputable def Wu (s:ℂ) (u:ℝ):ℂ :=
 ((Int.fract u:ℝ):ℂ)*(u:ℂ)^(-s - 1)
theorem YM (u:ℝ) (hu : 1 ≤ u) (s:ℂ) : ‖Wu s u‖ ≤ u^(-s.re - 1):=by
  have hu0 : 0 < u:=one_pos.trans_le hu
  have qa : ‖((Int.fract u:ℝ):ℂ)‖ ≤ 1:=by simpa using Int.WR u
  have hle : ‖Wu s u‖ ≤ ‖(u:ℂ)^(-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u:ℝ):ℂ)‖ * ‖(u:ℂ)^(-s - 1)‖ := by rw [Wu,norm_mul]
      _ ≤ 1 * ‖(u:ℂ)^(-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right qa (norm_nonneg _)
      _ = ‖(u:ℂ)^(-s - 1)‖ := one_mul _
  have hb : ‖(u:ℂ)^(-s - 1)‖ = u^(-s.re - 1):=by
    have hre : (-s - 1).re = -s.re - 1:=by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb
namespace ZetaAbelFractKernel
lemma aestronglyMeasurable (s:ℂ) (S : Set ℝ) (_ : MeasurableSet S) : AEStronglyMeasurable (fun u => Wu s u) (volume.restrict S):=by
 refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
 simpa using Complex.measurable_ofReal.pow_const (-s - 1)
lemma ug (s:ℂ) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1:ℝ))),
   ‖Wu s u‖ ≤ u^(-s.re - 1) :=
 ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
  YM u (le_of_lt hu) s
lemma intervalIntegrable (s:ℂ) {a b:ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable (fun u => Wu s u) volume a b:=by
 let μ := volume.restrict (Icc a b)
 set g:ℝ → ℝ:=fun u => ‖(u:ℂ)^(-s - 1)‖
 have qb:=aestronglyMeasurable s (Icc a b) measurableSet_Icc
 have qa : ∀ᵐ u ∂μ,‖Wu s u‖ ≤ g u:=by
  refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
  intro u huIcc
  have hu0 : 0 < u:=lt_of_lt_of_le one_pos (ha.trans huIcc.1)
  have qc : g u=u^(-s.re - 1):=by
   simp [g,Complex.norm_cpow_eq_rpow_re_of_pos hu0,sub_eq_add_neg]
  exact (YM u (ha.trans huIcc.1) s).trans (le_of_eq qc.symm)
 have hg : Integrable g μ := by
  simpa [μ,g] using!
   (Complex.VD (ha:=one_pos.trans_le ha)).norm.integrableOn_compact
    isCompact_Icc
 have hf0 : Integrable (fun _ : ℝ => (0:ℂ)) μ := by simp [μ]
 exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
  integrable_of_norm_sub_le qb hf0 hg
   (qa.mono fun u hu => by simpa [sub_eq_add_neg,μ,g] using hu)
theorem Wl (s:ℂ) (hs : 1 < s.re) :
  Tendsto (fun N:ℕ => ∫ u in (1:ℝ)..N,Wu s u) atTop
   (𝓝 (∫ u in Ioi (1:ℝ),Wu s u)) :=
 intervalIntegral.wT (f:=fun u => Wu s u)
  (g:=fun u => u^(-s.re - 1)) 1
  (aestronglyMeasurable s (Ioi (1:ℝ)) measurableSet_Ioi) (ug s)
  (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
theorem WI (s:ℂ) (hs : 0 < s.re) : Integrable (fun u => Wu s u) (volume.restrict (Ioi (1:ℝ))):=by
 set ε : ℝ:=s.re/2
 set g:ℝ → ℝ:=fun u => u^(-1 - ε)
 have hfm:=aestronglyMeasurable s (Ioi (1:ℝ)) measurableSet_Ioi
 have hε : 0 < ε := half_pos hs
 have hεle : ε ≤ s.re:=half_le_self (le_of_lt hs)
 have qa : ∀ᵐ u ∂(volume.restrict (Ioi (1:ℝ))),‖Wu s u‖ ≤ g u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
   (YM u (le_of_lt hu) s).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
 simpa [IntegrableOn] using
  IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm qa
lemma Zz (z:ℂ) : AEStronglyMeasurable (fun u:ℝ => -((Real.log u):ℂ)*Wu z u) (volume.restrict (Ioi (1:ℝ))):=by
 have qa : Measurable (fun u:ℝ => Wu z u) :=
  (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
 simpa only [neg_mul] using
  (Real.measurable_log.complex_ofReal.fun_mul qa).fun_neg.aestronglyMeasurable
lemma v1 (s:ℂ) :
  ∀ᶠ z in 𝓝 s,
   AEStronglyMeasurable (fun u:ℝ => Wu z u) (volume.restrict (Ioi (1:ℝ))) :=
 Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1:ℝ)) measurableSet_Ioi
theorem Wr (u:ℝ) (hu : 1 < u) (z:ℂ) : HasDerivAt (fun w => Wu w u) (-((Real.log u):ℂ)*Wu z u) z:=by
 have h:=HasDerivAt.Zi ((Int.fract u:ℝ):ℂ)
  (lt_trans zero_lt_one hu) z
 have qa : (fun w => Wu w u)=fun w => ((Int.fract u:ℝ):ℂ)*(u:ℂ)^(-w - 1):=by
  ext w; simp [Wu]
 exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq qa)).congr_deriv (by
  simp [Wu,Complex.ofReal_log (x:=u) (hx:=le_of_lt (lt_trans zero_lt_one hu)),
   mul_comm,mul_assoc,mul_left_comm])
theorem ZN (ε : ℝ) (u:ℝ) (hu : 1 < u) (x:ℂ) (hx : ε ≤ x.re) : ‖-((Real.log u):ℂ)*Wu x u‖ ≤ Real.log u*u^(-1 - ε):=by
  have hu1 : (1:ℝ) ≤ u:=le_of_lt hu
  have qc : ‖Wu x u‖ ≤ u^(-1 - ε) :=
    (YM u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have qa : ‖-((Real.log u):ℂ)‖ = Real.log u:=by
    have qb : 0 ≤ Real.log u:=le_of_lt (Real.log_pos hu)
    simp [norm_neg,Complex.norm_real,abs_of_nonneg qb]
  calc
    ‖-((Real.log u):ℂ)*Wu x u‖
        = Real.log u * ‖Wu x u‖ := by rw [norm_mul,qa]
    _ ≤ Real.log u*u^(-1 - ε):=mul_le_mul_of_nonneg_left qc (le_of_lt (Real.log_pos hu))
private lemma WJ {p:ℝ → Prop} (h : ∀ u ∈ Ioi (1:ℝ),p u) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1:ℝ))),p u :=
 ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)
private lemma Vz {z s:ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
  dist z s < δ :=
 lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)
lemma vy (F F':ℂ → ℝ → ℂ) (s:ℂ) (δ : ℝ) (hδ : 0 < δ) (qe : ∀ᶠ z in 𝓝 s,AEStronglyMeasurable (F z) (volume.restrict (Ioi (1:ℝ)))) (qf : Integrable (F s) (volume.restrict (Ioi (1:ℝ)))) (qb : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1:ℝ)))) (bound:ℝ → ℝ) (qa : Integrable bound (volume.restrict (Ioi (1:ℝ)))) (qc : ∀ᵐ u ∂(volume.restrict (Ioi (1:ℝ))),∀ z ∈ Metric.ball s δ,‖F' z u‖ ≤ bound u) (qd : ∀ᵐ u ∂(volume.restrict (Ioi (1:ℝ))),∀ z ∈ Metric.ball s δ,HasDerivAt (fun w => F w u) (F' z u) z) : HasDerivAt (fun z => ∫ u in Ioi (1:ℝ),F z u) (∫ u in Ioi (1:ℝ),F' s u) s:=by
 have h :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (μ := volume.restrict (Ioi (1:ℝ))) (F:=F) (F':=F') (x₀ := s)
   (s:=Metric.ball s δ) (bound:=bound) (Metric.ball_mem_nhds s hδ)
   (hF_meas:=qe) (hF_int:=qf) (hF'_meas:=qb)
   (h_bound:=qc) (bound_integrable:=qa) (h_diff:=qd)
 rcases h with ⟨_,hDeriv⟩
 exact hDeriv
theorem WB (s:ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (fun z => ∫ u in Ioi (1:ℝ),Wu z u) s:=by
 set ε : ℝ:=s.re/2
 have hεpos : 0 < ε := half_pos hs
 obtain ⟨δ,hδpos,hδprop⟩ :=
  Complex.vC (z₀ := s) (a := ε) (half_lt_self hs)
 set F:ℂ → ℝ → ℂ:=Wu
 set F':ℂ → ℝ → ℂ:=fun z u => -((Real.log u):ℂ)*F z u
 set bound:ℝ → ℝ:=fun u => (2 / ε)*u^(-1 - ε / 2)
 have qa : Integrable bound (volume.restrict (Ioi (1:ℝ))):=by
  simpa [bound,IntegrableOn] using
   (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
 have qb : ∀ᶠ z in 𝓝 s,DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1:ℝ),F z0 u) z:=by
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
  intro z hz
  set δ':ℝ := δ / 2
  have qc : dist z s < δ := Vz hz hδpos
  have hRe : ∀ y ∈ Metric.ball z δ',ε ≤ y.re:=fun y hy =>
   hδprop z y qc (Vz hy hδpos)
  have qd : ε ≤ z.re:=hδprop s z (by simpa [dist_self] using hδpos) qc
  exact (vy F F' z δ' (half_pos hδpos)
   (v1 z)
   (by simpa using WI z (lt_of_lt_of_le hεpos qd))
   (by simpa [F,F'] using Zz z)
   bound qa
   (WJ fun u hu w hw =>
    (ZN ε u hu w (hRe w hw)).trans
     (by simpa [bound] using Real.vd hεpos hu))
   (WJ fun u hu w hw => by simpa [F,F'] using Wr u hu w)).differentiableAt
 exact (Complex.analyticAt_iff_eventually_differentiableAt
  (f:=fun z => ∫ u in Ioi (1:ℝ),Wu z u)).2 qb
end ZetaAbelFractKernel
end
end
section
section
open Finset
open scoped BigOperators
variable {𝕜 : Type*} [AddCommGroup 𝕜]
theorem _root_.Finset.Vh {N:ℕ} (f:ℕ → 𝕜) : ∑ k ∈ Icc 1 N,f k = ∑ n ∈ range N,f (n+1):=by
  symm
  refine sum_bij (s:=range N) (t:=Icc 1 N)
    (f:=fun n => f (n+1)) (g:=fun k => f k)
    (i:=fun n _ => n+1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N:=mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n),Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1,hk2⟩
    refine ⟨k - 1,mem_range.mpr ?_,?_⟩
    · have qa : (k - 1)+1=k:=Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [qa] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl
theorem _root_.Finset.YS {N:ℕ} {f:ℕ → 𝕜} (h0 : f 0=0) : ∑ k ∈ Icc 0 N,f k = ∑ k ∈ Icc 1 N,f k:=by
  have qa : insert 0 (Icc 1 N)=Icc 0 N:=by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a:=0) (b:=N) (h:=Nat.zero_le N)
  have qb : (0:ℕ) ∉ Icc 1 N:=by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N,f k = ∑ k ∈ insert 0 (Icc 1 N),f k:=by simp [qa]
    _ = f 0 + ∑ k ∈ Icc 1 N,f k:=by simp
    _ = ∑ k ∈ Icc 1 N,f k:=by simp [h0]
theorem _root_.Finset.Z4 {m:ℕ} {f:ℕ → 𝕜} (h0 : f 0=0) : ∑ k ∈ Icc 0 m,f k = ∑ n ∈ range m,f (n+1):=by
 rw [YS h0,Vh]
theorem _root_.ZP {c:ℕ → 𝕜} (hc0 : c 0=0) (t:ℝ) :
  ∑ k ∈ Icc 0 ⌊t⌋₊,c k = ∑ n ∈ range ⌊t⌋₊,c (n+1) :=
 Finset.Z4 (m := ⌊t⌋₊) (f:=c) hc0
end
end
section
section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel
noncomputable def W2 (s:ℂ) (N:ℕ):ℂ :=
 ∑ n ∈ Finset.range N,(n+1:ℂ)^(-s)
namespace ZetaPartialSum
private lemma YV (u:ℝ) (hu : 0 ≤ u) : (Nat.floor u:ℂ)=(u:ℂ) - ((Int.fract u:ℝ):ℂ):=by
 have qa : (Nat.floor u:ℝ)=(Int.floor u:ℝ):=by
  simpa using natCast_floor_eq_intCast_floor (R:=ℝ) (a:=u) hu
 have qb : (Nat.floor u:ℂ)=((Int.floor u:ℝ):ℂ):=congrArg (fun x:ℝ => (x:ℂ)) qa
 have qc : (Int.floor u:ℝ)=u - Int.fract u:=(eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
 have qd : ((Int.floor u:ℝ):ℂ)=((u - Int.fract u:ℝ):ℂ):=congrArg (fun x:ℝ => (x:ℂ)) qc
 exact qb.trans (by simpa [sub_eq_add_neg] using qd)
private lemma Z2 (s:ℂ) {a b:ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable (fun u:ℝ => (u:ℂ)*(u:ℂ)^(-s - 1)) volume a b:=by
 have qa : ContinuousOn (fun u:ℝ => (u:ℂ)*(u:ℂ)^(-s - 1)) (Icc a b) :=
  Complex.continuous_ofReal.continuousOn.mul
   (Complex.VD (r := -s - 1) (ha:=one_pos.trans_le ha))
 exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a:=a) (b:=b)
  (f:=fun u:ℝ => (u:ℂ)*(u:ℂ)^(-s - 1)) hab).2
  (qa.integrableOn_compact isCompact_Icc)
private lemma W1 (s:ℂ) (N:ℕ) (hN : 1 ≤ N) : W2 s N=(N:ℂ)*(N:ℂ)^(-s) - ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(-s*(u:ℂ)^(-s - 1)):=by
  set f:ℝ → ℂ:=fun u => (u:ℂ)^(-s)
  let c:ℕ → ℂ:=fun k => if k=0 then 0 else (1:ℂ)
  have hle : (1:ℝ) ≤ N:=mod_cast hN
  have qb : ∀ t ∈ Set.Icc (1:ℝ) N,DifferentiableAt ℝ f t:=fun t ht => by
    by_cases hs : s=0; · simp [f,hs]
    simpa [f] using (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one ht.1).ne'
      (neg_ne_zero.mpr hs)).differentiableAt
  have qe : IntegrableOn (deriv f) (Set.Icc (1:ℝ) (N:ℝ)) :=
    (Complex.wX (s:=s) (a:=(1:ℝ)) (b:=(N:ℝ)) zero_lt_one).integrableOn_compact
      isCompact_Icc
  have qc :=
    sum_mul_eq_sub_integral_mul₀' (c:=c) (f:=f) (m:=N)
      (hc:=by simp [c]) (hf_diff:=qb) (hf_int:=qe)
  have qf : (∑ k ∈ Finset.Icc 0 N,f k*c k)=W2 s N:=by
    rw [Finset.Z4 (by simp [c])]
    simp [W2,f,c]
  have qa :
      (∫ u in (1:ℝ)..N,deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊,c k)
        = ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(-s*(u:ℂ)^(-s - 1)):=by
    apply intervalIntegral.Vj hle
    intro u hu
    rw [ZP (hc0:=by simp [c]) u,Complex.Wa s (lt_trans zero_lt_one hu.1)]
    simp [c,Finset.sum_const,Finset.card_range,mul_comm,mul_left_comm]
  calc
    W2 s N
        = f N*(∑ k ∈ Finset.Icc 0 N,c k)
            - ∫ u in (1:ℝ)..N,deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊,c k:=by
          simpa [qf] using qc.trans (by rw [← intervalIntegral.integral_of_le hle])
    _ = f N*(∑ k ∈ Finset.Icc 0 N,c k)
            - ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(-s*(u:ℂ)^(-s - 1)):=by
          rw [qa]
    _ = (N:ℂ)*(N:ℂ)^(-s)
            - ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(-s*(u:ℂ)^(-s - 1)):=by
          have qd : f N*(∑ k ∈ Finset.Icc 0 N,c k)=(N:ℂ)*f N:=by
            rw [Finset.Z4 (by simp [c])]
            simp [c,f,Finset.sum_const,Finset.card_range,mul_comm]
          rw [qd]; simp [f]
private lemma ui (s:ℂ) (N:ℕ) (hN : 1 ≤ N) : W2 s N=(N:ℂ)^(1 - s)+s * ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(u:ℂ)^(-s - 1):=by
 rw [W1 s N hN]
 have qa :
   ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(-s*(u:ℂ)^(-s - 1))
    = (-s) * ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(u:ℂ)^(-s - 1):=by
  rw [← intervalIntegral.integral_const_mul,intervalIntegral.Vj (mod_cast hN)]
  intro u _; simp [neg_mul,mul_left_comm]
 rw [qa,sub_eq_add_neg,neg_mul,neg_neg]
 simp [Complex.we N s (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))]
private lemma Wn (s:ℂ) (N:ℕ) (hN : 1 ≤ N) : ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(u:ℂ)^(-s - 1)=(∫ u in (1:ℝ)..N,(u:ℂ)^(-s)) - ∫ u in (1:ℝ)..N,Wu s u:=by
  have hab : (1:ℝ) ≤ N:=mod_cast hN
  have hI1:=Z2 s le_rfl hab
  have hI2:=ZetaAbelFractKernel.intervalIntegrable s le_rfl hab
  calc
    ∫ u in (1:ℝ)..N,(Nat.floor u:ℂ)*(u:ℂ)^(-s - 1)
        = ∫ u in (1:ℝ)..N,((u:ℂ) - ((Int.fract u:ℝ):ℂ))*(u:ℂ)^(-s - 1):=by
          apply intervalIntegral.Vj hab
          intro u hu
          simp [YV u (le_trans zero_le_one (le_of_lt hu.1)),sub_eq_add_neg]
    _ = (∫ u in (1:ℝ)..N,(u:ℂ)*(u:ℂ)^(-s - 1))
          - ∫ u in (1:ℝ)..N,Wu s u:=by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.Vj hab
          intro u _; simp [sub_mul,Wu]
    _ = (∫ u in (1:ℝ)..N,(u:ℂ)^(-s))
          - ∫ u in (1:ℝ)..N,Wu s u:=by
          congr 1
          apply intervalIntegral.Vj hab
          intro u hu
          exact Complex.Zu (s:=s) (hu:=lt_trans zero_lt_one hu.1)
private lemma W7 (s:ℂ) (hs : s ≠ 1) (N:ℕ) (hN : 1 ≤ N) : s * ∫ u in (1:ℝ)..N,(u:ℂ)^(-s)=s/(1 - s)*((N:ℂ)^(1 - s) - 1):=by
  have qa : (1:ℝ) ≤ (N:ℝ):=mod_cast hN
  have qb : ∫ u in (1:ℝ)..N,(u:ℂ)^(-s)
      = ((N:ℂ)^((-s)+1) - (1:ℂ)^((-s)+1))/((-s)+1):=by
    have qc : -s ≠ (-1:ℂ):=fun h => hs (neg_inj.mp h)
    simpa using integral_cpow (a:=(1:ℝ)) (b:=(N:ℝ)) (r := -s)
      (Or.inr ⟨qc,by simp [uIcc_of_le qa]⟩)
  calc s * ∫ u in (1:ℝ)..N,(u:ℂ)^(-s)
      = s*(((N:ℂ)^((-s)+1) - (1:ℂ)^((-s)+1))/((-s)+1)):=by
        simpa using congrArg (s * ·) qb
      _ = s*(((N:ℂ)^(1 - s) - 1)/(1 - s)):=by
        rw [one_cpow,show (1:ℂ) - s = -s+1 from by ring]
      _ = s/(1 - s)*((N:ℂ)^(1 - s) - 1):=by field_simp
private lemma W0 (s:ℂ) (N:ℕ) (hN : 1 ≤ N) : W2 s N=(N:ℂ)^(1 - s)+(s * ∫ u in (1:ℝ)..N,(u:ℂ)^(-s)) - (s * ∫ u in (1:ℝ)..N,Wu s u):=by
 rw [ui s N hN,Wn s N hN,mul_sub,add_sub_assoc]
theorem uf (s:ℂ) (hs : s ≠ 1) (N:ℕ) (hN : 1 ≤ N) : W2 s N=(N:ℂ)^(1 - s)/(1 - s)+1+1/(s - 1) - s * ∫ u in (1:ℝ)..N,Wu s u:=by
 have qa:=W0 s N hN
 rw [W7 s hs N hN] at qa
 let A:=(N:ℂ)^(1 - s)
 have qb : A+s/(1 - s)*(A - 1)=A/(1 - s)+1+1/(s - 1):=by
  field_simp [sub_ne_zero.mpr hs,sub_ne_zero.mpr hs.symm]; ring
 rwa [qb] at qa
lemma wE (w:ℂ) (hw : w.re < 0) : Tendsto (fun N:ℕ => (N:ℂ)^w) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 have h1 : (fun N:ℕ => (N:ℝ)^w.re) =ᶠ[atTop] fun N:ℕ => ‖(N:ℂ)^w‖ := by
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Complex.norm_natCast_cpow_of_pos hN w]
 rw [tendsto_congr' (EventuallyEq.symm h1)]
 rw [show w.re = -(-w.re) from by ring]
 exact (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop
theorem Wt (s:ℂ) (hs : 1 < s.re) : Tendsto (fun N:ℕ => W2 s N) atTop (𝓝 (riemannZeta s)):=by
 set g:ℕ → ℂ:=fun n => if n=0 then 0 else (n:ℂ)^(-s)
 set h:ℕ → ℂ:=fun n => (n+1:ℂ)^(-s)
 have qe : s ≠ 0:=by
  intro h0
  have : (0:ℝ) < s.re:=lt_trans (show (0:ℝ) < 1 by norm_num) hs
  simpa [h0] using ne_of_gt this
 have qb : Summable g:=by
  simpa [g,wj s qe] using
   (Complex.summable_one_div_nat_cpow (p:=s)).2 hs
 have qc : Summable h:=by
  have : Summable (fun n => g (n+1)):=(summable_nat_add_iff (f:=g) (k:=1)).2 qb
  simpa [Function.comp_apply,h,g] using this
 have hg0 : g 0=0:=by simp [g]
 have qa : (∑' n,h n) = ∑' n,g n:=by
  have : (∑' n,g n) = ∑' n,g (n+1):=by simpa [hg0,add_comm] using Summable.tsum_eq_zero_add qb
  simpa [h,g] using this.symm
 have qd : riemannZeta s = ∑' n,g n:=by
  simpa [g,wj s qe] using
   zeta_eq_tsum_one_div_nat_cpow (s:=s) hs
 simpa [W2,h,qa.trans qd.symm] using Summable.tendsto_sum_tsum_nat qc
end ZetaPartialSum
end
end
section
section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel
noncomputable def YR : ℝ:=1/10
theorem ZW : 0 < YR:=by
 change 0 < (1/10:ℝ)
 norm_num
theorem wO : YR < (1:ℝ):=by
 change (1/10:ℝ) < 1
 norm_num
theorem wG : YR < (2⁻¹ : ℝ):=by
 change (1/10:ℝ) < (2⁻¹ : ℝ)
 norm_num
def Y4 : Set ℂ :=
 {s | s ≠ (1:ℂ) ∧ YR < s.re}
theorem Zg : IsOpen Y4:=by
 change IsOpen ({s:ℂ | s ≠ 1} ∩ {s:ℂ | YR < s.re})
 exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)
theorem y0 : IsPreconnected Y4:=by
 convert (Complex.yn
   (a:=YR) (p:=(1:ℂ)) wO).isConnected.isPreconnected using 1
 ext z; simp [Y4,and_comm]
theorem wS : (2:ℂ) ∈ Y4:=by
 refine ⟨by norm_num,?_⟩
 change (1/10:ℝ) < (2:ℂ).re
 norm_num
theorem Zh {s:ℂ} (hs : s ∈ Y4) :
  0 < s.re:=lt_trans ZW hs.2
theorem wc {s:ℂ} (qa : s ≠ 1)
  (qb : YR < s.re) : s ∈ Y4 :=
 ⟨qa,qb⟩
noncomputable def YT (s:ℂ):ℂ :=
 1+1/(s - 1) - s * ∫ u in Ioi (1:ℝ),Wu s u
theorem Y6 (s:ℂ) (hs : 1 < s.re) : riemannZeta s=YT s:=by
 have qf : s ≠ 1:=by
  intro h
  have hre : s.re=1:=by simp [h]
  linarith
 set G:ℕ → ℂ:=fun N =>
  (N:ℂ)^(1 - s)/(1 - s)+1+1/(s - 1)
   - s * ∫ u in (1:ℝ)..N,Wu s u
 have hEv : ∀ᶠ N in atTop,W2 s N=G N :=
  (eventually_ge_atTop 1).mono fun N hN => (uf s qf N hN).trans rfl
 have qa:=(tendsto_congr' hEv).mp (Wt s hs)
 have hA : Tendsto (fun N:ℕ => (N:ℂ)^(1 - s)/(1 - s)) atTop (𝓝 0):=by
  simpa [div_eq_mul_inv,mul_comm] using
   (Tendsto.const_mul (1/(1 - s))
    (wE (1 - s)
     (by rw [Complex.sub_re,Complex.one_re]; linarith)))
 have hK : Tendsto (fun _ : ℕ => (1+1/(s - 1):ℂ)) atTop
   (𝓝 (1+1/(s - 1))):=tendsto_const_nhds
 have qc:=(Wl s hs).const_mul s
 set Aseq:ℕ → ℂ:=fun N => (N:ℂ)^(1 - s)/(1 - s)
 set Kseq:ℕ → ℂ:=fun _ => (1+1/(s - 1):ℂ)
 set Iseq:ℕ → ℂ:=fun N => s * ∫ u in (1:ℝ)..N,Wu s u
 have qg : Tendsto (fun N => Aseq N+Kseq N) atTop (𝓝 (1+1/(s - 1))):=by
  simpa using! ((continuous_fst.add continuous_snd).tendsto _).comp (hA.prodMk_nhds hK)
 have qb : Tendsto G atTop
   (𝓝 ((1+1/(s - 1)) - s * ∫ u in Ioi (1:ℝ),Wu s u)):=by
  have qh : Tendsto (fun N => Aseq N+Kseq N - Iseq N) atTop
    (𝓝 ((1+1/(s - 1)) - s * ∫ u in Ioi (1:ℝ),Wu s u)):=by
   simpa [Function.comp_apply,Function.comp_def,sub_eq_add_neg] using
    ((continuous_fst.add continuous_snd).tendsto _).comp (qg.prodMk_nhds qc.neg)
  have qd : (fun N => Aseq N+Kseq N - Iseq N)=G:=by
   funext N
   simp [Aseq,Kseq,Iseq,G,add_comm,add_left_comm,add_assoc,sub_eq_add_neg]
  simpa [qd] using qh
 have qe:=tendsto_nhds_unique qa qb
 simpa [YT,sub_eq_add_neg] using qe
theorem wM (s:ℂ) (hs : s ∈ Y4) : ‖YT s‖ ≤ 1 + ‖1/(s - 1)‖ + ‖s‖ / s.re:=by
  set g:ℝ → ℝ:=fun u => u^(-s.re - 1)
  let μ := (volume : Measure ℝ).restrict (Ioi (1:ℝ))
  have qb:=Zh hs
  have qc :
      ‖s‖ * ‖∫ u in Ioi (1:ℝ),Wu s u‖ ≤ ‖s‖ / s.re :=
    mul_le_mul_of_nonneg_left
      ((MeasureTheory.norm_integral_le_of_norm_le (μ := μ)
        (f:=fun u => Wu s u) (g:=g)
        (by
          simpa [μ,g,IntegrableOn] using
            (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos))
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
          intro u hu
          simpa [g] using YM u (le_of_lt hu) s)).trans
        (by simpa [μ,g,one_div] using
          (le_of_eq (by simp [ZL (s:=s) qb]))))
      (norm_nonneg s)
  have qa :
      ‖YT s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1:ℝ),Wu s u‖ := by
    simp only [YT,one_div]
    calc
      ‖1+(s - 1)⁻¹ - s * ∫ u in Ioi (1:ℝ),Wu s u‖
          ≤ ‖1+(s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1:ℝ),Wu s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1+(s - 1)⁻¹) (-s * ∫ u in Ioi (1:ℝ),Wu s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1:ℝ),Wu s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1:ℂ) ((s - 1)⁻¹)
        · exact (norm_mul_le (-s) (∫ u in Ioi (1:ℝ),Wu s u)).trans_eq
            (by rw [norm_neg])
  calc
    ‖YT s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1:ℝ),Wu s u‖ := qa
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re:=add_le_add_right qc _
    _ ≤ 1 + ‖1/(s - 1)‖ + ‖s‖ / s.re:=by simp [one_div]
theorem vK : AnalyticOn ℂ YT Y4:=by
 simp only [AnalyticOn,Y4,Set.mem_setOf_eq]
 intro s ⟨hs_ne,hs_re⟩
 apply AnalyticAt.analyticWithinAt
 refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
  (analyticAt_id.mul (WB s (lt_trans ZW hs_re)))
 exact sub_ne_zero.mpr hs_ne
theorem yX (s:ℂ) (hs : s ∈ Y4) : riemannZeta s=YT s:=by
 have hUo:=Zg
 have hζ : AnalyticOnNhd ℂ riemannZeta Y4:=by
  rw [← hUo.analyticOn_iff_analyticOnNhd]
  have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
   isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
  exact AnalyticOn.mono h fun _ hz => hz.1
 have hF : AnalyticOnNhd ℂ YT Y4:=by
  rw [← hUo.analyticOn_iff_analyticOnNhd]
  exact vK
 have hEq : riemannZeta =ᶠ[𝓝 (2:ℂ)] YT:=by
  have qa : IsOpen {w:ℂ | 1 < w.re} :=
   isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [qa.mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re)] with w hw
   using Y6 w hw
 exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  hζ hF y0 wS hEq) hs
end
end
section
section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex
theorem Wv (s:ℂ) (hs : s ∈ Y4) : ‖riemannZeta s‖ ≤ 1 + ‖1/(s - 1)‖ + ‖s‖ / s.re:=by
 rw [yX s hs]
 exact wM s hs
namespace StripBounds
end StripBounds
end
end
section
section
open Complex Set Filter Topology Metric
open scoped Real
namespace Complex
lemma yK (R:ℝ) (_hR : 0 < R) : ∃ M:ℝ,0 ≤ M ∧ ∀ w:ℂ,‖w‖ ≤ R → ‖completedRiemannZeta₀ w‖ ≤ M:=by
 have qa : ContinuousOn completedRiemannZeta₀ (Metric.closedBall 0 R) :=
  differentiable_completedZeta₀.continuous.continuousOn
 exact ZR qa
lemma yz (z:ℂ) : ∃ w:ℂ,completedRiemannZeta₀ w=completedRiemannZeta₀ z ∧ (2⁻¹ : ℝ) ≤ w.re ∧ ‖w‖ ≤ 1 + ‖z‖ := by
  refine ⟨if z.re < (2⁻¹ : ℝ) then 1 - z else z,?_,?_,?_⟩
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z)=1 - z:=by
        simp [hzr]
      simpa [hw] using (completedRiemannZeta₀_one_sub z)
    · simp [hzr]
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have : (if z.re < (2⁻¹ : ℝ) then 1 - z else z).re=1 - z.re:=by
        simp [hzr]
      linarith [this,hzr]
    · simpa [hzr] using le_of_not_gt hzr
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z)=1 - z:=by
        simp [hzr]
      have : ‖1 - z‖ ≤ ‖(1:ℂ)‖ + ‖z‖ := by
        simpa using (norm_sub_le (1:ℂ) z)
      simpa [hw,norm_one,add_comm,add_left_comm,add_assoc] using this
    · simp [hzr]
theorem ZS : ∀ ε : ℝ,0 < ε → ∃ C > 0,∀ z:ℂ, ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C*(1 + ‖z‖)^(1 + ε)):=by
  intro ε hε
  obtain ⟨M,hM_nonneg,hM⟩ := yK 3 (by norm_num)
  obtain ⟨CΓ,hCΓ_pos,hΓ⟩ := Complex.Gammaℝ.Stirling.WP
  let C:ℝ :=
    max (Real.log (M+1)+1) (((2:ℝ)^(1 + ε))*(10+CΓ / ε)+1)
  refine ⟨C,?_,?_⟩
  · have : (0:ℝ) < Real.log (M+1)+1:=by
      have qS : 0 ≤ Real.log (M+1):=by
        have : (1:ℝ) ≤ M+1:=by linarith [hM_nonneg]
        exact Real.log_nonneg this
      linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro z
    obtain ⟨w,hw_eq,hw_re,hw_norm_le⟩ := yz z
    have qt : 0 ≤ w.re:=by linarith
    have qf : ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := by
      simp [hw_eq]
    have qp : (1:ℝ) ≤ (1 + ‖z‖)^(1 + ε) :=
      Vu (z:=z) (by linarith [le_of_lt hε])
    by_cases hw_small : ‖w‖ ≤ 3
    · have hbw : ‖completedRiemannZeta₀ w‖ ≤ M:=hM w hw_small
      have qE : Real.log (M+1) ≤ C:=by
        have : Real.log (M+1)+1 ≤ C:=le_max_left _ _
        linarith
      have qT : 0 < (M+1:ℝ):=by linarith [hM_nonneg]
      have qg : M ≤ Real.exp (Real.log (M+1)):=by
        have : Real.exp (Real.log (M+1))=M+1:=by simpa using (Real.exp_log qT)
        linarith [this]
      have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (C*(1 + ‖z‖)^(1 + ε)):=by
        have h1 : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (Real.log (M+1)):=by
          exact le_trans hbw qg
        have h2 : Real.log (M+1) ≤ C*(1 + ‖z‖)^(1 + ε):=by
          have qu : Real.log (M+1) ≤ C:=qE
          have qF : C ≤ C*(1 + ‖z‖)^(1 + ε):=by
            have hC0 : 0 ≤ C:=le_trans (by
              have : (0:ℝ) < Real.log (M+1)+1:=by
                have qS : 0 ≤ Real.log (M+1):=Real.log_nonneg (by linarith [hM_nonneg])
                linarith
              exact this.le) (le_max_left _ _)
            have:=mul_le_mul_of_nonneg_left qp hC0
            simpa [mul_one] using this
          exact le_trans qu qF
        exact le_trans h1 (Real.exp_le_exp.2 h2)
      simpa [qf] using this
    · have qm : 3 < ‖w‖ := lt_of_not_ge hw_small
      have qn : 1 ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt qm)
      have qv : w ≠ 0:=by
        intro h0; have : (‖w‖ : ℝ)=0:=by simp [h0]
        linarith [qm]
      have qw : w ≠ 1:=by
        intro h1; have : (‖w‖ : ℝ)=1:=by simp [h1]
        linarith [qm]
      have qx : ‖Complex.Gammaℝ w‖ ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) :=
        hΓ w qt qn
      have qy:=wc qw
        (lt_of_lt_of_le wG hw_re)
      have qz:=Wv w qy
      have qA : ‖1/(w - 1)‖ ≤ 1:=by
        have qG : ‖w‖ ≤ ‖w - 1‖ + 1:=by
          have : ‖(w - 1)+(1:ℂ)‖ ≤ ‖w - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          simpa [sub_add_cancel w (1:ℂ),norm_one] using this
        have qU : (2:ℝ) ≤ ‖w - 1‖ := by
          have : ‖w‖ ≤ ‖w - 1‖ + 1:=by simpa [norm_one] using qG
          linarith [qm]
        have qH : (1:ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) qU
        simpa [one_div,norm_inv] using inv_le_one_of_one_le₀ qH
      have qV : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
        have qh : (0:ℝ) < (2⁻¹ : ℝ):=by norm_num
        have qW : (1/w.re:ℝ) ≤ 2:=by
          have : (1/w.re:ℝ) ≤ (1/(2⁻¹ : ℝ)) :=
            one_div_le_one_div_of_le qh hw_re
          simpa using this.trans_eq (by norm_num)
        calc
          ‖w‖ / w.re = ‖w‖ * (1/w.re):=by ring
          _ ≤ ‖w‖ * 2:=mul_le_mul_of_nonneg_left qW (norm_nonneg _)
          _ = 2 * ‖w‖ := by ring
      have qo : ‖riemannZeta w‖ ≤ 2+2 * ‖w‖ := by
        have qB : ‖riemannZeta w‖ ≤ 1 + ‖1/(w - 1)‖ + ‖w‖ / w.re:=by
          simpa [one_div] using qz
        linarith [qB,qA,qV]
      have qe : Complex.Gammaℝ w ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (by linarith [hw_re])
      have hΛ_def : completedRiemannZeta w=riemannZeta w*Complex.Gammaℝ w:=by
        have qi:=(riemannZeta_def_of_ne_zero (s:=w) qv)
        have qj:=congrArg (fun x => x*Complex.Gammaℝ w) qi
        have : riemannZeta w*Complex.Gammaℝ w=completedRiemannZeta w:=by
          simpa [div_eq_mul_inv,mul_assoc,qe] using qj
        simpa [mul_comm,mul_left_comm,mul_assoc] using this.symm
      have hΛ_bound :
          ‖completedRiemannZeta w‖ ≤ (2+2 * ‖w‖)*Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
        calc
          ‖completedRiemannZeta w‖ = ‖riemannZeta w*Complex.Gammaℝ w‖ := by simp [hΛ_def]
          _ ≤ ‖riemannZeta w‖ * ‖Complex.Gammaℝ w‖ := norm_mul_le _ _
          _ ≤ (2+2 * ‖w‖)*Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
            exact mul_le_mul qo qx (by positivity) (by positivity)
      have hΛ0_def : completedRiemannZeta₀ w =
          completedRiemannZeta w+1/w+1/(1 - w):=by
        have h:=completedRiemannZeta_eq w
        have h':=congrArg (fun x => x+(1/w)+(1/(1 - w))) h
        simpa [add_assoc,add_left_comm,add_comm,sub_eq_add_neg] using h'.symm
      have qI : ‖1/w‖ ≤ 1:=by
        have : (1:ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt qm)
        simpa [one_div,norm_inv] using inv_le_one_of_one_le₀ this
      have qJ : ‖1/(1 - w)‖ ≤ 1:=by
        have qG : ‖w‖ ≤ ‖w - 1‖ + 1:=by
          have : ‖(w - 1)+(1:ℂ)‖ ≤ ‖w - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          simpa [sub_add_cancel w (1:ℂ),norm_one] using this
        have : (2:ℝ) ≤ ‖w - 1‖ := by linarith [qm,qG]
        have : (1:ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) this
        simpa [one_div,norm_inv,norm_sub_rev] using inv_le_one_of_one_le₀ this
      have hΛ0_bound : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + 2:=by
        have : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + ‖1/w‖ + ‖1/(1 - w)‖ := by
          simpa [hΛ0_def,add_assoc] using
            (norm_add₃_le (a:=completedRiemannZeta w) (b:=(1/w)) (c:=(1/(1 - w))))
        linarith [this,qI,qJ]
      have qk : 0 ≤ CΓ * ‖w‖ * Real.log (1 + ‖w‖):=by
        have qS : 0 ≤ Real.log (1 + ‖w‖):=Real.log_nonneg (by linarith [norm_nonneg w])
        have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
        exact mul_nonneg (mul_nonneg hC0 (norm_nonneg w)) qS
      have qd : (1:ℝ) ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
        simpa using (Real.one_le_exp_iff.2 qk)
      have hΛ0_mul_exp :
          ‖completedRiemannZeta₀ w‖ ≤ (5+5 * ‖w‖)*Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
        have hw1 : (1:ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt qm)
        have h2 : (2:ℝ) ≤ (3+3 * ‖w‖)*Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
          nlinarith [qd,hw1]
        have :
            ‖completedRiemannZeta w‖ + 2 ≤
              (5+5 * ‖w‖)*Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)):=by
          nlinarith [hΛ_bound,h2]
        exact le_trans hΛ0_bound this
      have qS : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) ^ ε / ε :=
        Real.log_le_rpow_div (by linarith [norm_nonneg w]) hε
      have qK : CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ (CΓ / ε)*(1 + ‖w‖)^(1 + ε):=by
        have qL : ‖w‖ ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
        have qT : 0 < (1 + ‖w‖ : ℝ):=by linarith [norm_nonneg w]
        have qM : Real.log (1 + ‖w‖) ≤ (1 / ε)*(1 + ‖w‖) ^ ε := by
          simpa [div_eq_mul_inv,one_div,mul_assoc,mul_left_comm,mul_comm] using qS
        have hpowε_nonneg : 0 ≤ (1 + ‖w‖) ^ ε := by positivity
        have qC : ‖w‖ * Real.log (1 + ‖w‖) ≤ ‖w‖ * ((1 / ε)*(1 + ‖w‖) ^ ε) :=
          mul_le_mul_of_nonneg_left qM (norm_nonneg w)
        have qa : 0 ≤ (1 / ε)*(1 + ‖w‖) ^ ε := by
          exact mul_nonneg (by positivity) hpowε_nonneg
        have qD :
            ‖w‖ * ((1 / ε)*(1 + ‖w‖) ^ ε) ≤ (1 + ‖w‖)*((1 / ε)*(1 + ‖w‖) ^ ε) :=
          mul_le_mul_of_nonneg_right qL qa
        have qq : (1 + ‖w‖)*(1 + ‖w‖) ^ ε = (1 + ‖w‖)^(1 + ε):=by
          have h:=(Real.rpow_add qT (1:ℝ) ε)
          simpa [Real.rpow_one,mul_assoc,mul_left_comm,mul_comm] using h.symm
        have qN :
            ‖w‖ * Real.log (1 + ‖w‖) ≤ (1 / ε)*(1 + ‖w‖)^(1 + ε):=by
          have : ‖w‖ * Real.log (1 + ‖w‖) ≤ (1 + ‖w‖)*((1 / ε)*(1 + ‖w‖) ^ ε) :=
            le_trans qC qD
          calc
            ‖w‖ * Real.log (1 + ‖w‖)
                ≤ (1 + ‖w‖)*((1 / ε)*(1 + ‖w‖) ^ ε):=this
            _ = (1 / ε)*((1 + ‖w‖)*(1 + ‖w‖) ^ ε):=by ring
            _ = (1 / ε)*(1 + ‖w‖)^(1 + ε):=by simp [qq]
        have hCΓ0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
        have:=mul_le_mul_of_nonneg_left qN hCΓ0
        simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using this
      have qO :
          (5+5 * ‖w‖) ≤ Real.exp (10*(1 + ‖w‖)^(1 + ε)):=by
        have qX : (5+5 * ‖w‖ : ℝ) ≤ 10*(1 + ‖w‖):=by nlinarith [norm_nonneg w]
        have qP : (1:ℝ) ≤ (1 + ‖w‖):=by linarith [norm_nonneg w]
        have qY : (1 + ‖w‖) ≤ (1 + ‖w‖)^(1 + ε):=by
          have : (1:ℝ) ≤ (1 + ε : ℝ):=by linarith [le_of_lt hε]
          simpa [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le qP this)
        have : (10*(1 + ‖w‖):ℝ) ≤ 10*(1 + ‖w‖)^(1 + ε):=by nlinarith [qY]
        exact le_trans qX (le_trans this (Real.uh _))
      have qZ :
          ‖completedRiemannZeta₀ w‖ ≤
            Real.exp ((10+CΓ / ε)*(1 + ‖w‖)^(1 + ε)):=by
        set X : ℝ:=(1 + ‖w‖)^(1 + ε)
        have qc :
            Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) ≤ Real.exp ((CΓ / ε)*X) :=
          Real.exp_le_exp.2 (by simpa [X] using qK)
        have hC0 : 0 ≤ (5+5 * ‖w‖ : ℝ):=by positivity
        have h1 : ‖completedRiemannZeta₀ w‖ ≤ (5+5 * ‖w‖)*Real.exp ((CΓ / ε)*X) :=
          le_trans hΛ0_mul_exp (by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_left qc hC0))
        have h2 :
            (5+5 * ‖w‖)*Real.exp ((CΓ / ε)*X) ≤
              Real.exp (10*X)*Real.exp ((CΓ / ε)*X):=by
          have : (5+5 * ‖w‖) ≤ Real.exp (10*X):=by
            simpa [X] using qO
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have h3 : Real.exp (10*X)*Real.exp ((CΓ / ε)*X)=Real.exp ((10+CΓ / ε)*X):=by
          calc
            Real.exp (10*X)*Real.exp ((CΓ / ε)*X)
                = Real.exp (10*X+(CΓ / ε)*X):=by
                    simp [Real.exp_add]
            _ = Real.exp ((10+CΓ / ε)*X):=by ring_nf
        have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp ((10+CΓ / ε)*X) :=
          le_trans (le_trans h1 h2) (by simp [h3])
        simpa [X] using this
      have qr : (1 + ‖w‖ : ℝ) ≤ 2*(1 + ‖z‖):=by linarith [hw_norm_le,norm_nonneg z]
      have qb : (0:ℝ) ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
      have hε' : (0:ℝ) ≤ 1 + ε := by linarith [le_of_lt hε]
      have qs :
          (1 + ‖w‖)^(1 + ε) ≤ (2*(1 + ‖z‖))^(1 + ε) :=
        Real.rpow_le_rpow qb qr hε'
      have qQ : ((2:ℝ)^(1 + ε))*(10+CΓ / ε) ≤ C:=by
        have : ((2:ℝ)^(1 + ε))*(10+CΓ / ε)+1 ≤ C:=le_max_right _ _
        linarith
      have qR : 0 ≤ (1 + ‖z‖ : ℝ):=by linarith [norm_nonneg z]
      have ql :
          (2*(1 + ‖z‖))^(1 + ε)=(2:ℝ)^(1 + ε)*(1 + ‖z‖)^(1 + ε):=by
        simpa [mul_assoc] using
          (Real.mul_rpow (x:=(2:ℝ)) (y:=(1 + ‖z‖)) (z:=(1 + ε)) (by positivity) qR)
      have q0 :
          (10+CΓ / ε)*(1 + ‖w‖)^(1 + ε) ≤ C*(1 + ‖z‖)^(1 + ε):=by
        calc
          (10+CΓ / ε)*(1 + ‖w‖)^(1 + ε)
              ≤ (10+CΓ / ε)*(2*(1 + ‖z‖))^(1 + ε):=by gcongr
          _ = ((2:ℝ)^(1 + ε))*(10+CΓ / ε)*(1 + ‖z‖)^(1 + ε):=by
                simp [ql]
                ring
          _ ≤ C*(1 + ‖z‖)^(1 + ε):=by
                have : ((2:ℝ)^(1 + ε))*(10+CΓ / ε) ≤ C:=qQ
                gcongr
      have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (C*(1 + ‖z‖)^(1 + ε)):=by
        exact le_trans qZ (Real.exp_le_exp.2 q0)
      simpa [qf] using this
end Complex
end
end
section
section
open Complex Set
open scoped BigOperators
theorem Zp : completedRiemannZeta₀ (0:ℂ)=completedRiemannZeta₀ (1:ℂ):=by
 have h:=completedRiemannZeta₀_one_sub (0:ℂ)
 simpa using h.symm
end
end
section
section
noncomputable section
open Complex Set
open scoped BigOperators
theorem yr : Complex.Hadamard.Ws (1:ℝ) completedRiemannZeta₀ := by
 refine ⟨differentiable_completedZeta₀,?_⟩
 intro ε hε
 simpa [add_comm,add_left_comm,add_assoc] using
  (Complex.ZS ε hε)
theorem Zk : Complex.Hadamard.Ws (1:ℝ) uj:=by
  refine ⟨VB,?_⟩
  intro ε hε
  rcases yr.exists_bound hε with
    ⟨C,hCpos,hΛ⟩
  let b : ℝ:=1 + ε
  let D : ℝ:=4/b
  let C' : ℝ:=C+D+1
  have qe : 0 < b:=by dsimp [b]; linarith
  refine ⟨C',by positivity,?_⟩
  intro z
  let R : ℝ:=1 + ‖z‖
  have hR1 : 1 ≤ R:=by dsimp [R]; linarith [norm_nonneg z]
  have hRpos : 0 < R:=zero_lt_one.trans_le hR1
  have qd : 1 ≤ R^b :=
    Real.one_le_rpow hR1 qe.le
  have qf : ‖z*(z - 1)‖ ≤ R^2:=by
    have hz : ‖z‖ ≤ R:=by dsimp [R]; linarith [norm_nonneg z]
    have hz1 : ‖z - 1‖ ≤ R:=by
      simpa [R] using Complex.Yr z
    calc
      ‖z*(z - 1)‖ ≤ ‖z‖ * ‖z - 1‖ := norm_mul_le z (z - 1)
      _ ≤ R*R:=mul_le_mul hz hz1 (norm_nonneg _) (by positivity)
      _ = R^2:=by ring
  have qg : R^2 ≤ Real.exp (D*R^b):=by
    simpa [D] using Real.Vy (b:=b) (r:=R) qe hR1
  have hΛz : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C*R^b):=by
    simpa [R,b,add_assoc] using hΛ z
  have qh :
      ‖z*(z - 1)*completedRiemannZeta₀ z‖ ≤
        Real.exp ((C+D)*R^b):=by
    calc
      ‖z*(z - 1)*completedRiemannZeta₀ z‖
          ≤ ‖z*(z - 1)‖ * ‖completedRiemannZeta₀ z‖ := norm_mul_le _ _
      _ ≤ (R^2)*Real.exp (C*R^b) :=
          mul_le_mul qf hΛz (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (D*R^b)*Real.exp (C*R^b) :=
          mul_le_mul_of_nonneg_right qg (by positivity)
      _ = Real.exp ((C+D)*R^b):=by
          rw [← Real.exp_add]
          ring_nf
  have qa : 0 ≤ (C+D)*R^b:=by positivity
  have qc : (1:ℝ) ≤ Real.exp ((C+D)*R^b) :=
    Real.one_le_exp_iff.mpr qa
  have qb :
      2*Real.exp ((C+D)*R^b) ≤
        Real.exp (((C+D)*R^b)+1):=by
    calc
      2*Real.exp ((C+D)*R^b)
          = Real.exp (Real.log 2)*Real.exp ((C+D)*R^b):=by
              have qj : Real.exp (Real.log 2)=(2:ℝ):=by
                exact Real.exp_log (by norm_num)
              rw [qj]
      _ = Real.exp (Real.log 2+(C+D)*R^b):=by
          rw [Real.exp_add]
      _ ≤ Real.exp (((C+D)*R^b)+1):=by
          refine Real.exp_le_exp.2 ?_
          have qi : Real.log 2 ≤ (1:ℝ):=by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have h:=Real.add_one_le_exp (1:ℝ)
            norm_num at h
            exact h
          linarith
  have hxi :
      ‖uj z‖ ≤ Real.exp (((C+D)*R^b)+1):=by
    calc
      ‖uj z‖
          = ‖z*(z - 1)*completedRiemannZeta₀ z+1‖ / 2:=by
              simp [uj]
      _ ≤ (‖z*(z - 1)*completedRiemannZeta₀ z‖ + 1)/2:=by
          gcongr
          simpa using norm_add_le (z*(z - 1)*completedRiemannZeta₀ z) (1:ℂ)
      _ ≤ ‖z*(z - 1)*completedRiemannZeta₀ z‖ + 1:=by
          nlinarith [norm_nonneg (z*(z - 1)*completedRiemannZeta₀ z)]
      _ ≤ Real.exp ((C+D)*R^b)+1:=by
          gcongr
      _ ≤ 2*Real.exp ((C+D)*R^b):=by
          linarith
      _ ≤ Real.exp (((C+D)*R^b)+1):=qb
  exact hxi.trans (Real.exp_le_exp.2 (by
    calc
      ((C+D)*R^b)+1 ≤ ((C+D)*R^b)+R^b:=by
          gcongr
      _ = C'*R^b:=by
          ring))
theorem z8 : Summable (fun p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ) => ‖Complex.Hadamard.Wc p‖⁻¹ ^ (2:ℕ)):=by
 simpa using
  (Complex.Hadamard.Ws.vA
   (ρ := (1:ℝ)) (f:=uj) Zk
   (by norm_num) Wm)
theorem Zb : analyticOrderNatAt uj 0=0:=by
 by_contra h
 have qa : uj 0=0 :=
  apply_eq_zero_of_analyticOrderNatAt_ne_zero (f:=uj) (z₀ := 0) h
 rw [W4] at qa
 norm_num at qa
theorem zy
  {z:ℂ}
  (hz : ∀ p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),
   z ≠ Complex.Hadamard.Wc p) :
  logDeriv (Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ)) z =
   ∑' p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),
    (1/(z - Complex.Hadamard.Wc p) +
     1/Complex.Hadamard.Wc p) :=
 Complex.Hadamard.zn
  z8 hz
theorem zH {P : Polynomial ℂ} {z:ℂ} (qc : ∀ w:ℂ,uj w=Complex.exp (Polynomial.eval w P)*Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ) w) (hz : ∀ p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),z ≠ Complex.Hadamard.Wc p) : logDeriv uj z=Polynomial.eval z P.derivative + ∑' p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),(1/(z - Complex.Hadamard.Wc p)+1/Complex.Hadamard.Wc p):=by
  let G:ℂ → ℂ :=
    Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ)
  have qd : uj=fun w:ℂ => Complex.exp (Polynomial.eval w P)*G w:=by
    funext w
    simpa [G] using qc w
  have qa : DifferentiableAt ℂ (fun w:ℂ => Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).differentiableAt
  have qb :
      Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ) z ≠ 0 :=
    Complex.Hadamard.yE
      1 uj z8 hz
  calc
    logDeriv uj z =
        logDeriv (fun w:ℂ => Complex.exp (Polynomial.eval w P)*G w) z:=by
          rw [qd]
    _ = logDeriv (fun w:ℂ => Complex.exp (Polynomial.eval w P)) z+logDeriv G z:=by
          exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa [G] using qb)
            qa
            (by
              simpa [G] using
                Complex.Hadamard.yu
                  1 uj z8 z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),
          (1/(z - Complex.Hadamard.Wc p) +
            1/Complex.Hadamard.Wc p):=by
          rw [Polynomial.WC]
          rw [show logDeriv G z =
              ∑' p : Complex.Hadamard.Wz uj (Set.univ : Set ℂ),
                (1/(z - Complex.Hadamard.Wc p) +
                  1/Complex.Hadamard.Wc p) from
            by
              simpa [G] using
                zy
                  hz]
theorem Zx : ∃ (P : Polynomial ℂ),P.degree ≤ 1 ∧ ∀ z:ℂ,uj z=Complex.exp (Polynomial.eval z P)*z^(analyticOrderNatAt uj 0)*Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ) z:=by
 simpa using
  (Complex.Hadamard.ZQ
   (f:=uj) (ρ := (1:ℝ))
   (by norm_num) Wm
   Zk)
theorem yA : ∃ (P : Polynomial ℂ),P.degree ≤ 1 ∧ ∀ z:ℂ,uj z=Complex.exp (Polynomial.eval z P)*Complex.Hadamard.VJ 1 uj (Set.univ : Set ℂ) z:=by
 rcases Zx with ⟨P,hdeg,hfac⟩
 refine ⟨P,hdeg,?_⟩
 intro z
 simpa [Zb,mul_assoc] using hfac z
end
end
end
section
section
noncomputable section
open Complex Set
abbrev Vc : Type :=
 Complex.Hadamard.Wz uj (Set.univ : Set ℂ)
abbrev Y5 (p : Vc):ℂ :=
 Complex.Hadamard.Wc p
@[simp]
theorem Zj
  (p : Vc) :
  Y5 p ≠ 0 :=
 Complex.Hadamard.Yd p
theorem Za (p : Vc) : uj (Y5 p)=0:=by
 have qa :
   MeromorphicOn.divisor uj (Set.univ : Set ℂ)
     (Y5 p) ≠ 0 :=
  Complex.Hadamard.y4 p
 have qb :
   analyticOrderNatAt uj (Y5 p) ≠ 0:=by
  intro hOrderZero
  apply qa
  rw [Complex.Hadamard.vZ
   VB]
  simp [hOrderZero]
 exact apply_eq_zero_of_analyticOrderNatAt_ne_zero qb
theorem zx {s:ℂ} (hs0 : s ≠ 0) (qa : Gamma (s/2) ≠ 0) : completedRiemannZeta s=(Real.pi:ℂ)^(-s/2)*Gamma (s/2)*riemannZeta s:=by
 rw [riemannZeta_def_of_ne_zero hs0,Gammaℝ_def]
 field_simp [qa]
theorem va : Summable (fun p : Vc => ‖Y5 p‖⁻¹ ^ (2:ℕ)):=by
 simpa using z8
end
end
end
section
namespace Robin1984
noncomputable section
open Complex
theorem z2 {z:ℂ} (qb : Not (z=0)) (qc : Not (z=1)) (hXi : uj z=0) : completedRiemannZeta z=0:=by
  rw [v2 qb qc] at hXi
  have qa :
      z*(z - 1)*completedRiemannZeta z=0 :=
    (div_eq_zero_iff.mp hXi).resolve_right (by norm_num)
  rcases mul_eq_zero.mp qa with hFactor | hCompleted
  . rcases mul_eq_zero.mp hFactor with hz | hzSub
    . exact (qb hz).elim
    . exact (qc (sub_eq_zero.mp hzSub)).elim
  . exact hCompleted
theorem vi {z:ℂ} (qb : Not (z=0)) (qc : Not (z=1)) (hXi : uj z=0) : riemannZeta z=0:=by
 have qa :
   completedRiemannZeta z=0 :=
  z2
   qb qc hXi
 rw [riemannZeta_def_of_ne_zero qb,qa,zero_div]
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex
open scoped BigOperators
open scoped ComplexConjugate
theorem We : uj (1:ℂ)=1/2:=by
 simpa [W4] using (WA (0:ℂ))
theorem zi {P : Polynomial ℂ} (qe : P.degree <= 1) (qa : forall z:ℂ,uj z=Complex.exp (Polynomial.eval z P)*Complex.Hadamard.VJ 1 uj Set.univ z) (z:ℂ) : Polynomial.eval z P.derivative=logDeriv uj 0:=by
  have qd :
      forall p : Vc,
        Not ((0:ℂ)=Y5 p):=by
    intro p
    exact (Zj p).symm
  have qf :=
    zH
      (P:=P) (z:=(0:ℂ)) qa qd
  have qb :
      (fun p : Vc =>
        (1/((0:ℂ) - Y5 p) +
          1/Y5 p)) =
        (fun _p : Vc => (0:ℂ)):=by
    funext p
    have qg : Not (Y5 p=0) :=
      Zj p
    field_simp [qg]
    ring
  have qc :
      logDeriv uj 0=Polynomial.eval 0 P.derivative:=by
    rw [qb] at qf
    simpa using qf
  calc
    Polynomial.eval z P.derivative =
        Polynomial.eval 0 P.derivative :=
      Polynomial.zr
        qe z
    _ = logDeriv uj 0:=qc.symm
end
end Robin1984
end
section
namespace Kadiri
open Complex
noncomputable def WZ (s:ℂ):ℂ :=
 s - 1
noncomputable def ue (s:ℂ):ℂ :=
 Complex.exp (-(s/2)*(Real.log Real.pi:ℂ))
noncomputable def WS (s:ℂ):ℂ :=
 Gamma (s/2+1)
noncomputable def Wp (s:ℂ):ℂ :=
 WZ s*ue s*WS s*riemannZeta s
theorem VH (s:ℂ) : logDeriv WZ s=1/(s - 1):=by
 unfold WZ
 rw [logDeriv_apply]
 simp
theorem V2 (s:ℂ) : logDeriv ue s = -(1/2:ℂ)*Real.log Real.pi:=by
  unfold ue
  rw [show (fun s:ℂ => Complex.exp (-(s/2)*(Real.log Real.pi:ℂ))) =
      Complex.exp ∘ (fun s:ℂ => -(s/2)*(Real.log Real.pi:ℂ)) by rfl]
  rw [logDeriv_comp]
  · simp
  · fun_prop
  · fun_prop
theorem Vn (s:ℂ) (hΓdiff : ∀ m:ℕ,s/2+1 ≠ -m) : logDeriv WS s=(1/2:ℂ)*digamma (s/2+1):=by
  unfold WS
  rw [show (fun s:ℂ => Gamma (s/2+1)) =
      Gamma ∘ (fun s:ℂ => s/2+1) by rfl]
  rw [logDeriv_comp]
  · simp [digamma_def]
    ring
  · exact differentiableAt_Gamma _ hΓdiff
  · fun_prop
theorem Yq (s:ℂ) (hs1 : s ≠ 1) (hΓdiff : ∀ m:ℕ,s/2+1 ≠ -m) (hΓ : WS s ≠ 0) (hζ : riemannZeta s ≠ 0) : logDeriv Wp s=1/(s - 1) - (1/2:ℂ)*Real.log Real.pi+(1/2:ℂ)*digamma (s/2+1)+deriv riemannZeta s/riemannZeta s:=by
  have qe : WZ s ≠ 0:=by
    simp [WZ,sub_ne_zero,hs1]
  have hpi : ue s ≠ 0:=by
    simp [ue]
  have qb : DifferentiableAt ℂ WZ s:=by
    unfold WZ
    fun_prop
  have qd : DifferentiableAt ℂ ue s:=by
    unfold ue
    fun_prop
  have qa : DifferentiableAt ℂ WS s:=by
    unfold WS
    exact (differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop)
  have qc : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  unfold Wp
  rw [logDeriv_mul]
  · rw [logDeriv_mul]
    · rw [logDeriv_mul]
      · rw [VH,V2,
          Vn s hΓdiff,logDeriv_apply]
        ring
      · exact qe
      · exact hpi
      · exact qb
      · exact qd
    · exact mul_ne_zero qe hpi
    · exact hΓ
    · exact qb.mul qd
    · exact qa
  · exact mul_ne_zero (mul_ne_zero qe hpi) hΓ
  · exact hζ
  · exact (qb.mul qd).mul qa
  · exact qc
end Kadiri
end
section
namespace Robin1984
noncomputable section
open Complex
open scoped BigOperators
theorem YZ (s:ℂ) : Kadiri.ue s=(Real.pi:ℂ)^(-(s/2)):=by
  unfold Kadiri.ue
  rw [Complex.cpow_def_of_ne_zero,Complex.ofReal_log Real.pi_pos.le]
  . ring_nf
  . exact_mod_cast Real.pi_ne_zero
end
end Robin1984
end
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.GammaFacts.Series -/
section
noncomputable section

namespace Zeta23

namespace DigammaSeries

open Complex Filter Topology

def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1

set_option maxHeartbeats 1600000 in
lemma one_add_wTerm (n : ℕ) (z : ℂ) :
    1 + wTerm n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold wTerm
  ring

set_option maxHeartbeats 1600000 in
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

set_option maxHeartbeats 1600000 in
lemma norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : wTerm n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold wTerm
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖wTerm n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

set_option maxHeartbeats 1600000 in
lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

set_option maxHeartbeats 1600000 in
lemma summable_norm_wTerm (z : ℂ) : Summable (fun n => ‖wTerm n z‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wTerm_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

set_option maxHeartbeats 1600000 in
lemma multipliable_one_add_wTerm (z : ℂ) : Multipliable fun n => 1 + wTerm n z :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wTerm z).of_norm)

set_option maxHeartbeats 1600000 in
lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

set_option maxHeartbeats 1600000 in
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  
  have hprod : ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + wTerm n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wTerm n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

set_option maxHeartbeats 1600000 in
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (multipliable_one_add_wTerm z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

set_option maxHeartbeats 1600000 in
lemma logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + wTerm n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wTerm n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

set_option maxHeartbeats 1600000 in
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

set_option maxHeartbeats 1600000 in
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + wTerm n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖wTerm n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wTerm_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (wTerm n) := by
        unfold wTerm
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + wTerm n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wTerm]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + wTerm n s := by
      unfold wTerm
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + wTerm n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + wTerm n s)) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h

set_option maxHeartbeats 1600000 in
theorem digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end DigammaSeries

end Zeta23

end
end
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.GammaFacts.StirlingVert -/
section
noncomputable section

namespace Zeta23

namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

set_option maxHeartbeats 1600000 in
theorem intervalIntegral_mul_const_C (c : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
  intervalIntegral.integral_mul_const c f

set_option maxHeartbeats 1600000 in
theorem abs_im_le_norm_add {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + w)
  simpa using this

set_option maxHeartbeats 1600000 in
theorem re_add_pos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith

set_option maxHeartbeats 1600000 in
theorem add_mem_slitPlane {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_add_pos hw hx))

set_option maxHeartbeats 1600000 in
theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := re_add_pos hw hx; rw [h] at this; simp at this

set_option maxHeartbeats 1600000 in
theorem hasDerivAt_log_add {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    have := (Complex.hasDerivAt_log (add_mem_slitPlane hw hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

set_option maxHeartbeats 1600000 in
theorem integral_inv_add_eq_log_sub {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      exact hasDerivAt_log_add hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]

set_option maxHeartbeats 1600000 in
theorem inv_add_expand {w : ℂ} {x m : ℝ} (hxw : (x : ℂ) + w ≠ 0) (hmw : (m : ℂ) + w ≠ 0) :
    ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) := by
  field_simp
  push_cast
  ring

def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))

set_option maxHeartbeats 1600000 in
theorem integral_inv_add_eq {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by
  have hmw := add_ne_zero hw hm
  have hcongr : ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹ = ∫ x in m..(m + 1),
      (((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact inv_add_expand (add_ne_zero hw (by linarith [hx.1])) hmw
  rw [hcongr]
  have hI : ∀ {f : ℝ → ℂ}, Continuous f → IntervalIntegrable f volume m (m + 1) :=
    fun hf => hf.intervalIntegrable _ _
  have hR : IntervalIntegrable (fun x : ℝ =>
      ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) volume m (m + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
  have hmid : ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
      = ((1 / 2 : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
    have e : (fun x : ℝ => ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2)
        = fun x : ℝ => ((x - m : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
      funext x; rw [div_eq_mul_inv]
    rw [e, intervalIntegral_mul_const_C, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) m]
    simp only [sub_self, add_sub_cancel_left, integral_id]
    norm_num
  rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
    integral_sub (hI (by fun_prop)) (hI (by fun_prop)), intervalIntegral.integral_const, hmid,
    show m + 1 - m = (1 : ℝ) by ring, one_smul]
  unfold eps
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem norm_eps_le {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := abs_im_le_norm_add x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp

section Seq

variable {w : ℂ}

set_option maxHeartbeats 1600000 in
theorem natp1_re_pos (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
  simp; positivity

set_option maxHeartbeats 1600000 in
theorem natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
  have := natp1_re_pos hw n; rw [h] at this; simp at this

set_option maxHeartbeats 1600000 in
theorem natp1_le_norm (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
  have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
  simp at h; linarith

set_option maxHeartbeats 1600000 in
theorem inv_natp1_eq (hw : 0 < w.re) (n : ℕ) :
    ((n : ℂ) + 1 + w)⁻¹
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) / ((n : ℂ) + 1 + w) ^ 2 - eps w ((n : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 := integral_inv_add_eq hw hm
  have h2 := integral_inv_add_eq_log_sub hw hm
  rw [h2] at h1
  have e1 : ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w := by push_cast; ring
  have e2 : ((((n : ℝ) + 1 + 1 : ℝ)) : ℂ) + w = ((n + 1 : ℕ) : ℂ) + 1 + w := by push_cast; ring
  rw [e1, e2] at h1
  linear_combination (-1 : ℂ) * h1

def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))

set_option maxHeartbeats 1600000 in
theorem inv_natp1_sq_eq (hw : 0 < w.re) (n : ℕ) :
    1 / ((n : ℂ) + 1 + w) ^ 2
      = (((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n := by
  have h1 := natp1_ne_zero hw n
  have h2 := natp1_ne_zero hw (n + 1)
  have e : ((n + 1 : ℕ) : ℂ) + 1 + w = (n : ℂ) + 2 + w := by push_cast; ring
  rw [e] at h2 ⊢
  unfold rho
  field_simp
  ring

set_option maxHeartbeats 1600000 in
theorem norm_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have h1 := natp1_ne_zero hw n
  have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
  have ht0 : 0 < |w.im| := by linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)

set_option maxHeartbeats 1600000 in
theorem norm_eps_natp1_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have := norm_eps_le hw ht (m := (n : ℝ) + 1) (by positivity)
  rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
  exact this

set_option maxHeartbeats 1600000 in
theorem partial_sum_eq (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
      = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
        - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
        - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
        + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range N, (1 : ℂ) / (w + n + 1)
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) * ((((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n)
        - eps w ((n : ℝ) + 1) := by
    intro n _
    have A := inv_natp1_eq hw n
    have B := inv_natp1_sq_eq hw n
    rw [show (1 : ℂ) / (w + n + 1) = ((n : ℂ) + 1 + w)⁻¹ by rw [one_div]; ring_nf]
    linear_combination A + (1 / 2 : ℂ) * B
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub (fun n => Complex.log ((n : ℂ) + 1 + w)) N, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_range_sub' (fun n => ((n : ℂ) + 1 + w)⁻¹) N]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem norm_sq_natp1_ge (hw : 0 < w.re) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
  have him : ((n : ℂ) + 1 + w).im = w.im := by simp
  rw [hre, him]
  nlinarith

set_option maxHeartbeats 1600000 in
theorem inv_norm_sq_le_telescope (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := norm_sq_natp1_ge hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have htele : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [htele]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]

set_option maxHeartbeats 1600000 in
theorem sum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => inv_norm_sq_le_telescope hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith

set_option maxHeartbeats 1600000 in
theorem summable_inv_norm_sq (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (natp1_le_norm hw n) 2)

set_option maxHeartbeats 1600000 in
theorem summable_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / |w.im|)) fun n => ?_
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
    fun n => ?_
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_norm_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / |w.im|))
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_norm_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem tsum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_inv_norm_sq_le hw ht)

set_option maxHeartbeats 1600000 in
theorem norm_tsum_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (summable_norm_rho hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_rho hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp

set_option maxHeartbeats 1600000 in
theorem norm_tsum_eps_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_eps hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eps hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp

set_option maxHeartbeats 1600000 in
theorem tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  
  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (natp1_ne_zero hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, Zeta23.DigammaSeries.harmonic_cast_eq]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2

set_option maxHeartbeats 1600000 in
theorem tendsto_inv_natp1 (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv]
  have h := natp1_le_norm hw N
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

set_option maxHeartbeats 1600000 in
theorem digamma_eq (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp at this
    rw [← this] at ht; simp at ht; linarith
  have hL := (Zeta23.DigammaSeries.hasSum_digamma_series hmem).tendsto_sum_nat
  
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_rho hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_eps hw ht).hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this

set_option maxHeartbeats 1600000 in
theorem log_one_add_sub_log (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have h1 := integral_inv_add_eq hw (m := 0) le_rfl
  have h2 := integral_inv_add_eq_log_sub hw (m := 0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1

set_option maxHeartbeats 1600000 in
theorem norm_eps_zero_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := norm_eps_le hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp

set_option maxHeartbeats 1600000 in
theorem digamma_stirling (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1wn : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := digamma_eq hw ht
  have hlog := log_one_add_sub_log hw
  
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (norm_eps_zero_le hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (norm_tsum_rho_le hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := norm_tsum_eps_le hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num

end Seq
end StirlingVert
end Zeta23
end
end
/-!
Prime number theorem with an error term, packaged for the Erdős 454 long-chord step
(OMA.R_Erdos454_erdos_454_R1.H1). The last theorem, PNTBridge.piLi_bound, states
π(x) - li(x) = O(x exp(-c (log x)^(1/10))) for some c > 0, where li(x) is the integral of
1 / log u from 2 to x.

This block adapts the following works, each licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).

1. PrimeNumberTheoremAnd, by Alex Kontorovich, Terence Tao and contributors, at commit
   2c476fa6441c607096d93c8fc7ac0a227a655dae: parts of Mathlib/Algebra/Notation/Support.lean,
   Mathlib/Analysis/SpecialFunctions/Log/Basic.lean, Auxiliary.lean, ZetaConj.lean,
   EulerMaclaurin.lean, Fourier.lean, Rectangle.lean, ResidueCalcOnRectangles.lean,
   ZetaBounds.lean, SmoothExistence.lean, MellinCalculus.lean, MediumPNT.lean and
   Consequences.lean. Auxiliary.lean carries this notice:

   Copyright (c) 2024 Michael Stoll. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Michael Stoll

2. The quantitative prime-counting bridge in Erdos878Proofs/QuantitativePNT.lean, from the proof
   of Erdős Problem 878(iv) by Rivka Lipkovitz, developed with OpenAI Codex: the repository
   erdos-878-cofactor-asymptotic at commit 38d5164065e85d6ef02d1c39253389da1ca64fff.

Modified: ported to Lean 4.33.1 and the board's checker rules, trimmed to the declarations
needed for the error term, merged into one file, and the bridge moved into the namespace
PNTBridge with a final restatement, PNTBridge.piLi_bound.
-/

section PNT_Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end PNT_Support

section PNT_Basic

open Filter Real

theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNT_Basic

section PNT_Auxiliary

namespace Complex

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end PNT_Auxiliary

section PNT_ZetaConj

open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]

end PNT_ZetaConj

section PNT_EulerMaclaurin

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  have := aestronglyMeasurable_B1
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end PNT_EulerMaclaurin

section PNT_Fourier

open Complex

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end PNT_Fourier
abbrev HolomorphicOn (f : ℂ → ℂ) (s : Set ℂ) := DifferentiableOn ℂ f s

section PNT_ZetaBounds
open Complex Topology Filter Interval Set Asymptotics MeasureTheory
lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]
lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp
lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]
lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp
lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]
theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
lemma zetaExt : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 1 = 1 ∧
    ∀ s, s ≠ 1 → riemannZeta s = g s / (s - 1) := by
  classical
  set g := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  have hd (w : ℂ) (hw : w ≠ 1) : DifferentiableAt ℂ g w :=
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq
      (by filter_upwards [eventually_ne_nhds hw] with x hx; simp [g, hx])
  refine ⟨g, fun w ↦ ?_, by simp [g], fun s hs ↦ ?_⟩
  · rcases eq_or_ne w 1 with rfl | hw
    · exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        (eventually_nhdsWithin_of_forall hd) (continuousAt_update_same.mpr riemannZeta_residue_one)).differentiableAt
    · exact hd w hw
  · simp [g, hs, sub_ne_zero.mpr hs]
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])
lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf
lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1
lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]
lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s
lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)
lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub
lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num
lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h
lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma Finset.Icc_eq_Ico (M N : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]
lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]
lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_ofPred_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, ofPred_subset_ofPred, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    have e : U = {z : ℂ | 1 < z.re} ∪ {z | 0 < z.re} ∩ {z | 0 < z.im} ∪ {z | 0 < z.re} ∩ {z | z.im < 0}
        ∪ {z | 0 < z.re} ∩ {z | z.re < 1} := by
      ext z
      simp only [U, mem_union, mem_inter_iff, mem_ofPred_eq, ne_eq, Complex.ext_iff, one_re, one_im]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy z.re 1 with h | h | h
        · exact Or.inr ⟨h2, h⟩
        · rcases lt_trichotomy z.im 0 with h' | h' | h'
          · exact Or.inl (Or.inr ⟨h2, h'⟩)
          · exact absurd ⟨h, h'⟩ h1
          · exact Or.inl (Or.inl (Or.inr ⟨h2, h'⟩))
        · exact Or.inl (Or.inl (Or.inl h))
      · rintro (((h | h) | h) | h)
        · exact ⟨fun e ↦ by linarith [e.1], by linarith⟩
        · exact ⟨fun e ↦ by linarith [e.2, h.2], h.1⟩
        · exact ⟨fun e ↦ by linarith [e.2, h.2], h.1⟩
        · exact ⟨fun e ↦ by linarith [e.1, h.2], h.1⟩
    rw [e]
    exact (((convex_halfSpace_re_gt 1).isPreconnected.union (2 + I) (by norm_num) (by norm_num)
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected).union (2 - I)
      (by norm_num) (by norm_num) ((convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_im_lt 0)).isPreconnected).union (1 / 2 + I) (by norm_num) (by norm_num)
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [ofPred_subset_ofPred, imp_self, forall_const, mem_ofPred_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (riemannZeta0 N) s = deriv riemannZeta s := by
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have {x : ℂ} (hx : x ∈ U) : riemannZeta0 N x = riemannZeta x := by
    simp only [mem_ofPred_eq, U] at hx; exact Zeta0EqZeta (N := N) N_pos hx.2 hx.1
  refine deriv_eqOn isOpen_aux ?_ (by simp [s_ne_one, reS_pos])
  intro x hx
  have hζ := HolomorphicOn_riemannZeta.mono (by aesop)|>.hasDerivAt (s := U) <|
    isOpen_aux.mem_nhds hx
  exact hζ.hasDerivWithinAt.congr (fun y hy ↦ this hy) (this hx)
lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd
lemma lt_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a < b → b < c → c < d → a < d :=
  fun hab hbc hcd ↦ lt_trans (lt_trans hab hbc) hcd
lemma norm_add₅_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  apply le_trans <| norm_add_le (a + b + c + d) e
  simp only [add_le_add_iff_right]; apply norm_add₄_le
lemma norm_add₆_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E)
    (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  apply le_trans <| norm_add_le (a + b + c + d + e) f
  simp only [add_le_add_iff_right]; apply norm_add₅_le
lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by
  apply mul_le_mul (mul_le_mul h₁ h₂ c0 b0) h₃ e0 <| mul_nonneg b0 <| le_trans c0 h₂
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)
lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt.le
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]
lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith
lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp
lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]
lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one
lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num
lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)
lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2);
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, RCLike.norm_ofNat, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2)
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp
lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n
lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]
lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]
lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t
lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert! abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)
theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t
theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t
theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert! abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert! this using 1; congr; funext x; ring_nf
theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_iff_right₀ (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_iff_right₀ (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert! UpperBnd_aux2 t_gt hσ.1 using 1
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf
lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]
lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring
lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz
lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound
lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring
lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  dsimp only
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  have h6 := DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
  have e0 := Real.exp_pos A
  have := mul_le_mul_of_nonneg_right (by linarith [show 6 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ =
    3 * (2 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ) by ring] : 6 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ ≤ 48 * Real.exp A)
    (by linarith : 0 ≤ Real.log |t|)
  have := mul_le_mul_of_nonneg_left (by nlinarith : Real.log |t| ≤ Real.log |t| ^ 2) e0.le
  have := mul_le_mul_of_nonneg_left (by nlinarith : 1 ≤ Real.log |t| ^ 2) e0.le
  linarith [DerivUpperBnd_aux1 hA hσ.1 t_gt le_rfl, DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt,
    DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt, DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt,
    DerivUpperBnd_aux5 t_gt hσ Npos σ_gt, DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt]
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖deriv riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩
lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖riemannZeta σ‖ ≤ c / (σ - 1) := by
  obtain ⟨g, hg, -, hζ⟩ := zetaExt
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hg.continuous.comp continuous_ofReal).continuousOn
  refine ⟨max C 1, by positivity, fun σ hσ ↦ ?_⟩
  have h1 : (0:ℝ) < σ - 1 := by linarith [hσ.1]
  rw [hζ σ (by exact_mod_cast hσ.1.ne'), norm_div, ← ofReal_one, ← ofReal_sub, norm_real,
    Real.norm_of_nonneg h1.le]
  exact div_le_div_of_nonneg_right ((hC σ (Ioc_subset_Icc_self hσ)).trans (le_max_left _ _)) h1.le
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 * riemannZeta (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < ( 1 + x : ℂ).re := by simp[hx]
  have h₁ : 1 < (1 + x + I * y).re := by simp [hx]
  have h₂ : 1 < (1 + x + 2 * I * y).re := by simp [hx]
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using
    DirichletCharacter.norm_LSeries_product_ge_one (1 : DirichletCharacter ℂ 1) hx y
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖riemannZeta (σ + t * I)‖ ≤ ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  apply (div_le_iff₀ ?_).mpr
  · apply (Real.rpow_le_rpow_iff (z := 4) (by norm_num) ?_ (by norm_num)).mp
    · simp only [Real.one_rpow]
      rw [Real.mul_rpow, Real.mul_rpow, ← Real.rpow_mul, ← Real.rpow_mul]
      · simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.div_mul_cancel, Real.rpow_one]
        conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm]
        rw [← mul_assoc]
        have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
        simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast] at this
        convert this using 3 <;> ring_nf
      any_goals ring_nf
      any_goals apply norm_nonneg
      any_goals apply Real.rpow_nonneg <| norm_nonneg _
      apply mul_nonneg <;> apply Real.rpow_nonneg <| norm_nonneg _
    · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp [Real.rpow_nonneg]
  · have s_ne_one : σ + t * I ≠ 1 := by
      contrapose! σ_gt; apply le_of_eq; apply And.left; simpa [Complex.ext_iff] using σ_gt
    simpa using riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨A, ha, C, hC, h⟩ := ZetaUpperBnd
  obtain ⟨c, hc, h_inv⟩ := ZetaNear1BndExact
  refine ⟨(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4), by positivity, fun {σ} hσ t ht ↦ ?_⟩
  have h1 : 0 < σ - 1 := by linarith [hσ.1]
  have hL := logt_gt_one ht.le
  have h2t : 3 < |2 * t| := by rw [abs_mul, abs_two]; linarith
  have h2 : Real.log |2 * t| ≤ 2 * Real.log |t| := by
    rw [abs_mul, abs_two, Real.log_mul two_ne_zero (by linarith : (0:ℝ) < |t|).ne']
    linarith [Real.log_two_lt_d9]
  have h0 : 0 ≤ A / Real.log |2 * t| := div_nonneg ha.1.le (Real.log_nonneg (by linarith))
  have h3 := h σ (2 * t) h2t ⟨by linarith [hσ.1], hσ.2⟩
  push_cast at h3
  calc _ ≤ _ := ZetaInvBound1 hσ.1
    _ ≤ (c / (σ - 1)) ^ ((3 : ℝ) / 4) * (2 * C * Real.log |t|) ^ ((1 : ℝ) / 4) :=
      mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (h_inv σ hσ) (by norm_num))
        (Real.rpow_le_rpow (norm_nonneg _) (by linarith [mul_le_mul_of_nonneg_left h2 hC.le])
        (by norm_num)) (by positivity) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hc.le h1.le, Real.mul_rpow (by positivity) (by linarith), neg_div,
        Real.rpow_neg h1.le]
      ring
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨C, hC, h⟩ := ZetaInvBound2
  refine ⟨C⁻¹, inv_pos.mpr hC, fun {σ} hσ t ht ↦ ?_⟩
  have h1 : 0 < σ - 1 := by linarith [hσ.1]
  have ha := Real.rpow_pos_of_pos h1 ((3 : ℝ) / 4)
  have hL := Real.rpow_pos_of_pos (by linarith [logt_gt_one ht.le] : 0 < Real.log |t|) ((1 : ℝ) / 4)
  have := h hσ t ht
  rw [neg_div, Real.rpow_neg h1.le] at this
  calc _ = 1 / (C * ((σ - 1) ^ ((3 : ℝ) / 4))⁻¹ * Real.log |t| ^ ((1 : ℝ) / 4)) := by
        field_simp [ha.ne', hL.ne', hC.ne']
    _ ≤ _ := (one_div_le (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ.1)))
      (mul_pos (mul_pos hC (inv_pos.mpr ha)) hL)).mp this
lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, deriv riemannZeta (σ + t * I)) = riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ riemannZeta (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := deriv riemannZeta) ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| deriv riemannZeta)
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, hA, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, hA, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₂_le σ₁_lt_σ₂
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩
lemma ZetaInvBnd_aux' {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ (9 : ℝ) := by
  nth_rewrite 1 [← Real.rpow_one <| Real.log |t|]
  exact mod_cast Real.rpow_lt_rpow_left_iff (y := 1) (z := 9) logt_gt_one |>.mpr (by norm_num)
lemma ZetaInvBnd_aux {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| ≤ Real.log |t| ^ (9 : ℝ) :=
    ZetaInvBnd_aux' logt_gt_one |>.le
lemma ZetaInvBnd_aux2 {A C₁ C₂ : ℝ} (Apos : 0 < A) (C₁pos : 0 < C₁) (C₂pos : 0 < C₂)
    (hA : A ≤ 1 / 2 * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) :
    0 < (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹ := by
  simp only [inv_pos, sub_pos]
  apply div_lt_iff₀ (by positivity) |>.mp
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), mul_assoc]
  apply lt_div_iff₀' (by positivity) |>.mp
  nth_rewrite 1 [← Real.rpow_one A]
  rw [← Real.rpow_add (by positivity)]
  norm_num
  apply Real.rpow_lt_rpow_iff (z := 4) (by positivity) (by positivity) (by positivity) |>.mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num
  apply lt_of_le_of_lt hA
  rw [div_mul_comm, mul_one, Real.rpow_ofNat]
  apply half_lt_self
  positivity
lemma ZetaLowerBndIco :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) (1 + A / (Real.log |t|) ^ (9 : ℝ))),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨C', C'pos, hC₁⟩ := ZetaInvBound2
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd
  set C₁ := 1 / C'
  let A := min A' <| (1 / 2 : ℝ) * (C₁ / (C₂ * 2)) ^ (4 : ℝ)
  have Apos : 0 < A := by have := hA'.1; positivity
  have Ale : A ≤ 1 / 2 := by dsimp only [A]; apply min_le_iff.mpr; left; exact hA'.2
  set C := (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹
  have Cpos : 0 < C := by
    refine ZetaInvBnd_aux2 (by positivity) (by positivity) (by positivity) ?_
    apply min_le_right
  refine ⟨A, ⟨Apos, by linarith [hA'.2]⟩ , C⁻¹, inv_pos.mpr Cpos, ?_⟩
  intro σ t t_gt hσ
  have logt_gt_one := logt_gt_one t_gt.le
  have σ_ge : 1 - A / Real.log |t| ≤ σ := by
    apply le_trans ?_ hσ.1
    suffices A / Real.log |t| ^ (9 : ℝ) ≤ A / Real.log |t| by linarith
    exact div_le_div₀ Apos.le (by rfl) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  obtain ⟨_, _, neOne⟩ := UpperBnd_aux ⟨Apos, Ale⟩ t_gt σ_ge
  set σ' := 1 + A / Real.log |t| ^ (9 : ℝ)
  have σ'_gt : 1 < σ' := by simp only [σ', lt_add_iff_pos_right]; positivity
  have σ'_le : σ' ≤ 2 := by
    simp only [σ']
    suffices A / Real.log |t| ^ (9 : ℝ) < 1 by linarith
    apply div_lt_one (by positivity) |>.mpr
    exact lt_trans₄ (by linarith) logt_gt_one <| ZetaInvBnd_aux' logt_gt_one
  set s := σ + t * I
  set s' := σ' + t * I
  have e : C⁻¹ / Real.log |t| ^ (7 : ℝ) = 1 / (C * Real.log |t| ^ (7 : ℝ)) := by
    rw [div_mul_eq_div_div, one_div]
  rw [e]
  have pos_aux : 0 < (σ' - 1) := by linarith
  calc
    _ ≥ ‖riemannZeta s'‖ - ‖riemannZeta s - riemannZeta s'‖ := ?_
    _ ≥ C₁ * (σ' - 1) ^ ((3 : ℝ)/ 4) * Real.log |t|  ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ 2 * (σ' - σ) := ?_
    _ ≥ C₁ * (A / Real.log |t| ^ (9 : ℝ)) ^ ((3 : ℝ)/ 4) * Real.log |t| ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ (2 : ℝ) * 2 * A / Real.log |t| ^ (9 : ℝ) := ?_
    _ ≥ C₁ * A ^ ((3 : ℝ)/ 4) * Real.log |t| ^ (-7 : ℝ) - C₂ * 2 * A * Real.log |t| ^ (-7 : ℝ) := ?_
    _ = (C₁ * A ^ ((3 : ℝ)/ 4) - C₂ * 2 * A) * Real.log |t| ^ (-7 : ℝ) := by ring
    _ ≥ _ := ?_
  · apply ge_iff_le.mpr
    convert norm_sub_norm_le (a := riemannZeta s') (b := riemannZeta s' - riemannZeta s) using 1
    · rw [(by simp : riemannZeta s' - riemannZeta s = -(riemannZeta s - riemannZeta s'))]; simp only [norm_neg]
    · simp
  · apply sub_le_sub
    · have := one_div_le ?_ (by positivity) |>.mp <| hC₁ ⟨σ'_gt, σ'_le⟩ t t_gt
      · convert this using 1
        rw [one_div, mul_inv_rev, mul_comm, mul_inv_rev, mul_comm _ C'⁻¹]
        simp only [one_div C', C₁]
        congr <;> (rw [← Real.rpow_neg (by linarith), neg_div]); rw [neg_neg]
      · apply norm_pos_iff.mpr <| riemannZeta_ne_zero_of_one_lt_re (by simp [σ'_gt])
    · rw [(by simp : riemannZeta s - riemannZeta s' = -(riemannZeta s' - riemannZeta s)), norm_neg]
      refine hC₂ σ σ' t t_gt ?_ σ'_le <| by rw [Set.mem_Ico] at hσ; exact hσ.2
      apply le_trans ?_ hσ.1
      rw [tsub_le_iff_right, ← add_sub_right_comm, le_sub_iff_add_le, add_le_add_iff_left]
      exact div_le_div₀ hA'.1.le (by simp [A]) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  · apply sub_le_sub (by simp only [add_sub_cancel_left, σ']; exact_mod_cast le_rfl) ?_
    rw [mul_div_assoc, mul_assoc _ 2 _]
    apply mul_le_mul (by exact_mod_cast le_rfl) ?_ (by linarith [hσ.2]) (by positivity)
    suffices h : σ' + (1 - A / Real.log |t| ^ (9 : ℝ)) ≤ (1 + A / Real.log |t| ^ (9 : ℝ)) + σ by
      simp only [tsub_le_iff_right]
      convert! le_sub_right_of_add_le h using 1; ring_nf
    exact add_le_add (by linarith) (by linarith [hσ.1])
  · simp_rw [tsub_le_iff_right, div_eq_mul_inv _ (Real.log |t| ^ (9 : ℝ))]
    rw [← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
    conv => rhs; lhs; rw [mul_assoc, ← Real.rpow_add (by positivity)]
    rw [(by ring : C₂ * Real.log |t| ^ (2 : ℝ) * A * Real.log |t| ^ (-9 : ℝ) * 2 = C₂ * (Real.log |t| ^ (2 : ℝ) * Real.log |t| ^ (-9 : ℝ) ) * A * 2)]
    rw [← Real.rpow_add (by positivity)]; norm_num; group; exact le_rfl
  · apply div_le_iff₀ (by positivity) |>.mpr
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm C, ← mul_assoc, ← Real.rpow_add (by positivity)]
    have := inv_inv C ▸ mul_inv_cancel₀ (a := C⁻¹) (by positivity) |>.symm.le
    simpa [C] using this

end PNT_ZetaBounds

open Complex Filter Topology

namespace PolygammaEstimate

private theorem zero_strip (p : Vc) : 0 < (Y5 p).re ∧ (Y5 p).re < 1 := by
  have h0 := Zj p
  have hz := Za p
  have h1 : Y5 p ≠ 1 := by
    intro he
    rw [he, Robin1984.We] at hz
    norm_num at hz
  have hζ := Robin1984.vi h0 h1 hz
  constructor
  · by_contra! hn
    have hζ' := Robin1984.vi (sub_ne_zero.mpr h1.symm)
      (show 1 - Y5 p ≠ 1 by intro h; exact h0 (sub_eq_self.mp h))
      (show uj (1 - Y5 p) = 0 by rw [WA]; exact hz)
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith : 1 ≤ (1 - Y5 p).re) hζ'
  · exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hζ)

private theorem xi_lower {s : ℂ} (hs : 1 ≤ s.re) :
    (logDeriv uj 0).re ≤ (logDeriv uj s).re := by
  obtain ⟨P, hP, hf⟩ := yA
  have hne (p : Vc) : s ≠ Y5 p := by
    intro h
    rw [h] at hs
    exact (zero_strip p).2.not_ge hs
  rw [zH hf hne, Robin1984.zi hP hf, Complex.add_re]
  apply le_add_of_nonneg_right
  let f (p : Vc) := 1 / (s - Y5 p) + 1 / Y5 p
  change 0 ≤ (∑' p, f p).re
  by_cases h : Summable f
  · rw [Complex.re_tsum h]
    apply tsum_nonneg
    intro p
    dsimp [f]
    simp only [one_div, inv_re, sub_re, add_re]
    have hz := zero_strip p
    exact add_nonneg (div_nonneg (by linarith [hz.2]) (normSq_nonneg _))
      (div_nonneg hz.1.le (normSq_nonneg _))
  · simp [tsum_eq_zero_of_not_summable h]

private theorem xi_eq {s : ℂ} (hr : 0 < s.re) (h1 : s ≠ 1) : Kadiri.Wp s = uj s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hg := Gamma_ne_zero_of_re_pos (by simpa using half_pos hr : 0 < (s / 2).re)
  rw [Kadiri.Wp, Kadiri.WZ, Kadiri.WS, Robin1984.YZ, Gamma_add_one _ (div_ne_zero h0 two_ne_zero),
    v2 h0 h1, zx h0 hg]
  ring_nf

theorem zeta_deriv_re_lower {s : ℂ} (hs : s.re = 1) (h1 : s ≠ 1) :
    (logDeriv uj 0).re + Real.log Real.pi / 2 - (1 / (s-1)).re -
      (digamma (s/2+1)).re / 2 ≤ (logDeriv riemannZeta s).re := by
  have hr : 0 < s.re := by rw [hs]; norm_num
  have he : Kadiri.Wp =ᶠ[𝓝 s] uj := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hr,
      eventually_ne_nhds h1] with w hw hw1
    exact xi_eq hw hw1
  have hdiff (m : ℕ) : s / 2 + 1 ≠ -(m : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp [hs] at hh
    have : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  have h := Kadiri.Yq s h1 hdiff (Gamma_ne_zero hdiff) (riemannZeta_ne_zero_of_one_le_re hs.ge)
  rw [(logDeriv_congr_nhds he).self_of_nhds] at h
  have hh := congrArg Complex.re h
  simp [Complex.mul_re, logDeriv_apply] at hh ⊢
  have hxi := xi_lower hs.ge
  simp [logDeriv_apply] at hxi
  linarith

end PolygammaEstimate

namespace PolygammaEstimate

open Complex

private theorem digamma_log_bound {w : ℂ} (hr : 0 < w.re) (hi : 1 ≤ |w.im|) :
    ‖digamma w - log w‖ ≤ 4 := by
  have h := Zeta23.StirlingVert.digamma_stirling hr (by linarith)
  have hn : 1 ≤ ‖w‖ := hi.trans (abs_im_le_norm _)
  have hq : ‖(1/2:ℂ) / w‖ ≤ 1 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    norm_num
    linarith
  have hh : 1 ≤ w.im ^ 2 := by nlinarith [sq_abs w.im, sq_nonneg (|w.im|-1)]
  have hb : 3 / w.im ^ 2 ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have ht := norm_sub_le (digamma w - log w + (1/2:ℂ)/w) ((1/2:ℂ)/w)
  rw [add_sub_cancel_right] at ht
  linarith

theorem digamma_bounds {x : ℝ} (hx : 4 < x) :
    Real.log x - 5 ≤ (digamma (-(I*x))).re ∧
    ‖digamma (-(I*x))‖ ≤ 2*x + 10 ∧
    (digamma ((I*x+1)/2+1)).re ≤ Real.log x + 5 := by
  let z : ℂ := -(I*x)
  let w := z + 1
  let v : ℂ := (I*x+1)/2+1
  have hx0 : 0 < x := by linarith
  have hwre : w.re = 1 := by simp [w,z]
  have hwim : w.im = -x := by simp [w,z]
  have hvre : v.re = 3/2 := by simp [v]; norm_num
  have hvim : v.im = x/2 := by simp [v]
  have hb := digamma_log_bound (w := w) (by rw [hwre]; norm_num)
    (by rw [hwim,abs_neg,abs_of_pos hx0]; linarith)
  have hc := digamma_log_bound (w := v) (by rw [hvre]; norm_num)
    (by rw [hvim,abs_of_pos (by positivity)]; linarith)
  have h1 := neg_le_of_abs_le ((abs_re_le_norm (digamma w-log w)).trans hb)
  have h2 := (re_le_norm (digamma v-log v)).trans hc
  simp only [sub_re,log_re] at h1 h2
  have hwlo : x ≤ ‖w‖ := by simpa only [hwim, abs_neg, abs_of_pos hx0] using abs_im_le_norm w
  have hwup : ‖w‖ ≤ 1+x := by
    simpa only [hwre,hwim,abs_one,abs_neg,abs_of_pos hx0] using norm_le_abs_re_add_abs_im w
  have hvlo : 0 < ‖v‖ := by have := re_le_norm v; rw [hvre] at this; linarith
  have hvup : ‖v‖ ≤ 2*x := by
    have := norm_le_abs_re_add_abs_im v
    rw [hvre,hvim,abs_of_pos (by norm_num),abs_of_pos (by positivity)] at this
    linarith
  have hlog := Real.log_le_log hx0 hwlo
  have hlog' := Real.log_le_log hvlo hvup
  rw [Real.log_mul (by norm_num) hx0.ne'] at hlog'
  have hn : ‖log w‖ ≤ 1 + x + Real.pi := by
    have hh := norm_le_abs_re_add_abs_im (log w)
    rw [log_re,log_im,abs_of_nonneg (Real.log_nonneg (by linarith))] at hh
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le hx0 hwlo), abs_arg_le_pi w]
  have hshift := digamma_apply_add_one z (by
    intro n h
    have := congrArg Complex.im h
    simp [z] at this
    linarith)
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv, show ‖z‖ = x by simp [z,abs_of_pos hx0]]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hdiff : digamma z = (digamma w-log w) + log w - z⁻¹ := by
    dsimp [w]; rw [hshift]; ring
  refine ⟨?_,?_,?_⟩
  · change _ ≤ (digamma z).re
    have hshift' : (digamma w).re = (digamma z).re + (z⁻¹).re := congrArg Complex.re hshift
    linarith [(re_le_norm z⁻¹).trans hinv]
  · change ‖digamma z‖ ≤ _
    rw [hdiff]
    have h := norm_sub_le ((digamma w-log w)+log w) z⁻¹
    have h' := norm_add_le (digamma w-log w) (log w)
    linarith [Real.pi_lt_four]
  · change (digamma v).re ≤ _
    linarith [Real.log_two_lt_d9]

end PolygammaEstimate

namespace PolygammaEstimate

open Complex Filter Topology OMA.S_mse_1364979
open scoped ComplexConjugate

lemma factorization {x : ℝ} (hx : 0 < x) :
    genPolygamma1 (I * x) = riemannZeta (I * x + 1) / Gamma (-(I * x)) *
      (eulerGamma + digamma (-(I * x)) + logDeriv riemannZeta (I * x + 1)) := by
  let z : ℂ := I * x
  have hp (m : ℕ) : -z ≠ -(m : ℂ) := by
    intro he
    have := congrArg Complex.im he
    simp [z] at this
    linarith
  have hz : z + 1 ≠ 1 := by
    intro he
    have := congrArg Complex.im he
    simp [z] at this
    linarith
  have hg := Gamma_ne_zero hp
  have hζ : riemannZeta (z + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp [z])
  have he := ((hasDerivAt_id z).const_mul (eulerGamma : ℂ)).cexp
  have hs := (differentiableAt_riemannZeta hz).hasDerivAt.comp z ((hasDerivAt_id z).add_const 1)
  have hd := (differentiableAt_Gamma _ hp).hasDerivAt.comp z (hasDerivAt_id z).neg
  unfold genPolygamma1
  change exp (-(eulerGamma : ℂ) * z) * _ = _
  rw [show -(eulerGamma : ℂ) * z = -((eulerGamma : ℂ) * z) by ring, Complex.exp_neg]
  rw [show deriv (fun w : ℂ => exp ((eulerGamma : ℂ) * w) * riemannZeta (w + 1) / Gamma (-w)) (I * x) = _ from (((he.mul hs).div hd hg).deriv)]
  simp only [id_eq, Function.comp_apply, mul_one, mul_neg, digamma, logDeriv_apply]
  change _ = riemannZeta (z + 1) / Gamma (-z) *
    (eulerGamma + deriv Gamma (-z) / Gamma (-z) + deriv riemannZeta (z + 1) / riemannZeta (z + 1))
  simp only [Pi.mul_apply, Function.comp_apply]
  field_simp [Complex.exp_ne_zero, hg, hζ]
  ring

lemma gamma_norm {x : ℝ} (hx : 0 < x) :
    ‖Gamma (-(I * x))‖ ^ 2 * x = Real.pi / Real.sinh (Real.pi * x) := by
  let z : ℂ := I * x
  have hz : z ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have hc : conj z = -z := by simp [z]
  have hn : ‖Gamma z‖ = ‖Gamma (-z)‖ := by rw [← hc, Gamma_conj, norm_conj]
  have hs : sin (Real.pi * z) = (Real.sinh (Real.pi * x) : ℂ) * I := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * x : ℝ) : ℂ) * I by push_cast; dsimp [z]; ring,
      sin_mul_I, ofReal_sinh]
  have h := congrArg norm (Gamma_mul_Gamma_one_sub (-z))
  rw [sub_neg_eq_add, add_comm (1 : ℂ), Gamma_add_one z hz, mul_neg, sin_neg, hs] at h
  simp only [norm_mul, norm_div, norm_neg, norm_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx))] at h
  rw [show ‖z‖ = x by simp [z, abs_of_pos hx], hn] at h
  change ‖Gamma (-z)‖ ^ 2 * x = _
  linarith only [h]

lemma gamma_rate :
    Tendsto (fun x : ℝ => Real.log ‖Gamma (-(I * x))‖ / x) atTop (𝓝 (-(Real.pi / 2))) := by
  have heq : (fun x : ℝ => Real.log ‖Gamma (-(I * x))‖ / x) =ᶠ[atTop]
      (fun x : ℝ => (Real.log Real.pi - Real.log ((Real.exp (Real.pi * x) -
        Real.exp (-(Real.pi * x))) / 2) - Real.log x) / (2 * x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := gamma_norm hx
    have hS := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx)
    have hG : ‖Gamma (-(I * x))‖ ≠ 0 := by
      intro hh
      rw [hh] at h
      simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, zero_mul] at h
      exact (div_pos Real.pi_pos hS).ne' h.symm
    have hl := congrArg Real.log h
    rw [Real.log_mul (pow_ne_zero 2 hG) hx.ne', Real.log_pow,
      Real.log_div Real.pi_ne_zero hS.ne', Real.sinh_eq] at hl
    field_simp
    rw [mul_comm x Real.pi]
    linarith
  apply (tendsto_congr' heq).mpr
  have hlogx := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hdec : Tendsto (fun x : ℝ => Real.exp (-(2 * Real.pi * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
  have hfactor : Tendsto (fun x : ℝ => (1 - Real.exp (-(2 * Real.pi * x))) / 2) atTop (𝓝 (1/2)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hdec).div_const 2
  have hc := (hfactor.log (by norm_num)).div_atTop tendsto_id
  have hlim := ((((tendsto_const_nhds (x := Real.log Real.pi)).div_atTop tendsto_id).sub
    (tendsto_const_nhds (x := Real.pi))).sub hc).sub hlogx
  convert (hlim.div_const 2).congr' ?_ using 1
  · norm_num; ring
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hsplit : (Real.exp (Real.pi*x) - Real.exp (-(Real.pi*x))) / 2 =
      Real.exp (Real.pi*x) * ((1 - Real.exp (-(2*Real.pi*x)))/2) := by
    have he : Real.exp (Real.pi*x) * Real.exp (-(2*Real.pi*x)) = Real.exp (-(Real.pi*x)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination he/2
  have he : Real.exp (-(2*Real.pi*x)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos hx])
  dsimp
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  field_simp
  ring

end PolygammaEstimate

namespace PolygammaEstimate

open Complex Filter Topology OMA.S_mse_1364979

private noncomputable def correction (x : ℝ) : ℂ :=
  eulerGamma + digamma (-(I*x)) + logDeriv riemannZeta (I*x+1)

private theorem correction_lower : ∀ᶠ x : ℝ in atTop, 1 ≤ ‖correction x‖ := by
  filter_upwards [eventually_gt_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (2 * (10 - eulerGamma - (logDeriv uj 0).re - Real.log Real.pi / 2))] with x hx hlog
  have h1 : I*(x:ℂ)+1 ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h := zeta_deriv_re_lower (s := I*x+1) (by simp) h1
  have hp : (1 / ((I*(x:ℂ)+1)-1)).re = 0 := by simp [one_div, inv_re]
  rw [hp] at h
  have hd := digamma_bounds hx
  apply le_trans _ (re_le_norm (correction x))
  simp only [correction,add_re,ofReal_re]
  linarith [hd.1,hd.2.2]

private noncomputable def numerator (x : ℝ) : ℂ := riemannZeta (I*x+1) * correction x

private theorem numerator_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      c / x^7 ≤ ‖numerator x‖ ∧ ‖numerator x‖ ≤ C*x^2 := by
  obtain ⟨A,hA,U,hU,hu⟩ := ZetaUpperBnd
  obtain ⟨B,hB,D,hD,hd⟩ := ZetaDerivUpperBnd
  obtain ⟨E,hE,c,hc,hl⟩ := ZetaLowerBndIco
  refine ⟨c, U*(|eulerGamma|+12)+D, hc, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (4:ℝ), correction_lower] with x hx hcorr
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hle : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hx3 : 3 < |x| := by rw [abs_of_pos hx0]; linarith
  have hu' := hu 1 x hx3 (by rw [abs_of_pos hx0]; exact ⟨by linarith [div_pos hA.1 hlog], by norm_num⟩)
  have hd' := hd 1 x hx3 (by rw [abs_of_pos hx0]; exact ⟨by linarith [div_pos hB.1 hlog], by norm_num⟩)
  have hl' := hl 1 x hx3 (by
    rw [abs_of_pos hx0]
    have h := div_pos hE.1 (Real.rpow_pos_of_pos hlog 9)
    exact ⟨by linarith, by linarith⟩)
  simp only [Complex.ofReal_one, abs_of_pos hx0,
    add_comm (1:ℂ), mul_comm (x:ℂ) I] at hu' hd' hl'
  norm_cast at hl'
  let s : ℂ := I*x+1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp [s])
  constructor
  · calc
      c/x^7 ≤ c/Real.log x^7 := by gcongr
      _ ≤ ‖riemannZeta s‖ := hl'
      _ ≤ ‖riemannZeta s‖ * ‖correction x‖ := le_mul_of_one_le_right (norm_nonneg _) hcorr
      _ = ‖numerator x‖ := (norm_mul _ _).symm
  · have hn : numerator x = riemannZeta s * ((eulerGamma:ℂ) + digamma (-(I*x))) +
        deriv riemannZeta s := by
      unfold numerator correction
      change riemannZeta s * (_ + logDeriv riemannZeta s) = _
      rw [logDeriv_apply, mul_add]
      field_simp
    have hψ := (digamma_bounds hx).2.1
    have hpair : ‖(eulerGamma:ℂ) + digamma (-(I*x))‖ ≤ (|eulerGamma| + 12)*x := by
      have htri := norm_add_le (eulerGamma:ℂ) (digamma (-(I*x)))
      rw [Complex.norm_real,Real.norm_eq_abs] at htri
      nlinarith [mul_nonneg (abs_nonneg eulerGamma) (sub_nonneg.mpr hx1)]
    have hzupper : ‖riemannZeta s‖ ≤ U*x := hu'.trans (by gcongr)
    have hdUpper : ‖deriv riemannZeta s‖ ≤ D*x^2 := hd'.trans (by gcongr)
    rw [hn]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    calc
      _ ≤ (U*x)*((|eulerGamma|+12)*x) + D*x^2 :=
        add_le_add (mul_le_mul hzupper hpair (norm_nonneg _) (by positivity)) hdUpper
      _ = _ := by ring

private theorem numerator_rate : Tendsto (fun x : ℝ => Real.log ‖numerator x‖ / x) atTop (𝓝 0) := by
  obtain ⟨c,C,hc,hC,h⟩ := numerator_bounds
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlo := ((tendsto_const_nhds (x := Real.log c)).div_atTop tendsto_id).sub (hlog.const_mul 7)
  have hhi := ((tendsto_const_nhds (x := Real.log C)).div_atTop tendsto_id).add (hlog.const_mul 2)
  simp only [mul_zero,sub_zero,add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [h,eventually_gt_atTop (0 : ℝ)] with x h hx
    have hh := div_le_div_of_nonneg_right (Real.log_le_log (by positivity) h.1) hx.le
    rw [Real.log_div hc.ne' (pow_ne_zero _ hx.ne'), Real.log_pow] at hh
    dsimp
    convert hh using 1 <;> push_cast <;> ring
  · filter_upwards [h,eventually_gt_atTop (0 : ℝ)] with x h hx
    have hp : 0 < ‖numerator x‖ := lt_of_lt_of_le (by positivity : 0 < c/x^7) h.1
    have hh := div_le_div_of_nonneg_right (Real.log_le_log hp h.2) hx.le
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hx.ne'), Real.log_pow] at hh
    dsimp
    convert hh using 1 <;> push_cast <;> ring

end PolygammaEstimate

open Complex Filter Topology OMA.S_mse_1364979 PolygammaEstimate

theorem OMA.solution : type_of% @OMA.S_mse_1364979.main := by
  have h := numerator_rate.sub gamma_rate
  rw [zero_sub, neg_neg] at h
  apply h.congr'
  obtain ⟨c,C,hc,_,hb⟩ := numerator_bounds
  filter_upwards [eventually_gt_atTop (0 : ℝ),hb] with x hx hbound
  have hn : 0 < ‖numerator x‖ := lt_of_lt_of_le (by positivity : 0 < c/x^7) hbound.1
  have hg : ‖Gamma (-(I*x))‖ ≠ 0 := by
    intro he
    have heq := gamma_norm hx
    rw [he] at heq
    simp at heq
    exact (div_pos Real.pi_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx))).ne' heq.symm
  have heq : genPolygamma1 (I*x) = numerator x / Gamma (-(I*x)) := by
    rw [factorization hx]
    unfold numerator correction
    ring
  rw [heq,norm_div,Real.log_div hn.ne' hg]
  ring

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a “NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an “AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
