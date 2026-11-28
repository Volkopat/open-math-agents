import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1
import Mathlib

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
theorem vP : (-2:ℂ)*logDeriv uj 0=(Real.eulerMascheroniConstant:ℂ)+2 - (Real.log (4*Real.pi):ℂ):=by
  have qa :
      HasDerivAt completedRiemannZeta₀
        (deriv completedRiemannZeta₀ 0) 0 :=
    differentiable_completedZeta₀.differentiableAt.hasDerivAt
  have qb :
      HasDerivAt (fun s:ℂ => s*(s - 1)) (-1) 0:=by
    have qd :=
      (hasDerivAt_id (0:ℂ)).mul
        ((hasDerivAt_id (0:ℂ)).sub
          (hasDerivAt_const (0:ℂ) (1:ℂ)))
    refine
      (qd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro s
      rfl
    . simp [id_eq]
  have qc :
      HasDerivAt uj (-completedRiemannZeta₀ 0/2) 0:=by
    have qd :=
      (((qb.mul qa).add
        (hasDerivAt_const (0:ℂ) (1:ℂ))).div_const 2)
    refine
      (qd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro s
      rfl
    . ring
  rw [logDeriv_apply,qc.deriv,W4,
    Zp,completedRiemannZeta₀_one]
  rw [Complex.ofReal_log (by positivity : (0:ℝ) ≤ 4*Real.pi)]
  push_cast
  ring
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
theorem zq (hRH : RiemannHypothesis) (p : Vc) : (Y5 p).re=(1/2:ℝ):=by
  let z : ℂ:=Y5 p
  have qh : Not (z=0) :=
    Zj p
  have hXi : uj z=0 :=
    Za p
  have qi : uj (1:ℂ)=1/2:=by
    simpa [W4] using (WA (0:ℂ))
  have qj : Not (z=1):=by
    intro hz
    rw [hz,qi] at hXi
    norm_num at hXi
  have qk : riemannZeta z=0 :=
    vi qh qj hXi
  have ql : 0 < z.re:=by
    by_contra hNotPos
    have qg : z.re <= 0:=le_of_not_gt hNotPos
    have qe : uj (1 - z)=0:=by
      rw [WA]
      exact hXi
    have qb : Not (1 - z=0) :=
      sub_ne_zero.mpr (Ne.symm qj)
    have qd : Not (1 - z=1):=by
      intro h
      apply qh
      exact sub_eq_self.mp h
    have qc : riemannZeta (1 - z)=0 :=
      vi
        qb qd qe
    have qf : 1 <= (1 - z).re:=by
      change 1 <= 1 - z.re
      linarith
    exact (riemannZeta_ne_zero_of_one_le_re qf qc).elim
  apply hRH z qk
  . intro hTrivial
    choose n hn using hTrivial
    rw [hn] at ql
    norm_num at ql
    have qa :
        (0:ℝ) <= 2*((n:ℝ)+1):=by
      positivity
    exact (not_lt_of_ge qa) ql
  . exact qj
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
theorem w4 : logDeriv uj (1:ℂ) = -logDeriv uj 0:=by
  have qe :
      HasDerivAt uj
        (deriv uj (1 - (0:ℂ))) (1 - (0:ℂ)) :=
    VB.differentiableAt.hasDerivAt
  have qf :
      HasDerivAt (fun z:ℂ => 1 - z) (-1) 0 :=
    (hasDerivAt_id (0:ℂ)).const_sub 1
  have qg:=qe.comp (0:ℂ) qf
  have qa :
      HasDerivAt (fun z:ℂ => uj (1 - z))
        (-deriv uj (1:ℂ)) 0:=by
    refine
      (qg.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro z
      rfl
    . simp
  have qc :
      (fun z:ℂ => uj (1 - z))=uj:=by
    funext z
    exact WA z
  have qb :
      deriv uj 0 = -deriv uj (1:ℂ):=by
    have h:=qa.deriv
    rw [qc] at h
    exact h
  have qd :
      deriv uj (1:ℂ) = -deriv uj 0:=by
    have h:=congrArg Neg.neg qb
    simpa using h.symm
  rw [logDeriv_apply,logDeriv_apply,qd,
    We,W4]
  ring
theorem yo (hRH : RiemannHypothesis) (p : Vc) : 1/(1 - Y5 p)+1/Y5 p=(((Inv.inv (norm (Y5 p)))^(2 : Nat):ℝ):ℂ):=by
  let rho : ℂ:=Y5 p
  have qc : Not (rho=0) :=
    Zj p
  have hRe : rho.re=(1/2:ℝ) :=
    zq hRH p
  have qd : 1 - rho=conj rho:=by
    apply Complex.ext
    . rw [Complex.sub_re,Complex.one_re,Complex.conj_re,hRe]
      norm_num
    . simp
  have qa : Not (1 - rho=0):=by
    intro h
    rw [qd] at h
    apply qc
    have h':=congrArg conj h
    simpa using h'
  have qb : Not (norm rho=0) :=
    norm_ne_zero_iff.mpr qc
  change
    1/(1 - rho)+1/rho =
      (((Inv.inv (norm rho))^(2 : Nat):ℝ):ℂ)
  calc
    1/(1 - rho)+1/rho =
        1/(rho*(1 - rho)):=by
          field_simp [qc,qa]
          ring
    _ = (((Inv.inv (norm rho))^(2 : Nat):ℝ):ℂ):=by
      rw [qd,Complex.mul_conj,Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [qb]
theorem YX :
  Summable (fun p : Vc =>
   (Inv.inv (norm (Y5 p)))^(2 : Nat)) :=
 va
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
theorem yG (hRH : RiemannHypothesis) : tsum (fun p : Vc => (Inv.inv (norm (Y5 p)))^(2 : Nat))=Real.eulerMascheroniConstant+2 - Real.log (4*Real.pi):=by
  choose P hP using yA
  have qk : P.degree <= 1:=hP.1
  have qd:=hP.2
  have qg :
      forall p : Vc,
        Not ((0:ℂ)=Y5 p):=by
    intro p
    exact (Zj p).symm
  have qh :
      forall p : Vc,
        Not ((1:ℂ)=Y5 p):=by
    intro p hOne
    have hXi:=Za p
    rw [<- hOne,We] at hXi
    norm_num at hXi
  have ql :=
    zH
      (P:=P) (z:=(0:ℂ)) qd qg
  have qm :=
    zH
      (P:=P) (z:=(1:ℂ)) qd qh
  have qi :
      tsum (fun p : Vc =>
        (1/((0:ℂ) - Y5 p) +
          1/Y5 p))=0:=by
    have qe :
        (fun p : Vc =>
          (1/((0:ℂ) - Y5 p) +
            1/Y5 p)) =
          (fun _p : Vc => (0:ℂ)):=by
      funext p
      have qn : Not (Y5 p=0) :=
        Zj p
      field_simp [qn]
      ring
    rw [qe]
    simp
  have qc :
      logDeriv uj 0=Polynomial.eval 0 P.derivative:=by
    rw [qi,add_zero] at ql
    exact ql
  have qa :
      Polynomial.eval (1:ℂ) P.derivative =
        Polynomial.eval 0 P.derivative :=
    Polynomial.zr
      qk 1
  have qf :
      tsum (fun p : Vc =>
        (1/(1 - Y5 p) +
          1/Y5 p)) =
        (-2:ℂ)*logDeriv uj 0:=by
    calc
      tsum (fun p : Vc =>
          (1/(1 - Y5 p) +
            1/Y5 p)) =
          logDeriv uj 1 -
            Polynomial.eval 1 P.derivative:=by
              rw [qm]
              ring
      _ = -logDeriv uj 0 -
            Polynomial.eval 0 P.derivative:=by
              rw [w4,
                qa]
      _ = (-2:ℂ)*logDeriv uj 0:=by
              rw [qc]
              ring
  have qb :
      tsum (fun p : Vc =>
        (1/(1 - Y5 p) +
          1/Y5 p)) =
        (Real.eulerMascheroniConstant:ℂ)+2 -
          (Real.log (4*Real.pi):ℂ) :=
    qf.trans vP
  have qj :
      ((tsum (fun p : Vc =>
          (Inv.inv (norm (Y5 p)))^(2 : Nat)) :
          ℝ) :
          ℂ) =
        (Real.eulerMascheroniConstant:ℂ)+2 -
          (Real.log (4*Real.pi):ℂ):=by
    rw [Complex.ofReal_tsum]
    calc
      tsum (fun p : Vc =>
          (((Inv.inv (norm (Y5 p)))^(2 : Nat):ℝ) :
            ℂ)) =
          tsum (fun p : Vc =>
            (1/(1 - Y5 p) +
              1/Y5 p)):=by
                apply tsum_congr
                intro p
                exact
                  (yo
                    hRH p).symm
      _ = (Real.eulerMascheroniConstant:ℂ)+2 -
          (Real.log (4*Real.pi):ℂ) :=
            qb
  exact Complex.ofReal_inj.mp (by simpa using qj)
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
def WT (n : Nat) (rho:ℂ) (x:ℝ):ℂ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ =>
  (t:ℂ)^(rho - (n:ℂ) - 1) *
   (((n:ℝ)*Real.log t+1) /
    (Real.log t)^(2 : Nat):ℝ))
theorem Yf {a:ℂ} {x:ℝ} (hx : 1 < x) (ha : a.re < -1) (k : Nat) : IntegrableOn (fun t:ℝ => (t:ℂ)^a*(((Inv.inv ((Real.log t)^k):ℝ):ℂ))) (Ioi x):=by
  have qf : 0 < x:=lt_trans Real.zero_lt_one hx
  have qg :
      IntegrableOn (fun t:ℝ => (t:ℂ)^a) (Ioi x) :=
    integrableOn_Ioi_cpow_of_lt ha qf
  have qd : 0 < Real.log x:=Real.log_pos hx
  apply qg.mul_bdd (c:=Inv.inv ((Real.log x)^k))
  . have qa :
        Measurable (fun t:ℝ => Inv.inv ((Real.log t)^k)) :=
      (Measurable.pow_const Real.measurable_log k).inv
    exact
      (Complex.continuous_ofReal.measurable.comp qa).aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x <= t:=ht.le
    have qh : Real.log x <= Real.log t:=Real.log_le_log qf hxt
    have qb : 0 < Real.log t:=lt_of_lt_of_le qd qh
    have qi : (Real.log x)^k <= (Real.log t)^k:=by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ,pow_succ]
          exact mul_le_mul ih qh qd.le
            (pow_nonneg qb.le k)
    have qe : 0 < (Real.log t)^k:=pow_pos qb k
    have qc : 0 < (Real.log x)^k:=pow_pos qd k
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr qe)]
    simpa [one_div] using one_div_le_one_div_of_le qc qi
def WO (a:ℂ) (k : Nat) (x:ℝ):ℂ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ =>
  (t:ℂ)^(a - 1) *
   (((Inv.inv ((Real.log t)^k):ℝ):ℂ)))
def Vv
  (n : Nat) (rho:ℂ) (x:ℝ):ℂ :=
 rho/(rho - (n:ℂ))^(2 : Nat) *
  (-((x:ℂ)^(rho - (n:ℂ))) /
    ((Real.log x:ℝ):ℂ)^(2 : Nat) +
   2*WO (rho - (n:ℂ)) 3 x)
theorem ZK {n : Nat} {rho:ℂ} {x:ℝ} (qa : Not (rho=0)) : Vv n rho x/rho=Inv.inv ((rho - (n:ℂ))^(2 : Nat))*(-((x:ℂ)^(rho - (n:ℂ)))/((Real.log x:ℝ):ℂ)^(2 : Nat)+2*WO (rho - (n:ℂ)) 3 x):=by
  unfold Vv
  simp only [div_eq_mul_inv]
  calc
    rho*Inv.inv ((rho - (n:ℂ))^(2 : Nat)) *
          (-((x:ℂ)^(rho - (n:ℂ))) *
              Inv.inv (((Real.log x:ℝ):ℂ)^(2 : Nat)) +
            2*WO (rho - (n:ℂ)) 3 x) *
        Inv.inv rho =
        (rho*Inv.inv rho) *
          (Inv.inv ((rho - (n:ℂ))^(2 : Nat)) *
            (-((x:ℂ)^(rho - (n:ℂ))) *
                Inv.inv (((Real.log x:ℝ):ℂ)^(2 : Nat)) +
              2*WO (rho - (n:ℂ)) 3 x)):=by
      ring
    _ = _ := by
      simp [qa]
theorem w1 {n : Nat} (hn : 1 <= n) {rho:ℂ} (hRe : rho.re=(1/2:ℝ)) : norm rho <= norm (rho - (n:ℂ)):=by
 apply le_of_sq_le_sq
 case h =>
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
   Complex.natCast_re,Complex.natCast_im,sub_zero,hRe]
  have qa : (1:ℝ) <= (n:ℝ):=by
   exact_mod_cast hn
  nlinarith
 case hb => exact norm_nonneg _
theorem yY {n : Nat} (hn : 1 <= n) {rho:ℂ} (qe : Not (rho=0)) (hRe : rho.re=(1/2:ℝ)) : norm (((n:ℂ)/((n:ℂ) - rho))/rho) <= (n:ℝ)*(Inv.inv (norm rho))^(2 : Nat):=by
  have qc : norm rho <= norm (rho - (n:ℂ)) :=
    w1 hn hRe
  have qa :
      norm ((n:ℂ) - rho)=norm (rho - (n:ℂ)):=by
    rw [show (n:ℂ) - rho = -(rho - (n:ℂ)) by ring,
      norm_neg]
  have qb : 0 < norm rho:=norm_pos_iff.mpr qe
  have qd :
      Inv.inv (norm ((n:ℂ) - rho)) <= Inv.inv (norm rho):=by
    rw [qa]
    simpa [one_div] using one_div_le_one_div_of_le qb qc
  rw [norm_div,norm_div,Complex.norm_natCast]
  calc
    (n:ℝ)/norm ((n:ℂ) - rho)/norm rho =
        (n:ℝ)*Inv.inv (norm ((n:ℂ) - rho)) *
          Inv.inv (norm rho):=by ring
    _ <= (n:ℝ)*Inv.inv (norm rho)*Inv.inv (norm rho):=by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left qd (Nat.cast_nonneg n))
        (inv_nonneg.mpr (norm_nonneg rho))
    _ = (n:ℝ)*(Inv.inv (norm rho))^(2 : Nat):=by
      ring
def V1 (a:ℂ) (k : Nat) (t:ℝ):ℂ :=
 Inv.inv a*(t:ℂ)^a *
  (((Inv.inv ((Real.log t)^k):ℝ):ℂ))
theorem ZM {a:ℂ} (ha : Not (a=0)) (k : Nat) {t:ℝ} (ht : 1 < t) : HasDerivAt (V1 a k) ((t:ℂ)^(a - 1)*(((Inv.inv ((Real.log t)^k):ℝ):ℂ)) - ((k:ℂ)*Inv.inv a)*(t:ℂ)^(a - 1)*(((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ))) t:=by
  have qh : Not (t=0):=ne_of_gt (lt_trans Real.zero_lt_one ht)
  have qj : Not (t=1):=ne_of_gt ht
  have qf : Not (Real.log t=0) :=
    Real.log_ne_zero_of_pos_of_ne_one
      (lt_trans Real.zero_lt_one ht) qj
  have qi:=hasDerivAt_ofReal_cpow_const qh ha
  cases k with
  | zero =>
      have qd :
          V1 a 0 =
            (fun y:ℝ => Inv.inv a*(y:ℂ)^a):=by
        funext y
        simp [V1]
      rw [qd]
      simpa [ha] using qi.const_mul (Inv.inv a)
  | succ k =>
      have qe:=(Real.hasDerivAt_log qh).pow (k+1)
      have qa :
          Not ((Real.log t)^(k+1)=0) :=
        pow_ne_zero (k+1) qf
      have qg:=(qe.inv qa).ofReal_comp
      have qk:=(qi.mul qg).const_mul (Inv.inv a)
      have qd :
          V1 a (k+1) =
            (fun y:ℝ => Inv.inv a *
              ((fun z:ℝ => (z:ℂ)^a) y *
                (fun z:ℝ =>
                  (((Inv.inv ((Real.log z)^(k+1)):ℝ):ℂ))) y)):=by
        funext y
        simp [V1,mul_assoc]
      have qb :
          Inv.inv a *
              (a*(t:ℂ)^(a - 1) *
                  (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ)) +
                (t:ℂ)^a *
                  (((-( (k+1:ℝ)*(Real.log t)^k*Inv.inv t) /
                    ((Real.log t)^(k+1))^(2 : Nat):ℝ):ℂ))) =
            (t:ℂ)^(a - 1) *
                (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ)) -
              (((k+1 : Nat):ℂ)*Inv.inv a) *
                (t:ℂ)^(a - 1) *
                (((Inv.inv ((Real.log t)^(k+2)):ℝ):ℂ)):=by
        rw [Complex.cpow_sub a 1 (Complex.ofReal_ne_zero.mpr qh),
          Complex.cpow_one]
        push_cast
        field_simp [ha,qf,qh]
        ring
      rw [qd]
      have qc:=qk
      simp only [Pi.pow_apply,Pi.inv_apply,Nat.cast_add,Nat.cast_one,
        add_tsub_cancel_right] at qc
      rw [qb] at qc
      simpa [Nat.add_assoc] using qc
theorem wp {a:ℂ} (ha : a.re < 0) (k : Nat) : Filter.Tendsto (V1 a k) Filter.atTop (nhds 0):=by
  have qe : Not (a=0):=by
    intro h
    rw [h] at ha
    norm_num at ha
  have qh :
      Filter.Tendsto (fun t:ℝ => t^a.re) Filter.atTop (nhds 0):=by
    have qj : 0 < -a.re:=neg_pos.mpr ha
    simpa [neg_neg] using tendsto_rpow_neg_atTop qj
  have qa :
      Filter.Tendsto (fun t:ℝ => norm ((t:ℂ)^a))
        Filter.atTop (nhds 0) :=
    (Filter.tendsto_congr' (norm_ofReal_cpow_eventually_eq_atTop a)).mpr qh
  have qf :
      Filter.Tendsto
        (fun t:ℝ => norm (Inv.inv a)*norm ((t:ℂ)^a))
        Filter.atTop (nhds 0):=by
    simpa using (tendsto_const_nhds.mul qa)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ qf
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with t ht
  have qi : 0 < t:=lt_of_lt_of_le (Real.exp_pos 1) ht
  have qb : 1 <= Real.log t:=by
    rw [<- Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ht
  have qc : 1 <= (Real.log t)^k:=by
    induction k with
    | zero => simp
      | succ k ih =>
        rw [pow_succ]
        simpa using mul_le_mul ih qb zero_le_one
          (pow_nonneg (le_trans zero_le_one qb) k)
  have qd : 0 < (Real.log t)^k:=lt_of_lt_of_le zero_lt_one qc
  have qg : Inv.inv ((Real.log t)^k) <= 1:=by
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one qc
  rw [V1,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr qd)]
  simpa using mul_le_mul_of_nonneg_left qg
    (mul_nonneg (norm_nonneg (Inv.inv a))
      (norm_nonneg ((t:ℂ)^a)))
theorem YQ {a:ℂ} {x:ℝ} (hx : 1 < x) (ha : a.re < 0) (k : Nat) : WO a k x = -Inv.inv a*(x:ℂ)^a*(((Inv.inv ((Real.log x)^k):ℝ):ℂ))+((k:ℂ)*Inv.inv a)*WO a (k+1) x:=by
 have qe : Not (a=0):=by
  intro h
  rw [h] at ha
  norm_num at ha
 have qc : (a - 1).re < -1:=by
  simp
  linarith
 have qf :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv ((Real.log t)^k):ℝ):ℂ))) (Ioi x) :=
  Yf hx qc k
 have qh :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ))) (Ioi x) :=
  Yf hx qc (k+1)
 have qa :
   IntegrableOn (fun t:ℝ =>
    ((k:ℂ)*Inv.inv a) *
     ((t:ℂ)^(a - 1) *
      (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ))))
    (Ioi x) :=
  qh.const_mul ((k:ℂ)*Inv.inv a)
 have qb :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
      (((Inv.inv ((Real.log t)^k):ℝ):ℂ)) -
     ((k:ℂ)*Inv.inv a) *
      ((t:ℂ)^(a - 1) *
       (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ))))
    (Ioi x) :=
  qf.sub qa
 have qd :=
  MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
   (f:=V1 a k)
   (f':=fun t:ℝ =>
    (t:ℂ)^(a - 1) *
      (((Inv.inv ((Real.log t)^k):ℝ):ℂ)) -
     ((k:ℂ)*Inv.inv a) *
      ((t:ℂ)^(a - 1) *
       (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ))))
   (fun t ht => by
    simpa [mul_assoc] using
     ZM qe k
      (lt_of_lt_of_le hx ht))
   qb (wp ha k)
 have qg :
   integral (volume.restrict (Ioi x)) (fun t:ℝ =>
     (t:ℂ)^(a - 1) *
       (((Inv.inv ((Real.log t)^k):ℝ):ℂ)) -
      ((k:ℂ)*Inv.inv a) *
       ((t:ℂ)^(a - 1) *
        (((Inv.inv ((Real.log t)^(k+1)):ℝ):ℂ)))) =
    WO a k x -
     ((k:ℂ)*Inv.inv a)*WO a (k+1) x:=by
  rw [integral_sub qf qa,integral_const_mul]
  rfl
 rw [qg] at qd
 unfold V1 at qd
 linear_combination qd
theorem Vr {a:ℂ} {x:ℝ} (hx : 1 < x) (ha : a.re < 0) (k : Nat) : norm (WO a k x) <= (-x^a.re/a.re)*Inv.inv ((Real.log x)^k):=by
  have qj : 0 < x:=lt_trans Real.zero_lt_one hx
  have qb : 0 < Real.log x:=Real.log_pos hx
  have qa : a.re - 1 < -1:=by
    linarith
  have qk :
      IntegrableOn (fun t:ℝ => t^(a.re - 1)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt qa qj
  have qf :
      IntegrableOn (fun t:ℝ =>
        t^(a.re - 1)*Inv.inv ((Real.log x)^k)) (Ioi x) :=
    qk.mul_const _
  unfold WO
  calc
    norm (integral (volume.restrict (Ioi x)) (fun t:ℝ =>
        (t:ℂ)^(a - 1) *
          (((Inv.inv ((Real.log t)^k):ℝ):ℂ)))) <=
        integral (volume.restrict (Ioi x)) (fun t:ℝ =>
          t^(a.re - 1)*Inv.inv ((Real.log x)^k)):=by
      apply norm_integral_le_of_norm_le qf
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxt : x <= t:=ht.le
      have ql : 0 < t:=lt_of_lt_of_le qj hxt
      have qg : Real.log x <= Real.log t :=
        Real.log_le_log qj hxt
      have qc : 0 < Real.log t :=
        lt_of_lt_of_le qb qg
      have qh : (Real.log x)^k <= (Real.log t)^k:=by
        clear qf
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ,pow_succ]
            exact mul_le_mul ih qg qb.le
              (pow_nonneg qc.le k)
      have qd : 0 < (Real.log x)^k:=pow_pos qb k
      have qe : 0 < (Real.log t)^k:=pow_pos qc k
      have qi :
          Inv.inv ((Real.log t)^k) <=
            Inv.inv ((Real.log x)^k):=by
        simpa [one_div] using one_div_le_one_div_of_le qd qh
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ql,
        Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr qe)]
      simp only [Complex.sub_re,Complex.one_re]
      exact mul_le_mul_of_nonneg_left qi
        (Real.rpow_nonneg ql.le _)
    _ = (-x^a.re/a.re)*Inv.inv ((Real.log x)^k):=by
      rw [integral_mul_const,
        integral_Ioi_rpow_of_lt qa qj]
      ring_nf
theorem vb {n : Nat} (hn : 1 <= n) {rho:ℂ} (hRe : rho.re=(1/2:ℝ)) {x:ℝ} (hx : 1 < x) : norm (-((x:ℂ)^(rho - (n:ℂ)))/((Real.log x:ℝ):ℂ)^(2 : Nat)+2*WO (rho - (n:ℂ)) 3 x) <= x^((1/2:ℝ) - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^((1/2:ℝ) - (n:ℝ))/((1/2:ℝ) - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))):=by
  have qe : 0 < x:=lt_trans Real.zero_lt_one hx
  have qc : 0 < Real.log x:=Real.log_pos hx
  have qg : (rho - (n:ℂ)).re < 0:=by
    rw [Complex.sub_re,Complex.natCast_re,hRe]
    have qd : (1:ℝ) <= (n:ℝ):=by
      exact_mod_cast hn
    linarith
  have qb :
      norm
          (-((x:ℂ)^(rho - (n:ℂ))) /
            ((Real.log x:ℝ):ℂ)^(2 : Nat)) =
        x^((1/2:ℝ) - (n:ℝ)) *
          Inv.inv ((Real.log x)^(2 : Nat)):=by
    rw [norm_div,norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos qe,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos qc]
    simp only [Complex.sub_re,Complex.natCast_re,hRe]
    rw [div_eq_mul_inv]
  have qf:=Vr hx qg 3
  have qa :
      norm (WO (rho - (n:ℂ)) 3 x) <=
        (-x^((1/2:ℝ) - (n:ℝ)) /
            ((1/2:ℝ) - (n:ℝ))) *
          Inv.inv ((Real.log x)^(3 : Nat)):=by
    simpa only [Complex.sub_re,Complex.natCast_re,hRe] using qf
  calc
    norm
        (-((x:ℂ)^(rho - (n:ℂ))) /
            ((Real.log x:ℝ):ℂ)^(2 : Nat) +
          2*WO (rho - (n:ℂ)) 3 x) <=
        norm
            (-((x:ℂ)^(rho - (n:ℂ))) /
              ((Real.log x:ℝ):ℂ)^(2 : Nat)) +
          norm (2*WO (rho - (n:ℂ)) 3 x) :=
      norm_add_le _ _
    _ = x^((1/2:ℝ) - (n:ℝ)) *
          Inv.inv ((Real.log x)^(2 : Nat)) +
        2*norm (WO (rho - (n:ℂ)) 3 x):=by
      rw [qb,norm_mul]
      norm_num
    _ <= x^((1/2:ℝ) - (n:ℝ)) *
          Inv.inv ((Real.log x)^(2 : Nat)) +
        2 *
          ((-x^((1/2:ℝ) - (n:ℝ)) /
                ((1/2:ℝ) - (n:ℝ))) *
            Inv.inv ((Real.log x)^(3 : Nat))):=by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left qa zero_le_two)
theorem vk {n : Nat} (hn : 1 <= n) {rho:ℂ} (qg : Not (rho=0)) (hRe : rho.re=(1/2:ℝ)) {x:ℝ} (hx : 1 < x) : norm (Vv n rho x/rho) <= (Inv.inv (norm rho))^(2 : Nat)*(x^((1/2:ℝ) - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^((1/2:ℝ) - (n:ℝ))/((1/2:ℝ) - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat)))):=by
 have qf : norm rho <= norm (rho - (n:ℂ)) :=
  w1 hn hRe
 have qd : 0 < norm rho:=norm_pos_iff.mpr qg
 have qa : 0 < (norm rho)^(2 : Nat) :=
  pow_pos qd 2
 have qc :
   (norm rho)^(2 : Nat) <=
    (norm (rho - (n:ℂ)))^(2 : Nat):=by
  nlinarith [norm_nonneg (rho - (n:ℂ))]
 have qb :
   norm (Inv.inv ((rho - (n:ℂ))^(2 : Nat))) <=
    (Inv.inv (norm rho))^(2 : Nat):=by
  rw [norm_inv,norm_pow]
  simpa [one_div,inv_pow] using
   one_div_le_one_div_of_le qa qc
 have qe :=
  vb hn hRe hx
 rw [ZK qg,norm_mul]
 exact mul_le_mul qb qe (norm_nonneg _)
  (pow_nonneg (inv_nonneg.mpr (norm_nonneg rho)) 2)
theorem z5 {n : Nat} {rho:ℂ} {x:ℝ} (hx : 1 < x) (hRe : rho.re < n) : WT n rho x=(n:ℂ)*WO (rho - (n:ℂ)) 1 x+WO (rho - (n:ℂ)) 2 x:=by
 let a : ℂ:=rho - (n:ℂ)
 have qb : (a - 1).re < -1:=by
  dsimp [a]
  linarith
 have qc :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv (Real.log t):ℝ):ℂ))) (Ioi x):=by
  simpa using Yf hx qb 1
 have qd :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv ((Real.log t)^(2 : Nat)):ℝ):ℂ)))
    (Ioi x) :=
  Yf hx qb 2
 change WT n rho x =
  (n:ℂ)*WO a 1 x +
   WO a 2 x
 unfold WT WO
 have qa :
   (fun t:ℝ =>
    (t:ℂ)^(rho - (n:ℂ) - 1) *
     (((n:ℝ)*Real.log t+1) /
      (Real.log t)^(2 : Nat):ℝ)) =
    (fun t:ℝ =>
     (n:ℂ) *
       ((t:ℂ)^(a - 1) *
        (((Inv.inv (Real.log t):ℝ):ℂ))) +
      (t:ℂ)^(a - 1) *
       (((Inv.inv ((Real.log t)^(2 : Nat)):ℝ):ℂ))):=by
  funext t
  dsimp [a]
  rw [show rho - (n:ℂ) - 1 =
    (rho - (n:ℂ)) - 1 by ring]
  push_cast
  by_cases hLog : Real.log t=0
  case pos => simp [hLog]
  case neg => field_simp [hLog]
 rw [qa,integral_add (qc.const_mul (n:ℂ)) qd,
  integral_const_mul]
 simp only [pow_one]
theorem z6 {n : Nat} {rho:ℂ} {x:ℝ} (hx : 1 < x) (hRe : rho.re < n) : WT n rho x=(x:ℂ)^(rho - (n:ℂ))*(((Inv.inv (Real.log x):ℝ):ℂ))+rho*WO (rho - (n:ℂ)) 1 x:=by
 let a : ℂ:=rho - (n:ℂ)
 have qf : a.re < 0:=by
  dsimp [a]
  simp
  exact hRe
 have qd : Not (a=0):=by
  intro h
  have qe:=congrArg Complex.re h
  rw [Complex.zero_re] at qe
  linarith
 rw [z5 hx hRe]
 have qc:=YQ hx qf 1
 have qa :
   a*WO a 1 x =
    -(x:ℂ)^a *
      (((Inv.inv (Real.log x):ℝ):ℂ)) +
     WO a 2 x:=by
  rw [qc]
  push_cast
  field_simp [qd]
 have qg : rho=(n:ℂ)+a:=by
  dsimp [a]
  ring
 have qb :
   WO a 2 x =
    a*WO a 1 x +
     (x:ℂ)^a *
      (((Inv.inv (Real.log x):ℝ):ℂ)):=by
  clear qg
  linear_combination -qa
 change (n:ℂ)*WO a 1 x +
   WO a 2 x =
  (x:ℂ)^a *
    (((Inv.inv (Real.log x):ℝ):ℂ)) +
   rho*WO a 1 x
 rw [qb,qg]
 ring
theorem zK {n : Nat} {rho:ℂ} (qa : Not (rho=0)) {x:ℝ} (hx : 1 < x) (hRe : rho.re < n) : WT n rho x/rho=(x:ℂ)^(rho - (n:ℂ))/(rho*((Real.log x:ℝ):ℂ))+WO (rho - (n:ℂ)) 1 x:=by
 rw [z6 hx hRe]
 push_cast
 field_simp [qa]
theorem v3 {n : Nat} (hn : 1 <= n) {rho:ℂ} {x:ℝ} (hx : 1 < x) (hRe : rho.re < n) : WT n rho x=((n:ℂ)/((n:ℂ) - rho))*(x:ℂ)^(rho - (n:ℂ))*(((Inv.inv (Real.log x):ℝ):ℂ))+Vv n rho x:=by
 let a : ℂ:=rho - (n:ℂ)
 have qi : a.re < 0:=by
  dsimp [a]
  simp
  exact hRe
 have qf : Not (a=0):=by
  intro h
  have qg:=congrArg Complex.re h
  rw [Complex.zero_re] at qg
  linarith
 have qc : (a - 1).re < -1:=by
  simp
  linarith
 have qj :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv (Real.log t):ℝ):ℂ))) (Ioi x):=by
  simpa using Yf hx qc 1
 have qk :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(a - 1) *
     (((Inv.inv ((Real.log t)^(2 : Nat)):ℝ):ℂ)))
    (Ioi x) :=
  Yf hx qc 2
 have qa :
   WT n rho x =
    (n:ℂ)*WO a 1 x +
     WO a 2 x:=by
  unfold WT WO
  have qb :
    (fun t:ℝ =>
     (t:ℂ)^(rho - (n:ℂ) - 1) *
      (((n:ℝ)*Real.log t+1) /
       (Real.log t)^(2 : Nat):ℝ)) =
     (fun t:ℝ =>
      (n:ℂ) *
        ((t:ℂ)^(a - 1) *
         (((Inv.inv (Real.log t):ℝ):ℂ))) +
       (t:ℂ)^(a - 1) *
        (((Inv.inv ((Real.log t)^(2 : Nat)):ℝ):ℂ))):=by
   funext t
   dsimp [a]
   rw [show rho - (n:ℂ) - 1 =
     (rho - (n:ℂ)) - 1 by ring]
   push_cast
   by_cases hLog : Real.log t=0
   case pos => simp [hLog]
   case neg =>
    field_simp [hLog]
  rw [qb,integral_add (qj.const_mul (n:ℂ)) qk,
   integral_const_mul]
  simp only [pow_one]
 have qd:=YQ hx qi 1
 have qe:=YQ hx qi 2
 rw [qa,qd,qe]
 unfold Vv
 have hLog : Not (Real.log x=0):=ne_of_gt (Real.log_pos hx)
 have ql : (n:ℂ) - rho = -a:=by
  dsimp [a]
  ring
 have qh : rho - (n:ℂ)=a:=by
  rfl
 rw [ql,qh]
 push_cast
 field_simp [qf,hLog]
 ring
theorem zW {n : Nat} (hn : 1 <= n) {rho:ℂ} (qj : Not (rho=0)) (hRe : rho.re=(1/2:ℝ)) {x:ℝ} (hx : 1 < x) : norm (WT n rho x/rho) <= (Inv.inv (norm rho))^(2 : Nat)*((n:ℝ)*x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)+(x^((1/2:ℝ) - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^((1/2:ℝ) - (n:ℝ))/((1/2:ℝ) - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))))):=by
  have qh : rho.re < (n:ℝ):=by
    have qg : (1:ℝ) <= (n:ℝ):=by
      exact_mod_cast hn
    rw [hRe]
    linarith
  have qf : 0 < Real.log x:=Real.log_pos hx
  have qb :=
    yY hn qj hRe
  have qc :
      norm
          ((x:ℂ)^(rho - (n:ℂ)) *
            (((Inv.inv (Real.log x):ℝ):ℂ))) =
        x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x):=by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_trans Real.zero_lt_one hx),Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr qf)]
    simp only [Complex.sub_re,Complex.natCast_re,hRe]
  have qi :
      norm
          ((((n:ℂ)/((n:ℂ) - rho)) *
              (x:ℂ)^(rho - (n:ℂ)) *
              (((Inv.inv (Real.log x):ℝ):ℂ)))/rho) <=
        (Inv.inv (norm rho))^(2 : Nat) *
          ((n:ℝ)*x^((1/2:ℝ) - (n:ℝ)) *
            Inv.inv (Real.log x)):=by
    have qe :
        (((n:ℂ)/((n:ℂ) - rho)) *
              (x:ℂ)^(rho - (n:ℂ)) *
              (((Inv.inv (Real.log x):ℝ):ℂ)))/rho =
          (((n:ℂ)/((n:ℂ) - rho))/rho) *
            ((x:ℂ)^(rho - (n:ℂ)) *
              (((Inv.inv (Real.log x):ℝ):ℂ))):=by
      ring
    rw [qe,norm_mul,qc]
    have qa :
        0 <= x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one hx)) _)
        (inv_nonneg.mpr qf.le)
    calc
      norm (((n:ℂ)/((n:ℂ) - rho))/rho) *
          (x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)) <=
        ((n:ℝ)*(Inv.inv (norm rho))^(2 : Nat)) *
          (x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right qb qa
      _ = (Inv.inv (norm rho))^(2 : Nat) *
          ((n:ℝ)*x^((1/2:ℝ) - (n:ℝ)) *
            Inv.inv (Real.log x)):=by ring
  have qd :=
    vk hn qj hRe hx
  rw [v3 hn hx qh,add_div]
  calc
    norm
        ((((n:ℂ)/((n:ℂ) - rho)) *
              (x:ℂ)^(rho - (n:ℂ)) *
              (((Inv.inv (Real.log x):ℝ):ℂ)))/rho +
          Vv n rho x/rho) <=
        norm
            ((((n:ℂ)/((n:ℂ) - rho)) *
                (x:ℂ)^(rho - (n:ℂ)) *
                (((Inv.inv (Real.log x):ℝ):ℂ)))/rho) +
          norm (Vv n rho x/rho) :=
      norm_add_le _ _
    _ <= (Inv.inv (norm rho))^(2 : Nat) *
          ((n:ℝ)*x^((1/2:ℝ) - (n:ℝ)) *
            Inv.inv (Real.log x)) +
        (Inv.inv (norm rho))^(2 : Nat) *
          (x^((1/2:ℝ) - (n:ℝ)) *
              Inv.inv ((Real.log x)^(2 : Nat)) +
            2 *
              ((-x^((1/2:ℝ) - (n:ℝ)) /
                    ((1/2:ℝ) - (n:ℝ))) *
                Inv.inv ((Real.log x)^(3 : Nat)))) :=
      add_le_add qi qd
    _ = _ := by ring
theorem ZF (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : Summable (fun p : Vc => WT n (Y5 p) x/Y5 p):=by
 let C:ℝ :=
  (n:ℝ)*x^((1/2:ℝ) - (n:ℝ)) *
    Inv.inv (Real.log x) +
   (x^((1/2:ℝ) - (n:ℝ)) *
     Inv.inv ((Real.log x)^(2 : Nat)) +
    2 *
     ((-x^((1/2:ℝ) - (n:ℝ)) /
        ((1/2:ℝ) - (n:ℝ))) *
      Inv.inv ((Real.log x)^(3 : Nat))))
 have qa :
   Summable (fun p : Vc =>
    (Inv.inv (norm (Y5 p)))^(2 : Nat)*C) :=
  YX.mul_right C
 apply qa.of_norm_bounded
 intro p
 dsimp [C]
 exact zW hn
  (Zj p)
  (zq hRH p) hx
theorem wk (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : norm (tsum (fun p : Vc => WT n (Y5 p) x/Y5 p)) <= (Real.eulerMascheroniConstant+2 - Real.log (4*Real.pi))*((n:ℝ)*x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)+(x^((1/2:ℝ) - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^((1/2:ℝ) - (n:ℝ))/((1/2:ℝ) - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))))):=by
  let C:ℝ :=
    (n:ℝ)*x^((1/2:ℝ) - (n:ℝ)) *
        Inv.inv (Real.log x) +
      (x^((1/2:ℝ) - (n:ℝ)) *
          Inv.inv ((Real.log x)^(2 : Nat)) +
        2 *
          ((-x^((1/2:ℝ) - (n:ℝ)) /
                ((1/2:ℝ) - (n:ℝ))) *
            Inv.inv ((Real.log x)^(3 : Nat))))
  have qc:=ZF hRH hn hx
  have qa:=qc.norm
  have qd :
      Summable (fun p : Vc =>
        (Inv.inv (norm (Y5 p)))^(2 : Nat)*C) :=
    YX.mul_right C
  have qb : forall p : Vc,
      norm (WT n (Y5 p) x /
        Y5 p) <=
      (Inv.inv (norm (Y5 p)))^(2 : Nat)*C:=by
    intro p
    dsimp [C]
    exact zW hn
      (Zj p)
      (zq hRH p) hx
  calc
    norm (tsum (fun p : Vc =>
        WT n (Y5 p) x /
          Y5 p)) <=
        tsum (fun p : Vc =>
          norm (WT n (Y5 p) x /
            Y5 p)) :=
      norm_tsum_le_tsum_norm qa
    _ <= tsum (fun p : Vc =>
        (Inv.inv (norm (Y5 p)))^(2 : Nat)*C) :=
      qa.tsum_le_tsum qb qd
    _ = (tsum (fun p : Vc =>
          (Inv.inv (norm (Y5 p)))^(2 : Nat)))*C:=by
      rw [tsum_mul_right]
    _ = (Real.eulerMascheroniConstant+2 - Real.log (4*Real.pi))*C:=by
      rw [yG hRH]
    _ = _ := by rfl
theorem vO {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : (n:ℝ)*x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)+(x^((1/2:ℝ) - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^((1/2:ℝ) - (n:ℝ))/((1/2:ℝ) - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))))=x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)*((n:ℝ)+Inv.inv (Real.log x)+4*Inv.inv (((2*n - 1 : Nat):ℝ)*(Real.log x)^(2 : Nat))):=by
 have qh : Not (Real.log x=0):=ne_of_gt (Real.log_pos hx)
 have qe : Not (2*n - 1=0):=by
  omega
 have qc : Not ((((2*n - 1 : Nat):ℝ))=0):=by
  exact_mod_cast qe
 have qb : 1 <= 2*n:=by
  omega
 have qd :
   (((2*n - 1 : Nat):ℝ))=2*(n:ℝ) - 1:=by
  rw [Nat.cast_sub qb]
  push_cast
  rfl
 have qa :
   (1/2:ℝ) - (n:ℝ) =
    -(((2*n - 1 : Nat):ℝ))/2:=by
  rw [qd]
  ring
 have qf :
   Inv.inv ((Real.log x)^(2 : Nat)) =
    Inv.inv (Real.log x)*Inv.inv (Real.log x):=by
  rw [<- inv_pow]
  ring
 have qg :
   2 *
     ((-x^((1/2:ℝ) - (n:ℝ)) /
        ((1/2:ℝ) - (n:ℝ))) *
      Inv.inv ((Real.log x)^(3 : Nat))) =
    x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x) *
     (4*Inv.inv ((((2*n - 1 : Nat):ℝ)) *
      (Real.log x)^(2 : Nat))):=by
  rw [qa]
  field_simp [qh,qc]
  ring
 rw [qg,qf]
 ring
theorem yT (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : norm (tsum (fun p : Vc => WT n (Y5 p) x/Y5 p)) <= (Real.eulerMascheroniConstant+2 - Real.log (4*Real.pi))*(x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x)*((n:ℝ)+Inv.inv (Real.log x)+4*Inv.inv (((2*n - 1 : Nat):ℝ)*(Real.log x)^(2 : Nat)))):=by
 have qa:=wk hRH hn hx
 rw [vO hn hx] at qa
 exact qa
def robinRealWeight (n : Nat) (t:ℝ):ℝ :=
 t^(-(n:ℝ) - 1) *
  (((n:ℝ)*Real.log t+1) /
   (Real.log t)^(2 : Nat))
def Vo (n : Nat) (t:ℝ):ℝ :=
 -(t^(-(n:ℝ))*Inv.inv (Real.log t))
theorem wC (n : Nat) {t:ℝ} (ht : 1 < t) : HasDerivAt (Vo n) (robinRealWeight n t) t:=by
  have qc : Not (t=0) :=
    ne_of_gt (lt_trans Real.zero_lt_one ht)
  have qa : Not (Real.log t=0) :=
    ne_of_gt (Real.log_pos ht)
  have qd : 0 < t:=lt_trans Real.zero_lt_one ht
  have qe :
      t^(-(n:ℝ))=t^(-(n:ℝ) - 1)*t:=by
    calc
      t^(-(n:ℝ))=t^((-(n:ℝ) - 1)+1):=by
        congr 1
        ring
      _ = t^(-(n:ℝ) - 1)*t^(1:ℝ) :=
        Real.rpow_add qd _ _
      _ = t^(-(n:ℝ) - 1)*t:=by
        rw [Real.rpow_one]
  have qf :=
    Real.hasDerivAt_rpow_const (p := -(n:ℝ)) (Or.inl qc)
  have qb:=(Real.hasDerivAt_log qc).inv qa
  have qg:=(qf.mul qb).neg
  refine qg.congr_deriv ?_
  simp only [Pi.inv_apply]
  unfold robinRealWeight
  rw [qe]
  field_simp [qc,qa] <;> ring
theorem VW {n : Nat} {t:ℝ} (ht : 1 < t) : 0 <= robinRealWeight n t:=by
 unfold robinRealWeight
 have qa : 0 < Real.log t:=Real.log_pos ht
 exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one ht)) _)
  (div_nonneg
   (add_nonneg
    (mul_nonneg (Nat.cast_nonneg n) qa.le) zero_le_one)
   (sq_nonneg (Real.log t)))
theorem vW {n : Nat} (hn : 1 <= n) : Filter.Tendsto (Vo n) Filter.atTop (nhds 0):=by
 have qb : 0 < (n:ℝ):=by
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
 have qc :
   Filter.Tendsto (fun t:ℝ => t^(-(n:ℝ)))
    Filter.atTop (nhds 0):=by
  simpa using tendsto_rpow_neg_atTop qb
 have qa :
   Filter.Tendsto (fun t:ℝ => Inv.inv (Real.log t))
    Filter.atTop (nhds 0) :=
  Real.tendsto_log_atTop.inv_tendsto_atTop
 change Filter.Tendsto
  (fun t:ℝ => -(t^(-(n:ℝ))*Inv.inv (Real.log t)))
  Filter.atTop (nhds 0)
 simpa only [zero_mul,neg_zero] using (qc.mul qa).neg
theorem Vs {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : integral (volume.restrict (Ioi x)) (robinRealWeight n)=x^(-(n:ℝ))*Inv.inv (Real.log x):=by
 have qc : forall t:ℝ,Membership.mem (Ici x) t ->
   HasDerivAt (Vo n)
    (robinRealWeight n t) t:=by
  intro t ht
  exact wC n (lt_of_lt_of_le hx ht)
 have qb : forall t:ℝ,Membership.mem (Ioi x) t ->
   0 <= robinRealWeight n t:=by
  intro t ht
  exact VW (lt_trans hx ht)
 have qa:=MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
  qc qb (vW hn)
 rw [qa]
 simp [Vo]
theorem Ys {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : IntegrableOn (robinRealWeight n) (Ioi x):=by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g:=Vo n)
  . intro t ht
    exact wC n (lt_of_lt_of_le hx ht)
  . intro t ht
    exact VW (lt_trans hx ht)
  . exact vW hn
def Zs (t:ℝ):ℝ :=
 Real.log (2*Real.pi) +
  (1/2:ℝ)*Real.log (1 - 1/t^(2 : Nat))
theorem vB {t:ℝ} (ht : 2 <= t) : And (0 <= Zs t) (Zs t <= Real.log (2*Real.pi)):=by
 have ql : (4:ℝ) <= t^(2 : Nat):=by
  nlinarith
 have qj : (1:ℝ)/t^(2 : Nat) <= 1/4 :=
  one_div_le_one_div_of_le (by norm_num) ql
 have qb : 0 <= (1:ℝ)/t^(2 : Nat):=by
  positivity
 have qc : (1/2:ℝ) <= 1 - 1/t^(2 : Nat):=by
  linarith
 have qf : 0 < 1 - 1/t^(2 : Nat):=by
  linarith
 have qa : 1 - 1/t^(2 : Nat) <= 1:=by
  linarith
 have qd : Real.log (1 - 1/t^(2 : Nat)) <= 0 :=
  Real.log_nonpos qf.le qa
 have qg :
   Real.log (1/2:ℝ) <= Real.log (1 - 1/t^(2 : Nat)) :=
  Real.log_le_log (by norm_num) qc
 have qi : Real.log (1/2:ℝ) = -Real.log 2:=by
  rw [one_div,Real.log_inv]
 have qe : 0 < Real.log (2:ℝ) :=
  Real.log_pos (by norm_num)
 have qk : (2:ℝ) <= 2*Real.pi:=by
  nlinarith [Real.pi_gt_three]
 have qh : Real.log (2:ℝ) <= Real.log (2*Real.pi) :=
  Real.log_le_log (by norm_num) qk
 rw [qi] at qg
 unfold Zs
 exact And.intro (by nlinarith) (by linarith)
def YU (n : Nat) (x:ℝ):ℝ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ =>
  robinRealWeight n t*Zs t)
theorem zY {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) : IntegrableOn (fun t:ℝ => robinRealWeight n t*Zs t) (Ioi x):=by
  have qc : 1 < x:=lt_of_lt_of_le (by norm_num) hx
  have qa:=Ys hn qc
  apply qa.mul_bdd (c:=Real.log (2*Real.pi))
  . have qd : Measurable Zs:=by
      unfold Zs
      fun_prop
    exact qd.aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have qb :=
      vB (le_trans hx ht.le)
    rw [Real.norm_eq_abs,abs_of_nonneg qb.1]
    exact qb.2
theorem Ze {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) : And (0 <= YU n x) (YU n x <= Real.log (2*Real.pi)*x^(-(n:ℝ))*Inv.inv (Real.log x)):=by
  have qd : 1 < x:=lt_of_lt_of_le (by norm_num) hx
  have qc:=Ys hn qd
  have qa:=zY hn hx
  refine And.intro ?_ ?_
  . unfold YU
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg
      (VW (lt_trans qd ht))
      (vB (le_trans hx ht.le)).1
  . unfold YU
    have qb :
        integral (volume.restrict (Ioi x)) (fun t:ℝ =>
            robinRealWeight n t*Zs t) <=
          integral (volume.restrict (Ioi x)) (fun t:ℝ =>
            robinRealWeight n t*Real.log (2*Real.pi)):=by
      apply integral_mono_ae qa (qc.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_left
        (vB (le_trans hx ht.le)).2
        (VW (lt_trans qd ht))
    calc
      integral (volume.restrict (Ioi x)) (fun t:ℝ =>
          robinRealWeight n t*Zs t) <=
          integral (volume.restrict (Ioi x)) (fun t:ℝ =>
            robinRealWeight n t*Real.log (2*Real.pi)):=qb
      _ = Real.log (2*Real.pi)*x^(-(n:ℝ)) *
          Inv.inv (Real.log x):=by
        rw [integral_mul_const,Vs hn qd]
        ring
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open MeasureTheory Set
theorem Y2 (a:ℝ) (k : Nat) {x:ℝ} (hx : 1 < x) : WO (a:ℂ) k x=((integral (volume.restrict (Ioi x)) (fun t:ℝ => t^(a - 1)*Inv.inv ((Real.log t)^k)):ℝ):ℂ):=by
 unfold WO
 rw [<- integral_complex_ofReal]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 dsimp only
 have qa : 0 < t:=lt_trans Real.zero_lt_one (lt_trans hx ht)
 rw [Complex.ofReal_mul,Complex.ofReal_cpow qa.le]
 push_cast
 rfl
theorem Zf (a:ℝ) (k : Nat) {x:ℝ} (hx : 1 < x) : 0 <= (WO (a:ℂ) k x).re:=by
 rw [Y2 a k hx,Complex.ofReal_re]
 apply setIntegral_nonneg measurableSet_Ioi
 intro t ht
 have qa : 1 < t:=lt_trans hx ht
 have qb : 0 < t:=lt_trans Real.zero_lt_one qa
 exact mul_nonneg (Real.rpow_nonneg qb.le _)
  (inv_nonneg.mpr (pow_nonneg (Real.log_pos qa).le k))
theorem Yc {a:ℝ} (ha : a < 0) (k : Nat) {x:ℝ} (hx : 1 < x) : (WO (a:ℂ) k x).re <= (-x^a/a)*Inv.inv ((Real.log x)^k):=by
 exact (Complex.re_le_norm _).trans
  (Vr hx (show (a:ℂ).re < 0 from ha) k)
theorem w0 {a:ℝ} (ha : a < 0) (k : Nat) {x:ℝ} (hx : 1 < x) : (WO (a:ℂ) k x).re = -Inv.inv a*x^a*Inv.inv ((Real.log x)^k)+((k:ℝ)*Inv.inv a)*(WO (a:ℂ) (k+1) x).re:=by
 have qa:=YQ hx (show (a:ℂ).re < 0 from ha) k
 have qb : (x:ℂ)^(a:ℂ)=((x^a:ℝ):ℂ) :=
  (Complex.ofReal_cpow (lt_trans Real.zero_lt_one hx).le a).symm
 rw [qb,<- Complex.ofReal_inv] at qa
 have hRe:=congrArg Complex.re qa
 simpa only [Complex.add_re,Complex.mul_re,Complex.mul_im,
  Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
  Complex.natCast_re,Complex.natCast_im,mul_zero,zero_mul,sub_zero,neg_zero,
  zero_add,add_zero] using hRe
theorem yj (n : Nat) {r:ℝ} (hr : r < n) {x:ℝ} (hx : 1 < x) : (WT n (r:ℂ) x).re = -(n:ℝ)*Inv.inv (r - n)*x^(r - n)*Inv.inv (Real.log x)+((n:ℝ)*Inv.inv (r - n)+1)*(WO ((r - n:ℝ):ℂ) 2 x).re:=by
 have qb:=z5
  (n:=n) (rho:=(r:ℂ)) hx (show (r:ℂ).re < n from hr)
 have qc : (r:ℂ) - (n:ℂ)=((r - n:ℝ):ℂ):=by push_cast; rfl
 rw [qc] at qb
 have qa:=congrArg Complex.re qb
 simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
  zero_mul,sub_zero] at qa
 have qd:=w0 (show r - n < 0 by linarith) 1 hx
 simp only [Nat.cast_one,pow_one,one_mul] at qd
 rw [qa,qd]
 ring
end
end Robin1984
end
section
section
open Filter Topology Finset Nat
namespace Complex
lemma Wj (n:ℕ) : ‖((n:ℂ)+1)‖ = (n:ℝ)+1:=by
 rw [show ((n:ℂ)+1)=((n+1:ℕ):ℂ) by push_cast; ring,norm_natCast]
 push_cast
 ring
lemma VF (n:ℕ) : ∑ m ∈ Finset.range n,((m:ℂ)+1)⁻¹ = ((harmonic n : ℚ):ℂ):=by
 rw [harmonic]
 push_cast
 rfl
lemma VQ {z:ℂ} {m:ℕ} (hzm : z+m ≠ 0) : ((m:ℂ)+1)⁻¹ - (z+m)⁻¹ = (z - 1)*(((m:ℂ)+1)*(z+m))⁻¹ := by
 have hm : ((m:ℂ)+1) ≠ 0:=Nat.cast_add_one_ne_zero m
 field_simp
 ring
lemma YL {a R:ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z:ℂ} (hza : a ≤ z.re) (hzR : ‖z‖ ≤ R) (m:ℕ) : ‖((m:ℂ)+1)⁻¹ - (z+m)⁻¹‖ ≤ (R+1)/(a*((m:ℝ)+1)^2):=by
  have hm0 : (0:ℝ) ≤ m:=Nat.cast_nonneg m
  have hR0 : (0:ℝ) ≤ R:=le_trans (norm_nonneg z) hzR
  have qb : 0 < (z+m).re:=by
    rw [add_re,natCast_re]
    linarith
  have hzm : z+m ≠ 0:=fun h => by simp [h] at qb
  have qa : a*((m:ℝ)+1) ≤ ‖z+m‖ := by
    have h1 : (z+m).re ≤ ‖z+m‖ := re_le_norm _
    rw [add_re,natCast_re] at h1
    nlinarith
  have hz1 : ‖z - 1‖ ≤ R+1:=le_trans (norm_sub_le z 1) (by rw [norm_one]; linarith)
  rw [VQ hzm,norm_mul,norm_inv,norm_mul,Wj,
    ← div_eq_mul_inv]
  calc ‖z - 1‖ / (((m:ℝ)+1) * ‖z+m‖)
      ≤ (R+1)/(((m:ℝ)+1)*(a*((m:ℝ)+1))):=by
        gcongr
    _ = (R+1)/(a*((m:ℝ)+1)^2):=by ring_nf
lemma wH : Summable (fun m:ℕ => 1/((m:ℝ)+1)^2):=by
 have h:=Real.summable_one_div_nat_pow.mpr (one_lt_two : (1:ℕ) < 2)
 exact ((summable_nat_add_iff 1).mpr h).congr fun n => by push_cast; ring
lemma ZY {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] {a:ℕ → E} (h0 : Tendsto a atTop (𝓝 0)) (hs : Summable fun n => a n - a (n+1)) : HasSum (fun n => a n - a (n+1)) (a 0):=by
 have h1 : Tendsto (fun n => ∑ i ∈ Finset.range n,(a i - a (i+1))) atTop (𝓝 (a 0)):=by
  have he : ∀ n,∑ i ∈ Finset.range n,(a i - a (i+1))=a 0 - a n :=
   fun n => Finset.sum_range_sub' a n
  simp only [he]
  simpa using tendsto_const_nhds.sub h0
 have h2:=hs.hasSum
 rwa [tendsto_nhds_unique h2.tendsto_sum_nat h1] at h2
noncomputable def logGammaSeq (z:ℂ) (n:ℕ):ℂ :=
 z*(Real.log n:ℂ)+(Real.log (n !):ℂ) - ∑ m ∈ Finset.range (n+1),log (z+m)
lemma Wi {z:ℂ} (hz : 0 < z.re) (n:ℕ) : logGammaSeq z (n+1) - logGammaSeq z n=z*((Real.log ((n:ℝ)+1) - Real.log n:ℝ):ℂ) - log (1+z/((n:ℂ)+1)):=by
 have hn1 : (0:ℝ) < (n:ℝ)+1:=by positivity
 have hnC : ((n:ℂ)+1) ≠ 0:=Nat.cast_add_one_ne_zero n
 have hx : 1+z/((n:ℂ)+1) ≠ 0:=by
  intro h
  have qa : z = -((n:ℂ)+1):=by
   field_simp at h
   linear_combination h
  rw [qa] at hz
  simp only [neg_re,add_re,natCast_re,one_re] at hz
  have : (0:ℝ) ≤ (n:ℝ):=Nat.cast_nonneg n
  linarith
 have qb : (Real.log ((n+1)!):ℂ)
   = (Real.log ((n:ℝ)+1):ℂ)+(Real.log (n !):ℂ):=by
  have qc : Real.log (((n+1)! : ℕ):ℝ)
    = Real.log ((n:ℝ)+1)+Real.log ((n ! : ℕ):ℝ):=by
   rw [Nat.factorial_succ]
   push_cast
   rw [Real.log_mul (by positivity) (by exact_mod_cast n.factorial_ne_zero)]
  rw [← ofReal_add]
  exact_mod_cast congrArg (fun t:ℝ => (t:ℂ)) qc
 have qd : log (z+((n+1:ℕ):ℂ))
   = (Real.log ((n:ℝ)+1):ℂ)+log (1+z/((n:ℂ)+1)):=by
  have hxx : ((((n:ℝ)+1):ℝ):ℂ)*(1+z/((n:ℂ)+1))=z+((n+1:ℕ):ℂ):=by
   push_cast
   field_simp
   ring
  rw [← hxx,log_ofReal_mul hn1 hx]
 unfold logGammaSeq
 rw [Finset.sum_range_succ,qb,qd]
 push_cast
 ring
lemma V6 {z:ℂ} (hz : 0 < z.re) : CauchySeq (logGammaSeq z):=by
  apply cauchySeq_of_summable_dist
  apply Summable.of_norm_bounded_eventually_nat
    (g:=fun n => (2 * ‖z‖ + ‖z‖ ^ 2)*(1/((n:ℝ)+1)^2))
    (wH.mul_left _)
  filter_upwards [eventually_ge_atTop 1,eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn1 hn2
  have hnR : (1:ℝ) ≤ (n:ℝ):=by exact_mod_cast hn1
  have qc : 2 * ‖z‖ ≤ (n:ℝ):=le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
  have hw : ‖z/((n:ℂ)+1)‖ = ‖z‖ / ((n:ℝ)+1):=by
    rw [norm_div,Wj]
  have hw2 : ‖z/((n:ℂ)+1)‖ ≤ 1/2:=by
    rw [hw,div_le_iff₀ (by positivity)]
    linarith
  simp only [Nat.succ_eq_add_one]
  rw [Real.norm_of_nonneg dist_nonneg,dist_eq_norm,← norm_neg,neg_sub,
    Wi hz n]
  have key : z*((Real.log ((n:ℝ)+1) - Real.log n:ℝ):ℂ) - log (1+z/((n:ℂ)+1))
      = z*((Real.log ((n:ℝ)+1) - Real.log n - ((n:ℝ)+1)⁻¹ : ℝ):ℂ)
        + (z/((n:ℂ)+1) - log (1+z/((n:ℂ)+1))):=by
    push_cast
    ring
  rw [key]
  have hn0 : (0:ℝ) < n:=by linarith
  have qa : |Real.log ((n:ℝ)+1) - Real.log n - ((n:ℝ)+1)⁻¹|
      ≤ 2*(1/((n:ℝ)+1)^2):=by
    have qd : Real.log ((n:ℝ)+1) - Real.log n=Real.log (((n:ℝ)+1)/n) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have l1 : Real.log ((n:ℝ)+1) - Real.log n ≤ 1/n:=by
      rw [qd]
      have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/n by positivity)
      have he : ((n:ℝ)+1)/n - 1=1/n:=by
        field_simp
        ring
      linarith
    have l2 : ((n:ℝ)+1)⁻¹ ≤ Real.log ((n:ℝ)+1) - Real.log n:=by
      have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < (n:ℝ)/((n:ℝ)+1) by positivity)
      rw [Real.log_div hn0.ne' (by positivity)] at h
      have he : (n:ℝ)/((n:ℝ)+1) - 1 = -((n:ℝ)+1)⁻¹ := by
        field_simp
        ring
      rw [he] at h
      linarith
    have qb : 1/(n:ℝ) - ((n:ℝ)+1)⁻¹ ≤ 2*(1/((n:ℝ)+1)^2):=by
      have he : 1/(n:ℝ) - ((n:ℝ)+1)⁻¹ = 1/((n:ℝ)*((n:ℝ)+1)):=by
        field_simp
        ring
      rw [he,mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_le]
    constructor
    · have : (0:ℝ) ≤ 2*(1/((n:ℝ)+1)^2):=by positivity
      linarith
    · linarith
  calc ‖z*((Real.log ((n:ℝ)+1) - Real.log n - ((n:ℝ)+1)⁻¹ : ℝ):ℂ)
        + (z/((n:ℂ)+1) - log (1+z/((n:ℂ)+1)))‖
      ≤ ‖z*((Real.log ((n:ℝ)+1) - Real.log n - ((n:ℝ)+1)⁻¹ : ℝ):ℂ)‖
        + ‖z/((n:ℂ)+1) - log (1+z/((n:ℂ)+1))‖ := norm_add_le _ _
    _ ≤ ‖z‖ * (2*(1/((n:ℝ)+1)^2)) + ‖z‖ ^ 2*(1/((n:ℝ)+1)^2):=by
        apply _root_.add_le_add
        · rw [norm_mul,norm_real,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left qa (norm_nonneg z)
        · have hlt : ‖z/((n:ℂ)+1)‖ < 1:=lt_of_le_of_lt hw2 (by norm_num)
          have hb:=norm_log_one_add_sub_self_le hlt
          rw [← norm_neg,neg_sub]
          calc ‖log (1+z/((n:ℂ)+1)) - z/((n:ℂ)+1)‖
              ≤ ‖z/((n:ℂ)+1)‖ ^ 2*(1 - ‖z/((n:ℂ)+1)‖)⁻¹ / 2:=hb
            _ ≤ ‖z/((n:ℂ)+1)‖ ^ 2*2/2:=by
                have h2 : (1 - ‖z/((n:ℂ)+1)‖)⁻¹ ≤ 2:=by
                  rw [← one_div]
                  have h3:=one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2)
                    (by linarith : (1:ℝ)/2 ≤ 1 - ‖z/((n:ℂ)+1)‖)
                  simpa using h3
                gcongr
            _ = ‖z/((n:ℂ)+1)‖ ^ 2:=by ring
            _ = ‖z‖ ^ 2*(1/((n:ℝ)+1)^2):=by
                rw [hw,div_pow]
                ring
    _ = (2 * ‖z‖ + ‖z‖ ^ 2)*(1/((n:ℝ)+1)^2):=by ring
lemma WU {z:ℂ} (hz : 0 < z.re) {n:ℕ} (hn : n ≠ 0) : exp (logGammaSeq z n)=GammaSeq z n:=by
  have hne : ∀ m:ℕ,z+(m:ℂ) ≠ 0:=by
    intro m h
    have qa : 0 < (z+(m:ℂ)).re:=by
      rw [add_re,natCast_re]
      have : (0:ℝ) ≤ m:=Nat.cast_nonneg m
      linarith
    simp [h] at qa
  unfold logGammaSeq GammaSeq
  rw [exp_sub,exp_add,exp_sum]
  congr 1
  · congr 1
    · rw [natCast_log,cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),mul_comm z (log (n:ℂ))]
    · rw [natCast_log,exp_log (by exact_mod_cast n.factorial_ne_zero)]
  · exact Finset.prod_congr rfl fun m _ => exp_log (hne m)
lemma VA {z₀ : ℂ} (hz₀ : 0 < z₀.re) : HasSum (fun m:ℕ => ((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹) (digamma z₀ + Real.eulerMascheroniConstant):=by
 set a : ℝ:=min (z₀.re/2) 1 with ha_def
 set R:ℝ := ‖z₀‖ + 1 with hR_def
 have ha : 0 < a:=lt_min (by linarith) one_pos
 have ha1 : a ≤ 1:=min_le_right _ _
 set s : Set ℂ:={w:ℂ | a < w.re} ∩ {w:ℂ | ‖w‖ < R} with hs_def
 have qa : IsOpen s :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
 have haz : a < z₀.re:=by
  rw [ha_def]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
 have hz₀R : ‖z₀‖ < R:=by rw [hR_def]; linarith
 have hz₀s : z₀ ∈ s := ⟨haz,hz₀R⟩
 have qe : ∀ w ∈ s,a ≤ w.re ∧ ‖w‖ ≤ R:=fun w hw => ⟨le_of_lt hw.1,le_of_lt hw.2⟩
 have qb : ∀ w ∈ s,0 < w.re:=fun w hw => lt_trans ha hw.1
 have hu : Summable (fun m:ℕ => (R+1)/(a*((m:ℝ)+1)^2)):=by
  refine (wH.mul_left ((R+1)/a)).congr fun m => ?_
  rw [mul_one_div,div_div]
 have hM : TendstoUniformlyOn
   (fun (N:ℕ) (w:ℂ) => ∑ m ∈ Finset.range N,(((m:ℂ)+1)⁻¹ - (w+m)⁻¹))
   (fun (w:ℂ) => ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (w+m)⁻¹)) atTop s :=
  tendstoUniformlyOn_tsum_nat hu fun m w hw =>
   YL ha ha1 (qe w hw).1 (qe w hw).2 m
 have hM1 : TendstoUniformlyOn
   (fun (n:ℕ) (w:ℂ) => ∑ m ∈ Finset.range (n+1),(((m:ℂ)+1)⁻¹ - (w+m)⁻¹))
   (fun (w:ℂ) => ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (w+m)⁻¹)) atTop s:=by
  intro u hu'
  exact (tendsto_add_atTop_nat 1).eventually (hM u hu')
 have hcR : Tendsto (fun n:ℕ => Real.log n - (harmonic n:ℝ) - ((n:ℝ)+1)⁻¹) atTop
   (𝓝 (-Real.eulerMascheroniConstant)):=by
  have h1 : Tendsto (fun n:ℕ => Real.log n - (harmonic n:ℝ)) atTop
    (𝓝 (-Real.eulerMascheroniConstant)) :=
   Real.tendsto_harmonic_sub_log.neg.congr fun n => by ring
  have h2 : Tendsto (fun n:ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0):=by
   apply Filter.Tendsto.inv_tendsto_atTop
   exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa using h1.sub h2
 have hcC : Tendsto (fun n:ℕ => ((Real.log n - (harmonic n:ℝ) - ((n:ℝ)+1)⁻¹ : ℝ):ℂ))
   atTop (𝓝 (-(Real.eulerMascheroniConstant:ℂ))):=by
  have h:=(continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp hcR
  have qf : ((-Real.eulerMascheroniConstant:ℝ):ℂ) = -(Real.eulerMascheroniConstant:ℂ):=by
   push_cast
   ring
  rw [← qf]
  exact h
 have hcU:=hcC.tendstoUniformlyOn_const s
 have hF' : TendstoUniformlyOn
   (fun (n:ℕ) (w:ℂ) => (Real.log n:ℂ) - ∑ m ∈ Finset.range (n+1),(w+m)⁻¹)
   (fun (w:ℂ) => -(Real.eulerMascheroniConstant:ℂ)
    + ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (w+m)⁻¹)) atTop s:=by
  have qg:=hcU.add hM1
  refine qg.congr ?_
  filter_upwards with n
  intro w hw
  simp only [Pi.add_apply]
  rw [Finset.sum_sub_distrib,VF (n+1)]
  push_cast [harmonic_succ]
  ring
 have qc : ∀ n:ℕ,∀ x:ℂ,x ∈ s →
   HasDerivAt (fun w => logGammaSeq w n)
    ((Real.log n:ℂ) - ∑ m ∈ Finset.range (n+1),(x+m)⁻¹) x:=by
  intro n x hx
  have hre : 0 < x.re:=qb x hx
  have h1 : HasDerivAt (fun w:ℂ => w*(Real.log n:ℂ)+(Real.log (n !):ℂ))
    ((Real.log n:ℂ)) x:=(hasDerivAt_mul_const _).add_const _
  have h2 : HasDerivAt (fun w:ℂ => ∑ m ∈ Finset.range (n+1),log (w+m))
    (∑ m ∈ Finset.range (n+1),(x+m)⁻¹) x:=by
   apply HasDerivAt.fun_sum
    (A:=fun (m:ℕ) (w:ℂ) => log (w+m)) (A':=fun m:ℕ => (x+m)⁻¹)
   intro m _
   have qe : x+(m:ℂ) ∈ slitPlane:=by
    rw [mem_slitPlane_iff]
    left
    rw [add_re,natCast_re]
    have : (0:ℝ) ≤ m:=Nat.cast_nonneg m
    linarith
   have qd : HasDerivAt (fun w:ℂ => w+(m:ℂ)) 1 x:=(hasDerivAt_id x).add_const _
   simpa using! (hasDerivAt_log qe).comp x qd
  simpa only [logGammaSeq] using! h1.sub h2
 have qh : ∀ x:ℂ,x ∈ s →
   Tendsto (fun n => logGammaSeq x n) atTop (𝓝 (limUnder atTop (logGammaSeq x))) :=
  fun x hx => (V6 (qb x hx)).tendsto_limUnder
 have qi : HasDerivAt (fun w => limUnder atTop (logGammaSeq w))
   (-(Real.eulerMascheroniConstant:ℂ)
    + ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹)) z₀ :=
  hasDerivAt_of_tendstoUniformlyOn qa hF'
   (Filter.Eventually.of_forall fun n x hx => qc n x hx) qh hz₀s
 have hEq : ∀ w ∈ s,exp (limUnder atTop (logGammaSeq w))=Gamma w:=by
  intro w hw
  have h2:=(continuous_exp.tendsto _).comp (qh w hw)
  have h3 : Tendsto (fun n => GammaSeq w n) atTop
    (𝓝 (exp (limUnder atTop (logGammaSeq w)))):=by
   apply h2.congr'
   filter_upwards [eventually_ne_atTop 0] with n hn
   exact WU (qb w hw) hn
  exact tendsto_nhds_unique h3 (GammaSeq_tendsto_Gamma w)
 have hGd : HasDerivAt Gamma (Gamma z₀ * (-(Real.eulerMascheroniConstant:ℂ)
   + ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹))) z₀ := by
  have qj:=qi.cexp
  rw [hEq z₀ hz₀s] at qj
  exact qj.congr_of_eventuallyEq
   (Filter.eventuallyEq_of_mem (qa.mem_nhds hz₀s) fun w hw => (hEq w hw).symm)
 have hne : ∀ m:ℕ,z₀ ≠ -(m:ℂ):=by
  intro m h
  rw [h] at hz₀
  simp only [neg_re,natCast_re] at hz₀
  have : (0:ℝ) ≤ m:=Nat.cast_nonneg m
  linarith
 have qk : digamma z₀ = -(Real.eulerMascheroniConstant:ℂ)
   + ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹):=by
  rw [digamma_def,logDeriv_apply,hGd.deriv,mul_div_cancel_left₀ _ (Gamma_ne_zero hne)]
 have hsm : Summable (fun m:ℕ => ((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹) :=
  Summable.of_norm_bounded hu fun m =>
   YL ha ha1 haz.le hz₀R.le m
 have ht : ∑' m:ℕ,(((m:ℂ)+1)⁻¹ - (z₀ + m)⁻¹)
   = digamma z₀ + Real.eulerMascheroniConstant:=by
  rw [qk]
  ring
 exact ht ▸ hsm.hasSum
theorem W5 {z:ℂ} (hz : ∀ n:ℕ,z ≠ -n) : HasSum (fun n:ℕ => 1/((n:ℂ)+1) - 1/((n:ℂ)+z)) (digamma z+Real.eulerMascheroniConstant):=by
  suffices h : HasSum (fun m:ℕ => ((m:ℂ)+1)⁻¹ - (z+m)⁻¹)
      (digamma z+Real.eulerMascheroniConstant) by
    have e : (fun n:ℕ => 1/((n:ℂ)+1) - 1/((n:ℂ)+z))
        = fun m:ℕ => ((m:ℂ)+1)⁻¹ - (z+m)⁻¹ := by
      funext m
      rw [one_div,one_div,add_comm (m:ℂ) z]
    rw [e]
    exact h
  obtain ⟨N,hN⟩ : ∃ N:ℕ,-(N:ℝ) < z.re :=
    ⟨⌈-z.re⌉₊ + 1,by have:=Nat.le_ceil (-z.re); push_cast; linarith⟩
  induction N generalizing z with
  | zero =>
    apply VA
    simpa using hN
  | succ N ih =>
    by_cases hcase : -(N:ℝ) < z.re
    · exact ih hz hcase
    ·
      have hz1 : ∀ n:ℕ,z+1 ≠ -(n:ℂ):=by
        intro n hcon
        apply hz (n+1)
        push_cast
        linear_combination hcon
      have qb : -(N:ℝ) < (z+1).re:=by
        rw [add_re,one_re]
        push_cast at hN
        linarith
      have hih:=ih hz1 qb
      rw [digamma_apply_add_one z hz] at hih
      have hzm : ∀ n:ℕ,z+(n:ℂ) ≠ 0:=fun n hcon => hz n (by linear_combination hcon)
      have qa : ∀ n:ℕ,(n:ℝ) - ‖z‖ ≤ ‖z+n‖ := by
        intro n
        have h:=norm_sub_norm_le (n:ℂ) (-z)
        rw [sub_neg_eq_add,norm_neg,norm_natCast] at h
        rw [show z+(n:ℂ)=(n:ℂ)+z from add_comm _ _]
        exact h
      have ha0 : Tendsto (fun n:ℕ => (z+(n:ℂ))⁻¹) atTop (𝓝 0):=by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv]
        apply Filter.Tendsto.inv_tendsto_atTop
        apply tendsto_atTop_mono qa
        have h:=tendsto_atTop_add_const_right atTop (-‖z‖) tendsto_natCast_atTop_atTop
        exact h.congr fun n => by ring
      have hts : Summable (fun n:ℕ => (z+(n:ℂ))⁻¹ - (z+((n+1:ℕ):ℂ))⁻¹):=by
        apply Summable.of_norm_bounded_eventually_nat
          (g:=fun n:ℕ => 4*(1/((n:ℝ)+1)^2))
          (wH.mul_left _)
        filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖ + 1⌉₊] with n hn
        have hnR : 2 * ‖z‖ + 1 ≤ (n:ℝ):=le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
        have hb1 : ((n:ℝ)+1)/2 ≤ ‖z+n‖ := le_trans (by linarith) (qa n)
        have hb2 : ((n:ℝ)+1)/2 ≤ ‖z+((n+1:ℕ):ℂ)‖ := by
          refine le_trans ?_ (qa (n+1))
          push_cast
          linarith
        have hid : (z+(n:ℂ))⁻¹ - (z+((n+1:ℕ):ℂ))⁻¹
            = ((z+n)*(z+((n+1:ℕ):ℂ)))⁻¹ := by
          have h1:=hzm n
          have h2:=hzm (n+1)
          field_simp
          push_cast
          ring
        rw [hid,norm_inv,norm_mul,
          show (4:ℝ)*(1/((n:ℝ)+1)^2)
            = ((((n:ℝ)+1)/2)*(((n:ℝ)+1)/2))⁻¹ by field_simp; ring]
        gcongr
      have qc:=ZY ha0 hts
      simp only [Nat.cast_zero,add_zero] at qc
      have qd:=hih.sub qc
      have e2 : (fun n:ℕ => (((n:ℂ)+1)⁻¹ - (z+1+n)⁻¹)
            - ((z+(n:ℂ))⁻¹ - (z+((n+1:ℕ):ℂ))⁻¹))
          = fun n:ℕ => ((n:ℂ)+1)⁻¹ - (z+n)⁻¹ := by
        funext n
        push_cast
        ring
      rw [e2] at qd
      convert! qd using 1
      ring
theorem WX {z:ℂ} (hz : ∀ n:ℕ,z ≠ -n) : digamma z = -(Real.eulerMascheroniConstant:ℂ) + ∑' n:ℕ,(1/((n:ℂ)+1) - 1/((n:ℂ)+z)):=by
 rw [(W5 hz).tsum_eq]
 ring
end Complex
end
end
section
noncomputable section
open Complex
theorem yM {a:ℝ} (ha : 1 < a) : Summable (fun p : Vc => (Inv.inv (norm (Y5 p)))^a):=by
 have qc : (1:ℝ) < (1+a)/2:=by linarith
 have qa : (0:ℝ) <= (1+a)/2:=by linarith
 have qb : (1+a)/2 < a:=by linarith
 exact Complex.Hadamard.zR
  qa qb VB Wm
  (Zk.WF qc qa)
end
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
def V8 (n : Nat) (x t:ℝ):ℂ :=
 if t <= x then
  (x:ℂ)^(-(n:ℂ)) *
   (((Inv.inv (Real.log x):ℝ):ℂ))
 else
  (t:ℂ)^(-(n:ℂ)) *
   (((Inv.inv (Real.log t):ℝ):ℂ))
theorem ZH (n : Nat) {x:ℝ} (hx : 1 < x) : Continuous (V8 n x):=by
  unfold V8
  apply continuous_if_le continuous_id continuous_const
  . exact continuous_const.continuousOn
  . intro t ht
    have qe : 1 < t:=lt_of_lt_of_le hx ht
    have qc : Not (t=0) :=
      ne_of_gt (lt_trans Real.zero_lt_one qe)
    have qa : Not (Real.log t=0) :=
      ne_of_gt (Real.log_pos qe)
    have qd : ContinuousAt (fun y:ℝ =>
        (y:ℂ)^(-(n:ℂ))) t :=
      Complex.continuousAt_ofReal_cpow_const t (-(n:ℂ)) (Or.inr qc)
    have qb : ContinuousAt (fun y:ℝ => Inv.inv (Real.log y)) t :=
      ((Real.hasDerivAt_log qc).inv qa).continuousAt
    exact (qd.mul
      (Complex.continuous_ofReal.continuousAt.comp qb)).continuousWithinAt
  . intro t ht
    dsimp at ht
    rw [ht]
theorem wu (n : Nat) (s:ℂ) {x t:ℝ} (ht : t <= x) : (t:ℂ)^(s - 1)*V8 n x t=(t:ℂ)^(s - 1)*((x:ℂ)^(-(n:ℂ))*(((Inv.inv (Real.log x):ℝ):ℂ))):=by
 simp only [V8,if_pos ht]
theorem wz (n : Nat) (s:ℂ) {x t:ℝ} (hx : 1 < x) (ht : x < t) : (t:ℂ)^(s - 1)*V8 n x t=(t:ℂ)^(s - (n:ℂ) - 1)*(((Inv.inv (Real.log t):ℝ):ℂ)):=by
 have qa : Not ((t:ℂ)=0) :=
  Complex.ofReal_ne_zero.mpr
   (ne_of_gt (lt_trans (lt_trans Real.zero_lt_one hx) ht))
 simp only [V8,if_neg (not_le.mpr ht)]
 rw [<- mul_assoc,<- Complex.cpow_add (s - 1) (-(n:ℂ)) qa]
 congr 1
 congr 1
 ring
theorem vU {n : Nat} {s:ℂ} {x:ℝ} (hx : 1 < x) (qf : 0 < s.re) (qi : s.re < n) : MellinConvergent (V8 n x) s:=by
 have qg : 0 < x:=lt_trans Real.zero_lt_one hx
 have qb : -1 < (s - 1).re:=by
  simp only [Complex.sub_re,Complex.one_re]
  linarith
 have qa : (s - (n:ℂ) - 1).re < -1:=by
  simp only [Complex.sub_re,Complex.natCast_re,Complex.one_re]
  linarith
 have qe :
   IntegrableOn (fun t:ℝ => (t:ℂ)^(s - 1)) (Ioc 0 x):=by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le qg.le).mp
   (intervalIntegral.intervalIntegrable_cpow' qb)
 have qj :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(s - 1)*V8 n x t) (Ioc 0 x):=by
  have qc :
    IntegrableOn (fun t:ℝ =>
     (t:ℂ)^(s - 1) *
      ((x:ℂ)^(-(n:ℂ)) *
       (((Inv.inv (Real.log x):ℝ):ℂ)))) (Ioc 0 x) :=
   qe.mul_const _
  exact qc.congr_fun
   (fun t ht => (wu n s ht.2).symm)
   measurableSet_Ioc
 have qd :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(s - (n:ℂ) - 1) *
     (((Inv.inv (Real.log t):ℝ):ℂ))) (Ioi x):=by
  simpa using Yf hx qa 1
 have qh :
   IntegrableOn (fun t:ℝ =>
    (t:ℂ)^(s - 1)*V8 n x t) (Ioi x):=by
  exact qd.congr_fun
   (fun t ht => (wz n s hx ht).symm)
   measurableSet_Ioi
 unfold MellinConvergent
 simp only [smul_eq_mul]
 rw [<- Ioc_union_Ioi_eq_Ioi qg.le]
 exact qj.union qh
theorem yi {n : Nat} {s:ℂ} {x:ℝ} (hx : 1 < x) (qg : 0 < s.re) (qk : s.re < n) : mellin (V8 n x) s=WT n s x/s:=by
  have qh : 0 < x:=lt_trans Real.zero_lt_one hx
  have qc : Not ((x:ℂ)=0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt qh)
  have qd : Not (s=0):=by
    intro h
    rw [h] at qg
    norm_num at qg
  have qb : Not (Real.log x=0):=ne_of_gt (Real.log_pos hx)
  have qi:=vU hx qg qk
  have qa :
      IntegrableOn (fun t:ℝ =>
        (t:ℂ)^(s - 1)*V8 n x t) (Ioi 0):=by
    simpa only [MellinConvergent,smul_eq_mul] using qi
  have ql:=qa.mono_set (Ioc_subset_Ioi_self : Ioc 0 x <= Ioi 0)
  have qj:=qa.mono_set (Ioi_subset_Ioi qh.le)
  unfold mellin
  simp only [smul_eq_mul]
  rw [<- Ioc_union_Ioi_eq_Ioi qh.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi ql qj]
  have qe :
      integral (volume.restrict (Ioc 0 x)) (fun t:ℝ =>
          (t:ℂ)^(s - 1)*V8 n x t) =
        (x:ℂ)^(s - (n:ℂ)) /
          (s*((Real.log x:ℝ):ℂ)):=by
    calc
      integral (volume.restrict (Ioc 0 x)) (fun t:ℝ =>
          (t:ℂ)^(s - 1)*V8 n x t) =
          integral (volume.restrict (Ioc 0 x)) (fun t:ℝ =>
            (t:ℂ)^(s - 1) *
              ((x:ℂ)^(-(n:ℂ)) *
                (((Inv.inv (Real.log x):ℝ):ℂ)))):=by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact wu n s ht.2
      _ = ((x:ℂ)^s/s) *
          ((x:ℂ)^(-(n:ℂ)) *
            (((Inv.inv (Real.log x):ℝ):ℂ))):=by
        rw [integral_mul_const,
          <- intervalIntegral.integral_of_le qh.le,
          integral_cpow (Or.inl (by
            simp only [Complex.sub_re,Complex.one_re]
            linarith : -1 < (s - 1).re))]
        rw [show s - 1+1=s by ring]
        simp only [Complex.ofReal_zero,Complex.zero_cpow qd,sub_zero]
      _ = ((x:ℂ)^s*(x:ℂ)^(-(n:ℂ))) /
          (s*((Real.log x:ℝ):ℂ)):=by
        push_cast
        field_simp [qd,qb]
      _ = (x:ℂ)^(s - (n:ℂ)) /
          (s*((Real.log x:ℝ):ℂ)):=by
        rw [<- Complex.cpow_add s (-(n:ℂ)) qc]
        congr 2
  have qf :
      integral (volume.restrict (Ioi x)) (fun t:ℝ =>
          (t:ℂ)^(s - 1)*V8 n x t) =
        WO (s - (n:ℂ)) 1 x:=by
    unfold WO
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact wz n s hx ht
  rw [qe,qf]
  exact (zK qd hx qk).symm
theorem v5 {a:ℝ} (ha : Not (a=0)) : Integrable (fun t:ℝ => (Inv.inv (norm ((a:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)):=by
 have qa :
   Integrable (fun t:ℝ => Inv.inv (1+(t/a)^(2 : Nat))) :=
  integrable_inv_one_add_sq.comp_div ha
 have qd :
   Integrable (fun t:ℝ =>
    Inv.inv (1+(t/a)^(2 : Nat))*Inv.inv (a^(2 : Nat))) :=
  qa.mul_const _
 apply qd.congr
 filter_upwards with t
 have qb :
   norm ((a:ℂ)+(t:ℂ)*Complex.I)^(2 : Nat) =
    a^(2 : Nat)+t^(2 : Nat):=by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp
  ring
 have qc : 0 < a^(2 : Nat)+t^(2 : Nat):=by
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
 rw [inv_pow,qb]
 field_simp [ha,ne_of_gt qc]
theorem yN {n : Nat} {s:ℂ} {x:ℝ} (hx : 1 < x) (hs : s.re < n) : norm (-((x:ℂ)^(s - (n:ℂ)))/((Real.log x:ℝ):ℂ)^(2 : Nat)+2*WO (s - (n:ℂ)) 3 x) <= x^(s.re - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^(s.re - (n:ℝ))/(s.re - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))):=by
  have qc : 0 < x:=lt_trans Real.zero_lt_one hx
  have qb : 0 < Real.log x:=Real.log_pos hx
  have qe : (s - (n:ℂ)).re < 0:=by
    simp only [Complex.sub_re,Complex.natCast_re]
    linarith
  have qa :
      norm
          (-((x:ℂ)^(s - (n:ℂ))) /
            ((Real.log x:ℝ):ℂ)^(2 : Nat)) =
        x^(s.re - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat)):=by
    rw [norm_div,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos qc,
      norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos qb]
    simp only [Complex.sub_re,Complex.natCast_re]
    rw [div_eq_mul_inv]
  have qd :
      norm (WO (s - (n:ℂ)) 3 x) <=
        (-x^(s.re - (n:ℝ))/(s.re - (n:ℝ))) *
          Inv.inv ((Real.log x)^(3 : Nat)):=by
    simpa only [Complex.sub_re,Complex.natCast_re] using
      Vr hx qe 3
  calc
    norm
        (-((x:ℂ)^(s - (n:ℂ))) /
            ((Real.log x:ℝ):ℂ)^(2 : Nat) +
          2*WO (s - (n:ℂ)) 3 x) <=
        norm (-((x:ℂ)^(s - (n:ℂ))) /
          ((Real.log x:ℝ):ℂ)^(2 : Nat)) +
          norm (2*WO (s - (n:ℂ)) 3 x) :=
      norm_add_le _ _
    _ = x^(s.re - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat)) +
        2*norm (WO (s - (n:ℂ)) 3 x):=by
      rw [qa,norm_mul]
      norm_num
    _ <= _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left qd zero_le_two)
theorem vL (n : Nat) (s:ℂ) : norm (((n:ℂ)/((n:ℂ) - s))/s) <= ((n:ℝ)/2)*((Inv.inv (norm s))^(2 : Nat)+(Inv.inv (norm (s - (n:ℂ))))^(2 : Nat)):=by
  have qa :
      norm ((n:ℂ) - s)=norm (s - (n:ℂ)):=by
    rw [show (n:ℂ) - s = -(s - (n:ℂ)) by ring,norm_neg]
  have hAM :
      Inv.inv (norm (s - (n:ℂ)))*Inv.inv (norm s) <=
        ((Inv.inv (norm s))^(2 : Nat) +
          (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat))/2:=by
    nlinarith [sq_nonneg
      (Inv.inv (norm s) - Inv.inv (norm (s - (n:ℂ))))]
  rw [norm_div,norm_div,Complex.norm_natCast,qa]
  calc
    (n:ℝ)/norm (s - (n:ℂ))/norm s =
        (n:ℝ) *
          (Inv.inv (norm (s - (n:ℂ)))*Inv.inv (norm s)):=by ring
    _ <= (n:ℝ) *
        (((Inv.inv (norm s))^(2 : Nat) +
          (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat))/2) :=
      mul_le_mul_of_nonneg_left hAM (Nat.cast_nonneg n)
    _ = _ := by ring
theorem yS {n : Nat} (hn : 1 <= n) {s:ℂ} (qe : Not (s=0)) {x:ℝ} (hx : 1 < x) (hs : s.re < n) : norm (WT n s x/s) <= (((n:ℝ)/2)*x^(s.re - (n:ℝ))*Inv.inv (Real.log x))*((Inv.inv (norm s))^(2 : Nat)+(Inv.inv (norm (s - (n:ℂ))))^(2 : Nat))+(x^(s.re - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat))+2*((-x^(s.re - (n:ℝ))/(s.re - (n:ℝ)))*Inv.inv ((Real.log x)^(3 : Nat))))*(Inv.inv (norm (s - (n:ℂ))))^(2 : Nat):=by
  have qf : 0 < x:=lt_trans Real.zero_lt_one hx
  have qd : 0 < Real.log x:=Real.log_pos hx
  have qb :
      norm ((x:ℂ)^(s - (n:ℂ)) *
        (((Inv.inv (Real.log x):ℝ):ℂ))) =
        x^(s.re - (n:ℝ))*Inv.inv (Real.log x):=by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos qf,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr qd)]
    simp only [Complex.sub_re,Complex.natCast_re]
  have qa : 0 <= x^(s.re - (n:ℝ))*Inv.inv (Real.log x) :=
    mul_nonneg (Real.rpow_nonneg qf.le _) (inv_nonneg.mpr qd.le)
  have qg :
      norm ((((n:ℂ)/((n:ℂ) - s)) *
          (x:ℂ)^(s - (n:ℂ)) *
          (((Inv.inv (Real.log x):ℝ):ℂ)))/s) <=
        (((n:ℝ)/2)*x^(s.re - (n:ℝ))*Inv.inv (Real.log x)) *
          ((Inv.inv (norm s))^(2 : Nat) +
            (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat)):=by
    have qc :
        (((n:ℂ)/((n:ℂ) - s)) *
            (x:ℂ)^(s - (n:ℂ)) *
            (((Inv.inv (Real.log x):ℝ):ℂ)))/s =
          (((n:ℂ)/((n:ℂ) - s))/s) *
            ((x:ℂ)^(s - (n:ℂ)) *
              (((Inv.inv (Real.log x):ℝ):ℂ))):=by ring
    rw [qc,norm_mul,qb]
    calc
      norm (((n:ℂ)/((n:ℂ) - s))/s) *
          (x^(s.re - (n:ℝ))*Inv.inv (Real.log x)) <=
          (((n:ℝ)/2) *
            ((Inv.inv (norm s))^(2 : Nat) +
              (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat))) *
            (x^(s.re - (n:ℝ))*Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right
          (vL n s) qa
      _ = _ := by ring
  have qh :
      norm (Vv n s x/s) <=
        (x^(s.re - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat)) +
          2*((-x^(s.re - (n:ℝ))/(s.re - (n:ℝ))) *
            Inv.inv ((Real.log x)^(3 : Nat)))) *
          (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat):=by
    rw [ZK qe,norm_mul,norm_inv,norm_pow]
    have hB:=yN hx hs
    have h:=mul_le_mul_of_nonneg_left hB
      (inv_nonneg.mpr (sq_nonneg (norm (s - (n:ℂ)))))
    simpa only [inv_pow,mul_comm] using h
  rw [v3 hn hx hs,add_div]
  exact (norm_add_le _ _).trans (add_le_add qg qh)
theorem yb {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qk : 0 < c) (qm : c < n) : Complex.VerticalIntegrable (mellin (V8 n x)) c:=by
 let A : ℝ:=((n:ℝ)/2)*x^(c - (n:ℝ))*Inv.inv (Real.log x)
 let B : ℝ:=x^(c - (n:ℝ))*Inv.inv ((Real.log x)^(2 : Nat)) +
  2*((-x^(c - (n:ℝ))/(c - (n:ℝ))) *
   Inv.inv ((Real.log x)^(3 : Nat)))
 have qe : Not (c=0):=ne_of_gt qk
 have qd : Not (c - (n:ℝ)=0):=ne_of_lt (sub_neg.mpr qm)
 have hC:=v5 qe
 have hN:=v5 qd
 have qf : Integrable (fun t:ℝ =>
   A *
     ((Inv.inv (norm ((c:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat) +
      (Inv.inv (norm (((c - (n:ℝ):ℝ):ℂ) +
       (t:ℂ)*Complex.I)))^(2 : Nat)) +
    B*(Inv.inv (norm (((c - (n:ℝ):ℝ):ℂ) +
     (t:ℂ)*Complex.I)))^(2 : Nat)) :=
  ((hC.add hN).const_mul A).add (hN.const_mul B)
 have qa : Measurable (fun z : Prod ℝ ℝ =>
   (z.2:ℂ)^((c:ℂ)+(z.1:ℂ)*Complex.I - 1)):=by
  fun_prop
 have qb : Measurable (fun z : Prod ℝ ℝ => V8 n x z.2) :=
  (ZH n hx).measurable.comp measurable_snd
 have qg:=(qa.mul qb).stronglyMeasurable
 have qc : AEStronglyMeasurable (fun t:ℝ =>
   mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I))
   volume:=by
  have h : StronglyMeasurable (fun t:ℝ =>
    integral (volume.restrict (Ioi (0:ℝ))) (fun u:ℝ =>
     (u:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I - 1) *
      V8 n x u)):=qg.integral_prod_right'
  simpa only [mellin,smul_eq_mul] using h.aestronglyMeasurable
 unfold Complex.VerticalIntegrable
 apply qf.mono' qc
 filter_upwards with t
 have qn : ((c:ℂ)+(t:ℂ)*Complex.I).re=c:=by simp
 have qh : Not (((c:ℂ)+(t:ℂ)*Complex.I)=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  rw [qn,Complex.zero_re] at hRe
  exact qe hRe
 have ql : 0 < ((c:ℂ)+(t:ℂ)*Complex.I).re:=by
  rw [qn]
  exact qk
 have qo : ((c:ℂ)+(t:ℂ)*Complex.I).re < (n:ℝ):=by
  rw [qn]
  exact qm
 rw [yi hx ql qo]
 have qi:=yS hn qh hx qo
 have qj :
   (c:ℂ)+(t:ℂ)*Complex.I - (n:ℂ) =
    ((c - (n:ℝ):ℝ):ℂ)+(t:ℂ)*Complex.I:=by
  push_cast
  ring
 simpa only [qn,qj,A,B] using qi
theorem vH {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qa : 0 < c) (qb : c < n) {t:ℝ} (ht : 0 < t) : mellinInv c (mellin (V8 n x)) t=V8 n x t:=by
  apply mellinInv_mellin_eq c (V8 n x) ht
  . exact vU hx
      (by simpa using qa) (by simpa using qb)
  . exact yb hn hx qa qb
  . exact (ZH n hx).continuousAt
theorem ZV {s:ℂ} (hs : 1 < s.re) : Summable (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^s):=by
 refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr ?_
 intro m
 by_cases hm : m=0
 case pos => simp [hm]
 case neg => rw [LSeries.term_of_ne_zero hm]
theorem vY {s:ℂ} (hs : 1 < s.re) : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^s) = -deriv riemannZeta s/riemannZeta s:=by
 rw [<- ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,LSeries]
 apply tsum_congr
 intro m
 by_cases hm : m=0
 case pos => simp [hm]
 case neg => rw [LSeries.term_of_ne_zero hm]
theorem YA (c t:ℝ) (m : Nat) : norm ((ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I))=norm ((ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^(c:ℂ)):=by
  cases m with
  | zero => simp
  | succ m =>
      rw [norm_div,norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m),
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
      simp
theorem ZX {c:ℝ} (hc : 1 < c) {H:ℝ -> ℂ} (hH : Integrable H) : tsum (fun m : Nat => integral volume (fun t:ℝ => ((ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I))*H t))=integral volume (fun t:ℝ => (-deriv riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I)/riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I))*H t):=by
  let F : Nat -> ℝ -> ℂ:=fun m t =>
    ((ArithmeticFunction.vonMangoldt m:ℂ) /
      (m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I))*H t
  let A : Nat -> ℝ:=fun m =>
    norm ((ArithmeticFunction.vonMangoldt m:ℂ) /
      (m:ℂ)^(c:ℂ))
  have qf : forall m : Nat,forall t:ℝ,norm (F m t)=A m*norm (H t):=by
    intro m t
    dsimp [F,A]
    rw [norm_mul,YA]
  have qg : forall m : Nat,Integrable (F m):=by
    intro m
    have qb : Measurable (fun t:ℝ =>
        (ArithmeticFunction.vonMangoldt m:ℂ) /
          (m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I)):=by
      fun_prop
    have qe : AEStronglyMeasurable (F m) volume :=
      qb.aestronglyMeasurable.mul hH.aestronglyMeasurable
    apply (hH.norm.const_mul (A m)).mono' qe
    filter_upwards with t
    rw [qf]
  have qa : forall m : Nat,
      integral volume (fun t:ℝ => norm (F m t)) =
        A m*integral volume (fun t:ℝ => norm (H t)):=by
    intro m
    have qc : (fun t:ℝ => norm (F m t)) =
        (fun t:ℝ => A m*norm (H t)):=by
      funext t
      exact qf m t
    rw [qc,integral_const_mul]
  have qh : Summable A:=by
    exact (ZV (s:=(c:ℂ)) (by simpa using hc)).norm
  have qd : Summable (fun m : Nat => integral volume (fun t:ℝ => norm (F m t))):=by
    have h:=qh.mul_right (integral volume (fun t:ℝ => norm (H t)))
    exact h.congr (fun m => (qa m).symm)
  calc
    tsum (fun m : Nat => integral volume (F m)) =
        integral volume (fun t:ℝ => tsum (fun m : Nat => F m t)) :=
      integral_tsum_of_summable_integral_norm qg qd
    _ = integral volume (fun t:ℝ =>
        (-deriv riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I) /
          riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I))*H t):=by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F]
      rw [tsum_mul_right,vY (by simpa using hc)]
theorem zV {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qa : 0 < c) (qc : c < n) (m : Nat) : (ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ)=(((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => ((ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I))*mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)):=by
  by_cases hm : m=0
  case pos => simp [hm]
  case neg =>
    have qb : 0 < (m:ℝ):=by
      exact_mod_cast (Nat.pos_of_ne_zero hm)
    have qd:=vH hn hx qa qc qb
    simp only [mellinInv,RCLike.real_smul_eq_coe_mul,smul_eq_mul,
      Complex.ofReal_natCast] at qd
    rw [<- qd]
    calc
      (ArithmeticFunction.vonMangoldt m:ℂ) *
          ((((1/(2*Real.pi):ℝ):ℂ)) *
            integral volume (fun t:ℝ =>
              (m:ℂ)^(-((c:ℂ)+(t:ℂ)*Complex.I)) *
                mellin (V8 n x)
                  ((c:ℂ)+(t:ℂ)*Complex.I))) =
          (((1/(2*Real.pi):ℝ):ℂ)) *
            ((ArithmeticFunction.vonMangoldt m:ℂ) *
              integral volume (fun t:ℝ =>
                (m:ℂ)^(-((c:ℂ)+(t:ℂ)*Complex.I)) *
                  mellin (V8 n x)
                    ((c:ℂ)+(t:ℂ)*Complex.I))):=by ring
      _ = (((1/(2*Real.pi):ℝ):ℂ)) *
          integral volume (fun t:ℝ =>
            (ArithmeticFunction.vonMangoldt m:ℂ) *
              ((m:ℂ)^(-((c:ℂ)+(t:ℂ)*Complex.I)) *
                mellin (V8 n x)
                  ((c:ℂ)+(t:ℂ)*Complex.I))):=by
        rw [integral_const_mul]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        rw [Complex.cpow_neg,div_eq_mul_inv]
        ring
theorem vM {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (hc : 1 < c) (qd : c < n) : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ))=(((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => (-deriv riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I)/riemannZeta ((c:ℂ)+(t:ℂ)*Complex.I))*mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)):=by
  have qb : 0 < c:=lt_trans Real.zero_lt_one hc
  have qa:=yb hn hx qb qd
  have qc:=ZX hc qa
  calc
    tsum (fun m : Nat =>
        (ArithmeticFunction.vonMangoldt m:ℂ) *
          V8 n x (m:ℝ)) =
        tsum (fun m : Nat =>
          (((1/(2*Real.pi):ℝ):ℂ)) *
            integral volume (fun t:ℝ =>
              ((ArithmeticFunction.vonMangoldt m:ℂ) /
                (m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I)) *
                mellin (V8 n x)
                  ((c:ℂ)+(t:ℂ)*Complex.I))):=by
      apply tsum_congr
      intro m
      exact zV hn hx qb qd m
    _ = (((1/(2*Real.pi):ℝ):ℂ)) *
        tsum (fun m : Nat => integral volume (fun t:ℝ =>
          ((ArithmeticFunction.vonMangoldt m:ℂ) /
            (m:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I)) *
            mellin (V8 n x)
              ((c:ℂ)+(t:ℂ)*Complex.I))):=by
      rw [tsum_mul_left]
    _ = _ := by rw [qc]
theorem wy {H:ℝ -> ℂ} (hH : Integrable H) {c:ℝ} {rho:ℂ} (qe : rho.re < c) : Integrable (fun z : Prod ℝ ℝ => H z.1*(z.2:ℂ)^(rho - ((c:ℂ)+(z.1:ℂ)*Complex.I) - 1)) (volume.prod (volume.restrict (Ioi (1:ℝ)))):=by
 have qb : IntegrableOn (fun u:ℝ => u^(rho.re - c - 1)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) Real.zero_lt_one
 have qc:=hH.norm.mul_prod qb
 have qa : Measurable (fun z : Prod ℝ ℝ =>
   (z.2:ℂ)^(rho - ((c:ℂ)+(z.1:ℂ)*Complex.I) - 1)):=by
  fun_prop
 have qd : AEStronglyMeasurable (fun z : Prod ℝ ℝ => H z.1 *
   (z.2:ℂ)^(rho - ((c:ℂ)+(z.1:ℂ)*Complex.I) - 1))
   (volume.prod (volume.restrict (Ioi (1:ℝ)))) :=
  hH.aestronglyMeasurable.comp_fst.mul qa.aestronglyMeasurable
 apply qc.mono' qd
 have qf : Filter.Eventually (fun z : Prod ℝ ℝ => 1 < z.2)
   (ae (volume.prod (volume.restrict (Ioi (1:ℝ))))):=by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
   (measurableSet_Ioi.preimage measurable_snd)).mpr
  exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioi)
 filter_upwards [qf] with z hz
 rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < z.2)]
 simp
theorem yH {H:ℝ -> ℂ} (hH : Integrable H) {c:ℝ} {rho:ℂ} (qd : rho.re < c) : integral volume (fun t:ℝ => H t/((c:ℂ)+(t:ℂ)*Complex.I - rho))=integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ => (u:ℂ)^(rho - 1)*integral volume (fun t:ℝ => (u:ℂ)^(-((c:ℂ)+(t:ℂ)*Complex.I))*H t)):=by
  have qa:=wy hH qd
  have qb : forall t:ℝ,
      integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ =>
        H t*(u:ℂ)^(rho - ((c:ℂ)+(t:ℂ)*Complex.I) - 1)) =
      H t/((c:ℂ)+(t:ℂ)*Complex.I - rho):=by
    intro t
    rw [integral_const_mul,integral_Ioi_cpow_of_lt (by
      simp only [Complex.sub_re,Complex.add_re,Complex.one_re,
        Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im]
      linarith : (rho - ((c:ℂ)+(t:ℂ)*Complex.I) - 1).re < -1)
        Real.zero_lt_one]
    simp only [Complex.ofReal_one,Complex.one_cpow,sub_add_cancel]
    have qe : rho - ((c:ℂ)+(t:ℂ)*Complex.I) =
        -((c:ℂ)+(t:ℂ)*Complex.I - rho):=by ring
    rw [qe]
    simp only [div_eq_mul_inv,inv_neg,neg_mul,one_mul,neg_neg]
  calc
    integral volume (fun t:ℝ =>
        H t/((c:ℂ)+(t:ℂ)*Complex.I - rho)) =
      integral volume (fun t:ℝ =>
        integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ =>
          H t*(u:ℂ)^(rho - ((c:ℂ)+(t:ℂ)*Complex.I) - 1))):=by
        apply integral_congr_ae
        filter_upwards with t
        exact (qb t).symm
    _ = integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ =>
        integral volume (fun t:ℝ =>
          H t*(u:ℂ)^(rho - ((c:ℂ)+(t:ℂ)*Complex.I) - 1))) :=
      integral_integral_swap qa
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      have qc : Not ((u:ℂ)=0) :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans Real.zero_lt_one hu))
      rw [<- integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [show rho - ((c:ℂ)+(t:ℂ)*Complex.I) - 1 =
          (rho - 1)+(-((c:ℂ)+(t:ℂ)*Complex.I)) by ring,
        Complex.cpow_add _ _ qc]
      ring
theorem wD {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qb : 0 < c) (qc : c < n) {rho:ℂ} (qd : rho.re < c) : (((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)/((c:ℂ)+(t:ℂ)*Complex.I - rho))=integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ => (u:ℂ)^(rho - 1)*V8 n x u):=by
 rw [yH
  (yb hn hx qb qc) qd,
  <- integral_const_mul]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro u hu
 dsimp only
 have qe:=vH hn hx qb qc
  (lt_trans Real.zero_lt_one hu)
 simp only [mellinInv,RCLike.real_smul_eq_coe_mul,smul_eq_mul] at qe
 have qa:=congrArg (fun v:ℂ => (u:ℂ)^(rho - 1)*v) qe
 simpa only [mul_left_comm,mul_assoc,mul_comm] using! qa
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
theorem ys {n : Nat} {x:ℝ} (hx : 1 < x) {rho:ℂ} (qf : rho.re < n) : IntegrableOn (fun u:ℝ => (u:ℂ)^(rho - 1)*V8 n x u) (Ioi 1):=by
 have qb : Not (Membership.mem (uIcc (1:ℝ) x) 0):=by
  rw [uIcc_of_le hx.le]
  simp
 have qd : IntegrableOn (fun u:ℝ => (u:ℂ)^(rho - 1))
   (Ioc 1 x) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp
   (intervalIntegral.intervalIntegrable_cpow (Or.inr qb))
 have qa : IntegrableOn (fun u:ℝ =>
   (u:ℂ)^(rho - 1) *
    ((x:ℂ)^(-(n:ℂ))*(((Inv.inv (Real.log x):ℝ):ℂ))))
   (Ioc 1 x):=qd.mul_const _
 have qg : IntegrableOn (fun u:ℝ =>
   (u:ℂ)^(rho - 1)*V8 n x u) (Ioc 1 x) :=
  qa.congr_fun
   (fun u hu => (wu n rho hu.2).symm)
   measurableSet_Ioc
 have qc : IntegrableOn (fun u:ℝ =>
   (u:ℂ)^(rho - (n:ℂ) - 1) *
    (((Inv.inv (Real.log u):ℝ):ℂ))) (Ioi x):=by
  simpa using Yf hx (by
   simp only [Complex.sub_re,Complex.natCast_re,Complex.one_re]
   linarith : (rho - (n:ℂ) - 1).re < -1) 1
 have qe : IntegrableOn (fun u:ℝ =>
   (u:ℂ)^(rho - 1)*V8 n x u) (Ioi x) :=
  qc.congr_fun
   (fun u hu => (wz n rho hx hu).symm)
   measurableSet_Ioi
 rw [<- Ioc_union_Ioi_eq_Ioi hx.le]
 exact qg.union qe
theorem wr {n : Nat} {x:ℝ} (hx : 1 < x) {rho:ℂ} (qd : Not (rho=0)) (qi : rho.re < n) : integral (volume.restrict (Ioi (1:ℝ))) (fun u:ℝ => (u:ℂ)^(rho - 1)*V8 n x u)=WT n rho x/rho - V8 n x 1/rho:=by
  have qf : Not ((x:ℂ)=0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans Real.zero_lt_one hx))
  have qb : Not (Membership.mem (uIcc (1:ℝ) x) 0):=by
    rw [uIcc_of_le hx.le]
    simp
  have qe : Not (rho - 1 = -1):=by
    intro h
    apply qd
    linear_combination h
  have qj:=ys hx qi
  have qk:=qj.mono_set (Ioc_subset_Ioi_self : Ioc 1 x <= Ioi 1)
  have qg:=qj.mono_set (Ioi_subset_Ioi hx.le)
  rw [<- Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi qk qg]
  have qc : integral (volume.restrict (Ioc (1:ℝ) x)) (fun u:ℝ =>
      (u:ℂ)^(rho - 1)*V8 n x u) =
      ((x:ℂ)^rho - 1)/rho*V8 n x 1:=by
    calc
      integral (volume.restrict (Ioc (1:ℝ) x)) (fun u:ℝ =>
          (u:ℂ)^(rho - 1)*V8 n x u) =
        integral (volume.restrict (Ioc (1:ℝ) x)) (fun u:ℝ =>
          (u:ℂ)^(rho - 1)*V8 n x 1):=by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        simp only [V8,if_pos hu.2,if_pos hx.le]
      _ = _ := by
        rw [integral_mul_const,<- intervalIntegral.integral_of_le hx.le,
          integral_cpow (Or.inr (And.intro qe qb))]
        simp
  have qa : integral (volume.restrict (Ioi x)) (fun u:ℝ =>
      (u:ℂ)^(rho - 1)*V8 n x u) =
      WO (rho - (n:ℂ)) 1 x:=by
    unfold WO
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact wz n rho hx hu
  rw [qc,qa,
    zK qd hx qi]
  have qh : (x:ℂ)^rho*(x:ℂ)^(-(n:ℂ)) =
      (x:ℂ)^(rho - (n:ℂ)):=by
    rw [<- Complex.cpow_add _ _ qf]
    congr 1
  simp only [V8,if_pos hx.le,Complex.ofReal_inv]
  have ql : Not (((Real.log x:ℝ):ℂ)=0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos hx))
  field_simp [qd,ql]
  linear_combination qh
theorem Yl {H:ℝ -> ℂ} (hH : Integrable H) {c:ℝ} {rho:ℂ} (qc : rho.re < c) : Integrable (fun t:ℝ => H t/((c:ℂ)+(t:ℂ)*Complex.I - rho)):=by
  have qd : 0 < c - rho.re:=sub_pos.mpr qc
  have qa : Measurable (fun t:ℝ =>
      Inv.inv ((c:ℂ)+(t:ℂ)*Complex.I - rho)):=by
    fun_prop
  have qb : AEStronglyMeasurable (fun t:ℝ =>
      H t/((c:ℂ)+(t:ℂ)*Complex.I - rho)) volume:=by
    simpa only [div_eq_mul_inv] using!
      hH.aestronglyMeasurable.mul qa.aestronglyMeasurable
  apply (hH.norm.div_const (c - rho.re)).mono' qb
  filter_upwards with t
  have qe : c - rho.re <= norm ((c:ℂ)+(t:ℂ)*Complex.I - rho):=by
    calc
      c - rho.re <= abs (c - rho.re):=le_abs_self _
      _ <= norm ((c:ℂ)+(t:ℂ)*Complex.I - rho):=by
        simpa using Complex.abs_re_le_norm
          ((c:ℂ)+(t:ℂ)*Complex.I - rho)
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg (H t)) qd qe
theorem wZ {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qf : 0 < c) (qi : c < n) {rho:ℂ} (qc : Not (rho=0)) (qj : rho.re < c) : (((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)*(1/((c:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho))=WT n rho x/rho:=by
 let H:ℝ -> ℂ:=fun t =>
  mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)
 have qg : Integrable H :=
  yb hn hx qf qi
 have qa:=Yl qg qj
 have qd:=qg.div_const rho
 have qe : (((1/(2*Real.pi):ℝ):ℂ)) *
   integral volume H=V8 n x 1:=by
  have h:=vH hn hx qf qi Real.zero_lt_one
  simpa only [mellinInv,Complex.ofReal_one,Complex.one_cpow,
   RCLike.real_smul_eq_coe_mul,smul_eq_mul,one_mul,H] using! h
 have qb : (fun t:ℝ => H t *
   (1/((c:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho)) =
   (fun t:ℝ => H t/((c:ℂ)+(t:ℂ)*Complex.I - rho) +
    H t/rho):=by
  funext t
  ring
 change (((1/(2*Real.pi):ℝ):ℂ)) *
  integral volume (fun t:ℝ => H t *
   (1/((c:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho))=_
 rw [qb,integral_add qa qd,mul_add]
 have qh : (((1/(2*Real.pi):ℝ):ℂ)) *
   integral volume (fun t:ℝ =>
    H t/((c:ℂ)+(t:ℂ)*Complex.I - rho)) =
   WT n rho x/rho - V8 n x 1/rho:=by
  rw [wD hn hx qf qi qj,
   wr hx qc (lt_trans qj qi)]
 rw [qh,integral_div,<- mul_div_assoc,qe]
 ring
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
theorem Vq {r:ℝ} (hr : 0 < r) : (Inv.inv r)^(3/2:ℝ)=1/(r*Real.sqrt r):=by
 rw [<- Real.rpow_neg_eq_inv_rpow,Real.rpow_neg hr.le]
 rw [show (3/2:ℝ)=1+1/2 by norm_num,
  Real.rpow_add hr,Real.rpow_one,<- Real.sqrt_eq_rpow,one_div]
theorem w7 {R a b:ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (qb : R <= a+b) : 1/(R*a*b) <= 2*(Inv.inv R)^(3/2:ℝ)*((Inv.inv a)^(3/2:ℝ)+(Inv.inv b)^(3/2:ℝ)):=by
  rw [Vq hR,Vq ha,
    Vq hb]
  have qe : 0 < Real.sqrt R:=Real.sqrt_pos.mpr hR
  have qf : 0 < Real.sqrt a:=Real.sqrt_pos.mpr ha
  have qg : 0 < Real.sqrt b:=Real.sqrt_pos.mpr hb
  have qc : forall u v:ℝ,0 < u -> 0 < v -> u <= v ->
      R <= u+v ->
      1/(R*u*v) <= 2*(1/(R*Real.sqrt R))*(1/(u*Real.sqrt u)):=by
    intro u v hu hv huv hRuv
    have qh : 0 < Real.sqrt u:=Real.sqrt_pos.mpr hu
    have qa : (Real.sqrt R*Real.sqrt u)^2 <= (2*v)^2:=by
      rw [mul_pow,Real.sq_sqrt hR.le,Real.sq_sqrt hu.le]
      have hRu : R*u <= (u+v)*u:=mul_le_mul_of_nonneg_right hRuv hu.le
      have qj : u*u <= v*v:=mul_self_le_mul_self hu.le huv
      have hvu : v*u <= v*v:=mul_le_mul_of_nonneg_left huv hv.le
      nlinarith [sq_nonneg v]
    have qd : Real.sqrt R*Real.sqrt u <= 2*v:=by
      nlinarith [sq_nonneg (Real.sqrt R*Real.sqrt u - 2*v)]
    have qk : R*Real.sqrt R*(u*Real.sqrt u)/2 <= R*u*v:=by
      nlinarith [mul_le_mul_of_nonneg_left qd (by positivity : 0 <= R*u)]
    calc
      1/(R*u*v) <= 1/(R*Real.sqrt R*(u*Real.sqrt u)/2) :=
        one_div_le_one_div_of_le (by positivity) qk
      _ = 2*(1/(R*Real.sqrt R))*(1/(u*Real.sqrt u)):=by
        field_simp
  rcases le_total a b with hab | hba
  . have h:=qc a b ha hb hab qb
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by positivity)
  . have h:=qc b a hb ha hba (by linarith)
    have qi : R*a*b=R*b*a:=by ring
    rw [qi]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)
theorem wn {a:ℝ} (ha : 1 <= a) : Integrable (fun t:ℝ => (Inv.inv (norm ((a:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ)):=by
  have qf : Integrable (fun t:ℝ => (1+norm t)^(-(3/2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have qd:=qf.const_mul ((2:ℝ)^(3/2:ℝ))
  have qg : Measurable (fun t:ℝ =>
      (Inv.inv (norm ((a:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ)):=by
    fun_prop
  apply qd.mono' qg.aestronglyMeasurable
  filter_upwards with t
  let s : ℂ:=(a:ℂ)+(t:ℂ)*Complex.I
  have hRe : a <= norm s:=by
    calc
      a <= abs a:=le_abs_self a
      _ <= norm s:=by simpa [s] using Complex.abs_re_le_norm s
  have hIm : norm t <= norm s:=by
    simpa [s,Real.norm_eq_abs] using Complex.abs_im_le_norm s
  have qa : 0 < norm s:=by linarith
  have qb : 0 < 1+norm t:=by positivity
  have qe : (1+norm t)/2 <= norm s:=by linarith
  have qh : Inv.inv (norm s) <= 2*Inv.inv (1+norm t):=by
    have h:=one_div_le_one_div_of_le (by positivity : 0 < (1+norm t)/2) qe
    simpa only [one_div,inv_div,div_eq_mul_inv,mul_inv,inv_inv,
      one_mul,mul_one,mul_comm] using h
  have qc : 0 <= (Inv.inv (norm s))^(3/2:ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr qa.le) _
  change norm ((Inv.inv (norm s))^(3/2:ℝ)) <= _
  rw [Real.norm_eq_abs,abs_of_nonneg qc]
  calc
    (Inv.inv (norm s))^(3/2:ℝ) <=
        (2*Inv.inv (1+norm t))^(3/2:ℝ) :=
      Real.rpow_le_rpow (inv_nonneg.mpr qa.le) qh (by norm_num)
    _ = (2:ℝ)^(3/2:ℝ)*(1+norm t)^(-(3/2:ℝ)):=by
      rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr qb.le),
        <- Real.rpow_neg_eq_inv_rpow]
theorem yP {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : Exists fun C:ℝ => And (0 <= C) (forall t:ℝ,norm (mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)):=by
 let A : ℝ:=((n:ℝ)/2)*x^((3/2:ℝ) - n)*Inv.inv (Real.log x)
 let B : ℝ:=x^((3/2:ℝ) - n)*Inv.inv ((Real.log x)^2) +
  2*((-x^((3/2:ℝ) - n)/((3/2:ℝ) - n)) *
   Inv.inv ((Real.log x)^3))
 refine Exists.intro (10*abs A+9*abs B) (And.intro (by positivity) ?_)
 intro t
 let s : ℂ:=(3/2:ℂ)+(t:ℂ)*Complex.I
 have qc : (2:ℝ) <= n:=by exact_mod_cast hn
 have qi : s.re=(3/2:ℝ):=by simp [s]
 have qh : 0 < s.re:=by rw [qi]; norm_num
 have qj : s.re < (n:ℝ):=by rw [qi]; linarith
 have qd : Not (s=0):=by
  intro h
  rw [h] at qh
  norm_num at qh
 have qe : Not (s - (n:ℂ)=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  simp only [Complex.sub_re,Complex.natCast_re,Complex.zero_re,qi] at hRe
  linarith
 have qf : 0 < norm s:=norm_pos_iff.mpr qd
 have qg : 0 < norm (s - (n:ℂ)):=norm_pos_iff.mpr qe
 have hSq : norm s^(2 : Nat) <= 9*norm (s - (n:ℂ))^(2 : Nat):=by
  have qk : norm s^(2 : Nat)=(9/4:ℝ)+t^2:=by
   rw [Complex.sq_norm,Complex.normSq_apply]
   simp [s]
   ring
  have ql : norm (s - (n:ℂ))^(2 : Nat) =
    ((3/2:ℝ) - n)^2+t^2:=by
   rw [Complex.sq_norm,Complex.normSq_apply]
   simp [s]
   ring
  rw [qk,ql]
  have qb : 0 <= ((n:ℝ) - 1)*((n:ℝ) - 2) :=
   mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg t]
 have qm : (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat) <=
   9*(Inv.inv (norm s))^(2 : Nat):=by
  have h:=one_div_le_one_div_of_le
   (by positivity : 0 < norm s^(2 : Nat)/9)
   (by linarith : norm s^(2 : Nat)/9 <= norm (s - (n:ℂ))^(2 : Nat))
  simpa only [inv_pow,one_div,inv_div,div_eq_mul_inv,mul_inv,inv_inv,
   one_mul,mul_one,mul_comm] using h
 have qn : norm (mellin (V8 n x) s) <=
   A*((Inv.inv (norm s))^(2 : Nat) +
    (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat)) +
   B*(Inv.inv (norm (s - (n:ℂ))))^(2 : Nat):=by
  rw [yi hx qh qj]
  simpa only [qi,A,B] using
   yS (by omega : 1 <= n) qd hx qj
 apply qn.trans
 have qo:=add_le_add
  (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity :
   0 <= (Inv.inv (norm s))^(2 : Nat) +
    (Inv.inv (norm (s - (n:ℂ))))^(2 : Nat)))
  (mul_le_mul_of_nonneg_right (le_abs_self B)
   (sq_nonneg (Inv.inv (norm (s - (n:ℂ))))))
 have qa:=mul_le_mul_of_nonneg_left qm
  (add_nonneg (abs_nonneg A) (abs_nonneg B))
 change _ <= (10*abs A+9*abs B)*(Inv.inv (norm s))^(2 : Nat)
 nlinarith
theorem Zt {C:ℝ} (hC : 0 <= C) {z rho:ℂ} {t:ℝ} (qh : rho.re=(1/2:ℝ)) (hz : norm z <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : norm (z*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho)) <= 2*C*(Inv.inv (norm rho))^(3/2:ℝ)*((Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ)+(Inv.inv (norm ((1:ℂ)+((t - rho.im:ℝ):ℂ)*Complex.I)))^(3/2:ℝ)):=by
  let s : ℂ:=(3/2:ℂ)+(t:ℂ)*Complex.I
  have qi : s.re=(3/2:ℝ):=by simp [s]
  have qd : s - rho =
      (1:ℂ)+((t - rho.im:ℝ):ℂ)*Complex.I:=by
    apply Complex.ext
    . simp [s,qh]
      ring
    . simp [s]
  have qb : Not (rho=0):=by
    intro h
    rw [h] at qh
    norm_num at qh
  have qe : Not (s=0):=by
    intro h
    rw [h] at qi
    norm_num at qi
  have qc : Not (s - rho=0):=by
    intro h
    have qf:=congrArg Complex.re h
    simp only [Complex.sub_re,Complex.zero_re,qi,qh] at qf
    norm_num at qf
  have hR : 0 < norm rho:=norm_pos_iff.mpr qb
  have ha : 0 < norm s:=norm_pos_iff.mpr qe
  have hb : 0 < norm (s - rho):=norm_pos_iff.mpr qc
  have qa : norm rho <= norm s+norm (s - rho):=by
    calc
      norm rho=norm (s - (s - rho)):=by congr 1; ring
      _ <= norm s+norm (s - rho):=norm_sub_le _ _
  have qg : 1/(s - rho)+1/rho=s/(rho*(s - rho)):=by
    field_simp
    ring
  change norm (z*(1/(s - rho)+1/rho)) <= _
  change norm z <= C*(Inv.inv (norm s))^(2 : Nat) at hz
  rw [norm_mul,qg,norm_div,norm_mul]
  calc
    norm z*(norm s/(norm rho*norm (s - rho))) <=
        (C*(Inv.inv (norm s))^(2 : Nat)) *
          (norm s/(norm rho*norm (s - rho))) :=
      mul_le_mul_of_nonneg_right hz (by positivity)
    _ = C*(1/(norm rho*norm s*norm (s - rho))):=by
      field_simp
    _ <= C*(2*(Inv.inv (norm rho))^(3/2:ℝ) *
        ((Inv.inv (norm s))^(3/2:ℝ) +
          (Inv.inv (norm (s - rho)))^(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (w7 hR ha hb qa) hC
    _ = _ := by
      rw [qd]
      ring
theorem Y7 {H:ℝ -> ℂ} (hH : Integrable H) {rho:ℂ} (qa : rho.re=(1/2:ℝ)) : Integrable (fun t:ℝ => H t*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho)):=by
 have hR : Integrable (fun t:ℝ =>
   H t/((3/2:ℂ)+(t:ℂ)*Complex.I - rho)):=by
  simpa using! Yl hH
   (c:=(3/2:ℝ)) (by rw [qa]; norm_num)
 apply (hR.add (hH.div_const rho)).congr
 filter_upwards with t
 simp only [Pi.add_apply]
 ring
theorem vG (hRH : RiemannHypothesis) {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C) (qe : forall t:ℝ,norm (H t) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : Summable (fun p : Vc => integral volume (fun t:ℝ => norm (H t*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p)+1/Y5 p)))):=by
  let K:ℝ -> ℝ -> ℝ:=fun a t =>
    (Inv.inv (norm ((a:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ)
  let F : Vc -> ℝ -> ℂ:=fun p t => H t *
    (1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p) +
      1/Y5 p)
  have qf : Integrable (K (3/2)) :=
    wn (by norm_num)
  have qd : Integrable (K 1) :=
    wn le_rfl
  have hF : forall p : Vc,Integrable (F p):=by
    intro p
    exact Y7 hH
      (zq hRH p)
  have qa : forall p : Vc,
      integral volume (fun t:ℝ => norm (F p t)) <=
        (2*C*(integral volume (K (3/2))+integral volume (K 1))) *
          (Inv.inv (norm (Y5 p)))^(3/2:ℝ):=by
    intro p
    let rho : ℂ:=Y5 p
    let W : ℝ:=(Inv.inv (norm rho))^(3/2:ℝ)
    have qb : Integrable (fun t:ℝ => K 1 (t - rho.im)) :=
      qd.comp_sub_right rho.im
    have qc : Integrable (fun t:ℝ =>
        2*C*W*(K (3/2) t+K 1 (t - rho.im))) :=
      (qf.add qb).const_mul _
    calc
      integral volume (fun t:ℝ => norm (F p t)) <=
          integral volume (fun t:ℝ =>
            2*C*W*(K (3/2) t+K 1 (t - rho.im))):=by
        apply integral_mono_ae (hF p).norm qc
        filter_upwards with t
        simpa [F,K,W,rho] using Zt hC
          (zq hRH p) (qe t)
      _ = _ := by
        rw [integral_const_mul,integral_add qf qb,
          integral_sub_right_eq_self]
        dsimp [W,rho]
        ring
  have qg : Summable (fun p : Vc =>
      (2*C*(integral volume (K (3/2))+integral volume (K 1))) *
        (Inv.inv (norm (Y5 p)))^(3/2:ℝ)) :=
    (yM (by norm_num : (1:ℝ) < 3/2)).mul_left _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg (F p t))) qa qg
theorem Yj (hRH : RiemannHypothesis) {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C) (qb : forall t:ℝ,norm (H t) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : tsum (fun p : Vc => integral volume (fun t:ℝ => H t*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p)+1/Y5 p)))=integral volume (fun t:ℝ => tsum (fun p : Vc => H t*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p)+1/Y5 p))):=by
 have qa : Function.support (fun p : Vc =>
   (Inv.inv (norm (Y5 p)))^(2 : Nat))=Set.univ:=by
  ext p
  simp only [Function.mem_support,mem_univ,iff_true]
  exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
   (Zj p)))
 have qc:=va.countable_support
 rw [qa] at qc
 letI : Countable Vc:=Set.countable_univ_iff.mp qc
 exact integral_tsum_of_summable_integral_norm
  (fun p => Y7 hH
   (zq hRH p))
  (vG hRH hH hC qb)
theorem vs (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : (((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)*tsum (fun p : Vc => 1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p)+1/Y5 p))=tsum (fun p : Vc => WT n (Y5 p) x/Y5 p):=by
 choose C hC hBound using yP hn hx
 have qc : 1 <= n:=by omega
 have qb : (2:ℝ) <= n:=by exact_mod_cast hn
 have qe : (3/2:ℝ) < n:=by linarith
 let H:ℝ -> ℂ:=fun t =>
  mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)
 have hH : Integrable H:=by
  simpa [H,Complex.VerticalIntegrable] using! yb qc hx
   (by norm_num : (0:ℝ) < 3/2) qe
 have qd:=Yj hRH hH hC hBound
 have qa : integral volume (fun t:ℝ => H t *
   tsum (fun p : Vc =>
    1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p) +
     1/Y5 p)) =
   tsum (fun p : Vc => integral volume (fun t:ℝ =>
    H t*(1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p) +
     1/Y5 p))):=by
  rw [qd]
  apply integral_congr_ae
  filter_upwards with t
  rw [tsum_mul_left]
 change (((1/(2*Real.pi):ℝ):ℂ)) *
  integral volume (fun t:ℝ => H t *
   tsum (fun p : Vc =>
    1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p) +
     1/Y5 p))=_
 rw [qa,<- tsum_mul_left]
 apply tsum_congr
 intro p
 have hRe:=zq hRH p
 simpa [H] using! wZ qc hx
  (by norm_num : (0:ℝ) < 3/2) qe (Zj p)
  (by rw [hRe]; norm_num : (Y5 p).re < (3/2:ℝ))
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
theorem wA {s:ℂ} (hs : 1 < s.re) : (1/2:ℂ)*Complex.digamma (s/2+1) = -(Real.eulerMascheroniConstant:ℂ)/2+tsum (fun k : Nat => 1/(2*((k:ℂ)+1)) - 1/(s+2*((k:ℂ)+1))):=by
 have qc : forall k : Nat,Not (s/2+1 = -(k:ℂ)):=by
  intro k h
  have hRe:=congrArg Complex.re h
  simp at hRe
  have hk : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 rw [Complex.WX qc,mul_add]
 have qa : (1/2:ℂ) * -(Real.eulerMascheroniConstant:ℂ) =
   -(Real.eulerMascheroniConstant:ℂ)/2:=by ring
 rw [qa,<- tsum_mul_left]
 congr 1
 apply tsum_congr
 intro k
 have hk : Not ((k:ℂ)+1=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.zero_re] at hRe
  have qb : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 have qd : Not (s+2*((k:ℂ)+1)=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  simp at hRe
  have qb : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 rw [show (k:ℂ)+(s/2+1) =
  (s+2*((k:ℂ)+1))/2 by ring]
 field_simp [hk,qd]
theorem Zn {s rho z:ℂ} (hs : Not (s=0)) (qc : Not (rho=0)) (qd : Not (s - rho=0)) {C:ℝ} (hC : 0 <= C) (hz : norm z <= C*(Inv.inv (norm s))^(2 : Nat)) : norm (z*(1/(s - rho)+1/rho)) <= 2*C*(Inv.inv (norm rho))^(3/2:ℝ)*((Inv.inv (norm s))^(3/2:ℝ)+(Inv.inv (norm (s - rho)))^(3/2:ℝ)):=by
  have hR : 0 < norm rho:=norm_pos_iff.mpr qc
  have ha : 0 < norm s:=norm_pos_iff.mpr hs
  have hb : 0 < norm (s - rho):=norm_pos_iff.mpr qd
  have qa : norm rho <= norm s+norm (s - rho):=by
    calc
      norm rho=norm (s - (s - rho)):=by congr 1; ring
      _ <= norm s+norm (s - rho):=norm_sub_le _ _
  have qb : 1/(s - rho)+1/rho=s/(rho*(s - rho)):=by
    field_simp [qc,qd] <;> ring
  rw [norm_mul,qb,norm_div,norm_mul]
  calc
    norm z*(norm s/(norm rho*norm (s - rho))) <=
        (C*(Inv.inv (norm s))^(2 : Nat)) *
          (norm s/(norm rho*norm (s - rho))) :=
      mul_le_mul_of_nonneg_right hz (by positivity)
    _ = C*(1/(norm rho*norm s*norm (s - rho))):=by
      field_simp
    _ <= C*(2*(Inv.inv (norm rho))^(3/2:ℝ) *
        ((Inv.inv (norm s))^(3/2:ℝ) +
          (Inv.inv (norm (s - rho)))^(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (w7 hR ha hb qa) hC
    _ = _ := by ring
theorem VU {C:ℝ} (hC : 0 <= C) {z:ℂ} {t:ℝ} (k : Nat) (hz : norm z <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : norm (z*(1/(2*((k:ℂ)+1)) - 1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1)))) <= 4*C*(Inv.inv ((k:ℝ)+1))^(3/2:ℝ)*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ):=by
  let s : ℂ:=(3/2:ℂ)+(t:ℂ)*Complex.I
  let u : ℝ:=2*((k:ℝ)+1)
  let rho:ℂ := -(u:ℂ)
  have hk : 0 < (k:ℝ)+1:=by positivity
  have hu : 0 < u:=by dsimp [u]; positivity
  have qi : (u:ℂ)=2*((k:ℂ)+1):=by
    dsimp [u]
    push_cast
    ring
  have qr : s.re=(3/2:ℝ):=by simp [s]
  have qj : rho.re = -u:=by simp [rho]
  have qk : Not (s=0):=by
    intro h
    rw [h] at qr
    norm_num at qr
  have qa : Not (rho=0):=by
    intro h
    rw [h] at qj
    simp at qj
    linarith
  have qb : Not (s - rho=0):=by
    intro h
    have qn:=congrArg Complex.re h
    simp only [Complex.sub_re,qr,qj,Complex.zero_re] at qn
    linarith
  have ql : 0 < norm s:=norm_pos_iff.mpr qk
  have qc : norm rho=u:=by
    simp [rho,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
  have qg : norm s <= norm (s - rho):=by
    have qh : norm s^(2 : Nat) <= norm (s - rho)^(2 : Nat):=by
      rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
      simp only [Complex.sub_re,Complex.sub_im,qr,qj]
      have qm : rho.im=0:=by simp [rho]
      rw [qm]
      nlinarith
    nlinarith [norm_nonneg s,norm_nonneg (s - rho)]
  have qo : Inv.inv (norm (s - rho)) <= Inv.inv (norm s):=by
    simpa only [one_div] using one_div_le_one_div_of_le ql qg
  have qd : (Inv.inv (norm (s - rho)))^(3/2:ℝ) <=
      (Inv.inv (norm s))^(3/2:ℝ) :=
    Real.rpow_le_rpow (by positivity) qo (by norm_num)
  have qp : Inv.inv u <= Inv.inv ((k:ℝ)+1):=by
    have hku : (k:ℝ)+1 <= u:=by dsimp [u]; linarith
    simpa only [one_div] using one_div_le_one_div_of_le hk hku
  have qe : (Inv.inv u)^(3/2:ℝ) <=
      (Inv.inv ((k:ℝ)+1))^(3/2:ℝ) :=
    Real.rpow_le_rpow (by positivity) qp (by norm_num)
  have qq : z*(1/(u:ℂ) - 1/(s+(u:ℂ))) =
      -(z*(1/(s - rho)+1/rho)):=by
    dsimp [rho]
    simp only [sub_neg_eq_add,div_neg]
    ring
  rw [<- qi]
  change norm (z*(1/(u:ℂ) - 1/(s+(u:ℂ)))) <= _
  rw [qq,norm_neg]
  have qf:=Zn qk qa qb hC hz
  rw [qc] at qf
  apply qf.trans
  calc
    2*C*(Inv.inv u)^(3/2:ℝ) *
        ((Inv.inv (norm s))^(3/2:ℝ) +
          (Inv.inv (norm (s - rho)))^(3/2:ℝ)) <=
      2*C*(Inv.inv ((k:ℝ)+1))^(3/2:ℝ) *
        ((Inv.inv (norm s))^(3/2:ℝ) +
          (Inv.inv (norm s))^(3/2:ℝ)):=by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left qe (by positivity))
        (add_le_add le_rfl qd) (by positivity) (by positivity)
    _ = _ := by ring
theorem V9 {H:ℝ -> ℂ} (hH : Integrable H) (k : Nat) : Integrable (fun t:ℝ => H t*(1/(2*((k:ℂ)+1)) - 1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1)))):=by
 have qa : (-(2*((k:ℂ)+1))).re < (3/2:ℝ):=by
  simp
  have hk : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 have hR : Integrable (fun t:ℝ =>
   H t/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1))):=by
  simpa using! Yl hH (c:=(3/2:ℝ)) qa
 apply ((hH.div_const (2*((k:ℂ)+1))).sub hR).congr
 filter_upwards with t
 simp only [Pi.sub_apply]
 ring
theorem w2 {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C) (qa : forall t:ℝ,norm (H t) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : Summable (fun k : Nat => integral volume (fun t:ℝ => norm (H t*(1/(2*((k:ℂ)+1)) - 1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1)))))):=by
  let K:ℝ -> ℝ:=fun t =>
    (Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(3/2:ℝ)
  let W : Nat -> ℝ:=fun k => (Inv.inv ((k:ℝ)+1))^(3/2:ℝ)
  let F : Nat -> ℝ -> ℂ:=fun k t => H t *
    (1/(2*((k:ℂ)+1)) -
      1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1)))
  have hK : Integrable K:=by
    simpa [K] using! wn (by norm_num : (1:ℝ) <= 3/2)
  have hW : Summable W:=by
    have h:=(Real.summable_one_div_nat_add_rpow 1 (3/2)).mpr (by norm_num)
    apply h.congr
    intro k
    dsimp [W]
    rw [abs_of_pos (by positivity : (0:ℝ) < k+1),one_div,
      Real.inv_rpow (by positivity)]
  have qb : forall k : Nat,integral volume (fun t:ℝ => norm (F k t)) <=
      (4*C*integral volume K)*W k:=by
    intro k
    have hF : Integrable (F k):=V9 hH k
    have hM : Integrable (fun t:ℝ => 4*C*W k*K t):=hK.const_mul _
    calc
      integral volume (fun t:ℝ => norm (F k t)) <=
          integral volume (fun t:ℝ => 4*C*W k*K t):=by
        apply integral_mono_ae hF.norm hM
        filter_upwards with t
        exact VU hC k (qa t)
      _ = _ := by rw [integral_const_mul]; ring
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun t => norm_nonneg (F k t))) qb (hW.mul_left _)
theorem Va
  {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C)
  (qa : forall t:ℝ,norm (H t) <=
   C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) :
  tsum (fun k : Nat => integral volume (fun t:ℝ => H t *
    (1/(2*((k:ℂ)+1)) -
     1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1))))) =
   integral volume (fun t:ℝ => tsum (fun k : Nat => H t *
    (1/(2*((k:ℂ)+1)) -
     1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1))))) :=
 integral_tsum_of_summable_integral_norm (V9 hH)
  (w2 hH hC qa)
theorem yV {Iota : Type*} [Countable Iota] {mu : Measure ℝ} {F : Iota -> ℝ -> ℂ} (hF : forall i : Iota,Integrable (F i) mu) (qb : Summable (fun i : Iota => integral mu (fun t:ℝ => norm (F i t)))) : Integrable (fun t:ℝ => tsum (fun i : Iota => F i t)) mu:=by
  have qa : AEStronglyMeasurable (fun t:ℝ => tsum (fun i : Iota => F i t)) mu :=
    (AEMeasurable.tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  refine And.intro qa ?_
  rw [hasFiniteIntegral_iff_enorm]
  calc
    lintegral mu (fun t:ℝ => enorm (tsum (fun i : Iota => F i t))) <=
        lintegral mu (fun t:ℝ => tsum (fun i : Iota => enorm (F i t))) :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = tsum (fun i : Iota => lintegral mu (fun t:ℝ => enorm (F i t))) :=
      lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)
    _ = tsum (fun i : Iota => ENNReal.ofReal (integral mu (fun t:ℝ => norm (F i t)))):=by
      apply tsum_congr
      intro i
      exact (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    _ < Top.top:=qb.tsum_ofReal_lt_top
theorem wd {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) {c:ℝ} (qc : 0 < c) (qe : c < n) (k : Nat) : (((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I)*(1/(2*((k:ℂ)+1)) - 1/((c:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1))))=WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1)):=by
 let rho:ℂ := -(2*((k:ℂ)+1))
 have qb : Not (rho=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  simp [rho] at hRe
  have hk : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 have qf : rho.re < c:=by
  simp [rho]
  have hk : 0 <= (k:ℝ):=Nat.cast_nonneg k
  linarith
 have qd:=wZ hn hx qc qe qb qf
 have qa : (fun t:ℝ =>
   mellin (V8 n x) ((c:ℂ)+(t:ℂ)*Complex.I) *
    (1/(2*((k:ℂ)+1)) -
     1/((c:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1)))) =
   (fun t:ℝ => -(mellin (V8 n x)
    ((c:ℂ)+(t:ℂ)*Complex.I) *
     (1/((c:ℂ)+(t:ℂ)*Complex.I - rho)+1/rho))):=by
  funext t
  dsimp [rho]
  simp only [sub_neg_eq_add,div_neg]
  ring
 rw [qa,integral_neg,mul_neg,qd]
 simp only [rho,div_neg,neg_neg]
theorem Yb {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C) (qa : forall t:ℝ,norm (H t) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : Integrable (fun t:ℝ => H t*((1/2:ℂ)*Complex.digamma (((3/2:ℂ)+(t:ℂ)*Complex.I)/2+1)+(Real.eulerMascheroniConstant:ℂ)/2)):=by
 have qb:=yV
  (V9 hH) (w2 hH hC qa)
 apply qb.congr
 filter_upwards with t
 rw [tsum_mul_left,wA (by simp; norm_num)]
 ring
theorem vo {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : (((1/(2*Real.pi):ℝ):ℂ))*integral volume (fun t:ℝ => mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)*((1/2:ℂ)*Complex.digamma (((3/2:ℂ)+(t:ℂ)*Complex.I)/2+1)+(Real.eulerMascheroniConstant:ℂ)/2))=tsum (fun k : Nat => WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))):=by
 choose C hC hBound using yP hn hx
 have qc : 1 <= n:=by omega
 have qb : (2:ℝ) <= n:=by exact_mod_cast hn
 have qe : (3/2:ℝ) < n:=by linarith
 let H:ℝ -> ℂ:=fun t =>
  mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)
 have hH : Integrable H:=by
  simpa [H,Complex.VerticalIntegrable] using! yb
   qc hx (by norm_num : (0:ℝ) < 3/2) qe
 have qd:=Va hH hC hBound
 have qa : integral volume (fun t:ℝ => H t *
   ((1/2:ℂ)*Complex.digamma
    (((3/2:ℂ)+(t:ℂ)*Complex.I)/2+1) +
     (Real.eulerMascheroniConstant:ℂ)/2)) =
   tsum (fun k : Nat => integral volume (fun t:ℝ => H t *
    (1/(2*((k:ℂ)+1)) -
     1/((3/2:ℂ)+(t:ℂ)*Complex.I+2*((k:ℂ)+1))))):=by
  rw [qd]
  apply integral_congr_ae
  filter_upwards with t
  rw [tsum_mul_left,wA (by simp; norm_num)]
  ring
 change (((1/(2*Real.pi):ℝ):ℂ)) *
  integral volume (fun t:ℝ => H t *
   ((1/2:ℂ)*Complex.digamma
    (((3/2:ℂ)+(t:ℂ)*Complex.I)/2+1) +
     (Real.eulerMascheroniConstant:ℂ)/2))=_
 rw [qa,<- tsum_mul_left]
 apply tsum_congr
 intro k
 simpa [H] using! wd qc hx
  (by norm_num : (0:ℝ) < 3/2) qe k
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
theorem yc (s:ℂ) (hs1 : s ≠ 1) (hΓdiff : ∀ m:ℕ,s/2+1 ≠ -m) (hΓ : WS s ≠ 0) (hζ : riemannZeta s ≠ 0) : -deriv riemannZeta s/riemannZeta s = -logDeriv Wp s+1/(s - 1) - (1/2:ℂ)*Real.log Real.pi+(1/2:ℂ)*digamma (s/2+1):=by
 rw [Yq s hs1 hΓdiff hΓ hζ]
 ring
theorem zO (s B Z:ℂ) (hs1 : s ≠ 1) (hΓdiff : ∀ m:ℕ,s/2+1 ≠ -m) (hΓ : WS s ≠ 0) (hζ : riemannZeta s ≠ 0) (qa : logDeriv Wp s=B+Z) : -deriv riemannZeta s/riemannZeta s = -B - Z+1/(s - 1) - (1/2:ℂ)*Real.log Real.pi+(1/2:ℂ)*digamma (s/2+1):=by
 rw [yc s hs1 hΓdiff hΓ hζ,qa]
 ring
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
theorem yv {s:ℂ} (hs : 1 < s.re) : Kadiri.Wp s=uj s:=by
  have qe : Not (s=0):=by
    intro h
    have hRe:=congrArg Complex.re h
    norm_num at hRe
    linarith
  have qf : Not (s=1):=by
    intro h
    have hRe:=congrArg Complex.re h
    norm_num at hRe
    linarith
  have qd : 0 < (s/2).re:=by
    simp
    linarith
  have qb : Not (Gamma (s/2)=0) :=
    Complex.Gamma_ne_zero_of_re_pos qd
  have qa :
      Gamma (s/2+1)=(s/2)*Gamma (s/2) :=
    Gamma_add_one (s/2) (div_ne_zero qe two_ne_zero)
  have qc :=
    zx
      qe qb
  calc
    Kadiri.Wp s =
        (s*(s - 1)/2) *
          ((Real.pi:ℂ)^(-s/2) *
            Gamma (s/2)*riemannZeta s):=by
      rw [Kadiri.Wp,Kadiri.WZ,
        Kadiri.WS,YZ,
        qa]
      rw [show (-(s/2)) = -s/2 by ring]
      ring
    _ = (s*(s - 1)/2)*completedRiemannZeta s:=by
      rw [qc]
    _ = uj s:=by
      rw [v2 qe qf]
      ring
theorem zz {s:ℂ} (hs : 1 < s.re) : logDeriv Kadiri.Wp s=logDeriv uj s:=by
 have qa :
   Filter.EventuallyEq (nhds s)
    Kadiri.Wp uj:=by
  filter_upwards [
   (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
   with w hw
  exact yv hw
 exact (logDeriv_congr_nhds qa).self_of_nhds
theorem yU {s:ℂ} (hs : 1 < s.re) : -deriv riemannZeta s/riemannZeta s = -logDeriv uj 0 - tsum (fun p : Vc => 1/(s - Y5 p)+1/Y5 p)+1/(s - 1) - (1/2:ℂ)*Real.log Real.pi+(1/2:ℂ)*digamma (s/2+1):=by
 have qg : Not (s=0):=by
  intro h
  have hRe:=congrArg Complex.re h
  norm_num at hRe
  linarith
 have qj : Not (s=1):=by
  intro h
  have hRe:=congrArg Complex.re h
  norm_num at hRe
  linarith
 have qk : Not (riemannZeta s=0) :=
  riemannZeta_ne_zero_of_one_lt_re hs
 have qb :
   forall m : Nat,Not (s/2+1 = -(m:ℂ)):=by
  intro m h
  have hRe:=congrArg Complex.re h
  simp at hRe
  have qf : (0:ℝ) <= m:=by
   exact_mod_cast Nat.zero_le m
  linarith
 have qh : Not (Kadiri.WS s=0):=by
  unfold Kadiri.WS
  exact Gamma_ne_zero qb
 have qc :
   forall p : Vc,
    Not (s=Y5 p):=by
  intro p hEqual
  have hXi : uj s=0:=by
   rw [hEqual]
   exact Za p
  have qd : riemannZeta s=0 :=
   vi qg qj hXi
  exact qk qd
 choose P hP using yA
 have qi :=
  zH
   (P:=P) (z:=s) hP.2 qc
 have qa :
   Polynomial.eval s P.derivative=logDeriv uj 0 :=
  zi
   hP.1 hP.2 s
 have qe :
   logDeriv Kadiri.Wp s =
    logDeriv uj 0 +
     tsum (fun p : Vc =>
      1/(s - Y5 p) +
       1/Y5 p):=by
  rw [zz hs,
   qi,qa]
 exact Kadiri.zO
  s (logDeriv uj 0)
   (tsum (fun p : Vc =>
    1/(s - Y5 p) +
     1/Y5 p))
  qj qb qh qk qe
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
theorem ZG : -logDeriv uj 0 - (1/2:ℂ)*(Real.log Real.pi:ℂ) - (Real.eulerMascheroniConstant:ℂ)/2 - 1 = -(Real.log (2*Real.pi):ℂ):=by
 have qb : Real.log (4*Real.pi)+Real.log Real.pi =
   2*Real.log (2*Real.pi):=by
  rw [Real.log_mul (by norm_num : Not ((4:ℝ)=0)) Real.pi_ne_zero,
   Real.log_mul (by norm_num : Not ((2:ℝ)=0)) Real.pi_ne_zero]
  have qc : Real.log (4:ℝ)=Real.log 2+Real.log 2:=by
   rw [show (4:ℝ)=2*2 by norm_num,
    Real.log_mul (by norm_num : Not ((2:ℝ)=0)) (by norm_num : Not ((2:ℝ)=0))]
  rw [qc]
  ring
 have qa:=congrArg Complex.ofReal qb
 push_cast at qa
 have hXi:=vP
 linear_combination (1/2:ℂ)*hXi - (1/2:ℂ)*qa
theorem Zc : Countable Vc:=by
 have qa : Function.support (fun p : Vc =>
   (Inv.inv (norm (Y5 p)))^(2 : Nat))=Set.univ:=by
  ext p
  simp only [Function.mem_support,mem_univ,iff_true]
  exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
   (Zj p)))
 have qb:=va.countable_support
 rw [qa] at qb
 exact Set.countable_univ_iff.mp qb
theorem YH (hRH : RiemannHypothesis) {H:ℝ -> ℂ} (hH : Integrable H) {C:ℝ} (hC : 0 <= C) (qa : forall t:ℝ,norm (H t) <= C*(Inv.inv (norm ((3/2:ℂ)+(t:ℂ)*Complex.I)))^(2 : Nat)) : Integrable (fun t:ℝ => H t*tsum (fun p : Vc => 1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p)+1/Y5 p)):=by
 letI:=Zc
 have qb:=yV
  (fun p => Y7 hH
   (zq hRH p))
  (vG hRH hH hC qa)
 apply qb.congr
 filter_upwards with t
 rw [tsum_mul_left]
theorem ym (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ))=WT n 1 x - tsum (fun p : Vc => WT n (Y5 p) x/Y5 p) - (Real.log (2*Real.pi):ℂ)*V8 n x 1+tsum (fun k : Nat => WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))):=by
  choose C hC hBound using yP hn hx
  have qj : 1 <= n:=by omega
  have qe : (2:ℝ) <= n:=by exact_mod_cast hn
  have qk : (0:ℝ) < 3/2:=by norm_num
  have hc : (1:ℝ) < 3/2:=by norm_num
  have qm : (3/2:ℝ) < n:=by linarith
  let K : ℂ:=(((1/(2*Real.pi):ℝ):ℂ))
  let H:ℝ -> ℂ:=fun t =>
    mellin (V8 n x) ((3/2:ℂ)+(t:ℂ)*Complex.I)
  let C0:ℂ := -logDeriv uj 0 -
    (1/2:ℂ)*(Real.log Real.pi:ℂ) -
      (Real.eulerMascheroniConstant:ℂ)/2
  let Z:ℝ -> ℂ:=fun t => H t *
    tsum (fun p : Vc =>
      1/((3/2:ℂ)+(t:ℂ)*Complex.I - Y5 p) +
        1/Y5 p)
  let B:ℝ -> ℂ:=fun t =>
    H t/((3/2:ℂ)+(t:ℂ)*Complex.I - 1)
  let G:ℝ -> ℂ:=fun t => H t *
    ((1/2:ℂ)*Complex.digamma
      (((3/2:ℂ)+(t:ℂ)*Complex.I)/2+1) +
        (Real.eulerMascheroniConstant:ℂ)/2)
  have hH : Integrable H:=by
    simpa [H,Complex.VerticalIntegrable] using! yb
      qj hx qk qm
  have hZ : Integrable Z:=YH hRH hH hC hBound
  have hB : Integrable B:=by
    simpa [B] using! Yl hH
      (c:=(3/2:ℝ)) (rho:=1) (by norm_num)
  have hG : Integrable G:=Yb hH hC hBound
  have qf : Integrable (fun t:ℝ => C0*H t):=hH.const_mul C0
  have qd : forall t:ℝ,
      (-deriv riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I) /
        riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I))*H t =
        C0*H t - Z t+B t+G t:=by
    intro t
    rw [yU (by simp; norm_num)]
    dsimp only [C0,Z,B,G]
    ring
  have qa : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ) *
      V8 n x (m:ℝ)) =
      K*integral volume (fun t:ℝ =>
        (-deriv riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I) /
          riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I))*H t):=by
    simpa [K,H] using! vM qj hx hc qm
  have qb : integral volume (fun t:ℝ =>
      (-deriv riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I) /
        riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I))*H t) =
      C0*integral volume H - integral volume Z+integral volume B+integral volume G:=by
    calc
      integral volume (fun t:ℝ =>
          (-deriv riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I) /
            riemannZeta ((3/2:ℂ)+(t:ℂ)*Complex.I))*H t) =
          integral volume (fun t:ℝ => C0*H t - Z t+B t+G t) :=
        integral_congr_ae (Filter.Eventually.of_forall qd)
      _ = _ := by
        have qn:=integral_add ((qf.sub hZ).add hB) hG
        have qo:=integral_add (qf.sub hZ) hB
        have qp:=integral_sub qf hZ
        simp only [Pi.add_apply,Pi.sub_apply] at qn qo qp
        rw [qn,qo,qp,integral_const_mul]
  have qg : K*integral volume H=V8 n x 1:=by
    have h:=vH qj hx qk qm Real.zero_lt_one
    simpa [mellinInv,RCLike.real_smul_eq_coe_mul,smul_eq_mul,H,K] using! h
  have qh : K*integral volume Z =
      tsum (fun p : Vc =>
        WT n (Y5 p) x/Y5 p):=by
    simpa [K,Z,H] using! vs hRH hn hx
  have qi : K*integral volume G =
      tsum (fun k : Nat =>
        WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))):=by
    simpa [K,G,H] using! vo hn hx
  have ql : K*integral volume B=WT n 1 x - V8 n x 1:=by
    have h:=wD qj hx qk qm
      (rho:=1) (by norm_num)
    rw [wr hx (by norm_num : Not ((1:ℂ)=0))
      (by simp; linarith : (1:ℂ).re < (n:ℝ))] at h
    simpa [K,B,H] using! h
  have hC0 : C0 - 1 = -(Real.log (2*Real.pi):ℂ):=ZG
  rw [qa,qb]
  have qc : K*(C0*integral volume H - integral volume Z +
      integral volume B+integral volume G) =
      C0*(K*integral volume H) - K*integral volume Z +
        K*integral volume B+K*integral volume G:=by ring
  rw [qc,qg,qh,ql,qi]
  linear_combination V8 n x 1*hC0
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
theorem Ya (n : Nat) {x y:ℝ} (hx : 1 < x) (hy : 0 < y) : norm (V8 n x y) <= Inv.inv (Real.log x)*y^(-(n:ℝ)):=by
  have qa : forall r:ℝ,1 < r ->
      norm ((r:ℂ)^(-(n:ℂ)) *
        (((Inv.inv (Real.log r):ℝ):ℂ))) =
      r^(-(n:ℝ))*Inv.inv (Real.log r):=by
    intro r hr
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one hr),
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.log_pos hr))]
    simp
  by_cases hxy : y <= x
  . simp only [V8,if_pos hxy]
    rw [qa x hx]
    have qc : x^(-(n:ℝ)) <= y^(-(n:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hy hxy (neg_nonpos.mpr (Nat.cast_nonneg n))
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right qc (inv_nonneg.mpr (Real.log_pos hx).le)
  . have qb : 1 < y:=lt_trans hx (lt_of_not_ge hxy)
    simp only [V8,if_neg hxy]
    rw [qa y qb]
    have qd : Real.log x <= Real.log y :=
      (Real.log_le_log_iff (lt_trans Real.zero_lt_one hx) hy).mpr (le_of_not_ge hxy)
    have qe : Inv.inv (Real.log y) <= Inv.inv (Real.log x):=by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.log_pos hx) qd
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left qe (Real.rpow_nonneg hy.le _)
theorem Z3 {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : Summable (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ)):=by
  have qa : (2:ℝ) <= n:=by exact_mod_cast hn
  have qd : 1 < (n:ℂ).re:=by simp; linarith
  have qb:=(ZV qd).norm.mul_left (Inv.inv (Real.log x))
  apply qb.of_norm_bounded
  intro m
  by_cases hm : m=0
  . simp [hm]
  . have qc : 0 < (m:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [norm_mul]
    calc
      norm (ArithmeticFunction.vonMangoldt m:ℂ)*norm (V8 n x m) <=
          norm (ArithmeticFunction.vonMangoldt m:ℂ) *
            (Inv.inv (Real.log x)*(m:ℝ)^(-(n:ℝ))) :=
        mul_le_mul_of_nonneg_left (Ya n hx qc) (norm_nonneg _)
      _ = Inv.inv (Real.log x) *
          norm ((ArithmeticFunction.vonMangoldt m:ℂ)/(m:ℂ)^(n:ℂ)):=by
        rw [norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
        simp only [Complex.natCast_re]
        rw [Real.rpow_neg qc.le]
        ring
def Vg (n m : Nat) (t:ℝ):ℝ :=
 (Ici (m:ℝ)).indicator
  (fun u:ℝ => ArithmeticFunction.vonMangoldt m*robinRealWeight n u) t
theorem ZZ {n m : Nat} {t:ℝ} (ht : 1 < t) : 0 <= Vg n m t:=by
  unfold Vg
  by_cases hm : (m:ℝ) <= t
  . rw [Set.indicator_of_mem (s:=Ici (m:ℝ)) hm]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (VW ht)
  . rw [Set.indicator_of_notMem (s:=Ici (m:ℝ)) hm]
theorem v7 {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) (m : Nat) : IntegrableOn (Vg n m) (Ioi x):=by
 exact ((Ys hn hx).const_mul (ArithmeticFunction.vonMangoldt m)).indicator
  measurableSet_Ici
theorem Zv {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : ((integral (volume.restrict (Ioi x)) (robinRealWeight n):ℝ):ℂ)=(x:ℂ)^(-(n:ℂ))*(((Inv.inv (Real.log x):ℝ):ℂ)):=by
 rw [Vs hn hx,Complex.ofReal_mul,
  Complex.ofReal_cpow (lt_trans Real.zero_lt_one hx).le]
 simp
theorem Zr {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) (m : Nat) : integral (volume.restrict (Ioi x)) (fun t:ℝ => (Vg n m t:ℂ))=(ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ):=by
  rw [integral_complex_ofReal]
  by_cases hm : (m:ℝ) <= x
  . have qa : integral (volume.restrict (Ioi x)) (Vg n m) =
        ArithmeticFunction.vonMangoldt m *
          integral (volume.restrict (Ioi x)) (robinRealWeight n):=by
      calc
        integral (volume.restrict (Ioi x)) (Vg n m) =
            integral (volume.restrict (Ioi x)) (fun t:ℝ =>
              ArithmeticFunction.vonMangoldt m*robinRealWeight n t):=by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact Set.indicator_of_mem (s:=Ici (m:ℝ)) (le_trans hm (le_of_lt ht)) _
        _ = _ := integral_const_mul _ _
    rw [qa,Complex.ofReal_mul,Zv hn hx]
    simp only [V8,if_pos hm]
  . have qc : x < (m:ℝ):=lt_of_not_ge hm
    have qb : 1 < (m:ℝ):=lt_trans hx qc
    have qd : Set.inter (Ioi x) (Ici (m:ℝ))=Ici (m:ℝ):=by
      apply inter_eq_right.mpr
      intro t ht
      exact lt_of_lt_of_le qc ht
    have qa : integral (volume.restrict (Ioi x)) (Vg n m) =
        ArithmeticFunction.vonMangoldt m *
          integral (volume.restrict (Ioi (m:ℝ))) (robinRealWeight n):=by
      unfold Vg
      rw [setIntegral_indicator measurableSet_Ici]
      change integral (volume.restrict (Set.inter (Ioi x) (Ici (m:ℝ))))
        (fun t:ℝ => ArithmeticFunction.vonMangoldt m*robinRealWeight n t)=_
      rw [qd,integral_Ici_eq_integral_Ioi,integral_const_mul]
    rw [qa,Complex.ofReal_mul,Zv hn qb]
    simp only [V8,if_neg hm]
theorem z4 {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : Summable (fun m : Nat => integral (volume.restrict (Ioi x)) (fun t:ℝ => norm (Vg n m t:ℂ))):=by
  have qc : 1 <= n:=by omega
  have qb:=(Z3 hn hx).norm
  apply Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun t => norm_nonneg (Vg n m t:ℂ)))
    (fun m => ?_) qb
  have qd:=v7 qc hx m
  have qa : IntegrableOn
      (fun t:ℝ => (Vg n m t:ℂ)) (Ioi x):=qd.ofReal
  calc
    integral (volume.restrict (Ioi x)) (fun t:ℝ => norm (Vg n m t:ℂ)) =
        integral (volume.restrict (Ioi x)) (Vg n m):=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (ZZ (lt_trans hx ht))]
    _ = (integral (volume.restrict (Ioi x))
        (fun t:ℝ => (Vg n m t:ℂ))).re:=by
      rw [integral_complex_ofReal,Complex.ofReal_re]
    _ = ((ArithmeticFunction.vonMangoldt m:ℂ) *
        V8 n x (m:ℝ)).re:=by
      rw [Zr qc hx]
    _ <= norm ((ArithmeticFunction.vonMangoldt m:ℂ) *
        V8 n x (m:ℝ)) :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
theorem Z6 (n : Nat) {t:ℝ} (ht : 0 <= t) : tsum (fun m : Nat => (Vg n m t:ℂ))=(Chebyshev.psi t:ℂ)*(robinRealWeight n t:ℂ):=by
  have qa : forall m : Nat,Not (Membership.mem (Finset.Icc 0 (Nat.floor t)) m) ->
      (Vg n m t:ℂ)=0:=by
    intro m hm
    have qb : Not (m <= Nat.floor t):=by
      intro hmLe
      exact hm (Finset.mem_Icc.mpr (And.intro (Nat.zero_le m) hmLe))
    have hmT : Not ((m:ℝ) <= t):=by
      intro hmLe
      exact qb ((Nat.le_floor_iff ht).mpr hmLe)
    simp only [Vg,
      Set.indicator_of_notMem (s:=Ici (m:ℝ)) hmT,Complex.ofReal_zero]
  rw [tsum_eq_sum qa]
  calc
    Finset.sum (Finset.Icc 0 (Nat.floor t)) (fun m : Nat =>
        (Vg n m t:ℂ)) =
      Finset.sum (Finset.Icc 0 (Nat.floor t)) (fun m : Nat =>
        (ArithmeticFunction.vonMangoldt m:ℂ)*(robinRealWeight n t:ℂ)):=by
      apply Finset.sum_congr rfl
      intro m hm
      have hmT : (m:ℝ) <= t:=(Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hm).2
      simp only [Vg,
        Set.indicator_of_mem (s:=Ici (m:ℝ)) hmT,Complex.ofReal_mul]
    _ = _ := by
      rw [<- Finset.sum_mul,Chebyshev.psi_eq_sum_Icc]
      push_cast
      rfl
theorem y5 {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ)*V8 n x (m:ℝ))=integral (volume.restrict (Ioi x)) (fun t:ℝ => ((Chebyshev.psi t*robinRealWeight n t:ℝ):ℂ)):=by
  have qa : 1 <= n:=by omega
  have hF : forall m : Nat,IntegrableOn
      (fun t:ℝ => (Vg n m t:ℂ)) (Ioi x):=by
    intro m
    exact (v7 qa hx m).ofReal
  calc
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m:ℂ) *
        V8 n x (m:ℝ)) =
      tsum (fun m : Nat => integral (volume.restrict (Ioi x))
        (fun t:ℝ => (Vg n m t:ℂ))):=by
      apply tsum_congr
      intro m
      exact (Zr qa hx m).symm
    _ = integral (volume.restrict (Ioi x)) (fun t:ℝ =>
        tsum (fun m : Nat => (Vg n m t:ℂ))) :=
      integral_tsum_of_summable_integral_norm hF (z4 hn hx)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Z6 n (lt_trans (lt_trans Real.zero_lt_one hx) ht).le,
        Complex.ofReal_mul]
theorem vj {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : IntegrableOn (fun t:ℝ => ((Chebyshev.psi t*robinRealWeight n t:ℝ):ℂ)) (Ioi x):=by
 have qa : 1 <= n:=by omega
 have hF : forall m : Nat,IntegrableOn
   (fun t:ℝ => (Vg n m t:ℂ)) (Ioi x):=by
  intro m
  exact (v7 qa hx m).ofReal
 have qb : IntegrableOn (fun t:ℝ =>
   tsum (fun m : Nat => (Vg n m t:ℂ))) (Ioi x) :=
  yV hF (z4 hn hx)
 apply qb.congr_fun _ measurableSet_Ioi
 intro t ht
 dsimp only
 rw [Z6 n (lt_trans (lt_trans Real.zero_lt_one hx) ht).le,
  Complex.ofReal_mul]
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
def V0 (n k : Nat) (t:ℝ):ℝ :=
 robinRealWeight n t*(1/t^2)^(k+1)/(2*((k:ℝ)+1))
theorem Yx (n k : Nat) {t:ℝ} (ht : 2 <= t) : And (0 <= V0 n k t) (V0 n k t <= (1/4:ℝ)^(k+1)*robinRealWeight n t):=by
  have qb : 0 <= robinRealWeight n t:=VW (by linarith)
  have qc : (4:ℝ) <= t^2:=by nlinarith
  have qd : 1/t^2 <= (1/4:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) qc
  have qa : 0 <= 1/t^2:=by positivity
  have hk : 0 <= (k:ℝ):=Nat.cast_nonneg k
  have qf : 1 <= 2*((k:ℝ)+1):=by linarith
  have qe : (1/t^2)^(k+1) <= (1/4:ℝ)^(k+1):=by
    gcongr
  refine And.intro ?_ ?_
  . unfold V0
    positivity
  . have qg : (1/t^2)^(k+1)/(2*((k:ℝ)+1)) <= (1/t^2)^(k+1):=by
      have h:=div_le_div_of_nonneg_left (pow_nonneg qa (k+1))
        (by norm_num : (0:ℝ) < 1) qf
      simpa only [div_one] using h
    unfold V0
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left (qg.trans qe) qb).trans_eq (mul_comm _ _)
theorem wW {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) (k : Nat) : IntegrableOn (V0 n k) (Ioi x):=by
 have qb : 1 < x:=by linarith
 have qc : Measurable (V0 n k):=by
  unfold V0 robinRealWeight
  fun_prop
 apply ((Ys hn qb).const_mul ((1/4:ℝ)^(k+1))).mono'
  qc.aestronglyMeasurable
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
 have qa:=Yx n k (le_trans hx (le_of_lt ht))
 rw [Real.norm_eq_abs,abs_of_nonneg qa.1]
 exact qa.2
theorem yp {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) : Summable (fun k : Nat => integral (volume.restrict (Ioi x)) (fun t:ℝ => norm (V0 n k t:ℂ))):=by
  have qd : 1 < x:=by linarith
  have qa:=Ys hn qd
  have qe : Summable (fun k : Nat => (1/4:ℝ)^(k+1)):=by
    simpa only [pow_succ] using
      (summable_geometric_of_norm_lt_one (by norm_num : norm (1/4:ℝ) < 1)).mul_right (1/4)
  have qc : forall k : Nat,integral (volume.restrict (Ioi x))
      (fun t:ℝ => norm (V0 n k t:ℂ)) <=
      (1/4:ℝ)^(k+1)*integral (volume.restrict (Ioi x)) (robinRealWeight n):=by
    intro k
    have hF : IntegrableOn (fun t:ℝ => (V0 n k t:ℂ)) (Ioi x) :=
      (wW hn hx k).ofReal
    calc
      integral (volume.restrict (Ioi x)) (fun t:ℝ => norm (V0 n k t:ℂ)) <=
          integral (volume.restrict (Ioi x)) (fun t:ℝ =>
            (1/4:ℝ)^(k+1)*robinRealWeight n t):=by
        apply integral_mono_ae hF.norm (qa.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have qb:=Yx n k (le_trans hx (le_of_lt ht))
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg qb.1]
        exact qb.2
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun t => norm_nonneg (V0 n k t:ℂ)))
    qc (qe.mul_right _)
theorem YO (n : Nat) {t:ℝ} (ht : 2 <= t) : tsum (fun k : Nat => V0 n k t) = -(robinRealWeight n t/2)*Real.log (1 - 1/t^2):=by
 have qb : (4:ℝ) <= t^2:=by nlinarith
 have qc : 1/t^2 <= (1/4:ℝ) :=
  one_div_le_one_div_of_le (by norm_num) qb
 have qd : abs (1/t^2) < (1:ℝ):=by
  rw [abs_of_nonneg (by positivity : (0:ℝ) <= 1/t^2)]
  linarith
 have h:=(Real.hasSum_pow_div_log_of_abs_lt_one qd).mul_left (robinRealWeight n t/2)
 have qa : (fun k : Nat =>
   (robinRealWeight n t/2)*((1/t^2)^(k+1)/((k:ℝ)+1))) =
   (fun k : Nat => V0 n k t):=by
  funext k
  unfold V0
  field_simp [ne_of_gt (show 0 < t by linarith)] <;> ring
 rw [qa] at h
 rw [h.tsum_eq]
 ring
theorem yZ (n k : Nat) {t:ℝ} (ht : 1 < t) : ((t:ℂ)^(-(2*((k:ℂ)+1)) - (n:ℂ) - 1)*(((n:ℝ)*Real.log t+1)/(Real.log t)^2:ℝ))/(2*((k:ℂ)+1))=(V0 n k t:ℂ):=by
 have qc : 0 < t:=lt_trans Real.zero_lt_one ht
 have qb : t^(-(2*((k:ℝ)+1)) - (n:ℝ) - 1) =
   t^(-(n:ℝ) - 1)*(1/t^2)^(k+1):=by
  rw [show -(2*((k:ℝ)+1)) - (n:ℝ) - 1 =
    (-(n:ℝ) - 1)+(-2)*((k:ℝ)+1) by ring,
   Real.rpow_add qc,Real.rpow_mul qc.le]
  rw [show (k:ℝ)+1=((k+1 : Nat):ℝ) by simp,
   Real.rpow_natCast,Real.rpow_neg qc.le,Real.rpow_two]
  simp only [one_div]
 have qa : -(2*((k:ℂ)+1)) - (n:ℂ) - 1 =
   ((-(2*((k:ℝ)+1)) - (n:ℝ) - 1:ℝ):ℂ):=by
  push_cast
  ring
 rw [qa,<- Complex.ofReal_cpow qc.le,qb]
 unfold V0 robinRealWeight
 push_cast
 ring
theorem wN (n k : Nat) {x:ℝ} (hx : 1 < x) : WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))=integral (volume.restrict (Ioi x)) (fun t:ℝ => (V0 n k t:ℂ)):=by
 unfold WT
 rw [<- integral_div]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 dsimp only
 exact yZ n k (lt_trans hx ht)
theorem yq {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) : tsum (fun k : Nat => WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1)))=integral (volume.restrict (Ioi x)) (fun t:ℝ => ((-(robinRealWeight n t/2)*Real.log (1 - 1/t^2):ℝ):ℂ)):=by
  have qa : 1 < x:=by linarith
  have hF : forall k : Nat,IntegrableOn
      (fun t:ℝ => (V0 n k t:ℂ)) (Ioi x):=by
    intro k
    exact (wW hn hx k).ofReal
  calc
    tsum (fun k : Nat =>
        WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))) =
      tsum (fun k : Nat => integral (volume.restrict (Ioi x))
        (fun t:ℝ => (V0 n k t:ℂ))):=by
      apply tsum_congr
      intro k
      exact wN n k qa
    _ = integral (volume.restrict (Ioi x)) (fun t:ℝ =>
        tsum (fun k : Nat => (V0 n k t:ℂ))) :=
      integral_tsum_of_summable_integral_norm hF (yp hn hx)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [<- Complex.ofReal_tsum,YO n (le_trans hx (le_of_lt ht))]
theorem Yu {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 2 <= x) : -(Real.log (2*Real.pi):ℂ)*V8 n x 1+tsum (fun k : Nat => WT n (-(2*((k:ℂ)+1))) x/(2*((k:ℂ)+1))) = -(YU n x:ℂ):=by
 have qc : 1 < x:=by linarith
 have qb:=Ys hn qc
 have qd:=zY hn hx
 have qe : V8 n x 1 =
   ((integral (volume.restrict (Ioi x)) (robinRealWeight n):ℝ):ℂ):=by
  simp only [V8,if_pos qc.le]
  exact (Zv hn qc).symm
 have qa : (fun t:ℝ =>
   -(robinRealWeight n t/2)*Real.log (1 - 1/t^2)) =
   (fun t:ℝ => Real.log (2*Real.pi)*robinRealWeight n t -
    robinRealWeight n t*Zs t):=by
  funext t
  unfold Zs
  ring
 rw [yq hn hx,
  integral_complex_ofReal,qa]
 have qf:=integral_sub (qb.const_mul (Real.log (2*Real.pi))) qd
 rw [qf,integral_const_mul,qe]
 change -(Real.log (2*Real.pi):ℂ) *
   ((integral (volume.restrict (Ioi x)) (robinRealWeight n):ℝ):ℂ) +
   ((Real.log (2*Real.pi)*integral (volume.restrict (Ioi x)) (robinRealWeight n) -
    YU n x:ℝ):ℂ)=_
 push_cast
 ring
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open Complex MeasureTheory Set
def Yo (n : Nat) (x:ℝ):ℝ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ =>
  (Chebyshev.psi t - t)*robinRealWeight n t)
theorem Zw (n : Nat) {t:ℝ} (ht : 1 < t) : ((t*robinRealWeight n t:ℝ):ℂ)=(t:ℂ)^(-(n:ℂ))*(((n:ℝ)*Real.log t+1)/(Real.log t)^2:ℝ):=by
  have qb : 0 < t:=lt_trans Real.zero_lt_one ht
  have qa : t*t^(-(n:ℝ) - 1)=t^(-(n:ℝ)):=by
    calc
      t*t^(-(n:ℝ) - 1)=t^(1:ℝ)*t^(-(n:ℝ) - 1):=by rw [Real.rpow_one]
      _ = t^((1:ℝ)+(-(n:ℝ) - 1)):=(Real.rpow_add qb _ _).symm
      _ = _ := by congr 1; ring
  have qc : t*robinRealWeight n t =
      t^(-(n:ℝ))*(((n:ℝ)*Real.log t+1)/(Real.log t)^2):=by
    unfold robinRealWeight
    rw [<- mul_assoc,qa]
  rw [qc,Complex.ofReal_mul,Complex.ofReal_cpow qb.le]
  simp
theorem vp (n : Nat) {x:ℝ} (hx : 1 < x) : WT n 1 x=integral (volume.restrict (Ioi x)) (fun t:ℝ => ((t*robinRealWeight n t:ℝ):ℂ)):=by
 unfold WT
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 dsimp only
 rw [show (1:ℂ) - (n:ℂ) - 1 = -(n:ℂ) by ring]
 exact (Zw n (lt_trans hx ht)).symm
theorem vT {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : IntegrableOn (fun t:ℝ => ((t*robinRealWeight n t:ℝ):ℂ)) (Ioi x):=by
 have qa : (2:ℝ) <= n:=by exact_mod_cast hn
 have qb : (-(n:ℂ)).re < -1:=by simp; linarith
 have qc:=Yf hx qb 1
 have qd:=Yf hx qb 2
 have qe : IntegrableOn (fun t:ℝ =>
   (n:ℂ)*((t:ℂ)^(-(n:ℂ)) *
    (((Inv.inv ((Real.log t)^1):ℝ):ℂ))) +
   (t:ℂ)^(-(n:ℂ))*(((Inv.inv ((Real.log t)^2):ℝ):ℂ)))
   (Ioi x):=(qc.const_mul (n:ℂ)).add qd
 apply qe.congr_fun _ measurableSet_Ioi
 intro t ht
 dsimp only
 rw [Zw n (lt_trans hx ht)]
 simp only [pow_one]
 push_cast
 have qf : Not (((Real.log t:ℝ):ℂ)=0) :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (lt_trans hx ht)))
 field_simp [qf] <;> ring
theorem wY {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 1 < x) : IntegrableOn (fun t:ℝ => (Chebyshev.psi t - t)*robinRealWeight n t) (Ioi x):=by
 have qb:=vj hn hx
 have qa:=vT hn hx
 have qc:=(qb.sub qa).re
 have qd : IntegrableOn (fun t:ℝ =>
   (((Chebyshev.psi t*robinRealWeight n t:ℝ):ℂ) -
    ((t*robinRealWeight n t:ℝ):ℂ)).re) (Ioi x):=by
  simpa only [Pi.sub_apply,RCLike.re_to_complex] using! qc
 apply qd.congr_fun _ measurableSet_Ioi
 intro t ht
 dsimp only
 simp only [Complex.sub_re,Complex.ofReal_re]
 ring
theorem zF (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 2 <= x) : (Yo n x:ℂ) = -tsum (fun p : Vc => WT n (Y5 p) x/Y5 p) - (YU n x:ℂ):=by
 have qd : 1 < x:=by linarith
 have qe : 1 <= n:=by omega
 have qg:=vj hn qd
 have qf:=vT hn qd
 have qc : (Yo n x:ℂ) =
   integral (volume.restrict (Ioi x)) (fun t:ℝ =>
    ((Chebyshev.psi t*robinRealWeight n t:ℝ):ℂ)) -
   integral (volume.restrict (Ioi x)) (fun t:ℝ =>
    ((t*robinRealWeight n t:ℝ):ℂ)):=by
  rw [Yo,<- integral_complex_ofReal]
  have qb : (fun t:ℝ => (((Chebyshev.psi t - t)*robinRealWeight n t:ℝ):ℂ)) =
    (fun t:ℝ => ((Chebyshev.psi t*robinRealWeight n t:ℝ):ℂ) -
     ((t*robinRealWeight n t:ℝ):ℂ)):=by
   funext t
   push_cast
   ring
  rw [qb]
  exact integral_sub qg qf
 rw [qc,<- y5 hn qd,
  <- vp n qd,
  ym hRH hn qd]
 have qa:=Yu qe hx
 linear_combination qa
def robinPsiWeightedErrorScalar (n : Nat) (x:ℝ):ℝ :=
 (Real.eulerMascheroniConstant+2 - Real.log (4*Real.pi)) *
  (x^((1/2:ℝ) - (n:ℝ))*Inv.inv (Real.log x) *
   ((n:ℝ)+Inv.inv (Real.log x) +
    4*Inv.inv (((2*n - 1 : Nat):ℝ)*(Real.log x)^2)))
theorem YJ (n : Nat) (rho:ℂ) {t:ℝ} (ht : 1 < t) : (t:ℂ)^rho*(robinRealWeight n t:ℂ)=(t:ℂ)^(rho - (n:ℂ) - 1)*(((n:ℝ)*Real.log t+1)/(Real.log t)^2:ℝ):=by
 have qb : 0 < t:=lt_trans Real.zero_lt_one ht
 have qa : Not ((t:ℂ)=0):=Complex.ofReal_ne_zero.mpr qb.ne'
 unfold robinRealWeight
 rw [Complex.ofReal_mul,Complex.ofReal_cpow qb.le]
 push_cast
 rw [<- mul_assoc,<- Complex.cpow_add _ _ qa]
 congr 2
 ring
theorem vx (n : Nat) (rho:ℂ) {x:ℝ} (hx : 1 < x) : WT n rho x=integral (volume.restrict (Ioi x)) (fun t:ℝ => (t:ℂ)^rho*(robinRealWeight n t:ℂ)):=by
 unfold WT
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 exact (YJ n rho (lt_trans hx ht)).symm
theorem v8 {n : Nat} {rho:ℂ} {x:ℝ} (hx : 1 < x) (hRe : rho.re < n) : IntegrableOn (fun t:ℝ => (t:ℂ)^rho*(robinRealWeight n t:ℂ)) (Ioi x):=by
 have qa : (rho - (n:ℂ) - 1).re < -1:=by
  simp only [Complex.sub_re,Complex.natCast_re,Complex.one_re]
  linarith
 have qb:=Yf hx qa 1
 have qc:=Yf hx qa 2
 have qd:=(qb.const_mul (n:ℂ)).add qc
 apply IntegrableOn.congr_fun qd _ measurableSet_Ioi
 intro t ht
 dsimp only [Pi.add_apply]
 rw [YJ n rho (lt_trans hx ht)]
 simp only [pow_one]
 push_cast
 have qe : Not ((Real.log t:ℂ)=0) :=
  Complex.ofReal_ne_zero.mpr (Real.log_pos (lt_trans hx ht)).ne'
 field_simp [qe] <;> ring
theorem vn (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x:ℝ} (hx : 2 <= x) : And (-robinPsiWeightedErrorScalar n x - Real.log (2*Real.pi)*x^(-(n:ℝ))*Inv.inv (Real.log x) <= Yo n x) (Yo n x <= robinPsiWeightedErrorScalar n x):=by
 have qb : 1 < x:=by linarith
 have qc : 1 <= n:=by omega
 let Z : ℂ:=tsum (fun p : Vc =>
  WT n (Y5 p) x/Y5 p)
 have qd : norm Z <= robinPsiWeightedErrorScalar n x :=
  yT hRH qc qb
 have qe:=abs_le.mp ((Complex.abs_re_le_norm Z).trans qd)
 have qa:=congrArg Complex.re
  (zF hRH hn hx)
 change Yo n x =
  -Z.re - YU n x at qa
 have qf:=Ze qc hx
 constructor <;> linarith [qe.1,qe.2,qf.1,qf.2]
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open MeasureTheory Set
theorem v6 {n : Nat} {r x:ℝ} (hx : 1 < x) (hr : r < n) : IntegrableOn (fun t:ℝ => t^r*robinRealWeight n t) (Ioi x):=by
 have qa:=(v8 (rho:=(r:ℂ)) hx hr).norm
 apply IntegrableOn.congr_fun qa _ measurableSet_Ioi
 intro t ht
 dsimp only
 rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one (lt_trans hx ht)),
  Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (VW (lt_trans hx ht))]
 rfl
theorem Zm (n : Nat) (r:ℝ) {x:ℝ} (hx : 1 < x) : integral (volume.restrict (Ioi x)) (fun t:ℝ => t^r*robinRealWeight n t)=(WT n (r:ℂ) x).re:=by
 have hEq : WT n (r:ℂ) x =
   ((integral (volume.restrict (Ioi x)) (fun t:ℝ => t^r*robinRealWeight n t):ℝ):ℂ):=by
  rw [vx n (r:ℂ) hx,<- integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Complex.ofReal_mul,Complex.ofReal_cpow (lt_trans Real.zero_lt_one (lt_trans hx ht)).le]
 rw [hEq,Complex.ofReal_re]
theorem Vx {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) : Inv.inv (k:ℝ) < n:=by
 have qb : (1:ℝ) < k:=by exact_mod_cast (show 1 < k by omega)
 have qa : (1:ℝ) <= n:=by exact_mod_cast hn
 have qc : Inv.inv (k:ℝ) < 1:=by
  simpa only [one_div,inv_one] using one_div_lt_one_div_of_lt Real.zero_lt_one qb
 exact lt_of_lt_of_le qc qa
theorem y6 {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x:ℝ} (hx : 1 < x) : IntegrableOn (fun t:ℝ => Chebyshev.psi (t^(Inv.inv (k:ℝ)))*robinRealWeight n t) (Ioi x):=by
  have qe:=v6 hx (Vx hn hk)
  have qb : Measurable (fun t:ℝ => Chebyshev.psi (t^(Inv.inv (k:ℝ)))) :=
    Chebyshev.psi_mono.measurable.comp (by fun_prop)
  have qa : Measurable (robinRealWeight n):=by unfold robinRealWeight; fun_prop
  apply Integrable.mono' (qe.const_mul (Real.log 4+4))
    (qb.mul qa).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have qf : 1 < t:=lt_trans hx ht
  have qc : 0 <= t:=le_of_lt (lt_trans Real.zero_lt_one qf)
  have qd:=VW (n:=n) qf
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg _) qd)]
  calc
    _ <= ((Real.log 4+4)*t^(Inv.inv (k:ℝ)))*robinRealWeight n t :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg qc _)) qd
    _ = _ := by ring
def YF (n : Nat) (x:ℝ):ℝ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ =>
  (Chebyshev.psi t - Chebyshev.theta t)*robinRealWeight n t)
theorem vf {n : Nat} (hn : 1 <= n) {x:ℝ} (hx : 1 < x) : IntegrableOn (fun t:ℝ => (Chebyshev.psi t - Chebyshev.theta t)*robinRealWeight n t) (Ioi x):=by
 have qe:=y6 hn (by norm_num : 2 <= (2 : Nat)) hx
 have qc:=y6 hn (by norm_num : 2 <= (3 : Nat)) hx
 have qd:=y6 hn (by norm_num : 2 <= (5 : Nat)) hx
 have qa : Measurable (robinRealWeight n):=by unfold robinRealWeight; fun_prop
 apply Integrable.mono' ((qe.add qc).add qd)
  (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).mul qa).aestronglyMeasurable)
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
 have qb:=VW (n:=n) (lt_trans hx ht)
 dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply]
 rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)) qb)]
 simpa only [add_mul,Nat.cast_ofNat] using
  mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) qb
end
end Robin1984
end
section
namespace Robin1984
noncomputable section
open MeasureTheory Set
def robinThetaWeightedTailTwo (x:ℝ):ℝ :=
 integral (volume.restrict (Ioi x)) (fun t:ℝ => Chebyshev.theta t*robinRealWeight 2 t)
theorem yC {x:ℝ} (hx : 1 < x) : robinThetaWeightedTailTwo x=(WT 2 (1:ℂ) x).re+Yo 2 x - YF 2 x:=by
 have qb : IntegrableOn (fun t:ℝ => t*robinRealWeight 2 t) (Ioi x):=by
  simpa only [Real.rpow_one] using
   v6 (n:=2) (r:=1) hx (by norm_num)
 have qa : integral (volume.restrict (Ioi x)) (fun t:ℝ => t*robinRealWeight 2 t) =
   (WT 2 (1:ℂ) x).re:=by
  simpa only [Real.rpow_one,Complex.ofReal_one] using Zm 2 1 hx
 have hJ:=wY (n:=2) (by omega) hx
 have hK:=vf (n:=2) (by omega) hx
 have hEq : robinThetaWeightedTailTwo x =
   integral (volume.restrict (Ioi x)) (fun t:ℝ =>
    (t*robinRealWeight 2 t+(Chebyshev.psi t - t)*robinRealWeight 2 t) -
     (Chebyshev.psi t - Chebyshev.theta t)*robinRealWeight 2 t):=by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  ring
 have qc : IntegrableOn (fun t:ℝ =>
   t*robinRealWeight 2 t+(Chebyshev.psi t - t)*robinRealWeight 2 t) (Ioi x):=qb.add hJ
 rw [hEq,integral_sub qc hK,integral_add qb hJ,qa]
 rfl
theorem Z7 {x:ℝ} (hx : 1 < x) : And (2*x^(-(1:ℝ))*Inv.inv (Real.log x) - x^(-(1:ℝ))*Inv.inv ((Real.log x)^2) <= (WT 2 (1:ℂ) x).re) ((WT 2 (1:ℂ) x).re <= 2*x^(-(1:ℝ))*Inv.inv (Real.log x)):=by
 have hF:=yj 2
  (r:=(1:ℝ)) (by norm_num) hx
 have qa:=Zf (-(1:ℝ)) 2 hx
 have qb:=Yc (a := -(1:ℝ)) (by norm_num) 2 hx
 norm_num at hF qa qb
 constructor <;> linarith
theorem w6 {n : Nat} {x:ℝ} (hx : 1 <= x) : 0 <= YF n x:=by
 unfold YF
 apply setIntegral_nonneg measurableSet_Ioi
 intro t ht
 exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
  (VW (n:=n) (lt_of_le_of_lt hx ht))
theorem robinThetaWeightedTailTwo_upper (hRH : RiemannHypothesis) {x:ℝ} (hx : 2 <= x) : robinThetaWeightedTailTwo x <= 2*x^(-(1:ℝ))*Inv.inv (Real.log x)+robinPsiWeightedErrorScalar 2 x:=by
 have qc : 1 < x:=by linarith
 have qa:=yC qc
 have qd:=(Z7 qc).2
 have qe :=
  (vn hRH
   (n:=2) (by omega) hx).2
 have qb:=w6
  (n:=2) (by linarith : (1:ℝ) <= x)
 rw [qa]
 linarith
end
end Robin1984
end
open Real MeasureTheory Set Robin1984 in
theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro hRH b hb
  have hU := robinThetaWeightedTailTwo_upper hRH hb
  have hInt : (∫ t in Set.Ioi b, ((2 * log t + 1) / (t ^ 3 * (log t) ^ 2)) * Chebyshev.theta t) =
      robinThetaWeightedTailTwo b := by
    unfold robinThetaWeightedTailTwo
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htOne : 1 < t := by linarith [show b < t from ht]
    have htPos : 0 < t := by linarith
    have hLogPos : 0 < log t := log_pos htOne
    dsimp only
    unfold robinRealWeight
    norm_num [Real.rpow_neg htPos.le]
    field_simp [htPos.ne', hLogPos.ne']
  rw [hInt]
  simpa only [robinPsiWeightedErrorScalar, Nat.cast_ofNat, Nat.reduceMul,
    Nat.reduceSub, Nat.cast_one, div_eq_mul_inv] using hU
