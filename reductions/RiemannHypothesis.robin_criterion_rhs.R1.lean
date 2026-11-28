import FormalConjectures.Paper.RiemannHypothesisEquivalents
import Mathlib

/-!
# Robin's unconditional inequality, reduced to extremal integers

For n ≥ 131072 the exponent 1/(log n · log log n) is at most 1/28.
A maximum of σ(k)/(k·k^ε) exists by the harmonic bound. The finite
integer comparison in H1 places this maximum above 5040. Two applications of log x ≤ x−1 transfer the
inequality from the maximum to n. All integers with at most three distinct prime factors are settled unconditionally.

This uses the classical colossally abundant approach to Robin's criterion.
For a separate Lean development, see Robin1984/ColossallyAbundant/CAReduction.lean
and Robin1984/Equivalence/RobinTangentTransfer.lean in kimihiro64/Robin1984.
The finite startup comparison, the interval below 131072, and the infinite
extremal bound are independent hypotheses of the reduction.
-/

namespace OMA.R_RiemannHypothesis_robin_criterion_rhs_R1

namespace RobinSupport
open Real

lemma exp_rat_lt {k d : ℕ} {x : ℝ} (hd : d ≠ 0) (hx : 0 ≤ x)
    (test : (2.7183 : ℝ) ^ k < x ^ d) : exp ((k : ℝ) / d) < x := by
  by_contra! h
  have hpow := pow_le_pow_left₀ hx h d
  rw [← exp_nat_mul] at hpow
  have ident : (d : ℝ) * ((k : ℝ) / d) = k := by field_simp
  rw [ident, show exp (k : ℝ) = exp 1 ^ k by simp] at hpow
  have he : exp 1 ≤ 2.7183 := by linarith [exp_one_lt_d9]
  exact (not_lt_of_ge (hpow.trans (pow_le_pow_left₀ (exp_pos _).le he k))) test

theorem threshold {n : ℕ} (hn : 5040 < n) :
    (15 : ℝ) / 4 < exp eulerMascheroniConstant * log (log (n : ℝ)) := by
  have hr : (5 : ℚ) < harmonic 83 := by norm_num
  have hreal : (5 : ℝ) < (harmonic 83 : ℝ) := by exact_mod_cast hr
  have hγ : (harmonic 83 : ℝ) - log 84 < eulerMascheroniConstant := by
    simpa only [eulerMascheroniSeq, Nat.cast_ofNat, show (83:ℝ)+1=84 by norm_num] using eulerMascheroniSeq_lt_eulerMascheroniConstant 83
  have he := exp_lt_exp.mpr ((sub_lt_sub_right hreal (log 84)).trans hγ)
  rw [exp_sub, exp_log (by norm_num : (0 : ℝ) < 84)] at he
  have hpow : (2.718 : ℝ)^5 ≤ exp 5 := by
    rw [show exp 5 = exp 1 ^ 5 by simp]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) 5
  have gamma : (44 : ℝ) / 25 < exp eulerMascheroniConstant := by norm_num at hpow; linarith
  have h₁ : exp ((32 : ℝ) / 15) < 17/2 :=
    exp_rat_lt (k := 32) (d := 15) (by decide) (by norm_num) (by norm_num)
  have h₂ : exp ((17 : ℝ) / 2) < 5040 :=
    exp_rat_lt (k := 17) (d := 2) (by decide) (by norm_num) (by norm_num)
  have hn' : (5040 : ℝ) < n := by exact_mod_cast hn
  have hlog : (17 : ℝ)/2 < log (n : ℝ) := (lt_log_iff_exp_lt (by positivity)).mpr (h₂.trans hn')
  have ll : (32 : ℝ)/15 < log (log (n : ℝ)) :=
    (lt_log_iff_exp_lt (by linarith)).mpr (h₁.trans hlog)
  have prod := mul_lt_mul'' gamma ll (by norm_num) (by norm_num)
  linarith
end RobinSupport

namespace RobinSupport
open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private lemma extra_prod_le (s : Finset ℕ) (q : ℕ) {c : ℝ} (hc : 1 ≤ c) :
    ∏ p ∈ s, (if p = q then c else 1) ≤ c := by
  classical
  have e : (∏ p ∈ s, (if p = q then c else 1)) = if q ∈ s then c else 1 := by
    by_cases h : q ∈ s
    · rw [if_pos h]
      exact Finset.prod_eq_single_of_mem q h (fun b _ hb => by simp [ hb]) |>.trans (by simp)
    · rw [if_neg h]
      exact Finset.prod_eq_one fun b hb => by
        simp [ show b ≠ q from fun eq => h (eq ▸ hb)]
  rw [e]; split <;> simp_all

theorem sigma_support_three {n : ℕ} (hn : n ≠ 0) (hs : n.primeFactors.card ≤ 3) :
    (σ 1 n : ℝ) ≤ n * (15/4) := by
  classical
  let A (p : ℕ) := if p = 2 then (8/5:ℝ) else 1
  let B (p : ℕ) := if p = 3 then (6/5:ℝ) else 1
  have factor (p : ℕ) (hp : p.Prime) (k : ℕ) :
      (∑ i ∈ range (k+1), (p : ℝ)^i) ≤ (p : ℝ)^k * (5/4) * A p * B p := by
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have ratio : (p : ℝ)/((p : ℝ)-1) ≤ 5/4 * A p * B p := by
      by_cases h₂ : p = 2
      · subst p; norm_num [A,B]
      by_cases h₃ : p = 3
      · subst p; norm_num [A,B]
      have h₄ : p ≠ 4 := by rintro rfl; norm_num at hp
      have h₅ : 5 ≤ p := by have := hp.two_le; omega
      have h₅' : (5 : ℝ) ≤ p := by exact_mod_cast h₅
      rw [div_le_iff₀ (by linarith)]
      simp [A, B, h₂, h₃]
      linarith
    have geom : (∑ i ∈ range (k+1), (p : ℝ)^i) ≤ (p : ℝ)^k * (p/((p : ℝ)-1)) := by
      rw [← mul_div_assoc, le_div_iff₀ (by linarith), geom_sum_mul, pow_succ]
      linarith
    exact geom.trans ((mul_le_mul_of_nonneg_left ratio (by positivity)).trans_eq (by ring))
  have hprod : (∏ p ∈ n.primeFactors, (p:ℝ)^n.factorization p) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hpA : 0 ≤ ∏ p ∈ n.primeFactors, A p := Finset.prod_nonneg fun p _ => by
    dsimp [A]; split <;> norm_num
  have hpB : 0 ≤ ∏ p ∈ n.primeFactors, B p := Finset.prod_nonneg fun p _ => by
    dsimp [B]; split <;> norm_num
  have hA : (∏ p ∈ n.primeFactors, A p) ≤ 8/5 := extra_prod_le _ _ (by norm_num)
  have hB : (∏ p ∈ n.primeFactors, B p) ≤ 6/5 := extra_prod_le _ _ (by norm_num)
  have hpow : (5/4 : ℝ)^n.primeFactors.card ≤ (5/4 : ℝ)^3 := pow_le_pow_right₀ (by norm_num) hs
  calc
    (σ 1 n : ℝ) = ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p+1), (p:ℝ)^i := by
      simp only [sigma_one_apply, Nat.sum_divisors hn, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow]
    _ ≤ ∏ p ∈ n.primeFactors, ((p:ℝ)^n.factorization p * (5/4) * A p * B p) :=
      prod_le_prod (fun _ _ => by positivity) (fun p hp => factor p (Nat.prime_of_mem_primeFactors hp) _)
    _ = (n : ℝ) * ((5/4)^n.primeFactors.card * (∏ p ∈ n.primeFactors, A p) * ∏ p ∈ n.primeFactors, B p) := by
      simp only [prod_mul_distrib, prod_const, hprod]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := mul_le_mul (mul_le_mul hpow hA hpA (by norm_num)) hB hpB (by norm_num)
      norm_num at hh ⊢
      linarith
end RobinSupport

namespace RobinSupport
open Real
open scoped ArithmeticFunction.sigma

theorem robin_le_three {n : ℕ} (hn : 5040 < n) (hs : n.primeFactors.card ≤ 3) :
    (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n) := by
  have h := sigma_support_three (n := n) (by omega) hs
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ) * (15 / 4) := h
    _ < (n : ℝ) * (exp eulerMascheroniConstant * log (log n)) :=
      mul_lt_mul_of_pos_left (threshold hn) hpos
    _ = _ := by ring
end RobinSupport

namespace RobinRecords
open Real Finset Filter
open scoped Topology ArithmeticFunction.sigma

lemma abundance_bound {n : ℕ} (hn : 0 < n) :
    (σ 1 n : ℝ) / n ≤ 1 + log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_trans _ (harmonic_le_one_add_log n)
  apply (div_le_iff₀ hn').mpr
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Finset.sum_mul]
  simp only [pow_one, Rat.cast_inv, Rat.cast_natCast]
  calc
    (∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ)) =
        ∑ d ∈ n.divisors, (d : ℝ)⁻¹ * n := by
          apply sum_congr rfl
          intro d hd
          rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
          ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun d hd =>
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩)
      (fun d _ _ => by positivity)

lemma exists_max_weight {e : ℝ} (he : 0 < e) :
    ∃ m : ℕ, 0 < m ∧ ∀ k : ℕ, 0 < k → ((σ 1 k : ℝ)/(k:ℝ)/(k:ℝ)^e) ≤ ((σ 1 m : ℝ)/(m:ℝ)/(m:ℝ)^e) := by
  have hlog := (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop he)
  have lim : Tendsto (fun x : ℝ => (1+log x)/x^e) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def, add_mul] using hinv.add hlog
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((lim.comp tendsto_natCast_atTop_atTop).eventually_lt_const (by norm_num : (0:ℝ)<1))
  have one : 1 ∈ Icc 1 (max N 1) := mem_Icc.mpr ⟨le_rfl,le_max_right _ _⟩
  obtain ⟨m,hm,hmax⟩ := exists_max_image (Icc 1 (max N 1)) (fun k : ℕ => (σ 1 k : ℝ)/k/(k:ℝ)^e) ⟨1,one⟩
  refine ⟨m,(mem_Icc.mp hm).1,?_⟩
  intro k hk
  by_cases h : k ≤ max N 1
  · exact hmax _ (mem_Icc.mpr ⟨hk,h⟩)
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    calc
      ((σ 1 k : ℝ)/(k:ℝ)/(k:ℝ)^e) ≤ (1 + log k)/(k : ℝ)^e :=
        div_le_div_of_nonneg_right (abundance_bound hk) (rpow_pos_of_pos hk' e).le
      _ ≤ 1 := (hN k (by omega)).le
      _ = ((σ 1 1 : ℝ)/(1:ℝ)/(1:ℝ)^e) := by simp
      _ ≤ ((σ 1 m : ℝ)/(m:ℝ)/(m:ℝ)^e) := by simpa using hmax 1 one

/-- The power tangent to log(log x) at exp(u) majorizes it throughout its positive domain. -/
lemma log_tangent {u v : ℝ} (hu : 1 < u) (hv : 1 < v) :
    log (log v) - log (log u) ≤ (v-u)/(u*log u) := by
  have pu : 0 < u := by linarith
  have pv : 0 < v := by linarith
  have hlogu := log_pos hu
  have hlogv := log_pos hv
  have h₁ := log_le_sub_one_of_pos (div_pos hlogv hlogu)
  rw [log_div hlogv.ne' hlogu.ne'] at h₁
  have h₂ := log_le_sub_one_of_pos (div_pos pv pu)
  rw [log_div pv.ne' pu.ne'] at h₂
  apply h₁.trans
  apply (le_div_iff₀ (mul_pos pu hlogu)).mpr
  have half := (le_div_iff₀ pu).mp (show log v - log u + 1 ≤ v/u by linarith)
  field_simp [hlogu.ne']
  nlinarith

lemma tangent_ratios {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (un : 1 < log n) (um : 1 < log m) :
    log (log m) / m^((log n * log (log n))⁻¹) ≤
    log (log n) / n^((log n * log (log n))⁻¹) := by
  have h₁ := log_pos un
  have h₂ := log_pos um
  apply (log_le_log_iff (div_pos h₂ (rpow_pos_of_pos hm _)) (div_pos h₁ (rpow_pos_of_pos hn _))).mp
  rw [log_div h₂.ne' (rpow_pos_of_pos hm _).ne', log_div h₁.ne' (rpow_pos_of_pos hn _).ne',
      log_rpow hm, log_rpow hn]
  have ht := log_tangent un um
  rw [div_eq_mul_inv, sub_mul] at ht
  linarith only [ht]
end RobinRecords

namespace RobinRecords
open Real
open scoped ArithmeticFunction.sigma

lemma witness_beats
    (small : ∀ n : ℕ, n ≠ 0 → n ≤ 5040 →
      (σ 1 n * 55440)^28 * 55440 < (σ 1 55440 * n)^28 * n)
    {m : ℕ} (hm : 0 < m) (hm' : m ≤ 5040) {e : ℝ} (he : e ≤ (28:ℝ)⁻¹) :
    ((σ 1 m : ℝ)/(m:ℝ)/(m:ℝ)^e) < ((σ 1 55440 : ℝ)/(55440:ℝ)/(55440:ℝ)^e) := by
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have bound : (m : ℝ) ≤ 5040 := by exact_mod_cast hm'
  have bound' : (m : ℝ)/55440 ≤ 1 := by linarith
  let w : ℝ := σ 1 55440
  have wp : 0 < w := by
    dsimp [w]
    exact_mod_cast ArithmeticFunction.sigma_pos 1 55440 (by decide)
  have cmp : ((σ 1 m : ℝ) * 55440)^28 * 55440 < (w*(m:ℝ))^28 * m := by
    change _ < ((σ 1 55440 : ℝ) * (m:ℝ))^28 * m
    exact_mod_cast small m hm.ne' hm'
  let a : ℝ := (σ 1 m : ℝ) * 55440 / (w * m)
  have apos : 0 ≤ a := by dsimp [a]; positivity
  have pow_bound : a ^ (28:ℕ) < (m : ℝ)/55440 := by
    rw [show a ^ (28:ℕ) = ((σ 1 m : ℝ)*55440)^28/(w*(m:ℝ))^28 by simp [a,div_pow]]
    exact (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr (by simpa only [mul_comm] using cmp)
  have root : a < ((m:ℝ)/55440) ^ (28:ℝ)⁻¹ := by
    apply (Real.lt_rpow_inv_iff_of_pos apos (by positivity) (by norm_num)).mpr
    simpa only [show (28:ℝ)=(↑(28:ℕ):ℝ) by norm_num,Real.rpow_natCast] using pow_bound
  have h := root.trans_le (Real.rpow_le_rpow_of_exponent_ge (by positivity) bound' he)
  rw [Real.div_rpow mp.le (by norm_num)] at h
  dsimp [a] at h
  have cross := (div_lt_div_iff₀ (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<55440) e)).mp h
  change _ < w / 55440 / (55440:ℝ)^e
  rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith only [show (σ 1 m : ℝ) * (55440 * (55440:ℝ)^e) <
    w * ((m:ℝ)*(m:ℝ)^e) by simpa only [mul_assoc,mul_left_comm,mul_comm] using cross]

lemma log_large {n : ℕ} (hn : 5040 < n) : 1 < log (n:ℝ) := by
  have h : (5040:ℝ) < n := by exact_mod_cast hn
  apply (lt_log_iff_exp_lt (by linarith)).mpr
  linarith [exp_one_lt_d9]

lemma epsilon_small {n : ℕ} (hn : 131072 ≤ n) :
    (log (n:ℝ) * log (log n))⁻¹ ≤ (28:ℝ)⁻¹ := by
  have h : (131072:ℝ) ≤ n := by exact_mod_cast hn
  have e₁ : exp ((35:ℝ)/3) < 131072 :=
    RobinSupport.exp_rat_lt (k:=35) (d:=3) (by decide) (by norm_num) (by norm_num)
  have e₂ : exp ((12:ℝ)/5) < 35/3 :=
    RobinSupport.exp_rat_lt (k:=12) (d:=5) (by decide) (by norm_num) (by norm_num)
  have u : (35:ℝ)/3 < log (n:ℝ) := (lt_log_iff_exp_lt (by linarith)).mpr (e₁.trans_le h)
  have v : (12:ℝ)/5 < log (log (n:ℝ)) := (lt_log_iff_exp_lt (by linarith)).mpr (e₂.trans u)
  exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith [mul_lt_mul'' u v (by norm_num) (by norm_num)])
end RobinRecords

open Real RobinRecords
open scoped ArithmeticFunction.sigma

/-- A finite integer certificate excludes all small maximizers using the single
witness 55440. The comparison contains no real powers or logarithms. -/
def H1 : Prop := ∀ n : ℕ, n ≠ 0 → n ≤ 5040 →
  (σ 1 n * 55440)^28 * 55440 < (σ 1 55440 * n)^28 * n

/-- The finite interval below the point where the tangent exponent is at most 1/28. -/
def H2 : Prop := ∀ n : ℕ, 5040 < n → n < 131072 → 4 ≤ n.primeFactors.card →
  (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- Robin's inequality at colossally abundant integers of support at least four
which maximize the weighted divisor ratio for some exponent in (0,1/28]. -/
def H3 : Prop := ∀ m : ℕ, 5040 < m → 4 ≤ m.primeFactors.card →
  (∃ e : ℝ, 0 < e ∧ e ≤ (1:ℝ)/28 ∧ ∀ k : ℕ, 0 < k →
    (σ 1 k : ℝ)/k/(k:ℝ)^e ≤ (σ 1 m : ℝ)/m/(m:ℝ)^e) →
  (σ 1 m : ℝ) < exp eulerMascheroniConstant * m * log (log m)

theorem main : H1 → H2 → H3 → type_of% @RiemannHypothesis.robin_criterion_rhs := by
  intro h₀ h₁ h₂ n hn
  by_cases hs : n.primeFactors.card ≤ 3
  · exact RobinSupport.robin_le_three hn hs
  have pn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases hfinite : n < 131072
  · exact h₁ n hn hfinite (by omega)
  let e := (log (n:ℝ) * log (log n))⁻¹
  have lu := log_large hn
  have pe : 0 < e := inv_pos.mpr (mul_pos (by linarith) (log_pos lu))
  have se : e ≤ (28:ℝ)⁻¹ := epsilon_small (by omega)
  obtain ⟨m,hm,hmax⟩ := exists_max_weight pe
  have hm' : 5040 < m := by
    by_contra! small
    exact (witness_beats h₀ hm small se).not_ge (hmax 55440 (by decide))
  have pm : (0 : ℝ) < m := by exact_mod_cast hm
  have rm : (σ 1 m : ℝ) < exp eulerMascheroniConstant * m * log (log m) := by
    by_cases ms : m.primeFactors.card ≤ 3
    · exact RobinSupport.robin_le_three hm' ms
    · exact h₂ m hm' (by omega) ⟨e,pe,by simpa only [one_div] using se,hmax⟩
  have lift : ((σ 1 n : ℝ)/(n:ℝ)/(n:ℝ)^e) < exp eulerMascheroniConstant * (log (log n) / (n:ℝ)^e) := calc
    ((σ 1 n : ℝ)/(n:ℝ)/(n:ℝ)^e) ≤ ((σ 1 m : ℝ)/(m:ℝ)/(m:ℝ)^e) := hmax n (by omega)
    _ < exp eulerMascheroniConstant * (log (log m) / (m:ℝ)^e) := by
      rw [← mul_div_assoc,div_lt_div_iff_of_pos_right (rpow_pos_of_pos pm _),div_lt_iff₀ pm]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (tangent_ratios pn pm lu (log_large hm')) (exp_pos _).le
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right (rpow_pos_of_pos pn _),div_lt_iff₀ pn] at lift
  linarith
end OMA.R_RiemannHypothesis_robin_criterion_rhs_R1
