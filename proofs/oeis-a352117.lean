import OMAStatements.S_oeis_a352117

/-!
OEIS A352117: Expansion of e.g.f. 1/sqrt(2 - exp(2*x)).
Conjecture: a(n) = Sum_{k>=1} 2^(n - 3*k - 1/2) * k^n * binomial(2*k, k) for n > 0. - Velin Yanev
and Vaclav Kotesovec, Jul 21 2026

Proof. Near 0 the e.g.f. f satisfies f'(x) (2 - e^(2x)) = e^(2x) f(x) (`deriv_egf_eq`), and the
Leibniz rule at 0 turns this into a(n+1) = sum_(i<n) C(n,i) 2^(n-i) a(i+1) + sum_(i<=n) C(n,i) 2^i
a(n-i) (`rec_a`). The series R(n) = sum_k c(k) (2k)^n, c(k) = C(2k,k)/(8^k sqrt 2), satisfies the
same recurrence (`rec_R`): by the binomial theorem it reduces to 2 c(k+1) (2k+2) = (2k+1) c(k)
after shifting k by one. R(0) = 1 is the binomial series sum_k C(2k,k) y^k/4^k = (1-y)^(-1/2) at
y = 1/2 (`R_zero`). So a(n) = R(n) for every n (`a_eq_R`), and for n > 0 the term k = 0 vanishes.
-/

namespace OMA.S_oeis_a352117

open Finset Filter Topology


/-! ### The differential equation of the e.g.f. near 0 -/

lemma ev_lt : ∀ᶠ x in 𝓝 (0 : ℝ), Real.exp (2 * x) < 2 := by
  have h : ContinuousAt (fun x : ℝ => Real.exp (2 * x)) 0 := by fun_prop
  have h0 : Real.exp (2 * 0) < 2 := by norm_num
  exact h.eventually (gt_mem_nhds h0)

lemma hasDerivAt_egf {x : ℝ} (hx : Real.exp (2 * x) < 2) :
    HasDerivAt egf (Real.exp (2 * x) * egf x / (2 - Real.exp (2 * x))) x := by
  have hpos : 0 < 2 - Real.exp (2 * x) := by linarith
  have h1 : HasDerivAt (fun y => 2 - Real.exp (2 * y)) (-(Real.exp (2 * x) * (2 * 1))) x :=
    ((hasDerivAt_id x).const_mul 2).exp.const_sub 2
  have h2 := (h1.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  have e : egf = fun y => (Real.sqrt (2 - Real.exp (2 * y)))⁻¹ := by
    funext y
    simp [egf]
  rw [e]
  refine h2.congr_deriv ?_
  set s := Real.sqrt (2 - Real.exp (2 * x)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : 2 - Real.exp (2 * x) = s ^ 2 := (Real.sq_sqrt hpos.le).symm
  rw [hss]
  field_simp
  ring

lemma egf_contDiffAt {x : ℝ} (hx : Real.exp (2 * x) < 2) (m : ℕ) : ContDiffAt ℝ m egf x := by
  have hpos : 0 < 2 - Real.exp (2 * x) := by linarith
  have hsq : ContDiffAt ℝ m (fun y => Real.sqrt (2 - Real.exp (2 * y))) x :=
    (Real.contDiffAt_sqrt hpos.ne').comp x (by fun_prop)
  exact contDiffAt_const.div hsq (Real.sqrt_pos.mpr hpos).ne'

lemma deriv_egf_ev :
    deriv egf =ᶠ[𝓝 (0 : ℝ)] fun x => Real.exp (2 * x) * egf x / (2 - Real.exp (2 * x)) := by
  filter_upwards [ev_lt] with x hx
  exact (hasDerivAt_egf hx).deriv

lemma deriv_egf_contDiffAt (m : ℕ) : ContDiffAt ℝ m (deriv egf) 0 := by
  have h0 : Real.exp (2 * (0 : ℝ)) < 2 := by norm_num
  have h : ContDiffAt ℝ m (fun x => Real.exp (2 * x) * egf x / (2 - Real.exp (2 * x))) 0 := by
    refine ContDiffAt.div ?_ (by fun_prop) (by norm_num)
    exact (by fun_prop : ContDiffAt ℝ m (fun x : ℝ => Real.exp (2 * x)) 0).mul (egf_contDiffAt h0 m)
  exact h.congr_of_eventuallyEq deriv_egf_ev

lemma deriv_egf_eq :
    (fun x => deriv egf x * (2 - Real.exp (2 * x))) =ᶠ[𝓝 (0 : ℝ)] fun x => Real.exp (2 * x) * egf x := by
  filter_upwards [ev_lt] with x hx
  rw [(hasDerivAt_egf hx).deriv]
  have hpos : 0 < 2 - Real.exp (2 * x) := by linarith
  field_simp

lemma iter_exp (j : ℕ) : iteratedDeriv j (fun x : ℝ => Real.exp (2 * x)) 0 = 2 ^ j := by
  rw [iteratedDeriv_exp_const_mul]
  simp

lemma iter_h (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => 2 - Real.exp (2 * x)) 0 = (if j = 0 then 2 else 0) - 2 ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedDeriv_const_sub hj, iteratedDeriv_neg, iter_exp, if_neg hj.ne']
    ring

lemma iter_deriv_egf (i : ℕ) : iteratedDeriv i (deriv egf) 0 = a (i + 1) := by
  rw [a, iteratedDeriv_succ']

/-- The recurrence of a, from the differential equation by the Leibniz rule at 0. -/
lemma rec_a (n : ℕ) :
    a (n + 1) = ∑ i ∈ range n, (n.choose i : ℝ) * 2 ^ (n - i) * a (i + 1) +
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * 2 ^ i * a (n - i) := by
  have h := deriv_egf_eq.iteratedDeriv_eq n
  have h0 : Real.exp (2 * (0 : ℝ)) < 2 := by norm_num
  rw [iteratedDeriv_fun_mul (deriv_egf_contDiffAt n) (by fun_prop),
    iteratedDeriv_fun_mul (by fun_prop) (egf_contDiffAt h0 n)] at h
  simp only [iter_deriv_egf, iter_h, iter_exp] at h
  rw [sum_range_succ, Nat.choose_self, Nat.sub_self, if_pos rfl] at h
  have e : ∀ i ∈ range n, (n.choose i : ℝ) * a (i + 1) * ((if n - i = 0 then 2 else 0) - 2 ^ (n - i)) =
      -((n.choose i : ℝ) * 2 ^ (n - i) * a (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rw [if_neg (by omega)]
    ring
  rw [sum_congr rfl e, sum_neg_distrib] at h
  have e2 : ∀ i ∈ range (n + 1), (n.choose i : ℝ) * 2 ^ i * iteratedDeriv (n - i) egf 0 =
      (n.choose i : ℝ) * 2 ^ i * a (n - i) := fun i _ => rfl
  rw [sum_congr rfl e2] at h
  norm_num at h
  linarith

/-! ### The series side -/

/-- c(k) = C(2k,k) / (8^k sqrt 2). -/
noncomputable def c (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / (8 ^ k * Real.sqrt 2)

/-- R(n) = sum_k c(k) (2k)^n. -/
noncomputable def R (n : ℕ) : ℝ := ∑' k, c k * (2 * (k : ℝ)) ^ n

lemma c_nonneg (k : ℕ) : 0 ≤ c k := by
  unfold c
  positivity

lemma c_le (k : ℕ) : c k ≤ (1 / 2 : ℝ) ^ k := by
  unfold c
  have h1 : (Nat.centralBinom k : ℝ) ≤ 4 ^ k := by
    have := Nat.centralBinom_le_four_pow k
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  calc (Nat.centralBinom k : ℝ) ≤ 4 ^ k := h1
    _ = (1 / 2) ^ k * 8 ^ k := by
        rw [← mul_pow]
        norm_num
    _ ≤ (1 / 2) ^ k * (8 ^ k * Real.sqrt 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 8) k]

lemma summable_c (n : ℕ) : Summable (fun k : ℕ => c k * (2 * (k : ℝ)) ^ n) := by
  have hg : Summable (fun k : ℕ => (2 : ℝ) ^ n * ((k : ℝ) ^ n * (1 / 2 : ℝ) ^ k)) :=
    (summable_pow_mul_geometric_of_norm_lt_one n (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => by have := c_nonneg k; positivity) (fun k => ?_) hg
  rw [mul_pow]
  have := c_le k
  have h2 : 0 ≤ (2 : ℝ) ^ n * (k : ℝ) ^ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this h2]

lemma c_succ (k : ℕ) : 2 * c (k + 1) * (2 * ((k : ℝ) + 1)) = (2 * k + 1) * c k := by
  have h' : (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * k + 1) * Nat.centralBinom k / ((k : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have h : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * k + 1) * Nat.centralBinom k := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    linear_combination h
  have hs : 0 < Real.sqrt 2 := by positivity
  unfold c
  rw [h', pow_succ]
  field_simp
  ring

/-- The recurrence of R, the same as that of a. -/
lemma rec_R (n : ℕ) :
    R (n + 1) = ∑ i ∈ range n, (n.choose i : ℝ) * 2 ^ (n - i) * R (i + 1) +
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * 2 ^ i * R (n - i) := by
  have S := summable_c
  -- the first sum, termwise: 2k ((2k + 2)^n - (2k)^n) by the binomial theorem
  have sA : HasSum (fun k : ℕ => c k * (2 * (k : ℝ) * ((2 * (k : ℝ) + 2) ^ n - (2 * (k : ℝ)) ^ n)))
      (∑ i ∈ range n, (n.choose i : ℝ) * 2 ^ (n - i) * R (i + 1)) := by
    have h := hasSum_sum (s := range n)
      (fun i _ => (S (i + 1)).hasSum.mul_left ((n.choose i : ℝ) * 2 ^ (n - i)))
    have hf : (fun k : ℕ => c k * (2 * (k : ℝ) * ((2 * (k : ℝ) + 2) ^ n - (2 * (k : ℝ)) ^ n))) =
        fun k : ℕ => ∑ i ∈ range n, (n.choose i : ℝ) * 2 ^ (n - i) * (c k * (2 * (k : ℝ)) ^ (i + 1)) := by
      funext k
      have hb := add_pow (2 * (k : ℝ)) 2 n
      rw [sum_range_succ, Nat.choose_self, Nat.sub_self] at hb
      have e : ∑ i ∈ range n, (n.choose i : ℝ) * 2 ^ (n - i) * (c k * (2 * (k : ℝ)) ^ (i + 1)) =
          c k * (2 * k) * ∑ i ∈ range n, (2 * (k : ℝ)) ^ i * 2 ^ (n - i) * (n.choose i : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        ring
      rw [e, hb]
      push_cast
      ring
    rw [hf]
    exact h
  -- the second sum, termwise: (2k + 2)^n
  have sB : HasSum (fun k : ℕ => c k * (2 * (k : ℝ) + 2) ^ n)
      (∑ i ∈ range (n + 1), (n.choose i : ℝ) * 2 ^ i * R (n - i)) := by
    have h := hasSum_sum (s := range (n + 1))
      (fun i _ => (S (n - i)).hasSum.mul_left ((n.choose i : ℝ) * 2 ^ i))
    have hf : (fun k : ℕ => c k * (2 * (k : ℝ) + 2) ^ n) =
        fun k : ℕ => ∑ i ∈ range (n + 1), (n.choose i : ℝ) * 2 ^ i * (c k * (2 * (k : ℝ)) ^ (n - i)) := by
      funext k
      rw [add_comm, add_pow, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact h
  -- 2 R(n + 1) = sum_k (2k + 1) c(k) (2k + 2)^n, shifting k by one
  have sD : HasSum (fun k : ℕ => c k * (2 * k + 1) * (2 * (k : ℝ) + 2) ^ n) (2 * R (n + 1)) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr (S (n + 1)).hasSum
    simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, ne_eq, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero] at h1
    have hf : (fun k : ℕ => c k * (2 * k + 1) * (2 * (k : ℝ) + 2) ^ n) =
        fun k : ℕ => 2 * (c (k + 1) * (2 * ((k + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
      funext k
      have hc := c_succ k
      push_cast
      rw [pow_succ]
      linear_combination -(2 * (k : ℝ) + 2) ^ n * hc
    rw [hf]
    exact h1.mul_left 2
  have sE := (S (n + 1)).hasSum
  have key : (fun k : ℕ => c k * (2 * (k : ℝ) * ((2 * (k : ℝ) + 2) ^ n - (2 * (k : ℝ)) ^ n)) +
      c k * (2 * (k : ℝ) + 2) ^ n) =
      fun k : ℕ => c k * (2 * k + 1) * (2 * (k : ℝ) + 2) ^ n - c k * (2 * (k : ℝ)) ^ (n + 1) := by
    funext k
    ring
  have h2 := sD.sub sE
  rw [← key] at h2
  have := (sA.add sB).unique h2
  unfold R at this ⊢
  linarith

lemma asc_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2 : ℝ) = (Nat.factorial (2 * n) : ℝ) / (4 ^ n * Nat.factorial n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma coef_eq (n : ℕ) : Ring.choose ((1 / 2 : ℝ) + n - 1) n = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, asc_half, nsmul_eq_mul] at h
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.cast_choose ℝ (by omega : n ≤ 2 * n),
    show 2 * n - n = n by omega]
  field_simp
  field_simp at h
  linear_combination h

lemma R_zero : R 0 = 1 := by
  have hy : (1 / 2 : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    have : ‖(1 / 2 : ℝ)‖₊ < 1 := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm]
      norm_num
    exact_mod_cast this
  have hb := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum hy
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, coef_eq, zero_add, smul_eq_mul] at hb
  have e : (1 : ℝ) / (1 - 1 / 2) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.sqrt_eq_rpow]
    simp
  rw [e] at hb
  have hs : 0 < Real.sqrt 2 := by positivity
  have hf : c = fun k : ℕ => (Nat.centralBinom k : ℝ) / 4 ^ k * (1 / 2) ^ k / Real.sqrt 2 := by
    funext k
    unfold c
    rw [div_pow, show (8 : ℝ) ^ k = 4 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
    field_simp
    simp
  have hc : HasSum c 1 := by
    have h := hb.div_const (Real.sqrt 2)
    rw [div_self hs.ne'] at h
    rw [hf]
    exact h
  unfold R
  simp only [pow_zero, mul_one]
  exact hc.tsum_eq

lemma a_zero : a 0 = 1 := by
  simp [a, egf]
  norm_num

lemma a_eq_R (n : ℕ) : a n = R n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [a_zero, R_zero]
    · rw [rec_a n, rec_R n]
      congr 1
      · refine sum_congr rfl (fun i hi => ?_)
        rw [mem_range] at hi
        rw [ih (i + 1) (by omega)]
      · refine sum_congr rfl (fun i hi => ?_)
        rw [ih (n - i) (by omega)]

/-- Controls: the entry's listed terms, a(0) to a(18), from the recurrence. -/
theorem controls :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 37 ∧ a 4 = 377 ∧ a 5 = 4921 ∧ a 6 = 78365 ∧
    a 7 = 1473277 ∧ a 8 = 31938737 ∧ a 9 = 784384561 ∧ a 10 = 21523937525 ∧
    a 11 = 652667322517 ∧ a 12 = 21672312694697 ∧ a 13 = 782133969325801 ∧
    a 14 = 30481907097849485 ∧ a 15 = 1275870745561131757 ∧ a 16 = 57083444567425884257 ∧
    a 17 = 2718602143583362124641 ∧ a 18 = 137315150097164841942245 := by
  have v0 := a_zero
  have v1 : a 1 = 1 := by rw [rec_a 0]; norm_num [v0]
  have v2 : a 2 = 5 := by rw [rec_a 1]; norm_num [sum_range_succ, Nat.choose, v0, v1]
  have v3 : a 3 = 37 := by rw [rec_a 2]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2]
  have v4 : a 4 = 377 := by rw [rec_a 3]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3]
  have v5 : a 5 = 4921 := by
    rw [rec_a 4]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4]
  have v6 : a 6 = 78365 := by
    rw [rec_a 5]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5]
  have v7 : a 7 = 1473277 := by
    rw [rec_a 6]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6]
  have v8 : a 8 = 31938737 := by
    rw [rec_a 7]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7]
  have v9 : a 9 = 784384561 := by
    rw [rec_a 8]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8]
  have v10 : a 10 = 21523937525 := by
    rw [rec_a 9]; norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  have v11 : a 11 = 652667322517 := by
    rw [rec_a 10]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  have v12 : a 12 = 21672312694697 := by
    rw [rec_a 11]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  have v13 : a 13 = 782133969325801 := by
    rw [rec_a 12]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  have v14 : a 14 = 30481907097849485 := by
    rw [rec_a 13]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
      v13]
  have v15 : a 15 = 1275870745561131757 := by
    rw [rec_a 14]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
      v13, v14]
  have v16 : a 16 = 57083444567425884257 := by
    rw [rec_a 15]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
      v13, v14, v15]
  have v17 : a 17 = 2718602143583362124641 := by
    rw [rec_a 16]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
      v13, v14, v15, v16]
  have v18 : a 18 = 137315150097164841942245 := by
    rw [rec_a 17]
    norm_num [sum_range_succ, Nat.choose, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
      v13, v14, v15, v16, v17]
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18⟩

/-- Yanev and Kotesovec's conjecture. -/
theorem conjecture : ∀ n : ℕ, 0 < n →
    HasSum (fun k : ℕ => (2 : ℝ) ^ ((n : ℝ) - 3 * ((k : ℝ) + 1) - 1 / 2) * ((k : ℝ) + 1) ^ n *
      ((2 * (k + 1)).choose (k + 1) : ℝ)) (a n) := by
  intro n hn
  have h1 := (hasSum_nat_add_iff' 1).mpr (summable_c n).hasSum
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_pow hn.ne', sub_zero] at h1
  rw [a_eq_R]
  have hf : (fun k : ℕ => (2 : ℝ) ^ ((n : ℝ) - 3 * ((k : ℝ) + 1) - 1 / 2) * ((k : ℝ) + 1) ^ n *
      ((2 * (k + 1)).choose (k + 1) : ℝ)) = fun k : ℕ => c (k + 1) * (2 * ((k + 1 : ℕ) : ℝ)) ^ n := by
    funext k
    unfold c
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e : (2 : ℝ) ^ ((n : ℝ) - 3 * ((k : ℝ) + 1) - 1 / 2) = 2 ^ n / (8 ^ (k + 1) * Real.sqrt 2) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_natCast,
        show (3 : ℝ) * ((k : ℝ) + 1) = ((3 * (k + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
        ← Real.sqrt_eq_rpow, pow_mul]
      norm_num
      rw [div_div]
    rw [e]
    push_cast
    rw [mul_pow]
    field_simp
  rw [hf]
  exact h1

end OMA.S_oeis_a352117

theorem OMA.solution : type_of% @OMA.S_oeis_a352117.main :=
  OMA.S_oeis_a352117.conjecture
