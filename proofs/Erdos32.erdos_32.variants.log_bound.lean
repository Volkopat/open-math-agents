import FormalConjectures.ErdosProblems.«32»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.PSeries

/-! # Disproof of the O(log N) bound for additive complements to the primes (Erdős Problem 32) -/
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/32.lean:86 (declaration Erdos32.erdos_32.variants.log_bound)
-- Follows Artyom Radomskii (arXiv:2610.14127).

open Filter Topology

namespace OMA32Rad2

/- ## Part 1: Elementary Mertens estimates (adapted from Erdos32.variants.ruzsa) -/

private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    rw [Nat.mem_primesLE]
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨(hpp.dvd_factorial).mp (Nat.dvd_of_mem_primeFactors hp), hpp⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp [hp]

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ∈ Finset.Ico 1 (n + 1) := by
      rw [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this

lemma mertens_first_upper_explicit (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast Nat.factorial_pos n
    · exact_mod_cast Nat.factorial_le_pow n
  have h2 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial).factorization p : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hpp n
    have h4 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add hpp.pos
    have h5 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]; linarith
    linarith
  have h6 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h7 : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have h8 : n * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h8 hn0

private lemma mertens_log_succ_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h' : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

private lemma mertens_tail_step (x : ℝ) (hx : 1 < x) :
    Real.log x / (x * (x - 1)) + (Real.log (x + 1) + 1) / x ≤ (Real.log x + 1) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have := mertens_log_succ_le x hx0; linarith
  have h2 : (x - 1) * (Real.log (x + 1) - Real.log x) ≤ (x - 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left h1 hx1.le
  have h3 : (x - 1) * (1 / x) ≤ 1 := by
    rw [mul_one_div, div_le_one hx0]; linarith
  have key : (Real.log x + 1) / (x - 1) - Real.log x / (x * (x - 1))
      - (Real.log (x + 1) + 1) / x
      = (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    field_simp
    ring
  have h4 : 0 ≤ (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    apply div_nonneg
    · linarith
    · positivity
  linarith

private lemma mertens_tail_bound (n : ℕ) :
    ∑ m ∈ Finset.Icc 2 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
      + (Real.log ((n : ℝ) + 2) + 1) / ((n : ℝ) + 1) ≤ Real.log 2 + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := mertens_tail_step ((k : ℝ) + 2) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have e0 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have e1 : (k : ℝ) + 2 - 1 = k + 1 := by ring
    have e2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 2 + 1 := by push_cast; ring
    have e3 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [e0, e2, e3]
    rw [e1] at h ⊢
    linarith

private lemma mertens_first_lower_explicit (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - (2 + Real.log 2) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
    rw [div_le_iff₀ hf] at h
    have h' := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h'
    linarith
  have h2 : Real.log (n.factorial : ℝ)
      ≤ ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n.factorial).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
    have h4 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at h4
    linarith
  have h5 : ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p
        + n * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      linarith
    field_simp
    ring
  have h6 : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ Real.log 2 + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hsub : Nat.primesLE (k + 1) ⊆ Finset.Icc 2 (k + 1) := by
      rw [Nat.primesLE_eq_filter_Icc_two]; exact Finset.filter_subset _ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) (fun m hm _ => by
        rw [Finset.mem_Icc] at hm
        have h2m : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        apply div_nonneg (Real.log_nonneg (by linarith))
        apply mul_nonneg <;> linarith)
    have hb := mertens_tail_bound k
    have hpos : 0 ≤ (Real.log ((k : ℝ) + 2) + 1) / ((k : ℝ) + 1) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      apply div_nonneg
      · have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)
        linarith
      · linarith
    linarith
  have h7 : n * (Real.log n - (2 + Real.log 2))
      ≤ n * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    have := mul_le_mul_of_nonneg_left h6 hn0.le
    nlinarith
  exact le_of_mul_le_mul_left h7 hn0

lemma mertens_first_explicit (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / p - Real.log n| ≤ 2 + Real.log 2 := by
  rw [abs_le]
  have h1 := mertens_first_upper_explicit n hn
  have h2 := mertens_first_lower_explicit n hn
  have h3 : Real.log 4 ≤ 2 + Real.log 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  constructor <;> linarith

private lemma primesLE_sum_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Nat.primesLE (n + 1), f p
      = ∑ p ∈ Nat.primesLE n, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE n)]; ring
  · simp

private lemma mertens_sum_by_parts (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p
      = (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log (n : ℝ))
        + ∑ m ∈ Finset.Ico 2 n, (∑ p ∈ Nat.primesLE m, Real.log p / p)
            * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : Nat.primesLE 2 = {2} := by decide
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    simp [h2]
    field_simp
  | succ n hn ih =>
    rw [primesLE_sum_succ, primesLE_sum_succ, Finset.sum_Ico_succ_top hn, ih]
    have hx : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hl : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 1)
      exact (Real.log_pos h1).ne'
    split_ifs with hp
    · have e : (∑ p ∈ Nat.primesLE n, Real.log p / p
            + Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * (1 / Real.log ((n + 1 : ℕ) : ℝ))
          = (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log ((n + 1 : ℕ) : ℝ))
            + 1 / ((n + 1 : ℕ) : ℝ) := by
        field_simp
      rw [e]; ring
    · ring

private lemma mertens_loglog_step (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ u + 1 / 2) :
    u * (1 / u - 1 / v) ≤ Real.log v - Real.log u
      ∧ Real.log v - Real.log u ≤ (u + 1 / 2) * (1 / u - 1 / v) := by
  have hv0 : 0 < v := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < v / u by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < v / u by positivity)
  rw [Real.log_div hv0.ne' hu.ne'] at h1 h2
  constructor
  · have e : u * (1 / u - 1 / v) = 1 - (v / u)⁻¹ := by field_simp
    linarith
  · have e : (u + 1 / 2) * (1 / u - 1 / v) - (v / u - 1)
        = (v - u) * (u + 1 / 2 - v) / (u * v) := by
      field_simp
    have h3 : 0 ≤ (v - u) * (u + 1 / 2 - v) / (u * v) := by
      apply div_nonneg
      · apply mul_nonneg <;> linarith
      · positivity
    linarith

private noncomputable def primeLogWeight (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log p / p

private noncomputable def logStep (n : ℕ) : ℝ :=
  1 / Real.log (n + 2 : ℕ) - 1 / Real.log (n + 1 + 2 : ℕ)

private lemma logStep_nonneg (n : ℕ) : 0 ≤ logStep n := by
  unfold logStep
  apply sub_nonneg.mpr
  refine one_div_le_one_div_of_le (Real.log_pos (by norm_cast; omega)) ?_
  exact Real.log_le_log (by positivity) (by norm_cast; omega)

private lemma summable_logStep : Summable logStep := by
  refine summable_of_sum_range_le logStep_nonneg (c := 1 / Real.log 2) fun n => ?_
  simp only [logStep]
  rw [Finset.sum_range_sub']
  have h : 0 ≤ 1 / Real.log (n + 2 : ℕ) :=
    div_nonneg zero_le_one (Real.log_natCast_nonneg _)
  simp only [zero_add, Nat.cast_ofNat]
  linarith

private noncomputable def mertensIncrement (n : ℕ) : ℝ :=
  primeLogWeight (n + 2) * logStep n -
    (Real.log (Real.log (n + 1 + 2 : ℕ)) - Real.log (Real.log (n + 2 : ℕ)))

private lemma norm_mertensIncrement_le (n : ℕ) :
    ‖mertensIncrement n‖ ≤ (2 + Real.log 2 + 1 / 2) * logStep n := by
  let k := n + 2
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by dsimp [k]; omega)
  let u := Real.log (k : ℝ)
  let v := Real.log ((k + 1 : ℕ) : ℝ)
  have hu : 0 < u := Real.log_pos (by linarith)
  have huv : u ≤ v := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
  have hv : v ≤ u + 1 / 2 := by
    dsimp [u, v]
    push_cast
    have h₁ := mertens_log_succ_le (k : ℝ) (by linarith)
    have h₂ := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk
    linarith
  have hw : 1 / u - 1 / v = logStep n := by
    have h : n + 1 + 2 = k + 1 := rfl
    simp [logStep, u, v, k, h]
  obtain ⟨hlo, hhi⟩ := mertens_loglog_step u v hu huv hv
  rw [hw] at hlo hhi
  have hs : |primeLogWeight k - u| ≤ 2 + Real.log 2 :=
    mertens_first_explicit k (by dsimp [k]; omega)
  rw [abs_le] at hs
  have hsw₁ := mul_le_mul_of_nonneg_right hs.1 (logStep_nonneg n)
  have hsw₂ := mul_le_mul_of_nonneg_right hs.2 (logStep_nonneg n)
  have hstep : n + 1 + 2 = k + 1 := rfl
  unfold mertensIncrement
  rw [hstep, Real.norm_eq_abs, abs_le]
  change -((2 + Real.log 2 + 1 / 2) * logStep n) ≤
      primeLogWeight k * logStep n - (Real.log v - Real.log u) ∧ _
  constructor <;> linarith

private lemma tendsto_primeLogWeight_div :
    Tendsto (fun n : ℕ => primeLogWeight n / Real.log n) atTop (𝓝 1) := by
  let C := 2 + Real.log 2
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hl : Tendsto (fun n : ℕ => 1 - C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hC
  have hh : Tendsto (fun n : ℕ => 1 + C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hC
  apply hl.squeeze' hh
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.1]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.2]

lemma exists_prime_reciprocal_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ n.primesLE, (1 : ℝ) / p) -
      Real.log (Real.log n)) atTop (𝓝 B) := by
  have hs : Summable mertensIncrement :=
    (summable_logStep.mul_left (2 + Real.log 2 + 1 / 2)).of_norm_bounded norm_mertensIncrement_le
  let B := 1 - Real.log (Real.log 2) + ∑' k, mertensIncrement k
  refine ⟨B, (tendsto_add_atTop_iff_nat 2).mp ?_⟩
  have hf (n : ℕ) :
      (∑ p ∈ (n + 2).primesLE, (1 : ℝ) / p) - Real.log (Real.log (n + 2 : ℕ)) =
        (primeLogWeight (n + 2) / Real.log (n + 2 : ℕ) - Real.log (Real.log 2)) +
          ∑ k ∈ Finset.range n, mertensIncrement k := by
    rw [mertens_sum_by_parts _ (by omega), Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, mertensIncrement]
    rw [Finset.sum_sub_distrib]
    have hn : (∑ k ∈ Finset.range n, (Real.log (Real.log (k + 1 + 2 : ℕ)) -
        Real.log (Real.log (k + 2 : ℕ)))) =
        Real.log (Real.log (n + 2 : ℕ)) - Real.log (Real.log 2) := by
      rw [Finset.sum_range_sub (fun k : ℕ => Real.log (Real.log (k + 2 : ℕ))) n]
      rfl
    rw [hn]
    have heq (k : ℕ) : k + 2 + 1 = k + 1 + 2 := by omega
    simp only [primeLogWeight, logStep, Nat.add_comm 2, heq, div_eq_mul_inv, one_mul]
    ring
  simp_rw [hf]
  have h := (tendsto_add_atTop_iff_nat 2).mpr tendsto_primeLogWeight_div
  exact (h.sub tendsto_const_nhds).add hs.hasSum.tendsto_sum_nat

private lemma neg_log_one_sub_sub_bounds {u : ℝ} (hu' : u ≤ 1 / 2) :
    0 ≤ -Real.log (1 - u) - u ∧ -Real.log (1 - u) - u ≤ 2 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  have hl := Real.log_le_sub_one_of_pos hpos
  have hh := Real.one_sub_inv_le_log_of_pos hpos
  have hf : (1 - u)⁻¹ - 1 - u = u ^ 2 / (1 - u) := by
    field_simp
    ring
  have hq : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - u) by linarith)
      (sq_nonneg u)
    linarith
  exact ⟨by linarith, by linarith⟩

private noncomputable def primeLogCorrection (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - 1 / (n : ℝ)) - 1 / n else 0

private lemma summable_primeLogCorrection : Summable primeLogCorrection := by
  have hbase := (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))).mul_left (2 : ℝ)
  refine hbase.of_norm_bounded ?_
  intro n
  unfold primeLogCorrection
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hhalf : (1 : ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    obtain ⟨hlo, hhi⟩ := neg_log_one_sub_sub_bounds hhalf
    simp only [Real.norm_eq_abs, abs_of_nonneg hlo]
    simpa [one_div, inv_pow] using hhi
  · simp

lemma exists_prime_log_product_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ =>
      (∑ p ∈ n.primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log n))
      atTop (𝓝 B) := by
  obtain ⟨b, hb⟩ := exists_prime_reciprocal_limit
  have hc := summable_primeLogCorrection.hasSum.tendsto_sum_nat
  refine ⟨b + ∑' n, primeLogCorrection n, ?_⟩
  have hcc := (tendsto_add_atTop_iff_nat 1).mpr hc
  refine (hb.add hcc).congr fun n => ?_
  rw [show (∑ i ∈ Finset.range (n + 1), primeLogCorrection i) =
      ∑ p ∈ n.primesLE, (-Real.log (1 - 1 / (p : ℝ)) - 1 / p) by
    simp only [primeLogCorrection, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]]
  rw [Finset.sum_sub_distrib]
  ring

/-- Two-sided Mertens product estimate: `∏_{p ≤ n} (1 - 1/p)⁻¹ ≍ log n`. -/
lemma exists_mertens_prod_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      c₁ * Real.log n ≤ ∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))⁻¹ ∧
      ∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))⁻¹ ≤ c₂ * Real.log n := by
  obtain ⟨B, hB⟩ := exists_prime_log_product_limit
  have hexp : Tendsto (fun n : ℕ => (∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))⁻¹) / Real.log n)
      atTop (𝓝 (Real.exp B)) := by
    refine ((Real.continuous_exp.tendsto B).comp hB).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log hlog, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hsub : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)
    rw [Real.exp_neg, Real.exp_log hsub]
  have hlo : ∀ᶠ n : ℕ in atTop, Real.exp B / 2 < (∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))⁻¹) / Real.log n :=
    hexp.eventually (eventually_gt_nhds (by linarith [Real.exp_pos B]))
  have hhi : ∀ᶠ n : ℕ in atTop, (∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))⁻¹) / Real.log n < 2 * Real.exp B :=
    hexp.eventually (eventually_lt_nhds (by linarith [Real.exp_pos B]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlo.and (hhi.and (eventually_ge_atTop 2)))
  refine ⟨Real.exp B / 2, 2 * Real.exp B, by positivity, by positivity, max N₀ 2, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨h1, h2, hn2⟩ := hN₀ n ((le_max_left _ _).trans hn)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  exact ⟨(lt_div_iff₀ hlog).mp h1 |>.le, (div_lt_iff₀ hlog).mp h2 |>.le⟩

/-- Bounded error for Mertens' second theorem. -/
lemma exists_mertens_recip_bounds :
    ∃ M : ℝ, 0 < M ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      |(∑ p ∈ n.primesLE, (1 : ℝ) / p) - Real.log (Real.log n)| ≤ M := by
  obtain ⟨B, hB⟩ := exists_prime_reciprocal_limit
  have h1 := hB.eventually (Metric.ball_mem_nhds B zero_lt_one)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h1.and (eventually_ge_atTop 2))
  refine ⟨|B| + 1, by positivity, max N₀ 2, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨hb, _⟩ := hN₀ n ((le_max_left _ _).trans hn)
  rw [Real.dist_eq] at hb
  have htri := abs_sub_abs_le_abs_sub ((∑ p ∈ n.primesLE, (1 : ℝ) / p) - Real.log (Real.log n)) B
  linarith

/-- Discrete summation by parts for `∑_{z < p ≤ y} 1 / (p * log p) ≤ 6 / log z`. -/
lemma sum_primes_inv_mul_log_le {z y : ℕ} (hz : 4 ≤ z) (hzy : z ≤ y) :
    ∑ p ∈ y.primesLE \ z.primesLE, (1 : ℝ) / ((p : ℝ) * Real.log p) ≤ 6 / Real.log z := by
  let S : ℕ → ℝ := fun m => ∑ p ∈ m.primesLE \ z.primesLE, Real.log p / p
  have hS_id : ∀ m : ℕ, z ≤ m →
      ∑ p ∈ m.primesLE \ z.primesLE, (1 : ℝ) / ((p : ℝ) * Real.log p) =
        S m / (Real.log m) ^ 2 +
          ∑ j ∈ Finset.Ico z m, S j * (1 / (Real.log j) ^ 2 - 1 / (Real.log (j + 1 : ℕ)) ^ 2) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp [S]
    | succ m hm ih =>
      have hsdiff_succ : ∀ g : ℕ → ℝ,
          ∑ p ∈ (m + 1).primesLE \ z.primesLE, g p =
            ∑ p ∈ m.primesLE \ z.primesLE, g p + if (m + 1).Prime then g (m + 1) else 0 := by
        intro g
        rw [Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (by omega : z ≤ m + 1)),
          Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hm), primesLE_sum_succ]
        ring
      rw [hsdiff_succ, ih, Finset.sum_Ico_succ_top hm]
      have hSsucc : S (m + 1) = S m + if (m + 1).Prime then Real.log (m + 1 : ℕ) / (m + 1 : ℕ) else 0 := by
        dsimp [S]; exact hsdiff_succ _
      rw [hSsucc]
      have hm1 : (1 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast (by omega : 1 < m + 1)
      have hl : Real.log (m + 1 : ℕ) ≠ 0 := (Real.log_pos hm1).ne'
      have hmp : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      split_ifs with hp
      · field_simp
        ring
      · ring
  rw [hS_id y hzy]
  have hS_le : ∀ m : ℕ, z ≤ m → S m ≤ 2 * Real.log m := by
    intro m hm
    have h1 : S m ≤ ∑ p ∈ m.primesLE, Real.log p / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro p hp _
      have hpp := Nat.prime_of_mem_primesLE hp
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (by positivity)
    have h2 := mertens_first_upper_explicit m (by omega)
    have h3 : Real.log 4 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ m))
    linarith
  have hz_log : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hy_log : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hfirst : S y / (Real.log y) ^ 2 ≤ 2 / Real.log z := by
    have hSy := hS_le y hzy
    have h1 : S y / (Real.log y) ^ 2 ≤ 2 / Real.log y := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hy_log) hy_log]
      nlinarith
    have h2 : 2 / Real.log y ≤ 2 / Real.log z :=
      div_le_div_of_nonneg_left (by norm_num) hz_log (Real.log_le_log (by positivity) (by exact_mod_cast hzy))
    linarith
  have hsec : ∑ j ∈ Finset.Ico z y, S j * (1 / (Real.log j) ^ 2 - 1 / (Real.log (j + 1 : ℕ)) ^ 2)
      ≤ 4 / Real.log z := by
    have hstep : ∀ j ∈ Finset.Ico z y,
        S j * (1 / (Real.log j) ^ 2 - 1 / (Real.log (j + 1 : ℕ)) ^ 2)
          ≤ 4 * (1 / Real.log j - 1 / Real.log (j + 1 : ℕ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      set u := Real.log j
      set v := Real.log (j + 1 : ℕ)
      have hu : 0 < u := Real.log_pos (by exact_mod_cast (by omega : 1 < j))
      have huv : u ≤ v := Real.log_le_log (by exact_mod_cast (by omega : 0 < j)) (by exact_mod_cast Nat.le_succ j)
      have hv : 0 < v := hu.trans_le huv
      have hdiff_nn : 0 ≤ 1 / u ^ 2 - 1 / v ^ 2 := by
        apply sub_nonneg.mpr
        exact one_div_le_one_div_of_le (sq_pos_of_pos hu) (sq_le_sq' (by linarith) huv)
      have h1 : S j * (1 / u ^ 2 - 1 / v ^ 2) ≤ (2 * u) * (1 / u ^ 2 - 1 / v ^ 2) :=
        mul_le_mul_of_nonneg_right (hS_le j hj.1) hdiff_nn
      have h2 : (2 * u) * (1 / u ^ 2 - 1 / v ^ 2) ≤ 4 * (1 / u - 1 / v) := by
        have e1 : 4 * (1 / u - 1 / v) - (2 * u) * (1 / u ^ 2 - 1 / v ^ 2) =
            2 * (v - u) ^ 2 / (u * v ^ 2) := by
          field_simp
          ring
        have hnn : 0 ≤ 2 * (v - u) ^ 2 / (u * v ^ 2) := by positivity
        linarith
      exact h1.trans h2
    calc
      ∑ j ∈ Finset.Ico z y, S j * (1 / (Real.log j) ^ 2 - 1 / (Real.log (j + 1 : ℕ)) ^ 2)
          ≤ ∑ j ∈ Finset.Ico z y, 4 * (1 / Real.log j - 1 / Real.log (j + 1 : ℕ)) :=
        Finset.sum_le_sum hstep
      _ = 4 * ∑ j ∈ Finset.Ico z y, (1 / Real.log j - 1 / Real.log (j + 1 : ℕ)) := by
        rw [← Finset.mul_sum]
      _ = 4 * (1 / Real.log z - 1 / Real.log y) := by
        congr 1
        rw [Finset.sum_Ico_eq_sum_range]
        have hsub := Finset.sum_range_sub' (fun k : ℕ => 1 / Real.log ((z + k : ℕ) : ℝ)) (y - z)
        have hcongr : ∑ k ∈ Finset.range (y - z),
            (1 / Real.log ((z + k : ℕ) : ℝ) - 1 / Real.log ((z + k + 1 : ℕ) : ℝ)) =
            1 / Real.log ((z + 0 : ℕ) : ℝ) - 1 / Real.log ((z + (y - z) : ℕ) : ℝ) := hsub
        simpa [Nat.add_sub_of_le hzy, Nat.add_assoc] using hcongr
      _ ≤ 4 / Real.log z := by
        have hpos : 0 ≤ 1 / Real.log y := by positivity
        have heq : 4 * (1 / Real.log z - 1 / Real.log y) = 4 / Real.log z - 4 * (1 / Real.log y) := by ring
        linarith
  have hsum6 : 2 / Real.log z + 4 / Real.log z = 6 / Real.log z := by ring
  linarith

/- ## Part 2: Elementary analytic helpers -/

lemma exp_sub_one_le_mul_exp {v : ℝ} (_hv : 0 ≤ v) :
    Real.exp v - 1 ≤ v * Real.exp v := by
  have h := Real.add_one_le_exp (-v)
  rw [Real.exp_neg] at h
  have hexp : 0 < Real.exp v := Real.exp_pos v
  have hmul := mul_le_mul_of_nonneg_right h hexp.le
  rw [inv_mul_cancel₀ hexp.ne'] at hmul
  linarith

lemma exp_sub_one_le_of_le {v M : ℝ} (hv : 0 ≤ v) (hM : v ≤ M) :
    Real.exp v - 1 ≤ Real.exp M * v := by
  have h1 := exp_sub_one_le_mul_exp hv
  have h2 : v * Real.exp v ≤ v * Real.exp M :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hM) hv
  linarith

lemma prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, (1 + f i) ≤ Real.exp (∑ i ∈ s, f i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi; linarith [hf i hi]
  · intro i _; linarith [Real.add_one_le_exp (f i)]

lemma sum_inv_sq_Ioc_le {z y : ℕ} (hz : 1 ≤ z) :
    ∑ n ∈ Finset.Ioc z y, (1 : ℝ) / ((n : ℝ) ^ 2) ≤ 1 / (z : ℝ) := by
  by_cases hzy : z ≤ y
  · have hstep : ∀ n ∈ Finset.Ioc z y,
        (1 : ℝ) / ((n : ℝ) ^ 2) ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hnp : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn1, Nat.cast_one]
      rw [hcast] at hnp ⊢
      have e : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        field_simp; ring
      rw [e]
      exact one_div_le_one_div_of_le (mul_pos hn0 hnp) (by nlinarith)
    calc
      ∑ n ∈ Finset.Ioc z y, (1 : ℝ) / ((n : ℝ) ^ 2)
          ≤ ∑ n ∈ Finset.Ioc z y, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) :=
        Finset.sum_le_sum hstep
      _ = ∑ k ∈ Finset.range (y - z), (1 / ((z + k : ℕ) : ℝ) - 1 / ((z + k + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_bij (fun n _ => n - (z + 1)) ?_ ?_ ?_ ?_
        · intro n hn; rw [Finset.mem_Ioc] at hn; rw [Finset.mem_range]; omega
        · intro n₁ hn₁ n₂ hn₂ h; rw [Finset.mem_Ioc] at hn₁ hn₂; omega
        · intro k hk; rw [Finset.mem_range] at hk
          exact ⟨z + k + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn; rw [Finset.mem_Ioc] at hn
          have e1 : z + (n - (z + 1)) = n - 1 := by omega
          have e2 : n - 1 + 1 = n := by omega
          rw [e1, e2]
      _ = 1 / (z : ℝ) - 1 / (y : ℝ) := by
        have hsub := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((z + k : ℕ) : ℝ)) (y - z)
        simpa [Nat.add_sub_of_le hzy, Nat.add_assoc] using hsub
      _ ≤ 1 / (z : ℝ) := by
        have : (0 : ℝ) ≤ 1 / (y : ℝ) := by positivity
        linarith
  · have hemp : Finset.Ioc z y = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    positivity

/- ## Part 3: Subset-of-primes representation for squarefree divisors -/

def val (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

noncomputable def phi (t : Finset ℕ) : ℝ := ∏ p ∈ t, ((p : ℝ) - 1)

lemma val_empty : val ∅ = 1 := rfl

lemma phi_empty : phi ∅ = 1 := rfl

lemma val_pos {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) : 0 < val t :=
  Finset.prod_pos fun p hp => (ht p hp).pos

lemma val_one_le {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) : 1 ≤ val t :=
  val_pos ht

lemma phi_pos {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) : 0 < phi t :=
  Finset.prod_pos fun p hp => by
    have : (1 : ℝ) < p := by exact_mod_cast (ht p hp).one_lt
    linarith

lemma val_insert {p : ℕ} {t : Finset ℕ} (hp : p ∉ t) : val (insert p t) = p * val t :=
  Finset.prod_insert hp

lemma phi_insert {p : ℕ} {t : Finset ℕ} (hp : p ∉ t) :
    phi (insert p t) = ((p : ℝ) - 1) * phi t :=
  Finset.prod_insert hp

lemma val_union_of_disjoint {s t : Finset ℕ} (h : Disjoint s t) :
    val (s ∪ t) = val s * val t :=
  Finset.prod_union h

lemma phi_union_of_disjoint {s t : Finset ℕ} (h : Disjoint s t) :
    phi (s ∪ t) = phi s * phi t :=
  Finset.prod_union h

lemma mem_iff_dvd_val {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) {p : ℕ} (hp : p.Prime) :
    p ∈ t ↔ p ∣ val t := by
  constructor
  · intro hmem; exact Finset.dvd_prod_of_mem _ hmem
  · intro hdvd
    obtain ⟨q, hq, hpq⟩ := hp.prime.dvd_finsetProd_iff id |>.mp hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq hp (ht q hq)).mp hpq
    rwa [heq]

lemma val_inj_on_primes {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (heq : val s = val t) : s = t := by
  ext p
  by_cases hp : p.Prime
  · rw [mem_iff_dvd_val hs hp, mem_iff_dvd_val ht hp, heq]
  · constructor
    · intro h; exact absurd (hs p h) hp
    · intro h; exact absurd (ht p h) hp

lemma sum_powerset_inv_phi (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ t ∈ S.powerset, 1 / phi t = ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
  have h1 : ∀ t ∈ S.powerset, 1 / phi t = ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ := by
    intro t _
    simp [phi, one_div, Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    linarith
  field_simp
  ring

lemma sum_powerset_rpow_div_phi (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime) (γ : ℝ) :
    ∑ t ∈ S.powerset, ((val t : ℝ) ^ γ) / phi t =
      ∏ p ∈ S, (1 + ((p : ℝ) ^ γ) / ((p : ℝ) - 1)) := by
  have h1 : ∀ t ∈ S.powerset,
      ((val t : ℝ) ^ γ) / phi t = ∏ p ∈ t, ((p : ℝ) ^ γ) / ((p : ℝ) - 1) := by
    intro t _
    simp only [val, phi, Nat.cast_prod]
    rw [← Real.finsetProd_rpow t (fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p),
      Finset.prod_div_distrib]
  rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]

lemma sum_powerset_filter_mem_inv_phi (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {q : ℕ} (hq : q ∈ S) :
    ∑ t ∈ S.powerset.filter (fun t => q ∈ t), 1 / phi t =
      (∑ t ∈ S.powerset, 1 / phi t) / (q : ℝ) := by
  have hqP := hS q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqP.ne_zero
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < q := by exact_mod_cast hqP.one_lt
    linarith
  have hbij : ∑ t ∈ S.powerset.filter (fun t => q ∈ t), 1 / phi t =
      ∑ e ∈ (S.erase q).powerset, 1 / phi (insert q e) := by
    refine Finset.sum_bij (fun t _ => t.erase q) ?_ ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_powerset] at ht
      rw [Finset.mem_powerset]
      exact Finset.erase_subset_erase q ht.1
    · intro t₁ ht₁ t₂ ht₂ h
      rw [Finset.mem_filter] at ht₁ ht₂
      rw [← Finset.insert_erase ht₁.2, ← Finset.insert_erase ht₂.2, h]
    · intro e he
      rw [Finset.mem_powerset] at he
      refine ⟨insert q e, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset_iff.mpr ⟨hq, he.trans (Finset.erase_subset q S)⟩,
          Finset.mem_insert_self q e⟩
      · exact Finset.erase_insert (fun hq' => (Finset.mem_erase.mp (he hq')).1 rfl)
    · intro t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.insert_erase ht.2]
  rw [hbij]
  have hfact : ∑ e ∈ (S.erase q).powerset, 1 / phi (insert q e) =
      (1 / ((q : ℝ) - 1)) * ∑ e ∈ (S.erase q).powerset, 1 / phi e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_powerset] at he
    have hqn : q ∉ e := fun hq' => (Finset.mem_erase.mp (he hq')).1 rfl
    rw [phi_insert hqn, one_div_mul_one_div]
  rw [hfact, sum_powerset_inv_phi S hS,
    sum_powerset_inv_phi (S.erase q) (fun p hp => hS p (Finset.mem_of_mem_erase hp))]
  rw [← Finset.mul_prod_erase S (fun p => (1 - 1 / (p : ℝ))⁻¹) hq]
  have hcoeff : (1 / ((q : ℝ) - 1)) = (1 - 1 / (q : ℝ))⁻¹ / (q : ℝ) := by
    field_simp
  rw [hcoeff]
  ring

lemma sum_biUnion_le {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ b ∈ s.biUnion t, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hsub : s.biUnion t ⊆ (insert a s).biUnion t :=
      Finset.biUnion_subset_biUnion_of_subset_left t (Finset.subset_insert a s)
    have h1 : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      have hdisj : ∑ b ∈ t a ∪ s.biUnion t, f b + ∑ b ∈ t a ∩ s.biUnion t, f b =
          ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := Finset.sum_union_inter
      have hinter_nn : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b :=
        Finset.sum_nonneg fun b hb => hf b (Finset.mem_biUnion.mpr
          ⟨a, Finset.mem_insert_self a s, (Finset.mem_inter.mp hb).1⟩)
      linarith
    have h2 := ih fun b hb => hf b (hsub hb)
    linarith

lemma sum_powerset_erase_empty_by_max (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    ∑ t ∈ S.powerset.erase ∅, f t =
      ∑ p ∈ S, ∑ e ∈ (S.filter (· < p)).powerset, f (insert p e) := by
  have hsig : ∑ p ∈ S, ∑ e ∈ (S.filter (· < p)).powerset, f (insert p e) =
      ∑ pe ∈ S.sigma (fun p => (S.filter (· < p)).powerset), f (insert pe.1 pe.2) :=
    Finset.sum_sigma' S (fun p => (S.filter (· < p)).powerset) (fun p e => f (insert p e))
  rw [hsig]
  refine Finset.sum_bij
    (fun t ht =>
      have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
      ⟨t.max' hne, t.erase (t.max' hne)⟩)
    ?_ ?_ ?_ ?_
  · intro t ht
    have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
    have hsub : t ⊆ S := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
    refine Finset.mem_sigma.mpr ⟨hsub (Finset.max'_mem t hne), Finset.mem_powerset.mpr ?_⟩
    intro q hq
    rw [Finset.mem_erase] at hq
    rw [Finset.mem_filter]
    exact ⟨hsub hq.2, lt_of_le_of_ne (Finset.le_max' t q hq.2) hq.1⟩
  · intro t₁ ht₁ t₂ ht₂ h
    have hne₁ : t₁.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht₁).1
    have hne₂ : t₂.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht₂).1
    have h1 : t₁.max' hne₁ = t₂.max' hne₂ := congrArg Sigma.fst h
    have h2 : t₁.erase (t₁.max' hne₁) = t₂.erase (t₂.max' hne₂) := by
      have := congrArg Sigma.snd h
      simpa using this
    rw [← Finset.insert_erase (Finset.max'_mem t₁ hne₁),
      ← Finset.insert_erase (Finset.max'_mem t₂ hne₂), h2, h1]
  · intro ⟨p, e⟩ hpe
    rw [Finset.mem_sigma, Finset.mem_powerset] at hpe
    refine ⟨insert p e, ?_, ?_⟩
    · rw [Finset.mem_erase, Finset.mem_powerset]
      refine ⟨Finset.insert_ne_empty p e, ?_⟩
      exact Finset.insert_subset_iff.mpr ⟨hpe.1, hpe.2.trans (Finset.filter_subset _ _)⟩
    · have hne : (insert p e).Nonempty := Finset.insert_nonempty p e
      have hmax : (insert p e).max' hne = p := by
        apply le_antisymm
        · apply Finset.max'_le
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hqe
          · exact le_rfl
          · exact (Finset.mem_filter.mp (hpe.2 hqe)).2.le
        · exact Finset.le_max' _ _ (Finset.mem_insert_self p e)
      have hpn : p ∉ e := fun hp => lt_irrefl p (Finset.mem_filter.mp (hpe.2 hp)).2
      ext
      · simp [hmax]
      · simp [hmax, Finset.erase_insert hpn]
  · intro t ht
    have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
    simp [Finset.insert_erase (Finset.max'_mem t hne)]

/- ## Part 4: Parameters and Section 3.1-3.2 (Exceptional primes, Divisor sums, Coefficients) -/

def zParam (x : ℕ) : ℕ := x ^ 6

noncomputable def yParam (x : ℕ) : ℕ := ⌊Real.exp ((x : ℝ) / (Real.log x) ^ 5)⌋₊

noncomputable def DParam (x : ℕ) : ℝ := Real.exp ((x : ℝ) / 4)

noncomputable def TParam (x : ℕ) : ℕ := ⌊Real.exp (x : ℝ)⌋₊

noncomputable def betaParam (x : ℕ) : ℝ := (Real.log x) ^ 5 / (x : ℝ)

noncomputable def uParam (x : ℕ) : ℝ := (Real.log x) ^ 5 / 4

noncomputable def primes0 (x : ℕ) : Finset ℕ := (yParam x).primesLE \ (zParam x).primesLE

lemma prime_of_mem_primes0 {x p : ℕ} (hp : p ∈ primes0 x) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1

lemma gt_z_of_mem_primes0 {x p : ℕ} (hp : p ∈ primes0 x) : zParam x < p := by
  have h1 := Finset.mem_sdiff.mp hp
  have hpp := Nat.prime_of_mem_primesLE h1.1
  by_contra! hle
  exact h1.2 (Nat.mem_primesLE.mpr ⟨hle, hpp⟩)

lemma le_y_of_mem_primes0 {x p : ℕ} (hp : p ∈ primes0 x) : p ≤ yParam x :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).1

/-- Asymptotic properties of `zParam`, `yParam`, `DParam`, `TParam`, `betaParam`, `uParam`. -/
lemma eventually_param_bounds (N₀ : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      16 ≤ x ∧
      N₀ ≤ zParam x ∧
      16 ≤ zParam x ∧
      2 ≤ Real.log (x : ℝ) ∧
      zParam x < yParam x ∧
      (x : ℝ) / (2 * (Real.log x) ^ 5) ≤ Real.log (yParam x : ℝ) ∧
      Real.log (yParam x : ℝ) ≤ (x : ℝ) / (Real.log x) ^ 5 ∧
      (1 / 2 : ℝ) * Real.log x ≤
        Real.log (Real.log (yParam x : ℝ)) - Real.log (Real.log (zParam x : ℝ)) ∧
      Real.log (Real.log (yParam x : ℝ)) - Real.log (Real.log (zParam x : ℝ)) ≤ Real.log x ∧
      Real.exp (x : ℝ) / 2 ≤ (TParam x : ℝ) ∧
      (yParam x : ℝ) ≤ Real.exp (x : ℝ) := by
  have hpow6 : (fun x : ℝ => (Real.log x) ^ 6) =o[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) := by
    simpa [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (6 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have h6 := hpow6.bound (show (0 : ℝ) < 1 / 24 by norm_num)
  have h6N : ∀ᶠ x : ℕ in atTop, (Real.log (x : ℝ)) ^ 6 ≤ (1 / 24) * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h6,
      eventually_ge_atTop 2] with x hx hx2
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 6),
      abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    exact hx
  filter_upwards [h6N, eventually_ge_atTop (max 16 N₀)] with x hx6 hxN
  have hx16 : 16 ≤ x := (le_max_left 16 N₀).trans hxN
  have hxN0 : N₀ ≤ x := (le_max_right 16 N₀).trans hxN
  have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog2 : 2 ≤ Real.log (x : ℝ) := by
    have h1 : Real.exp 2 ≤ (16 : ℝ) := by
      have := Real.exp_one_lt_d9
      have := Real.exp_pos 1
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have h2 : Real.exp 2 ≤ (x : ℝ) := h1.trans (by exact_mod_cast hx16)
    have := Real.log_le_log (Real.exp_pos 2) h2
    rwa [Real.log_exp] at this
  have hlog_pos : 0 < Real.log (x : ℝ) := by linarith
  have hsqrt_le : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) := by
    have h1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
    calc (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hsq_sqrt : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
    rw [← Real.rpow_add hx_pos]
    norm_num
  have hdiv_ge : 24 * (x : ℝ) ^ ((1 : ℝ) / 2) * Real.log x ≤ (x : ℝ) / (Real.log x) ^ 5 := by
    rw [le_div_iff₀ (pow_pos hlog_pos 5)]
    have hmul : 24 * (Real.log x) ^ 6 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by linarith
    have hmul2 := mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hx_pos.le ((1 : ℝ) / 2))
    calc 24 * (x : ℝ) ^ ((1 : ℝ) / 2) * Real.log x * (Real.log x) ^ 5
        = (x : ℝ) ^ ((1 : ℝ) / 2) * (24 * (Real.log x) ^ 6) := by ring
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) := hmul2
      _ = (x : ℝ) := hsq_sqrt
  have hsqrt_ge4 : 4 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : (16 : ℝ) ≤ x := by exact_mod_cast hx16
    have h2 : (4 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have harg_ge : 12 * Real.log x ≤ (x : ℝ) / (Real.log x) ^ 5 := by nlinarith
  have harg_ge2 : 2 ≤ (x : ℝ) / (Real.log x) ^ 5 := by linarith
  have hexp_ge2 : 2 ≤ Real.exp ((x : ℝ) / (Real.log x) ^ 5) := by
    linarith [Real.add_one_le_exp ((x : ℝ) / (Real.log x) ^ 5)]
  have hy_ge_half : Real.exp ((x : ℝ) / (Real.log x) ^ 5) / 2 ≤ (yParam x : ℝ) := by
    have h := Nat.sub_one_lt_floor (Real.exp ((x : ℝ) / (Real.log x) ^ 5))
    dsimp [yParam]
    linarith
  have hy_pos : (0 : ℝ) < (yParam x : ℝ) := by linarith [Real.exp_pos ((x : ℝ) / (Real.log x) ^ 5)]
  have hy_le_exp : (yParam x : ℝ) ≤ Real.exp ((x : ℝ) / (Real.log x) ^ 5) :=
    Nat.floor_le (Real.exp_pos _).le
  have hlogy_upper : Real.log (yParam x : ℝ) ≤ (x : ℝ) / (Real.log x) ^ 5 := by
    have := Real.log_le_log hy_pos hy_le_exp
    rwa [Real.log_exp] at this
  have hlogy_lower : (x : ℝ) / (2 * (Real.log x) ^ 5) ≤ Real.log (yParam x : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hy_ge_half
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    have h2 : Real.log 2 ≤ (x : ℝ) / (2 * (Real.log x) ^ 5) := by
      have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have : 1 ≤ (x : ℝ) / (2 * (Real.log x) ^ 5) := by
        rw [le_div_iff₀ (by positivity)]
        have : (Real.log x) ^ 5 * 2 ≤ (x : ℝ) := by
          have := (le_div_iff₀ (pow_pos hlog_pos 5)).mp harg_ge2
          linarith
        linarith
      linarith
    have e : (x : ℝ) / (Real.log x) ^ 5 - (x : ℝ) / (2 * (Real.log x) ^ 5) =
        (x : ℝ) / (2 * (Real.log x) ^ 5) := by ring
    linarith
  have hlogz : Real.log (zParam x : ℝ) = 6 * Real.log x := by
    simp [zParam, Real.log_pow]
  have hlogz_pos : 0 < Real.log (zParam x : ℝ) := by rw [hlogz]; linarith
  have hlogy_pos : 0 < Real.log (yParam x : ℝ) := by
    have : 0 < (x : ℝ) / (2 * (Real.log x) ^ 5) := by positivity
    linarith
  have hz_lt_y : zParam x < yParam x := by
    have hlt : Real.log (zParam x : ℝ) < Real.log (yParam x : ℝ) := by
      rw [hlogz]
      have : 6 * Real.log x ≤ (x : ℝ) / (2 * (Real.log x) ^ 5) := by
        have e : (x : ℝ) / (2 * (Real.log x) ^ 5) = ((x : ℝ) / (Real.log x) ^ 5) / 2 := by ring
        linarith
      have hstr : 6 * Real.log x < (x : ℝ) / (2 * (Real.log x) ^ 5) := by
        have e : (x : ℝ) / (2 * (Real.log x) ^ 5) = ((x : ℝ) / (Real.log x) ^ 5) / 2 := by ring
        nlinarith
      linarith
    have hz_pos : (0 : ℝ) < (zParam x : ℝ) := by
      simp only [zParam, Nat.cast_pow]; positivity
    exact_mod_cast (Real.log_lt_log_iff hz_pos hy_pos).mp hlt
  have hloglog_lo : (1 / 2 : ℝ) * Real.log x ≤
      Real.log (Real.log (yParam x : ℝ)) - Real.log (Real.log (zParam x : ℝ)) := by
    rw [← Real.log_div hlogy_pos.ne' hlogz_pos.ne']
    have hratio : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ) := by
      rw [le_div_iff₀ hlogz_pos, hlogz]
      have h1 : 6 * Real.log x * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) / (2 * (Real.log x) ^ 5) := by
        have e : (x : ℝ) / (2 * (Real.log x) ^ 5) = ((x : ℝ) / (Real.log x) ^ 5) / 2 := by ring
        nlinarith
      linarith
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hx_pos _) hratio
    rwa [Real.log_rpow hx_pos] at hlog
  have hloglog_hi : Real.log (Real.log (yParam x : ℝ)) - Real.log (Real.log (zParam x : ℝ)) ≤
      Real.log x := by
    rw [← Real.log_div hlogy_pos.ne' hlogz_pos.ne']
    apply Real.log_le_log (div_pos hlogy_pos hlogz_pos)
    rw [div_le_iff₀ hlogz_pos, hlogz]
    have h1 : (x : ℝ) / (Real.log x) ^ 5 ≤ (x : ℝ) := by
      rw [div_le_iff₀ (pow_pos hlog_pos 5)]
      have h2 : (1 : ℝ) ≤ (Real.log x) ^ 5 := one_le_pow₀ (by linarith)
      nlinarith
    nlinarith
  have hT_ge : Real.exp (x : ℝ) / 2 ≤ (TParam x : ℝ) := by
    have h1 : (2 : ℝ) ≤ Real.exp (x : ℝ) := by
      have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      linarith [Real.add_one_le_exp (x : ℝ)]
    have h2 := Nat.sub_one_lt_floor (Real.exp (x : ℝ))
    dsimp [TParam]
    linarith
  have hy_le_expx : (yParam x : ℝ) ≤ Real.exp (x : ℝ) := by
    refine hy_le_exp.trans (Real.exp_le_exp.mpr ?_)
    rw [div_le_iff₀ (pow_pos hlog_pos 5)]
    have h2 : (1 : ℝ) ≤ (Real.log x) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hx_le_z : x ≤ zParam x := by
    dsimp [zParam]
    exact Nat.le_self_pow (by norm_num) x
  refine ⟨hx16, hxN0.trans hx_le_z, hx16.trans hx_le_z, hlog2, hz_lt_y,
    hlogy_lower, hlogy_upper, hloglog_lo, hloglog_hi, hT_ge, hy_le_expx⟩

/-- Lemma 3.1 (Exceptional primes): bounding `∑_{p ∈ primes0, p ∣ Δ} 1/p`. -/
lemma lem_exceptional_primes {x k : ℕ} (hx : 16 ≤ x) (hk : k ≤ x)
    (s : Fin k → ℤ) (hs_inj : Function.Injective s)
    (hs_bound : ∀ i, ((s i).natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ))) :
    let pairs := Finset.univ.filter (fun pq : Fin k × Fin k => pq.1 < pq.2)
    let Δ : ℕ := ∏ pq ∈ pairs, (s pq.1 - s pq.2).natAbs
    0 < Δ ∧
    ∑ p ∈ (primes0 x).filter (fun p => p ∣ Δ), (1 : ℝ) / (p : ℝ) ≤
      4 * (x : ℝ) ^ 3 / ((zParam x : ℝ) * Real.log (zParam x : ℝ)) := by
  intro pairs Δ
  have hΔ_pos : 0 < Δ := by
    apply Finset.prod_pos
    intro pq hpq
    rw [Finset.mem_filter] at hpq
    exact Int.natAbs_pos.mpr (sub_ne_zero.mpr (fun h => ne_of_lt hpq.2 (hs_inj h)))
  refine ⟨hΔ_pos, ?_⟩
  set E := (primes0 x).filter (fun p => p ∣ Δ)
  have hE_prime : ∀ p ∈ E, p.Prime := fun p hp => prime_of_mem_primes0 (Finset.mem_filter.mp hp).1
  have hE_dvd : val E ∣ Δ := by
    dsimp [val]
    refine Finset.prod_primes_dvd Δ (fun p hp => (hE_prime p hp).prime) ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hE_log : ∑ p ∈ E, Real.log (p : ℝ) ≤ Real.log (Δ : ℝ) := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (hE_prime p hp).ne_zero)]
    have hle : (val E : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast Nat.le_of_dvd hΔ_pos hE_dvd
    simpa [val, Nat.cast_prod] using Real.log_le_log (by exact_mod_cast val_pos hE_prime) hle
  have hz_pos : (0 : ℝ) < zParam x := by
    dsimp [zParam]; positivity
  have hlogz_pos : 0 < Real.log (zParam x : ℝ) := by
    apply Real.log_pos
    have : 2 ≤ x ^ 6 := by
      have : 2 ≤ x := by omega
      exact this.trans (Nat.le_self_pow (by norm_num) x)
    exact_mod_cast this
  have hsum_le : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ Real.log (Δ : ℝ) / ((zParam x : ℝ) * Real.log (zParam x : ℝ)) := by
    rw [le_div_iff₀ (mul_pos hz_pos hlogz_pos), Finset.sum_mul]
    calc
      ∑ p ∈ E, (1 : ℝ) / (p : ℝ) * ((zParam x : ℝ) * Real.log (zParam x : ℝ))
          ≤ ∑ p ∈ E, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hgt : zParam x < p := gt_z_of_mem_primes0 (Finset.mem_filter.mp hp).1
        have hp_gt : (zParam x : ℝ) < (p : ℝ) := by exact_mod_cast hgt
        have hp_pos : (0 : ℝ) < p := hz_pos.trans hp_gt
        have hlog_le : Real.log (zParam x : ℝ) ≤ Real.log (p : ℝ) :=
          Real.log_le_log hz_pos hp_gt.le
        have h1 : (zParam x : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hp_pos).mpr hp_gt.le
        calc (1 : ℝ) / (p : ℝ) * ((zParam x : ℝ) * Real.log (zParam x : ℝ))
            = ((zParam x : ℝ) / (p : ℝ)) * Real.log (zParam x : ℝ) := by ring
          _ ≤ 1 * Real.log (p : ℝ) := mul_le_mul h1 hlog_le hlogz_pos.le zero_le_one
          _ = Real.log (p : ℝ) := one_mul _
      _ ≤ Real.log (Δ : ℝ) := hE_log
  have hΔ_log : Real.log (Δ : ℝ) ≤ 4 * (x : ℝ) ^ 3 := by
    have hprod_log : Real.log (Δ : ℝ) = ∑ pq ∈ pairs, Real.log ((s pq.1 - s pq.2).natAbs : ℝ) := by
      dsimp [Δ]
      rw [Nat.cast_prod, Real.log_prod]
      intro pq hpq
      rw [Finset.mem_filter] at hpq
      exact_mod_cast (Int.natAbs_pos.mpr (sub_ne_zero.mpr (fun h => ne_of_lt hpq.2 (hs_inj h)))).ne'
    rw [hprod_log]
    have hterm : ∀ pq ∈ pairs, Real.log ((s pq.1 - s pq.2).natAbs : ℝ) ≤ 6 * (x : ℝ) + Real.log 2 := by
      intro pq hpq
      rw [Finset.mem_filter] at hpq
      have hpos : 0 < ((s pq.1 - s pq.2).natAbs : ℝ) := by
        exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr (fun h => ne_of_lt hpq.2 (hs_inj h)))
      have htri : ((s pq.1 - s pq.2).natAbs : ℝ) ≤ 2 * Real.exp (6 * (x : ℝ)) := by
        have h1 : (s pq.1 - s pq.2).natAbs ≤ (s pq.1).natAbs + (s pq.2).natAbs :=
          Int.natAbs_sub_le _ _
        have h2 : ((s pq.1 - s pq.2).natAbs : ℝ) ≤ ((s pq.1).natAbs : ℝ) + ((s pq.2).natAbs : ℝ) := by
          exact_mod_cast h1
        linarith [hs_bound pq.1, hs_bound pq.2]
      calc Real.log ((s pq.1 - s pq.2).natAbs : ℝ)
          ≤ Real.log (2 * Real.exp (6 * (x : ℝ))) := Real.log_le_log hpos htri
        _ = Real.log 2 + Real.log (Real.exp (6 * (x : ℝ))) :=
            Real.log_mul (by norm_num) (Real.exp_pos _).ne'
        _ = 6 * (x : ℝ) + Real.log 2 := by rw [Real.log_exp]; ring
    have hcard : 2 * pairs.card ≤ k * k := by
      have hdisj : Disjoint pairs (Finset.univ.filter (fun pq : Fin k × Fin k => pq.2 < pq.1)) := by
        rw [Finset.disjoint_left]
        intro pq h1 h2
        rw [Finset.mem_filter] at h1 h2
        exact lt_asymm h1.2 h2.2
      have hsym : (Finset.univ.filter (fun pq : Fin k × Fin k => pq.2 < pq.1)).card = pairs.card := by
        refine Finset.card_bij (fun pq _ => (pq.2, pq.1)) ?_ ?_ ?_
        · intro pq hpq; rw [Finset.mem_filter] at hpq ⊢; exact ⟨Finset.mem_univ _, hpq.2⟩
        · intro pq₁ _ pq₂ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro pq hpq; rw [Finset.mem_filter] at hpq
          exact ⟨(pq.2, pq.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq.2⟩, rfl⟩
      have hunion : (pairs ∪ Finset.univ.filter (fun pq : Fin k × Fin k => pq.2 < pq.1)).card ≤
          (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj, hsym, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin] at hunion
      omega
    have hcardR : (pairs.card : ℝ) ≤ (x : ℝ) ^ 2 / 2 := by
      have h1 : 2 * (pairs.card : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hcard
      have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk
      nlinarith
    have hx16R : (16 : ℝ) ≤ x := by exact_mod_cast hx
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h6pos : 0 ≤ 6 * (x : ℝ) + Real.log 2 := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    calc
      ∑ pq ∈ pairs, Real.log ((s pq.1 - s pq.2).natAbs : ℝ)
          ≤ ∑ _pq ∈ pairs, (6 * (x : ℝ) + Real.log 2) := Finset.sum_le_sum hterm
      _ = (pairs.card : ℝ) * (6 * (x : ℝ) + Real.log 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((x : ℝ) ^ 2 / 2) * (6 * (x : ℝ) + Real.log 2) :=
          mul_le_mul_of_nonneg_right hcardR h6pos
      _ ≤ 4 * (x : ℝ) ^ 3 := by nlinarith
  exact hsum_le.trans (div_le_div_of_nonneg_right hΔ_log (mul_pos hz_pos hlogz_pos).le)

noncomputable def primesStar (x Δ : ℕ) : Finset ℕ :=
  (primes0 x).filter (fun p => ¬ p ∣ Δ)

lemma primesStar_subset (x Δ : ℕ) : primesStar x Δ ⊆ primes0 x :=
  Finset.filter_subset _ _

lemma prime_of_mem_primesStar {x Δ p : ℕ} (hp : p ∈ primesStar x Δ) : p.Prime :=
  prime_of_mem_primes0 (primesStar_subset x Δ hp)

lemma gt_z_of_mem_primesStar {x Δ p : ℕ} (hp : p ∈ primesStar x Δ) : zParam x < p :=
  gt_z_of_mem_primes0 (primesStar_subset x Δ hp)

lemma le_y_of_mem_primesStar {x Δ p : ℕ} (hp : p ∈ primesStar x Δ) : p ≤ yParam x :=
  le_y_of_mem_primes0 (primesStar_subset x Δ hp)

noncomputable def U0 (x : ℕ) : ℝ := ∑ t ∈ (primes0 x).powerset, 1 / phi t

noncomputable def B0 (x : ℕ) : ℝ :=
  ∑ t ∈ (primes0 x).powerset.erase ∅, 1 / (phi t * Real.log (val t : ℝ))

noncomputable def Bstar (x Δ : ℕ) : ℝ :=
  ∑ t ∈ (primesStar x Δ).powerset.erase ∅, 1 / (phi t * Real.log (val t : ℝ))

private lemma prod_sdiff_primesLE_inv_one_sub {z m : ℕ} (hzm : z ≤ m) :
    ∏ p ∈ m.primesLE \ z.primesLE, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ m.primesLE, (1 - 1 / (p : ℝ))⁻¹) / (∏ p ∈ z.primesLE, (1 - 1 / (p : ℝ))⁻¹) := by
  have hsub := Nat.primesLE_mono hzm
  have hne : (∏ p ∈ z.primesLE, (1 - 1 / (p : ℝ))⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    exact inv_ne_zero (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)).ne'
  rw [eq_div_iff hne, Finset.prod_sdiff hsub]

private lemma sum_powerset_log_val_div_phi (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ e ∈ S.powerset, Real.log (val e : ℝ) / phi e =
      (∑ e ∈ S.powerset, 1 / phi e) * ∑ q ∈ S, Real.log (q : ℝ) / (q : ℝ) := by
  have h1 : ∀ e ∈ S.powerset,
      Real.log (val e : ℝ) / phi e = ∑ q ∈ S, if q ∈ e then Real.log (q : ℝ) / phi e else 0 := by
    intro e he
    rw [Finset.mem_powerset] at he
    have hlog : Real.log (val e : ℝ) = ∑ q ∈ e, Real.log (q : ℝ) := by
      dsimp [val]
      rw [Nat.cast_prod, Real.log_prod]
      intro q hq
      exact_mod_cast (hS q (he hq)).ne_zero
    rw [hlog, Finset.sum_div, ← Finset.sum_filter]
    have hfilt : S.filter (fun q => q ∈ e) = e := by
      ext q
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hq => he hq
    rw [hfilt]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  have hpull : ∑ e ∈ S.powerset.filter (fun e => q ∈ e), Real.log (q : ℝ) / phi e =
      Real.log (q : ℝ) * ∑ e ∈ S.powerset.filter (fun e => q ∈ e), 1 / phi e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hpull, sum_powerset_filter_mem_inv_phi S hS hq]
  ring

set_option maxHeartbeats 800000 in
/-- Lemma 3.2 (Divisor-sum estimates): `U0 ≪ log y / log z` and `Bstar ≍ 1`. -/
lemma lem_divisor_sums :
    ∃ b_lo b_hi c_U : ℝ, 0 < b_lo ∧ 0 < b_hi ∧ 0 < c_U ∧
    ∃ X₁ : ℕ, 16 ≤ X₁ ∧ ∀ x : ℕ, X₁ ≤ x →
      U0 x ≤ c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) ∧
      ∀ (k : ℕ) (s : Fin k → ℤ), k ≤ x → Function.Injective s →
        (∀ i, ((s i).natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ))) →
        let pairs := Finset.univ.filter (fun pq : Fin k × Fin k => pq.1 < pq.2)
        let Δ : ℕ := ∏ pq ∈ pairs, (s pq.1 - s pq.2).natAbs
        b_lo ≤ Bstar x Δ ∧ Bstar x Δ ≤ b_hi := by
  obtain ⟨c₁, c₂, hc₁, hc₂, N₁, _, hprod⟩ := exists_mertens_prod_bounds
  obtain ⟨M, hM, N₂, _, hrecip⟩ := exists_mertens_recip_bounds
  let N₀ := max N₁ N₂
  let b0_lo := c₁ / (144 * c₂)
  let b0_hi := 2 * c₂ / (3 * c₁)
  let c_U := c₂ / c₁
  have hb0_lo : 0 < b0_lo := by dsimp [b0_lo]; positivity
  have hb0_hi : 0 < b0_hi := by dsimp [b0_hi]; positivity
  have hc_U : 0 < c_U := by dsimp [c_U]; positivity
  have hlog_ge : ∀ᶠ x : ℕ in atTop, 8 * M ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (8 * M)
  have hx_sq : ∀ᶠ x : ℕ in atTop, (8 * c_U / b0_lo) ≤ (x : ℝ) ^ 2 := by
    have ht : Tendsto (fun x : ℕ => (x : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop (8 * c_U / b0_lo)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp ((eventually_param_bounds N₀).and (hlog_ge.and hx_sq))
  refine ⟨b0_lo / 2, b0_hi, c_U, by positivity, hb0_hi, hc_U, max X₁ 16, le_max_right _ _, ?_⟩
  intro x hx
  obtain ⟨⟨hx16, hzN₀, hz16, hlog2, hz_lt_y, hlogy_lo, hlogy_hi, hll_lo, hll_hi, _, _⟩,
    hlogM, hx2⟩ := hX₁ x ((le_max_left _ _).trans hx)
  have hzN₁ : N₁ ≤ zParam x := (le_max_left N₁ N₂).trans hzN₀
  have hzN₂ : N₂ ≤ zParam x := (le_max_right N₁ N₂).trans hzN₀
  have hyN₁ : N₁ ≤ yParam x := hzN₁.trans hz_lt_y.le
  have hyN₂ : N₂ ≤ yParam x := hzN₂.trans hz_lt_y.le
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hlogz_eq : Real.log (zParam x : ℝ) = 6 * Real.log (x : ℝ) := by
    simp [zParam, Real.log_pow]
  have hlogz_pos : 0 < Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
  have hU0_eq : U0 x = ∏ p ∈ primes0 x, (1 - 1 / (p : ℝ))⁻¹ :=
    sum_powerset_inv_phi (primes0 x) (fun p hp => prime_of_mem_primes0 hp)
  have hU0_le : U0 x ≤ c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) := by
    rw [hU0_eq, primes0, prod_sdiff_primesLE_inv_one_sub hz_lt_y.le]
    have hnum := (hprod (yParam x) hyN₁).2
    have hden := (hprod (zParam x) hzN₁).1
    have hden_pos : 0 < c₁ * Real.log (zParam x : ℝ) := mul_pos hc₁ hlogz_pos
    calc
      (∏ p ∈ (yParam x).primesLE, (1 - 1 / (p : ℝ))⁻¹) /
          (∏ p ∈ (zParam x).primesLE, (1 - 1 / (p : ℝ))⁻¹)
          ≤ (c₂ * Real.log (yParam x : ℝ)) / (c₁ * Real.log (zParam x : ℝ)) :=
        div_le_div₀ (by positivity) hnum hden_pos hden
      _ = c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) := by
        dsimp [c_U]; ring
  refine ⟨hU0_le, ?_⟩
  intro k s hk hs_inj hs_bound pairs Δ
  -- Step 1: Bound B0 x from above and below via grouping by largest prime factor
  have hB0_group : B0 x = ∑ p ∈ primes0 x, (1 / ((p : ℝ) - 1)) *
      ∑ e ∈ ((primes0 x).filter (· < p)).powerset,
        1 / (phi e * Real.log ((p * val e : ℕ) : ℝ)) := by
    unfold B0
    rw [sum_powerset_erase_empty_by_max]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_powerset] at he
    have hpn : p ∉ e := fun hp => lt_irrefl p (Finset.mem_filter.mp (he hp)).2
    rw [phi_insert hpn, val_insert hpn, one_div, one_div, one_div, mul_inv, mul_inv]
    ring
  have hTp_bounds : ∀ p ∈ primes0 x,
      let P_lt := (primes0 x).filter (· < p)
      let T_p := ∑ e ∈ P_lt.powerset, 1 / (phi e * Real.log ((p * val e : ℕ) : ℝ))
      (c₁ / (6 * c₂)) / Real.log (zParam x : ℝ) ≤ T_p ∧
      T_p ≤ (c₂ / c₁) / Real.log (zParam x : ℝ) := by
    intro p hp P_lt T_p
    have hpP : p.Prime := prime_of_mem_primes0 hp
    have hp_gt_z : zParam x < p := gt_z_of_mem_primes0 hp
    have hp_le_y : p ≤ yParam x := le_y_of_mem_primes0 hp
    have hpN₁ : N₁ ≤ p := hzN₁.trans hp_gt_z.le
    have hp_ge4 : 4 ≤ p := by omega
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpP.one_lt)
    have hPlt_prime : ∀ q ∈ P_lt, q.Prime := fun q hq =>
      prime_of_mem_primes0 (Finset.mem_filter.mp hq).1
    have hPlt_ins : insert p P_lt = p.primesLE \ (zParam x).primesLE := by
      ext q
      simp only [Finset.mem_insert, P_lt, Finset.mem_filter, primes0, Finset.mem_sdiff,
        Nat.mem_primesLE]
      constructor
      · rintro (rfl | ⟨⟨⟨_, hqp⟩, hqz⟩, hlt⟩)
        · exact ⟨⟨le_rfl, hpP⟩, fun h => not_lt.mpr h.1 hp_gt_z⟩
        · exact ⟨⟨hlt.le, hqp⟩, hqz⟩
      · rintro ⟨⟨hqle, hqp⟩, hqz⟩
        rcases eq_or_lt_of_le hqle with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨⟨hqle.trans hp_le_y, hqp⟩, hqz⟩, hlt⟩
    have hpn_Plt : p ∉ P_lt := fun h => lt_irrefl p (Finset.mem_filter.mp h).2
    let V_p := ∑ e ∈ P_lt.powerset, 1 / phi e
    have hVp_eq : V_p = (1 - 1 / (p : ℝ)) *
        ((∏ q ∈ p.primesLE, (1 - 1 / (q : ℝ))⁻¹) /
         (∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹)) := by
      change ∑ e ∈ P_lt.powerset, 1 / phi e = _
      rw [sum_powerset_inv_phi P_lt hPlt_prime]
      have hprod_ins : ∏ q ∈ insert p P_lt, (1 - 1 / (q : ℝ))⁻¹ =
          (1 - 1 / (p : ℝ))⁻¹ * ∏ q ∈ P_lt, (1 - 1 / (q : ℝ))⁻¹ :=
        Finset.prod_insert hpn_Plt
      rw [hPlt_ins, prod_sdiff_primesLE_inv_one_sub hp_gt_z.le] at hprod_ins
      have h1sub_pos : 0 < 1 - 1 / (p : ℝ) :=
        sub_pos.mpr ((div_lt_one (by exact_mod_cast hpP.pos)).mpr (by exact_mod_cast hpP.one_lt))
      have hmul := congrArg (fun t => (1 - 1 / (p : ℝ)) * t) hprod_ins
      rw [← mul_assoc, mul_inv_cancel₀ h1sub_pos.ne', one_mul] at hmul
      exact hmul.symm
    have h1sub_ge : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpP.two_le
      have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    have h1sub_le : 1 - 1 / (p : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / p := by positivity
      linarith
    have hVp_lo : (c₁ / (2 * c₂)) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ)) ≤ V_p := by
      rw [hVp_eq]
      have hnum := (hprod p hpN₁).1
      have hden := (hprod (zParam x) hzN₁).2
      have hden_pos : 0 < ∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹ :=
        Finset.prod_pos fun q hq => inv_pos.mpr (sub_pos.mpr
          ((div_lt_one (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).pos)).mpr
            (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_lt)))
      have hdiv : (c₁ * Real.log (p : ℝ)) / (c₂ * Real.log (zParam x : ℝ)) ≤
          (∏ q ∈ p.primesLE, (1 - 1 / (q : ℝ))⁻¹) /
          (∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹) :=
        div_le_div₀ ((mul_nonneg hc₁.le hlogp_pos.le).trans hnum) hnum hden_pos hden
      calc
        (c₁ / (2 * c₂)) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ))
            = (1 / 2) * ((c₁ * Real.log (p : ℝ)) / (c₂ * Real.log (zParam x : ℝ))) := by ring
        _ ≤ (1 - 1 / (p : ℝ)) * ((∏ q ∈ p.primesLE, (1 - 1 / (q : ℝ))⁻¹) /
            (∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹)) :=
          mul_le_mul h1sub_ge hdiv (div_nonneg (mul_nonneg hc₁.le hlogp_pos.le)
            (mul_nonneg hc₂.le hlogz_pos.le)) (by linarith)
    have hVp_hi : V_p ≤ (c₂ / c₁) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ)) := by
      rw [hVp_eq]
      have hnum := (hprod p hpN₁).2
      have hden := (hprod (zParam x) hzN₁).1
      have hdiv : (∏ q ∈ p.primesLE, (1 - 1 / (q : ℝ))⁻¹) /
          (∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹) ≤
          (c₂ * Real.log (p : ℝ)) / (c₁ * Real.log (zParam x : ℝ)) :=
        div_le_div₀ (by positivity) hnum (mul_pos hc₁ hlogz_pos) hden
      calc
        (1 - 1 / (p : ℝ)) * ((∏ q ∈ p.primesLE, (1 - 1 / (q : ℝ))⁻¹) /
            (∏ q ∈ (zParam x).primesLE, (1 - 1 / (q : ℝ))⁻¹))
            ≤ 1 * ((c₂ * Real.log (p : ℝ)) / (c₁ * Real.log (zParam x : ℝ))) :=
          mul_le_mul h1sub_le hdiv (by
            apply div_nonneg <;> exact Finset.prod_nonneg fun q hq => inv_nonneg.mpr (sub_nonneg.mpr
              ((div_le_one (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).pos)).mpr
                (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le)))) zero_le_one
        _ = (c₂ / c₁) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ)) := by ring
    have hVp_pos : 0 < V_p := lt_of_lt_of_le (by positivity) hVp_lo
    -- Upper bound on T_p
    have hTp_hi : T_p ≤ (c₂ / c₁) / Real.log (zParam x : ℝ) := by
      have h1 : T_p ≤ V_p / Real.log (p : ℝ) := by
        dsimp [T_p, V_p]
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.mem_powerset] at he
        have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
        have hphi : 0 < phi e := phi_pos heP
        have hve : (1 : ℝ) ≤ (val e : ℝ) := by exact_mod_cast val_one_le heP
        have hple : (p : ℝ) ≤ ((p * val e : ℕ) : ℝ) := by
          push_cast; nlinarith [hpP.pos]
        have hlog_le : Real.log (p : ℝ) ≤ Real.log ((p * val e : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpP.pos) hple
        rw [div_div]
        exact one_div_le_one_div_of_le (mul_pos hphi hlogp_pos)
          (mul_le_mul_of_nonneg_left hlog_le hphi.le)
      calc T_p ≤ V_p / Real.log (p : ℝ) := h1
        _ ≤ ((c₂ / c₁) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ))) / Real.log (p : ℝ) :=
            div_le_div_of_nonneg_right hVp_hi hlogp_pos.le
        _ = (c₂ / c₁) / Real.log (zParam x : ℝ) := by field_simp
    -- Lower bound on T_p via Cauchy-Schwarz
    have hTp_lo : (c₁ / (6 * c₂)) / Real.log (zParam x : ℝ) ≤ T_p := by
      let L_p := ∑ e ∈ P_lt.powerset, Real.log ((p * val e : ℕ) : ℝ) / phi e
      have hCS : V_p ^ 2 ≤ T_p * L_p := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq P_lt.powerset
          (fun e => Real.sqrt (1 / (phi e * Real.log ((p * val e : ℕ) : ℝ))))
          (fun e => Real.sqrt (Real.log ((p * val e : ℕ) : ℝ) / phi e))
        have hLHS : ∑ e ∈ P_lt.powerset,
            Real.sqrt (1 / (phi e * Real.log ((p * val e : ℕ) : ℝ))) *
            Real.sqrt (Real.log ((p * val e : ℕ) : ℝ) / phi e) = V_p := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_powerset] at he
          have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
          have hphi : 0 < phi e := phi_pos heP
          have hlogpe : 0 < Real.log ((p * val e : ℕ) : ℝ) := by
            apply Real.log_pos
            have : 1 < p * val e := by nlinarith [hpP.one_lt, val_one_le heP]
            exact_mod_cast this
          rw [← Real.sqrt_mul (by positivity)]
          have e1 : 1 / (phi e * Real.log ((p * val e : ℕ) : ℝ)) *
              (Real.log ((p * val e : ℕ) : ℝ) / phi e) = (1 / phi e) ^ 2 := by
            field_simp
          rw [e1, Real.sqrt_sq (by positivity)]
        have hR1 : ∑ e ∈ P_lt.powerset,
            (Real.sqrt (1 / (phi e * Real.log ((p * val e : ℕ) : ℝ)))) ^ 2 = T_p := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_powerset] at he
          have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
          have hphi : 0 < phi e := phi_pos heP
          have hlogpe : 0 < Real.log ((p * val e : ℕ) : ℝ) := by
            apply Real.log_pos
            have : 1 < p * val e := by nlinarith [hpP.one_lt, val_one_le heP]
            exact_mod_cast this
          exact Real.sq_sqrt (by positivity)
        have hR2 : ∑ e ∈ P_lt.powerset,
            (Real.sqrt (Real.log ((p * val e : ℕ) : ℝ) / phi e)) ^ 2 = L_p := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_powerset] at he
          have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
          have hphi : 0 < phi e := phi_pos heP
          have hlogpe : 0 < Real.log ((p * val e : ℕ) : ℝ) := by
            apply Real.log_pos
            have : 1 < p * val e := by nlinarith [hpP.one_lt, val_one_le heP]
            exact_mod_cast this
          exact Real.sq_sqrt (by positivity)
        rwa [hLHS, hR1, hR2] at hcs
      have hLp_le : L_p ≤ 3 * Real.log (p : ℝ) * V_p := by
        have hsplit : L_p = Real.log (p : ℝ) * V_p +
            ∑ e ∈ P_lt.powerset, Real.log (val e : ℝ) / phi e := by
          dsimp [L_p, V_p]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_powerset] at he
          have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
          rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hpP.ne_zero)
            (by exact_mod_cast (val_pos heP).ne')]
          ring
        rw [hsplit, sum_powerset_log_val_div_phi P_lt hPlt_prime]
        have hPlt_sub : P_lt ⊆ p.primesLE := by
          intro q hq
          rw [Finset.mem_filter] at hq
          exact Nat.mem_primesLE.mpr ⟨hq.2.le, prime_of_mem_primes0 hq.1⟩
        have hsum_le : ∑ q ∈ P_lt, Real.log (q : ℝ) / (q : ℝ) ≤ 2 * Real.log (p : ℝ) := by
          have h1 : ∑ q ∈ P_lt, Real.log (q : ℝ) / (q : ℝ) ≤
              ∑ q ∈ p.primesLE, Real.log (q : ℝ) / (q : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hPlt_sub fun q hq _ =>
              div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le))
                (Nat.cast_nonneg q)
          have h2 := mertens_first_upper_explicit p hpP.one_le
          have h3 : Real.log 4 ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hp_ge4)
          linarith
        have hmul := mul_le_mul_of_nonneg_left hsum_le hVp_pos.le
        change Real.log (p : ℝ) * V_p + V_p * ∑ q ∈ P_lt, Real.log (q : ℝ) / (q : ℝ) ≤ _
        linarith
      have hTp_ge : V_p / (3 * Real.log (p : ℝ)) ≤ T_p := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : V_p * V_p ≤ T_p * (3 * Real.log (p : ℝ) * V_p) := by
          have hTp_nn : 0 ≤ T_p := Finset.sum_nonneg fun e he => by
            rw [Finset.mem_powerset] at he
            have heP : ∀ q ∈ e, q.Prime := fun q hq => hPlt_prime q (he hq)
            have hphi : 0 < phi e := phi_pos heP
            have hlogpe : 0 ≤ Real.log ((p * val e : ℕ) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast Nat.mul_pos hpP.pos (val_pos heP))
            positivity
          calc V_p * V_p = V_p ^ 2 := (sq V_p).symm
            _ ≤ T_p * L_p := hCS
            _ ≤ T_p * (3 * Real.log (p : ℝ) * V_p) := mul_le_mul_of_nonneg_left hLp_le hTp_nn
        nlinarith
      calc (c₁ / (6 * c₂)) / Real.log (zParam x : ℝ)
          = ((c₁ / (2 * c₂)) * (Real.log (p : ℝ) / Real.log (zParam x : ℝ))) /
            (3 * Real.log (p : ℝ)) := by field_simp; ring
        _ ≤ V_p / (3 * Real.log (p : ℝ)) := div_le_div_of_nonneg_right hVp_lo (by positivity)
        _ ≤ T_p := hTp_ge
    exact ⟨hTp_lo, hTp_hi⟩
  -- Step 2: Estimate ∑ p ∈ primes0 x, 1 / (p - 1)
  have hrecip_diff :
      (1 / 4 : ℝ) * Real.log (x : ℝ) ≤ ∑ p ∈ primes0 x, (1 : ℝ) / (p : ℝ) ∧
      ∑ p ∈ primes0 x, (1 : ℝ) / (p : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have hsum : ∑ p ∈ primes0 x, (1 : ℝ) / (p : ℝ) =
        (∑ p ∈ (yParam x).primesLE, (1 : ℝ) / p) - (∑ p ∈ (zParam x).primesLE, (1 : ℝ) / p) :=
      Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hz_lt_y.le)
    rw [hsum]
    have hy_r := abs_le.mp (hrecip (yParam x) hyN₂)
    have hz_r := abs_le.mp (hrecip (zParam x) hzN₂)
    constructor <;> linarith
  have hrecip_pred_lo : (1 / 4 : ℝ) * Real.log (x : ℝ) ≤ ∑ p ∈ primes0 x, 1 / ((p : ℝ) - 1) := by
    refine hrecip_diff.1.trans (Finset.sum_le_sum fun p hp => ?_)
    have hpP := prime_of_mem_primes0 hp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      linarith
    exact one_div_le_one_div_of_le hp1 (by linarith)
  have hrecip_pred_hi : ∑ p ∈ primes0 x, 1 / ((p : ℝ) - 1) ≤ 4 * Real.log (x : ℝ) := by
    have hle : ∑ p ∈ primes0 x, 1 / ((p : ℝ) - 1) ≤ 2 * ∑ p ∈ primes0 x, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpP := prime_of_mem_primes0 hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpP.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hp0 : (0 : ℝ) < p := by linarith
      rw [show 2 * ((1 : ℝ) / (p : ℝ)) = 2 / (p : ℝ) by ring, div_le_div_iff₀ hp1 hp0]
      linarith
    linarith [hrecip_diff.2]
  have hB0_lo : b0_lo ≤ B0 x := by
    rw [hB0_group]
    calc b0_lo = ((c₁ / (6 * c₂)) / Real.log (zParam x : ℝ)) * ((1 / 4 : ℝ) * Real.log (x : ℝ)) := by
          dsimp [b0_lo]; rw [hlogz_eq]; field_simp; ring
      _ ≤ ((c₁ / (6 * c₂)) / Real.log (zParam x : ℝ)) * ∑ p ∈ primes0 x, 1 / ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hrecip_pred_lo (by positivity)
      _ = ∑ p ∈ primes0 x, (1 / ((p : ℝ) - 1)) * ((c₁ / (6 * c₂)) / Real.log (zParam x : ℝ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ _ := Finset.sum_le_sum fun p hp => by
          have hpP := prime_of_mem_primes0 hp
          have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
            have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
            linarith
          exact mul_le_mul_of_nonneg_left (hTp_bounds p hp).1 (by positivity)
  have hB0_hi : B0 x ≤ b0_hi := by
    rw [hB0_group]
    calc _ ≤ ∑ p ∈ primes0 x, (1 / ((p : ℝ) - 1)) * ((c₂ / c₁) / Real.log (zParam x : ℝ)) :=
          Finset.sum_le_sum fun p hp => by
            have hpP := prime_of_mem_primes0 hp
            have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
              have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
              linarith
            exact mul_le_mul_of_nonneg_left (hTp_bounds p hp).2 (by positivity)
      _ = ((c₂ / c₁) / Real.log (zParam x : ℝ)) * ∑ p ∈ primes0 x, 1 / ((p : ℝ) - 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ ((c₂ / c₁) / Real.log (zParam x : ℝ)) * (4 * Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left hrecip_pred_hi (by positivity)
      _ = b0_hi := by
          dsimp [b0_hi]; rw [hlogz_eq]; field_simp; ring
  -- Step 3: Bound B0 x - Bstar x Δ
  have hsub_pow : (primesStar x Δ).powerset.erase ∅ ⊆ (primes0 x).powerset.erase ∅ :=
    Finset.erase_subset_erase ∅ (Finset.powerset_mono.mpr (primesStar_subset x Δ))
  have hterm_nn : ∀ t ∈ (primes0 x).powerset.erase ∅,
      0 ≤ 1 / (phi t * Real.log (val t : ℝ)) := by
    intro t ht
    have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
    have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
    have htP : ∀ q ∈ t, q.Prime := fun q hq => prime_of_mem_primes0 (hsub hq)
    have hphi := phi_pos htP
    obtain ⟨q, hq⟩ := hne
    have hval_gt : 1 < val t := by
      have hdvd : q ∣ val t := Finset.dvd_prod_of_mem _ hq
      have hqle : q ≤ val t := Nat.le_of_dvd (val_pos htP) hdvd
      exact lt_of_lt_of_le (htP q hq).one_lt hqle
    have hlog : 0 < Real.log (val t : ℝ) := Real.log_pos (by exact_mod_cast hval_gt)
    positivity
  have hBstar_le : Bstar x Δ ≤ B0 x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_pow fun t ht _ => hterm_nn t ht
  set E := (primes0 x).filter (fun p => p ∣ Δ)
  have hdiff_le : B0 x - Bstar x Δ ≤
      (U0 x / Real.log (zParam x : ℝ)) * ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := by
    unfold B0 Bstar
    rw [← Finset.sum_sdiff_eq_sub hsub_pow]
    have hcover : (primes0 x).powerset.erase ∅ \ (primesStar x Δ).powerset.erase ∅ ⊆
        E.biUnion (fun p => (primes0 x).powerset.filter (fun t => p ∈ t)) := by
      intro t ht
      rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_powerset, Finset.mem_erase,
        Finset.mem_powerset] at ht
      have hnot : ¬ t ⊆ primesStar x Δ := fun hsub => ht.2 ⟨ht.1.1, hsub⟩
      rw [Finset.not_subset] at hnot
      obtain ⟨p, hpt, hpnot⟩ := hnot
      have hp0 : p ∈ primes0 x := ht.1.2 hpt
      have hpdvd : p ∣ Δ := by
        by_contra hnd
        exact hpnot (Finset.mem_filter.mpr ⟨hp0, hnd⟩)
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨hp0, hpdvd⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht.1.2, hpt⟩⟩
    have hstep1 : ∑ t ∈ (primes0 x).powerset.erase ∅ \ (primesStar x Δ).powerset.erase ∅,
        1 / (phi t * Real.log (val t : ℝ)) ≤
        ∑ t ∈ (primes0 x).powerset.erase ∅ \ (primesStar x Δ).powerset.erase ∅,
          (1 / Real.log (zParam x : ℝ)) * (1 / phi t) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht1 := (Finset.mem_sdiff.mp ht).1
      have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht1).1
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht1).2
      have htP : ∀ q ∈ t, q.Prime := fun q hq => prime_of_mem_primes0 (hsub hq)
      obtain ⟨q, hq⟩ := hne
      have hqz : zParam x < val t :=
        lt_of_lt_of_le (gt_z_of_mem_primes0 (hsub hq))
          (Nat.le_of_dvd (val_pos htP) (Finset.dvd_prod_of_mem _ hq))
      have hlog_le : Real.log (zParam x : ℝ) ≤ Real.log (val t : ℝ) :=
        Real.log_le_log (by dsimp [zParam]; positivity) (by exact_mod_cast hqz.le)
      have hphi := phi_pos htP
      rw [show (1 / Real.log (zParam x : ℝ)) * (1 / phi t) =
          1 / (phi t * Real.log (zParam x : ℝ)) by ring]
      exact one_div_le_one_div_of_le (mul_pos hphi hlogz_pos)
        (mul_le_mul_of_nonneg_left hlog_le hphi.le)
    have hstep2 : ∑ t ∈ (primes0 x).powerset.erase ∅ \ (primesStar x Δ).powerset.erase ∅,
        (1 / Real.log (zParam x : ℝ)) * (1 / phi t) ≤
        ∑ t ∈ E.biUnion (fun p => (primes0 x).powerset.filter (fun t => p ∈ t)),
          (1 / Real.log (zParam x : ℝ)) * (1 / phi t) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover fun t ht _ => by
        obtain ⟨_, _, ht2⟩ := Finset.mem_biUnion.mp ht
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp ht2).1
        have hphi := phi_pos (fun q hq => prime_of_mem_primes0 (hsub hq))
        positivity
    have hstep3 : ∑ t ∈ E.biUnion (fun p => (primes0 x).powerset.filter (fun t => p ∈ t)),
        (1 / Real.log (zParam x : ℝ)) * (1 / phi t) ≤
        ∑ p ∈ E, ∑ t ∈ (primes0 x).powerset.filter (fun t => p ∈ t),
          (1 / Real.log (zParam x : ℝ)) * (1 / phi t) :=
      sum_biUnion_le E _ _ fun t ht => by
        obtain ⟨_, _, ht2⟩ := Finset.mem_biUnion.mp ht
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp ht2).1
        have hphi := phi_pos (fun q hq => prime_of_mem_primes0 (hsub hq))
        positivity
    have hstep4 : ∑ p ∈ E, ∑ t ∈ (primes0 x).powerset.filter (fun t => p ∈ t),
        (1 / Real.log (zParam x : ℝ)) * (1 / phi t) =
        (U0 x / Real.log (zParam x : ℝ)) * ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mul_sum,
        sum_powerset_filter_mem_inv_phi (primes0 x) (fun q hq => prime_of_mem_primes0 hq)
          (Finset.mem_filter.mp hp).1]
      dsimp [U0]
      ring
    exact (hstep1.trans hstep2).trans (hstep3.trans_eq hstep4)
  have hE_bound := (lem_exceptional_primes hx16 hk s hs_inj hs_bound).2
  have hdiff_small : B0 x - Bstar x Δ ≤ b0_lo / 2 := by
    have h1 : (U0 x / Real.log (zParam x : ℝ)) ≤ c_U * (x : ℝ) := by
      have hlogy_x : Real.log (yParam x : ℝ) ≤ (x : ℝ) := by
        refine hlogy_hi.trans ?_
        rw [div_le_iff₀ (pow_pos hlogx_pos 5)]
        have : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ 5 := one_le_pow₀ (by linarith)
        nlinarith
      have hlogz_ge1 : (1 : ℝ) ≤ Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
      calc U0 x / Real.log (zParam x : ℝ)
          ≤ (c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ))) / Real.log (zParam x : ℝ) :=
            div_le_div_of_nonneg_right hU0_le hlogz_pos.le
        _ = c_U * Real.log (yParam x : ℝ) / (Real.log (zParam x : ℝ)) ^ 2 := by ring
        _ ≤ c_U * (x : ℝ) / 1 := by
            apply div_le_div₀ (by positivity)
            · exact mul_le_mul_of_nonneg_left hlogy_x hc_U.le
            · norm_num
            · nlinarith
        _ = c_U * (x : ℝ) := div_one _
    have h2 : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ 4 / (x : ℝ) ^ 3 := by
      have hlogz_ge1 : (1 : ℝ) ≤ Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
      have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have hz_cast : (zParam x : ℝ) = (x : ℝ) ^ 6 := by simp [zParam]
      calc ∑ p ∈ E, (1 : ℝ) / (p : ℝ)
          ≤ 4 * (x : ℝ) ^ 3 / ((zParam x : ℝ) * Real.log (zParam x : ℝ)) := hE_bound
        _ ≤ 4 * (x : ℝ) ^ 3 / ((x : ℝ) ^ 6 * 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            calc (x : ℝ) ^ 6 * 1 = (zParam x : ℝ) * 1 := by rw [hz_cast]
              _ ≤ (zParam x : ℝ) * Real.log (zParam x : ℝ) :=
                  mul_le_mul_of_nonneg_left hlogz_ge1 (by rw [hz_cast]; positivity)
        _ = 4 / (x : ℝ) ^ 3 := by field_simp
    have h3 : B0 x - Bstar x Δ ≤ 4 * c_U / (x : ℝ) ^ 2 := by
      have hE_nn : 0 ≤ ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
      calc B0 x - Bstar x Δ
          ≤ (U0 x / Real.log (zParam x : ℝ)) * ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := hdiff_le
        _ ≤ (c_U * (x : ℝ)) * (4 / (x : ℝ) ^ 3) := mul_le_mul h1 h2 hE_nn (by positivity)
        _ = 4 * c_U / (x : ℝ) ^ 2 := by
            have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
            field_simp
    have h4 : 4 * c_U / (x : ℝ) ^ 2 ≤ b0_lo / 2 := by
      have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      rw [div_le_iff₀ (sq_pos_of_pos hx_pos)]
      have hmul := (div_le_iff₀ hb0_lo).mp hx2
      linarith
    exact h3.trans h4
  exact ⟨by linarith, hBstar_le.trans hB0_hi⟩

/- Coefficient definitions and Lemma 3.3 (Coefficient bounds) -/

noncomputable def aCoeff (x Δ : ℕ) (t : Finset ℕ) : ℝ :=
  if t = ∅ then 1 else -1 / (Bstar x Δ * Real.log (val t : ℝ))

noncomputable def Aγ (x Δ : ℕ) (γ : ℝ) : ℝ :=
  ∑ t ∈ (primesStar x Δ).powerset, (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ γ) / phi t

noncomputable def A0 (x Δ : ℕ) : ℝ := Aγ x Δ 0

set_option maxHeartbeats 800000 in
lemma lem_coefficient_bounds {b_lo c_U : ℝ} (hb_lo : 0 < b_lo) (hc_U : 0 < c_U) :
    ∃ C_tilt C_1 C_p : ℝ, 0 < C_tilt ∧ 1 ≤ C_1 ∧ 0 < C_p ∧
    ∃ X₂ : ℕ, 16 ≤ X₂ ∧ ∀ x : ℕ, X₂ ≤ x →
      U0 x ≤ c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) →
      ∀ Δ : ℕ, b_lo ≤ Bstar x Δ →
        (∑ t ∈ (primesStar x Δ).powerset, aCoeff x Δ t / phi t = 0) ∧
        (∀ t ∈ (primesStar x Δ).powerset, |aCoeff x Δ t| ≤ 1) ∧
        (1 ≤ A0 x Δ) ∧
        (∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * betaParam x →
          ∑ t ∈ (primesStar x Δ).powerset.erase ∅,
            |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ C_tilt ∧
          Aγ x Δ γ ≤ A0 x Δ + C_1 * γ) ∧
        (∀ p ∈ primesStar x Δ,
          ∑ t ∈ (primesStar x Δ).powerset.filter (fun t => p ∈ t),
            |aCoeff x Δ t| / phi t ≤ C_p / (p : ℝ)) := by
  let C_Ugamma := Real.exp (4 * Real.exp 2) * c_U
  let C_tilt := Real.exp 2 + C_Ugamma / b_lo
  let C_1 := max 1 (C_tilt / b_lo)
  let C_p := 2 * (1 / b_lo + 1)
  have hlog_big : ∀ᶠ x : ℕ in atTop, 1 / b_lo ≤ 6 * Real.log (x : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 6)).eventually_ge_atTop (1 / b_lo)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp ((eventually_param_bounds 16).and hlog_big)
  refine ⟨C_tilt, C_1, C_p, by dsimp [C_tilt, C_Ugamma]; positivity, le_max_left _ _,
    by dsimp [C_p]; positivity, max X₂ 16, le_max_right _ _, ?_⟩
  intro x hx hU0_le Δ hB_lo
  obtain ⟨⟨hx16, _, hz16, hlog2, hz_lt_y, hlogy_lo, hlogy_hi, _, _, _, _⟩,
    hlog_blo⟩ := hX₂ x ((le_max_left _ _).trans hx)
  have hB_pos : 0 < Bstar x Δ := hb_lo.trans_le hB_lo
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hlogz_eq : Real.log (zParam x : ℝ) = 6 * Real.log (x : ℝ) := by
    simp [zParam, Real.log_pow]
  have hlogz_pos : 0 < Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
  have hlogy_pos : 0 < Real.log (yParam x : ℝ) := by
    have : 0 < (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 5) := by positivity
    linarith
  have hPstar_prime : ∀ p ∈ primesStar x Δ, p.Prime := fun p hp => prime_of_mem_primesStar hp
  -- Helper: for nonempty t ⊆ primesStar, val t > zParam x
  have hval_gt_z : ∀ t ∈ (primesStar x Δ).powerset.erase ∅, zParam x < val t := by
    intro t ht
    have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
    have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
    obtain ⟨q, hq⟩ := hne
    exact lt_of_lt_of_le (gt_z_of_mem_primesStar (hsub hq))
      (Nat.le_of_dvd (val_pos (fun p hp => hPstar_prime p (hsub hp)))
        (Finset.dvd_prod_of_mem _ hq))
  have hlog_val_ge_z : ∀ t ∈ (primesStar x Δ).powerset.erase ∅,
      Real.log (zParam x : ℝ) ≤ Real.log (val t : ℝ) := by
    intro t ht
    exact Real.log_le_log (by dsimp [zParam]; positivity) (by exact_mod_cast (hval_gt_z t ht).le)
  -- (1) Exact cancellation
  have hcancel : ∑ t ∈ (primesStar x Δ).powerset, aCoeff x Δ t / phi t = 0 := by
    have hmem : ∅ ∈ (primesStar x Δ).powerset := Finset.empty_mem_powerset _
    rw [← Finset.add_sum_erase _ _ hmem]
    have h0 : aCoeff x Δ ∅ / phi ∅ = 1 := by simp [aCoeff, phi_empty]
    have hrest : ∑ t ∈ (primesStar x Δ).powerset.erase ∅, aCoeff x Δ t / phi t =
        -(1 / Bstar x Δ) * Bstar x Δ := by
      change ∑ t ∈ (primesStar x Δ).powerset.erase ∅, aCoeff x Δ t / phi t =
        -(1 / Bstar x Δ) * ∑ t ∈ (primesStar x Δ).powerset.erase ∅,
          1 / (phi t * Real.log (val t : ℝ))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hne : t ≠ ∅ := (Finset.mem_erase.mp ht).1
      simp only [aCoeff, hne, ↓reduceIte, div_eq_mul_inv, mul_inv]
      ring
    rw [h0, hrest]
    field_simp [hB_pos.ne']
    ring
  -- (2) |a(t)| ≤ 1
  have habs_le : ∀ t ∈ (primesStar x Δ).powerset, |aCoeff x Δ t| ≤ 1 := by
    intro t ht
    by_cases h0 : t = ∅
    · simp [aCoeff, h0]
    · have ht' : t ∈ (primesStar x Δ).powerset.erase ∅ := Finset.mem_erase.mpr ⟨h0, ht⟩
      have hlogt : Real.log (zParam x : ℝ) ≤ Real.log (val t : ℝ) := hlog_val_ge_z t ht'
      have hlogt_pos : 0 < Real.log (val t : ℝ) := hlogz_pos.trans_le hlogt
      simp only [aCoeff, h0, ↓reduceIte, abs_div, abs_neg, abs_one,
        abs_of_pos (mul_pos hB_pos hlogt_pos)]
      rw [div_le_one (mul_pos hB_pos hlogt_pos)]
      have h1 : 1 ≤ b_lo * (6 * Real.log (x : ℝ)) := (div_le_iff₀ hb_lo).mp hlog_blo |>.trans_eq (mul_comm _ _)
      have h2 : b_lo * (6 * Real.log (x : ℝ)) ≤ Bstar x Δ * Real.log (val t : ℝ) := by
        rw [← hlogz_eq]
        exact mul_le_mul hB_lo hlogt hlogz_pos.le hB_pos.le
      linarith
  -- (3) 1 ≤ A0 x Δ
  have hA0_ge1 : 1 ≤ A0 x Δ := by
    unfold A0 Aγ
    have hmem : ∅ ∈ (primesStar x Δ).powerset := Finset.empty_mem_powerset _
    have hle := Finset.single_le_sum (f := fun t => (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ (0 : ℝ)) / phi t)
      (fun t ht => by
        have hsub := Finset.mem_powerset.mp ht
        have hphi := phi_pos (fun p hp => hPstar_prime p (hsub hp))
        positivity) hmem
    simpa [aCoeff, val_empty, phi_empty] using hle
  -- (4) Tilt bounds for 0 ≤ γ ≤ 2 * betaParam x
  have htilt : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * betaParam x →
      ∑ t ∈ (primesStar x Δ).powerset.erase ∅,
        |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ C_tilt ∧
      Aγ x Δ γ ≤ A0 x Δ + C_1 * γ := by
    intro γ hγ0 hγhi
    -- First bound U_γ = ∑ t ∈ (primes0 x).powerset, (val t)^γ / phi t
    let Uγ := ∑ t ∈ (primes0 x).powerset, ((val t : ℝ) ^ γ) / phi t
    have hUγ_le : Uγ ≤ C_Ugamma * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) := by
      have hUγ_prod : Uγ = ∏ p ∈ primes0 x, (1 + ((p : ℝ) ^ γ) / ((p : ℝ) - 1)) :=
        sum_powerset_rpow_div_phi (primes0 x) (fun p hp => prime_of_mem_primes0 hp) γ
      have hU0_prod : U0 x = ∏ p ∈ primes0 x, (1 + 1 / ((p : ℝ) - 1)) := by
        rw [U0, sum_powerset_inv_phi (primes0 x) (fun p hp => prime_of_mem_primes0 hp)]
        apply Finset.prod_congr rfl
        intro p hp
        have hpP := prime_of_mem_primes0 hp
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
          linarith
        field_simp; ring
      have hratio : Uγ = U0 x * ∏ p ∈ primes0 x, (1 + ((p : ℝ) ^ γ - 1) / (p : ℝ)) := by
        rw [hUγ_prod, hU0_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        have hpP := prime_of_mem_primes0 hp
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
          linarith
        field_simp; ring
      have hnn : ∀ p ∈ primes0 x, 0 ≤ ((p : ℝ) ^ γ - 1) / (p : ℝ) := by
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primes0 hp).one_le
        exact div_nonneg (sub_nonneg.mpr (Real.one_le_rpow hp1 hγ0)) (by linarith)
      have hprod_bound : ∏ p ∈ primes0 x, (1 + ((p : ℝ) ^ γ - 1) / (p : ℝ)) ≤
          Real.exp (4 * Real.exp 2) := by
        refine (prod_one_add_le_exp_sum _ _ hnn).trans (Real.exp_le_exp.mpr ?_)
        have hterm : ∀ p ∈ primes0 x,
            ((p : ℝ) ^ γ - 1) / (p : ℝ) ≤ (Real.exp 2 * γ) * (Real.log (p : ℝ) / (p : ℝ)) := by
          intro p hp
          have hpP := prime_of_mem_primes0 hp
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpP.pos
          have hp_le_y : (p : ℝ) ≤ (yParam x : ℝ) := by exact_mod_cast le_y_of_mem_primes0 hp
          have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpP.one_le)
          have hlogp_le : Real.log (p : ℝ) ≤ Real.log (yParam x : ℝ) :=
            Real.log_le_log hp_pos hp_le_y
          have hγlog : γ * Real.log (p : ℝ) ≤ 2 := by
            have h1 : γ * Real.log (p : ℝ) ≤ (2 * betaParam x) * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) :=
              mul_le_mul hγhi (hlogp_le.trans hlogy_hi) hlogp_nn (by dsimp [betaParam]; positivity)
            have h2 : (2 * betaParam x) * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) = 2 := by
              dsimp [betaParam]
              have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
              field_simp
            linarith
          have hexp_le : (p : ℝ) ^ γ - 1 ≤ Real.exp 2 * (γ * Real.log (p : ℝ)) := by
            rw [Real.rpow_def_of_pos hp_pos, mul_comm (Real.log (p : ℝ)) γ]
            exact exp_sub_one_le_of_le (mul_nonneg hγ0 hlogp_nn) hγlog
          calc ((p : ℝ) ^ γ - 1) / (p : ℝ)
              ≤ (Real.exp 2 * (γ * Real.log (p : ℝ))) / (p : ℝ) :=
                div_le_div_of_nonneg_right hexp_le hp_pos.le
            _ = (Real.exp 2 * γ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
        calc ∑ p ∈ primes0 x, ((p : ℝ) ^ γ - 1) / (p : ℝ)
            ≤ ∑ p ∈ primes0 x, (Real.exp 2 * γ) * (Real.log (p : ℝ) / (p : ℝ)) :=
              Finset.sum_le_sum hterm
          _ = (Real.exp 2 * γ) * ∑ p ∈ primes0 x, Real.log (p : ℝ) / (p : ℝ) := by
              rw [← Finset.mul_sum]
          _ ≤ (Real.exp 2 * γ) * (2 * Real.log (yParam x : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hsub : primes0 x ⊆ (yParam x).primesLE := Finset.sdiff_subset
              have h1 : ∑ p ∈ primes0 x, Real.log (p : ℝ) / (p : ℝ) ≤
                  ∑ p ∈ (yParam x).primesLE, Real.log (p : ℝ) / (p : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
                  div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
                    (Nat.cast_nonneg p)
              have h2 := mertens_first_upper_explicit (yParam x) (by omega)
              have h3 : Real.log 4 ≤ Real.log (yParam x : ℝ) :=
                Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ yParam x))
              linarith
          _ ≤ 4 * Real.exp 2 := by
              have hγy : γ * Real.log (yParam x : ℝ) ≤ 2 := by
                have h1 := mul_le_mul hγhi hlogy_hi hlogy_pos.le (by dsimp [betaParam]; positivity)
                have h2 : (2 * betaParam x) * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) = 2 := by
                  dsimp [betaParam]
                  have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
                  field_simp
                linarith
              nlinarith [Real.exp_pos 2]
      rw [hratio]
      have hU0_nn : 0 ≤ U0 x := Finset.sum_nonneg fun t ht => by
        have hphi := phi_pos (fun p hp => prime_of_mem_primes0 (Finset.mem_powerset.mp ht hp))
        positivity
      calc U0 x * ∏ p ∈ primes0 x, (1 + ((p : ℝ) ^ γ - 1) / (p : ℝ))
          ≤ (c_U * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ))) * Real.exp (4 * Real.exp 2) :=
            mul_le_mul hU0_le hprod_bound (Finset.prod_nonneg fun p hp => by linarith [hnn p hp])
              (by positivity)
        _ = C_Ugamma * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ)) := by
            dsimp [C_Ugamma]; ring
    -- Split ∑ |a(t)| (val t)^γ / phi t into val t ≤ y and val t > y
    set S_ne := (primesStar x Δ).powerset.erase ∅
    have hsplit_sum :
        ∑ t ∈ S_ne, |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t =
        (∑ t ∈ S_ne.filter (fun t => val t ≤ yParam x), |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t) +
        (∑ t ∈ S_ne.filter (fun t => ¬ val t ≤ yParam x), |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t) :=
      (Finset.sum_filter_add_sum_filter_not S_ne (fun t => val t ≤ yParam x) _).symm
    have hpart1 : ∑ t ∈ S_ne.filter (fun t => val t ≤ yParam x),
        |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ Real.exp 2 := by
      have h1 : ∀ t ∈ S_ne.filter (fun t => val t ≤ yParam x),
          |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤
            (Real.exp 2 / Bstar x Δ) * (1 / (phi t * Real.log (val t : ℝ))) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have hne : t ≠ ∅ := (Finset.mem_erase.mp ht.1).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht.1).2
        have htP : ∀ p ∈ t, p.Prime := fun p hp => hPstar_prime p (hsub hp)
        have hphi := phi_pos htP
        have hvt_pos : (0 : ℝ) < val t := by exact_mod_cast val_pos htP
        have hlogt_pos : 0 < Real.log (val t : ℝ) := hlogz_pos.trans_le (hlog_val_ge_z t ht.1)
        have hpow_le : (val t : ℝ) ^ γ ≤ Real.exp 2 := by
          rw [Real.rpow_def_of_pos hvt_pos]
          apply Real.exp_le_exp.mpr
          have hlogt_le : Real.log (val t : ℝ) ≤ Real.log (yParam x : ℝ) :=
            Real.log_le_log hvt_pos (by exact_mod_cast ht.2)
          have h1 := mul_le_mul hγhi (hlogt_le.trans hlogy_hi) hlogt_pos.le
            (by dsimp [betaParam]; positivity)
          have h2 : (2 * betaParam x) * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) = 2 := by
            dsimp [betaParam]
            have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
            field_simp
          linarith
        simp only [aCoeff, hne, ↓reduceIte, abs_div, abs_neg, abs_one,
          abs_of_pos (mul_pos hB_pos hlogt_pos)]
        have e : (Real.exp 2 / Bstar x Δ) * (1 / (phi t * Real.log (val t : ℝ))) =
            1 / (Bstar x Δ * Real.log (val t : ℝ)) * Real.exp 2 / phi t := by ring
        rw [e]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le (by positivity)) hphi.le
      calc ∑ t ∈ S_ne.filter (fun t => val t ≤ yParam x),
            |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t
          ≤ ∑ t ∈ S_ne.filter (fun t => val t ≤ yParam x),
              (Real.exp 2 / Bstar x Δ) * (1 / (phi t * Real.log (val t : ℝ))) :=
            Finset.sum_le_sum h1
        _ ≤ ∑ t ∈ S_ne, (Real.exp 2 / Bstar x Δ) * (1 / (phi t * Real.log (val t : ℝ))) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun t ht _ => by
              have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
              have hphi := phi_pos (fun p hp => hPstar_prime p (hsub hp))
              have hlogt := hlogz_pos.trans_le (hlog_val_ge_z t ht)
              positivity
        _ = (Real.exp 2 / Bstar x Δ) * Bstar x Δ := by rw [← Finset.mul_sum]; rfl
        _ = Real.exp 2 := by field_simp [hB_pos.ne']
    have hpart2 : ∑ t ∈ S_ne.filter (fun t => ¬ val t ≤ yParam x),
        |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ C_Ugamma / b_lo := by
      have h1 : ∀ t ∈ S_ne.filter (fun t => ¬ val t ≤ yParam x),
          |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤
            (1 / (Bstar x Δ * Real.log (yParam x : ℝ))) * (((val t : ℝ) ^ γ) / phi t) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have hne : t ≠ ∅ := (Finset.mem_erase.mp ht.1).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht.1).2
        have htP : ∀ p ∈ t, p.Prime := fun p hp => hPstar_prime p (hsub hp)
        have hphi := phi_pos htP
        have hlogt_ge : Real.log (yParam x : ℝ) ≤ Real.log (val t : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < yParam x))
            (by exact_mod_cast (Nat.lt_of_not_ge ht.2).le)
        have hlogt_pos : 0 < Real.log (val t : ℝ) := hlogy_pos.trans_le hlogt_ge
        simp only [aCoeff, hne, ↓reduceIte, abs_div, abs_neg, abs_one,
          abs_of_pos (mul_pos hB_pos hlogt_pos)]
        have e : (1 / (Bstar x Δ * Real.log (yParam x : ℝ))) * (((val t : ℝ) ^ γ) / phi t) =
            (1 / (Bstar x Δ * Real.log (yParam x : ℝ))) * ((val t : ℝ) ^ γ) / phi t := by ring
        rw [e]
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hphi.le
        exact one_div_le_one_div_of_le (mul_pos hB_pos hlogy_pos)
          (mul_le_mul_of_nonneg_left hlogt_ge hB_pos.le)
      have hsub0 : S_ne.filter (fun t => ¬ val t ≤ yParam x) ⊆ (primes0 x).powerset :=
        (Finset.filter_subset _ _).trans ((Finset.erase_subset _ _).trans
          (Finset.powerset_mono.mpr (primesStar_subset x Δ)))
      calc ∑ t ∈ S_ne.filter (fun t => ¬ val t ≤ yParam x),
            |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t
          ≤ ∑ t ∈ S_ne.filter (fun t => ¬ val t ≤ yParam x),
              (1 / (Bstar x Δ * Real.log (yParam x : ℝ))) * (((val t : ℝ) ^ γ) / phi t) :=
            Finset.sum_le_sum h1
        _ ≤ ∑ t ∈ (primes0 x).powerset,
              (1 / (Bstar x Δ * Real.log (yParam x : ℝ))) * (((val t : ℝ) ^ γ) / phi t) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub0 fun t ht _ => by
              have hphi := phi_pos (fun p hp => prime_of_mem_primes0 (Finset.mem_powerset.mp ht hp))
              positivity
        _ = Uγ / (Bstar x Δ * Real.log (yParam x : ℝ)) := by
            rw [← Finset.mul_sum]; dsimp [Uγ]; ring
        _ ≤ (C_Ugamma * (Real.log (yParam x : ℝ) / Real.log (zParam x : ℝ))) /
            (Bstar x Δ * Real.log (yParam x : ℝ)) :=
            div_le_div_of_nonneg_right hUγ_le (mul_pos hB_pos hlogy_pos).le
        _ = C_Ugamma / (Bstar x Δ * Real.log (zParam x : ℝ)) := by
            field_simp [hlogy_pos.ne', hlogz_pos.ne', hB_pos.ne']
        _ ≤ C_Ugamma / (b_lo * 1) := by
            apply div_le_div_of_nonneg_left (by dsimp [C_Ugamma]; positivity) (by positivity)
            have hlogz_ge1 : (1 : ℝ) ≤ Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
            exact mul_le_mul hB_lo hlogz_ge1 zero_le_one hB_pos.le
        _ = C_Ugamma / b_lo := by rw [mul_one]
    have hsum_tilt : ∑ t ∈ S_ne, |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ C_tilt := by
      rw [hsplit_sum]; dsimp [C_tilt]; linarith
    -- Now bound Aγ - A0
    have hA_diff : Aγ x Δ γ - A0 x Δ ≤ C_1 * γ := by
      unfold A0 Aγ
      rw [← Finset.sum_sub_distrib]
      have hmem : ∅ ∈ (primesStar x Δ).powerset := Finset.empty_mem_powerset _
      rw [← Finset.add_sum_erase _ _ hmem]
      have h0 : (aCoeff x Δ ∅) ^ 2 * ((val ∅ : ℝ) ^ γ) / phi ∅ -
          (aCoeff x Δ ∅) ^ 2 * ((val ∅ : ℝ) ^ (0 : ℝ)) / phi ∅ = 0 := by
        simp [val_empty, phi_empty]
      rw [h0, zero_add]
      have hterm : ∀ t ∈ S_ne,
          (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ γ) / phi t -
          (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ (0 : ℝ)) / phi t ≤
          (γ / Bstar x Δ) * (|aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t) := by
        intro t ht
        have hne : t ≠ ∅ := (Finset.mem_erase.mp ht).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
        have htP : ∀ p ∈ t, p.Prime := fun p hp => hPstar_prime p (hsub hp)
        have hphi := phi_pos htP
        have hvt_pos : (0 : ℝ) < val t := by exact_mod_cast val_pos htP
        have hlogt_pos : 0 < Real.log (val t : ℝ) := hlogz_pos.trans_le (hlog_val_ge_z t ht)
        have hexp_bound : (val t : ℝ) ^ γ - 1 ≤ γ * Real.log (val t : ℝ) * ((val t : ℝ) ^ γ) := by
          rw [Real.rpow_def_of_pos hvt_pos, mul_comm (Real.log (val t : ℝ)) γ]
          exact exp_sub_one_le_mul_exp (mul_nonneg hγ0 hlogt_pos.le)
        have hsq : (aCoeff x Δ t) ^ 2 * Real.log (val t : ℝ) = |aCoeff x Δ t| / Bstar x Δ := by
          simp only [aCoeff, hne, ↓reduceIte, abs_div, abs_neg, abs_one,
            abs_of_pos (mul_pos hB_pos hlogt_pos)]
          field_simp [hB_pos.ne', hlogt_pos.ne']
        calc (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ γ) / phi t -
              (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ (0 : ℝ)) / phi t
            = (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ γ - 1) / phi t := by
                rw [Real.rpow_zero]; ring
          _ ≤ (aCoeff x Δ t) ^ 2 * (γ * Real.log (val t : ℝ) * ((val t : ℝ) ^ γ)) / phi t :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hexp_bound (sq_nonneg _)) hphi.le
          _ = γ * ((aCoeff x Δ t) ^ 2 * Real.log (val t : ℝ)) * ((val t : ℝ) ^ γ) / phi t := by ring
          _ = γ * (|aCoeff x Δ t| / Bstar x Δ) * ((val t : ℝ) ^ γ) / phi t := by rw [hsq]
          _ = (γ / Bstar x Δ) * (|aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t) := by ring
      calc ∑ t ∈ S_ne,
            ((aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ γ) / phi t -
             (aCoeff x Δ t) ^ 2 * ((val t : ℝ) ^ (0 : ℝ)) / phi t)
          ≤ ∑ t ∈ S_ne, (γ / Bstar x Δ) * (|aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t) :=
            Finset.sum_le_sum hterm
        _ = (γ / Bstar x Δ) * ∑ t ∈ S_ne, |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t := by
            rw [← Finset.mul_sum]
        _ ≤ (γ / b_lo) * C_tilt := by
            have h1 : γ / Bstar x Δ ≤ γ / b_lo :=
              div_le_div_of_nonneg_left hγ0 hb_lo hB_lo
            have hnn : 0 ≤ ∑ t ∈ S_ne, |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t :=
              Finset.sum_nonneg fun t ht =>
                div_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                  (phi_pos (fun p hp => hPstar_prime p (Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2 hp))).le
            exact mul_le_mul h1 hsum_tilt hnn (div_nonneg hγ0 hb_lo.le)
        _ = (C_tilt / b_lo) * γ := by ring
        _ ≤ C_1 * γ := mul_le_mul_of_nonneg_right (le_max_right _ _) hγ0
    exact ⟨hsum_tilt, by linarith⟩
  -- (5) Prime-divisibility sum bound
  have hprime_sum : ∀ p ∈ primesStar x Δ,
      ∑ t ∈ (primesStar x Δ).powerset.filter (fun t => p ∈ t),
        |aCoeff x Δ t| / phi t ≤ C_p / (p : ℝ) := by
    intro p hp
    have hpP := hPstar_prime p hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      linarith
    have hlogp_ge_z : Real.log (zParam x : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by dsimp [zParam]; positivity) (by exact_mod_cast (gt_z_of_mem_primesStar hp).le)
    have hlogp_pos : 0 < Real.log (p : ℝ) := hlogz_pos.trans_le hlogp_ge_z
    have hbij : ∑ t ∈ (primesStar x Δ).powerset.filter (fun t => p ∈ t),
        |aCoeff x Δ t| / phi t =
        ∑ e ∈ ((primesStar x Δ).erase p).powerset,
          |aCoeff x Δ (insert p e)| / phi (insert p e) := by
      refine Finset.sum_bij (fun t _ => t.erase p) ?_ ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_powerset] at ht
        rw [Finset.mem_powerset]
        exact Finset.erase_subset_erase p ht.1
      · intro t₁ ht₁ t₂ ht₂ h
        rw [Finset.mem_filter] at ht₁ ht₂
        rw [← Finset.insert_erase ht₁.2, ← Finset.insert_erase ht₂.2, h]
      · intro e he
        rw [Finset.mem_powerset] at he
        refine ⟨insert p e, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.insert_subset_iff.mpr ⟨hp, he.trans (Finset.erase_subset p _)⟩,
            Finset.mem_insert_self p e⟩
        · exact Finset.erase_insert (fun hp' => (Finset.mem_erase.mp (he hp')).1 rfl)
      · intro t ht
        rw [Finset.mem_filter] at ht
        rw [Finset.insert_erase ht.2]
    rw [hbij]
    have hmem0 : ∅ ∈ ((primesStar x Δ).erase p).powerset := Finset.empty_mem_powerset _
    rw [← Finset.add_sum_erase _ _ hmem0]
    have h0 : |aCoeff x Δ (insert p ∅)| / phi (insert p ∅) =
        1 / (Bstar x Δ * ((p : ℝ) - 1) * Real.log (p : ℝ)) := by
      have hne : insert p ∅ ≠ ∅ := Finset.insert_ne_empty p ∅
      have hval : val (insert p ∅) = p := by simp [val]
      have hphi : phi (insert p ∅) = (p : ℝ) - 1 := by simp [phi]
      simp only [aCoeff, hne, ↓reduceIte, hval, hphi, abs_div, abs_neg, abs_one,
        abs_of_pos (mul_pos hB_pos hlogp_pos)]
      field_simp [hB_pos.ne', hp1.ne', hlogp_pos.ne']
    have hrest : ∑ e ∈ ((primesStar x Δ).erase p).powerset.erase ∅,
        |aCoeff x Δ (insert p e)| / phi (insert p e) ≤
        1 / ((p : ℝ) - 1) := by
      have hstep : ∀ e ∈ ((primesStar x Δ).erase p).powerset.erase ∅,
          |aCoeff x Δ (insert p e)| / phi (insert p e) ≤
            (1 / (Bstar x Δ * ((p : ℝ) - 1))) * (1 / (phi e * Real.log (val e : ℝ))) := by
        intro e he
        have he_ne : e ≠ ∅ := (Finset.mem_erase.mp he).1
        have he_sub : e ⊆ (primesStar x Δ).erase p := Finset.mem_powerset.mp (Finset.mem_erase.mp he).2
        have hpn : p ∉ e := fun hp' => (Finset.mem_erase.mp (he_sub hp')).1 rfl
        have he_star : e ⊆ primesStar x Δ := he_sub.trans (Finset.erase_subset p _)
        have heP : ∀ q ∈ e, q.Prime := fun q hq => hPstar_prime q (he_star hq)
        have hphi_e := phi_pos heP
        have hve_pos : (0 : ℝ) < val e := by exact_mod_cast val_pos heP
        have hloge_pos : 0 < Real.log (val e : ℝ) :=
          hlogz_pos.trans_le (hlog_val_ge_z e (Finset.mem_erase.mpr ⟨he_ne, Finset.mem_powerset.mpr he_star⟩))
        have hlogpe_ge : Real.log (val e : ℝ) ≤ Real.log (val (insert p e) : ℝ) := by
          rw [val_insert hpn]
          apply Real.log_le_log hve_pos
          push_cast
          nlinarith [hpP.one_le]
        have hlogpe_pos : 0 < Real.log (val (insert p e) : ℝ) := hloge_pos.trans_le hlogpe_ge
        have hins_ne : insert p e ≠ ∅ := Finset.insert_ne_empty p e
        simp only [aCoeff, hins_ne, ↓reduceIte, abs_div, abs_neg, abs_one,
          abs_of_pos (mul_pos hB_pos hlogpe_pos)]
        rw [phi_insert hpn]
        have e1 : 1 / (Bstar x Δ * Real.log (val (insert p e) : ℝ)) / (((p : ℝ) - 1) * phi e) =
            1 / (Bstar x Δ * ((p : ℝ) - 1) * phi e * Real.log (val (insert p e) : ℝ)) := by
          field_simp [hB_pos.ne', hp1.ne', hphi_e.ne', hlogpe_pos.ne']
        have e2 : 1 / (Bstar x Δ * ((p : ℝ) - 1)) * (1 / (phi e * Real.log (val e : ℝ))) =
            1 / (Bstar x Δ * ((p : ℝ) - 1) * phi e * Real.log (val e : ℝ)) := by
          field_simp [hB_pos.ne', hp1.ne', hphi_e.ne', hloge_pos.ne']
        rw [e1, e2]
        exact one_div_le_one_div_of_le
          (mul_pos (mul_pos (mul_pos hB_pos hp1) hphi_e) hloge_pos)
          (mul_le_mul_of_nonneg_left hlogpe_ge (mul_pos (mul_pos hB_pos hp1) hphi_e).le)
      have hsub_er : ((primesStar x Δ).erase p).powerset.erase ∅ ⊆
          (primesStar x Δ).powerset.erase ∅ :=
        Finset.erase_subset_erase ∅ (Finset.powerset_mono.mpr (Finset.erase_subset p _))
      calc ∑ e ∈ ((primesStar x Δ).erase p).powerset.erase ∅,
            |aCoeff x Δ (insert p e)| / phi (insert p e)
          ≤ ∑ e ∈ ((primesStar x Δ).erase p).powerset.erase ∅,
              (1 / (Bstar x Δ * ((p : ℝ) - 1))) * (1 / (phi e * Real.log (val e : ℝ))) :=
            Finset.sum_le_sum hstep
        _ ≤ ∑ e ∈ (primesStar x Δ).powerset.erase ∅,
              (1 / (Bstar x Δ * ((p : ℝ) - 1))) * (1 / (phi e * Real.log (val e : ℝ))) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_er fun e he _ =>
              mul_nonneg (div_nonneg zero_le_one (mul_nonneg hB_pos.le hp1.le))
                (div_nonneg zero_le_one (mul_nonneg
                  (phi_pos (fun q hq => hPstar_prime q (Finset.mem_powerset.mp (Finset.mem_erase.mp he).2 hq))).le
                  (hlogz_pos.trans_le (hlog_val_ge_z e he)).le))
        _ = (1 / (Bstar x Δ * ((p : ℝ) - 1))) * Bstar x Δ := by rw [← Finset.mul_sum]; rfl
        _ = 1 / ((p : ℝ) - 1) := by field_simp [hB_pos.ne', hp1.ne']
    rw [h0]
    have h0_le : 1 / (Bstar x Δ * ((p : ℝ) - 1) * Real.log (p : ℝ)) ≤
        (1 / b_lo) * (1 / ((p : ℝ) - 1)) := by
      have hlogp_ge1 : (1 : ℝ) ≤ Real.log (p : ℝ) := by
        have : (1 : ℝ) ≤ Real.log (zParam x : ℝ) := by rw [hlogz_eq]; linarith
        linarith
      have e3 : (1 / b_lo) * (1 / ((p : ℝ) - 1)) = 1 / (b_lo * ((p : ℝ) - 1) * 1) := by
        field_simp [hb_lo.ne', hp1.ne']
      rw [e3]
      exact one_div_le_one_div_of_le (mul_pos (mul_pos hb_lo hp1) zero_lt_one)
        (mul_le_mul (mul_le_mul_of_nonneg_right hB_lo hp1.le) hlogp_ge1 zero_le_one
          (mul_pos hB_pos hp1).le)
    have hpred_le : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpP.two_le
      rw [div_le_div_iff₀ hp1 hp_pos]
      linarith
    calc 1 / (Bstar x Δ * ((p : ℝ) - 1) * Real.log (p : ℝ)) +
          ∑ e ∈ ((primesStar x Δ).erase p).powerset.erase ∅,
            |aCoeff x Δ (insert p e)| / phi (insert p e)
        ≤ (1 / b_lo + 1) * (1 / ((p : ℝ) - 1)) := by linarith
      _ ≤ (1 / b_lo + 1) * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hpred_le (add_nonneg (div_nonneg zero_le_one hb_lo.le) zero_le_one)
      _ = C_p / (p : ℝ) := by dsimp [C_p]; ring
  exact ⟨hcancel, habs_le, hA0_ge1, htilt, hprime_sum⟩

/- ## Part 5: Section 3.3 - CRT Independence and Local Moments -/

noncomputable def avg (M : ℕ) (F : ℕ → ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ t ∈ Finset.range M, F t

lemma avg_add (M : ℕ) (F G : ℕ → ℝ) :
    avg M (fun t => F t + G t) = avg M F + avg M G := by
  simp only [avg, Finset.sum_add_distrib, mul_add]

lemma avg_sub (M : ℕ) (F G : ℕ → ℝ) :
    avg M (fun t => F t - G t) = avg M F - avg M G := by
  simp only [avg, Finset.sum_sub_distrib, mul_sub]

lemma avg_const_mul (M : ℕ) (c : ℝ) (F : ℕ → ℝ) :
    avg M (fun t => c * F t) = c * avg M F := by
  simp only [avg, ← Finset.mul_sum]; ring

lemma avg_sum {ι : Type*} (M : ℕ) (s : Finset ι) (F : ι → ℕ → ℝ) :
    avg M (fun t => ∑ i ∈ s, F i t) = ∑ i ∈ s, avg M (F i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma avg_zero (M : ℕ) : avg M (fun _ => 0) = 0 := by
  simp [avg]

lemma sum_range_mul_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (f g : ℕ → ℝ) (hf : ∀ t, f (t % a) = f t) (hg : ∀ t, g (t % b) = g t) :
    ∑ t ∈ Finset.range (a * b), f t * g t =
      (∑ x ∈ Finset.range a, f x) * (∑ y ∈ Finset.range b, g y) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij (fun t _ => (t % a, t % b)) ?_ ?_ ?_ ?_
  · intro t _
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt t ha),
      Finset.mem_range.mpr (Nat.mod_lt t hb)⟩
  · intro t₁ ht₁ t₂ ht₂ h
    have ha_eq : t₁ % a = t₂ % a := congrArg Prod.fst h
    have hb_eq : t₁ % b = t₂ % b := congrArg Prod.snd h
    have hmod : t₁ ≡ t₂ [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨ha_eq, hb_eq⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp ht₁),
      Nat.mod_eq_of_lt (Finset.mem_range.mp ht₂)] at hmod
    exact hmod
  · intro xy hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    have hxa : xy.1 < a := Finset.mem_range.mp hx
    have hyb : xy.2 < b := Finset.mem_range.mp hy
    let c := Nat.chineseRemainder hcop xy.1 xy.2
    refine ⟨c.val % (a * b), Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos ha hb)), ?_⟩
    apply Prod.ext
    · have h1 : c.val % (a * b) % a = c.val % a := Nat.mod_mod_of_dvd c.val (dvd_mul_right a b)
      rw [h1, show c.val % a = xy.1 % a from c.property.1, Nat.mod_eq_of_lt hxa]
    · have h2 : c.val % (a * b) % b = c.val % b := Nat.mod_mod_of_dvd c.val (dvd_mul_left b a)
      rw [h2, show c.val % b = xy.2 % b from c.property.2, Nat.mod_eq_of_lt hyb]
  · intro t _
    rw [hf t, hg t]

lemma avg_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ℕ → ℕ → ℝ) (hper : ∀ p ∈ S, ∀ t, f p (t % p) = f p t) :
    avg (val S) (fun t => ∏ p ∈ S, f p t) = ∏ p ∈ S, avg p (f p) := by
  induction S using Finset.induction_on with
  | empty => simp [avg, val_empty]
  | insert q S' hq ih =>
    have hqP : q.Prime := hS q (Finset.mem_insert_self q S')
    have hS' : ∀ p ∈ S', p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hper' : ∀ p ∈ S', ∀ t, f p (t % p) = f p t :=
      fun p hp => hper p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (val S') := by
      refine hqP.coprime_iff_not_dvd.mpr ?_
      intro hdvd
      exact hq ((mem_iff_dvd_val hS' hqP).mpr hdvd)
    have hper_prod : ∀ t, (∏ p ∈ S', f p (t % val S')) = ∏ p ∈ S', f p t := by
      intro t
      apply Finset.prod_congr rfl
      intro p hp
      have hp_dvd : p ∣ val S' := Finset.dvd_prod_of_mem _ hp
      rw [← hper' p hp (t % val S'), Nat.mod_mod_of_dvd t hp_dvd, hper' p hp t]
    rw [val_insert hq, Finset.prod_insert hq, ← ih hS' hper']
    unfold avg
    have hsum : ∑ t ∈ Finset.range (q * val S'), ∏ p ∈ insert q S', f p t =
        (∑ x ∈ Finset.range q, f q x) * (∑ y ∈ Finset.range (val S'), ∏ p ∈ S', f p y) := by
      have hcongr : ∑ t ∈ Finset.range (q * val S'), ∏ p ∈ insert q S', f p t =
          ∑ t ∈ Finset.range (q * val S'), f q t * ∏ p ∈ S', f p t :=
        Finset.sum_congr rfl fun t _ => Finset.prod_insert hq
      rw [hcongr]
      exact sum_range_mul_of_coprime hqP.pos (val_pos hS') hcop
        (f q) (fun t => ∏ p ∈ S', f p t) (hper q (Finset.mem_insert_self q S')) hper_prod
    rw [hsum]
    push_cast
    ring

def Lform {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k) (t : ℕ) : ℤ :=
  b + (Q : ℤ) * (t : ℤ) + s i

noncomputable def psi {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k) (p t : ℕ) : ℝ :=
  if (p : ℤ) ∣ Lform Q b s i t then -1 else 1 / ((p : ℝ) - 1)

noncomputable def psiProd {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k)
    (r : Finset ℕ) (t : ℕ) : ℝ :=
  ∏ p ∈ r, psi Q b s i p t

lemma dvd_Lform_mod_iff {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k) (p t : ℕ) :
    (p : ℤ) ∣ Lform Q b s i (t % p) ↔ (p : ℤ) ∣ Lform Q b s i t := by
  have hdiff : Lform Q b s i t - Lform Q b s i (t % p) =
      (Q : ℤ) * ((p : ℤ) * ((t / p : ℕ) : ℤ)) := by
    unfold Lform
    have hdiv : (t : ℤ) = (p : ℤ) * ((t / p : ℕ) : ℤ) + ((t % p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod t p).symm
    rw [hdiv]; ring
  have hdvd : (p : ℤ) ∣ Lform Q b s i t - Lform Q b s i (t % p) :=
    ⟨(Q : ℤ) * ((t / p : ℕ) : ℤ), by linarith⟩
  exact ⟨fun h => by
    have := dvd_add h hdvd
    rwa [add_sub_cancel] at this,
    fun h => by
    have := dvd_sub h hdvd
    rwa [sub_sub_cancel] at this⟩

lemma psi_mod {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k) (p t : ℕ) :
    psi Q b s i p (t % p) = psi Q b s i p t := by
  simp only [psi, dvd_Lform_mod_iff]

lemma exists_unique_root_Lform {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k)
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p Q) :
    ∃ r ∈ Finset.range p, (p : ℤ) ∣ Lform Q b s i r ∧
      ∀ t ∈ Finset.range p, (p : ℤ) ∣ Lform Q b s i t → t = r := by
  have hbez : (p : ℤ) * Nat.gcdA p Q + (Q : ℤ) * Nat.gcdB p Q = 1 := by
    have h := Nat.gcd_eq_gcd_ab p Q
    rw [hcop.gcd_eq_one] at h
    exact_mod_cast h.symm
  have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  let rZ : ℤ := (-(b + s i) * Nat.gcdB p Q) % (p : ℤ)
  have hrZ_nn : 0 ≤ rZ := Int.emod_nonneg _ hp_pos.ne'
  have hrZ_lt : rZ < (p : ℤ) := Int.emod_lt_of_pos _ hp_pos
  let r : ℕ := rZ.toNat
  have hr_cast : (r : ℤ) = rZ := Int.toNat_of_nonneg hrZ_nn
  have hr_lt : r < p := by omega
  have hr_dvd : (p : ℤ) ∣ Lform Q b s i r := by
    unfold Lform
    rw [hr_cast]
    have hmod_dvd : (p : ℤ) ∣ (-(b + s i) * Nat.gcdB p Q) - rZ := by
      refine ⟨(-(b + s i) * Nat.gcdB p Q) / (p : ℤ), ?_⟩
      have := Int.mul_ediv_add_emod (-(b + s i) * Nat.gcdB p Q) (p : ℤ)
      dsimp [rZ]; linarith
    have h1 : b + (Q : ℤ) * (-(b + s i) * Nat.gcdB p Q) + s i =
        (p : ℤ) * ((b + s i) * Nat.gcdA p Q) := by
      have hmul : (Q : ℤ) * Nat.gcdB p Q = 1 - (p : ℤ) * Nat.gcdA p Q := by linarith
      calc b + (Q : ℤ) * (-(b + s i) * Nat.gcdB p Q) + s i
          = (b + s i) * (1 - (Q : ℤ) * Nat.gcdB p Q) := by ring
        _ = (b + s i) * ((p : ℤ) * Nat.gcdA p Q) := by rw [hmul]; ring
        _ = (p : ℤ) * ((b + s i) * Nat.gcdA p Q) := by ring
    have h2 : (p : ℤ) ∣ b + (Q : ℤ) * (-(b + s i) * Nat.gcdB p Q) + s i :=
      ⟨(b + s i) * Nat.gcdA p Q, h1⟩
    have h3 : (b + (Q : ℤ) * (-(b + s i) * Nat.gcdB p Q) + s i) -
        (b + (Q : ℤ) * rZ + s i) = (Q : ℤ) * ((-(b + s i) * Nat.gcdB p Q) - rZ) := by ring
    have h4 : (p : ℤ) ∣ (b + (Q : ℤ) * (-(b + s i) * Nat.gcdB p Q) + s i) -
        (b + (Q : ℤ) * rZ + s i) := by
      rw [h3]; exact dvd_mul_of_dvd_right hmod_dvd _
    have := dvd_sub h2 h4
    rwa [sub_sub_cancel] at this
  refine ⟨r, Finset.mem_range.mpr hr_lt, hr_dvd, ?_⟩
  intro t ht ht_dvd
  have ht_lt : t < p := Finset.mem_range.mp ht
  have hsub : (p : ℤ) ∣ (Q : ℤ) * ((t : ℤ) - (r : ℤ)) := by
    have e : (Q : ℤ) * ((t : ℤ) - (r : ℤ)) = Lform Q b s i t - Lform Q b s i r := by
      unfold Lform; ring
    rw [e]
    exact dvd_sub ht_dvd hr_dvd
  have hcopZ : IsCoprime (p : ℤ) (Q : ℤ) := ⟨Nat.gcdA p Q, Nat.gcdB p Q, by linarith⟩
  have htr_dvd : (p : ℤ) ∣ (t : ℤ) - (r : ℤ) := hcopZ.dvd_of_dvd_mul_left hsub
  obtain ⟨m, hm⟩ := htr_dvd
  have hm0 : m = 0 := by nlinarith
  have htr0 : (t : ℤ) - (r : ℤ) = 0 := by rw [hm, hm0, mul_zero]
  omega

lemma lem_local_moments {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p Q) :
    (∀ i : Fin k, avg p (psi Q b s i p) = 0) ∧
    (∀ i : Fin k, avg p (fun t => (psi Q b s i p t) ^ 2) = 1 / ((p : ℝ) - 1)) ∧
    (∀ i j : Fin k, ¬ (p : ℤ) ∣ (s i - s j) →
      avg p (fun t => psi Q b s i p t * psi Q b s j p t) = -1 / ((p : ℝ) - 1) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hmean : ∀ i : Fin k, avg p (psi Q b s i p) = 0 := by
    intro i
    obtain ⟨r, hr, hr_dvd, hr_uniq⟩ := exists_unique_root_Lform Q b s i hp hcop
    unfold avg
    rw [← Finset.add_sum_erase _ _ hr]
    have hr_val : psi Q b s i p r = -1 := by simp [psi, hr_dvd]
    have hrest : ∑ t ∈ (Finset.range p).erase r, psi Q b s i p t =
        ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) := by
      have hcongr : ∑ t ∈ (Finset.range p).erase r, psi Q b s i p t =
          ∑ _t ∈ (Finset.range p).erase r, (1 / ((p : ℝ) - 1)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hne : t ≠ r := (Finset.mem_erase.mp ht).1
        have hnd : ¬ (p : ℤ) ∣ Lform Q b s i t := fun hd =>
          hne (hr_uniq t (Finset.mem_erase.mp ht).2 hd)
        simp [psi, hnd]
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem hr, Finset.card_range, nsmul_eq_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hr_val, hrest]
    field_simp [hp0, hp1]
    ring
  have hsq : ∀ i : Fin k, avg p (fun t => (psi Q b s i p t) ^ 2) = 1 / ((p : ℝ) - 1) := by
    intro i
    obtain ⟨r, hr, hr_dvd, hr_uniq⟩ := exists_unique_root_Lform Q b s i hp hcop
    unfold avg
    rw [← Finset.add_sum_erase _ _ hr]
    have hr_val : (psi Q b s i p r) ^ 2 = 1 := by simp [psi, hr_dvd]
    have hrest : ∑ t ∈ (Finset.range p).erase r, (psi Q b s i p t) ^ 2 =
        ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) ^ 2 := by
      have hcongr : ∑ t ∈ (Finset.range p).erase r, (psi Q b s i p t) ^ 2 =
          ∑ _t ∈ (Finset.range p).erase r, (1 / ((p : ℝ) - 1)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        have hne : t ≠ r := (Finset.mem_erase.mp ht).1
        have hnd : ¬ (p : ℤ) ∣ Lform Q b s i t := fun hd =>
          hne (hr_uniq t (Finset.mem_erase.mp ht).2 hd)
        simp [psi, hnd]
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem hr, Finset.card_range, nsmul_eq_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hr_val, hrest]
    field_simp [hp0, hp1]
    ring
  have hcross : ∀ i j : Fin k, ¬ (p : ℤ) ∣ (s i - s j) →
      avg p (fun t => psi Q b s i p t * psi Q b s j p t) = -1 / ((p : ℝ) - 1) ^ 2 := by
    intro i j hnd_diff
    obtain ⟨ri, hri, hri_dvd, hri_uniq⟩ := exists_unique_root_Lform Q b s i hp hcop
    obtain ⟨rj, hrj, hrj_dvd, hrj_uniq⟩ := exists_unique_root_Lform Q b s j hp hcop
    have hne_r : ri ≠ rj := by
      intro heq; subst heq
      apply hnd_diff
      have e : s i - s j = Lform Q b s i ri - Lform Q b s j ri := by unfold Lform; ring
      rw [e]; exact dvd_sub hri_dvd hrj_dvd
    have hrj_er : rj ∈ (Finset.range p).erase ri := Finset.mem_erase.mpr ⟨hne_r.symm, hrj⟩
    unfold avg
    rw [← Finset.add_sum_erase _ _ hri, ← Finset.add_sum_erase _ _ hrj_er]
    have h1 : psi Q b s i p ri * psi Q b s j p ri = -1 / ((p : ℝ) - 1) := by
      have hnd : ¬ (p : ℤ) ∣ Lform Q b s j ri := fun hd => hne_r (hrj_uniq ri hri hd)
      simp [psi, hri_dvd, hnd]; ring
    have h2 : psi Q b s i p rj * psi Q b s j p rj = -1 / ((p : ℝ) - 1) := by
      have hnd : ¬ (p : ℤ) ∣ Lform Q b s i rj := fun hd => hne_r.symm (hri_uniq rj hrj hd)
      simp [psi, hrj_dvd, hnd]; ring
    have hrest : ∑ t ∈ ((Finset.range p).erase ri).erase rj, psi Q b s i p t * psi Q b s j p t =
        ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ 2 := by
      have hcongr : ∑ t ∈ ((Finset.range p).erase ri).erase rj, psi Q b s i p t * psi Q b s j p t =
          ∑ _t ∈ ((Finset.range p).erase ri).erase rj, (1 / ((p : ℝ) - 1)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        have hne2 : t ≠ rj := (Finset.mem_erase.mp ht).1
        have ht1 := (Finset.mem_erase.mp ht).2
        have hne1 : t ≠ ri := (Finset.mem_erase.mp ht1).1
        have htr := (Finset.mem_erase.mp ht1).2
        have hndi : ¬ (p : ℤ) ∣ Lform Q b s i t := fun hd => hne1 (hri_uniq t htr hd)
        have hndj : ¬ (p : ℤ) ∣ Lform Q b s j t := fun hd => hne2 (hrj_uniq t htr hd)
        simp [psi, hndi, hndj, sq]
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem hrj_er,
        Finset.card_erase_of_mem hri, Finset.card_range, nsmul_eq_mul]
      have hp2 : 2 ≤ p := hp.two_le
      have hcast : ((p - 1 - 1 : ℕ) : ℝ) = (p : ℝ) - 2 := by
        have : p - 1 - 1 = p - 2 := by omega
        rw [this, Nat.cast_sub hp2]; norm_num
      rw [hcast]
    rw [h1, h2, hrest]
    field_simp [hp0, hp1]
    ring
  exact ⟨hmean, hsq, hcross⟩

/- ## Part 6: Tuple set Dset, Union Bijection, and Lemma 3.5 (Gram Estimate) -/

open scoped Classical in
noncomputable def Dset (Pstar : Finset ℕ) (D : ℝ) (k : ℕ) : Finset (Fin k → Finset ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Pstar.powerset)).filter
    (fun r => (∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j)) ∧ ((∏ i : Fin k, val (r i) : ℕ) : ℝ) ≤ D)

def unionOf {k : ℕ} (r : Fin k → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion r

lemma mem_Dset_iff {Pstar : Finset ℕ} {D : ℝ} {k : ℕ} {r : Fin k → Finset ℕ} :
    r ∈ Dset Pstar D k ↔
      (∀ i, r i ⊆ Pstar) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j)) ∧
      ((∏ i : Fin k, val (r i) : ℕ) : ℝ) ≤ D := by
  classical
  simp only [Dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_powerset]

lemma unionOf_subset {Pstar : Finset ℕ} {D : ℝ} {k : ℕ} {r : Fin k → Finset ℕ}
    (hr : r ∈ Dset Pstar D k) : unionOf r ⊆ Pstar := by
  intro p hp
  obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
  exact (mem_Dset_iff.mp hr).1 i hpi

lemma val_unionOf {k : ℕ} {r : Fin k → Finset ℕ}
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j)) :
    val (unionOf r) = ∏ i : Fin k, val (r i) := by
  unfold val unionOf
  exact Finset.prod_biUnion (fun i _ j _ hij => hdisj i j hij)

lemma phi_unionOf {k : ℕ} {r : Fin k → Finset ℕ}
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j)) :
    phi (unionOf r) = ∏ i : Fin k, phi (r i) := by
  unfold phi unionOf
  exact Finset.prod_biUnion (fun i _ j _ hij => hdisj i j hij)

noncomputable def idxOf {k : ℕ} (r : Fin k → Finset ℕ) (p : ℕ) (hp : p ∈ unionOf r) : Fin k :=
  Classical.choose (Finset.mem_biUnion.mp hp)

lemma mem_idxOf {k : ℕ} (r : Fin k → Finset ℕ) {p : ℕ} (hp : p ∈ unionOf r) :
    p ∈ r (idxOf r p hp) :=
  (Classical.choose_spec (Finset.mem_biUnion.mp hp)).2

lemma idxOf_eq_of_mem {k : ℕ} {r : Fin k → Finset ℕ}
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j))
    {p : ℕ} {i : Fin k} (hpi : p ∈ r i) (hp : p ∈ unionOf r) :
    idxOf r p hp = i := by
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj _ _ hne) (mem_idxOf r hp) hpi

open scoped Classical in
noncomputable def tupleOf {k : ℕ} (U : Finset ℕ) (f : {p // p ∈ U} → Fin k) : Fin k → Finset ℕ :=
  fun i => U.filter (fun p => ∃ hp : p ∈ U, f ⟨p, hp⟩ = i)

lemma mem_tupleOf_iff {k : ℕ} (U : Finset ℕ) (f : {p // p ∈ U} → Fin k) (i : Fin k) (p : ℕ) :
    p ∈ tupleOf U f i ↔ ∃ hp : p ∈ U, f ⟨p, hp⟩ = i := by
  classical
  simp only [tupleOf, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma unionOf_tupleOf {k : ℕ} (U : Finset ℕ) (f : {p // p ∈ U} → Fin k) :
    unionOf (tupleOf U f) = U := by
  ext p
  simp only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_tupleOf_iff]
  exact ⟨fun ⟨_, hp, _⟩ => hp, fun hp => ⟨f ⟨p, hp⟩, hp, rfl⟩⟩

lemma tupleOf_disjoint {k : ℕ} (U : Finset ℕ) (f : {p // p ∈ U} → Fin k) :
    ∀ i j : Fin k, i ≠ j → Disjoint (tupleOf U f i) (tupleOf U f j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro p hi hj
  obtain ⟨hp, hfi⟩ := (mem_tupleOf_iff U f i p).mp hi
  obtain ⟨_, hfj⟩ := (mem_tupleOf_iff U f j p).mp hj
  exact hij (hfi.symm.trans hfj)

lemma tupleOf_mem_Dset {Pstar : Finset ℕ} {D : ℝ} {k : ℕ} {U : Finset ℕ}
    (hU_sub : U ⊆ Pstar) (hU_le : (val U : ℝ) ≤ D) (f : {p // p ∈ U} → Fin k) :
    tupleOf U f ∈ Dset Pstar D k := by
  rw [mem_Dset_iff]
  have hdisj := tupleOf_disjoint U f
  refine ⟨fun i p hp => hU_sub ((mem_tupleOf_iff U f i p).mp hp).1, hdisj, ?_⟩
  rw [← val_unionOf hdisj, unionOf_tupleOf]
  exact hU_le

lemma idxOf_tupleOf {k : ℕ} (U : Finset ℕ) (f : {p // p ∈ U} → Fin k)
    {p : ℕ} (hp : p ∈ U) (hp' : p ∈ unionOf (tupleOf U f)) :
    idxOf (tupleOf U f) p hp' = f ⟨p, hp⟩ :=
  idxOf_eq_of_mem (tupleOf_disjoint U f) ((mem_tupleOf_iff U f (f ⟨p, hp⟩) p).mpr ⟨hp, rfl⟩) hp'

open scoped Classical in
lemma sum_Dset_filter_union_eq_pi {Pstar : Finset ℕ} {D : ℝ} {k : ℕ} {U : Finset ℕ}
    (hU_sub : U ⊆ Pstar) (hU_le : (val U : ℝ) ≤ D) (g : (Fin k → Finset ℕ) → ℝ) :
    ∑ r ∈ (Dset Pstar D k).filter (fun r => unionOf r = U), g r =
      ∑ f : {p // p ∈ U} → Fin k, g (tupleOf U f) := by
  symm
  refine Finset.sum_bij (fun f _ => tupleOf U f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_filter.mpr ⟨tupleOf_mem_Dset hU_sub hU_le f, unionOf_tupleOf U f⟩
  · intro f₁ _ f₂ _ h
    funext ⟨p, hp⟩
    have h1 := congrFun h (f₁ ⟨p, hp⟩)
    have hp1 : p ∈ tupleOf U f₁ (f₁ ⟨p, hp⟩) := (mem_tupleOf_iff U f₁ _ p).mpr ⟨hp, rfl⟩
    rw [h1] at hp1
    exact ((mem_tupleOf_iff U f₂ _ p).mp hp1).2.symm
  · intro r hr
    rw [Finset.mem_filter] at hr
    have hdisj := (mem_Dset_iff.mp hr.1).2.1
    refine ⟨fun ⟨p, hp⟩ => idxOf r p (by rw [hr.2]; exact hp), Finset.mem_univ _, ?_⟩
    funext i
    ext p
    rw [mem_tupleOf_iff]
    constructor
    · rintro ⟨hpU, hidx⟩
      dsimp only at hidx
      have hmem := mem_idxOf r (by rw [hr.2]; exact hpU)
      rwa [hidx] at hmem
    · intro hpi
      have hpU : p ∈ U := by rw [← hr.2]; exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hpi⟩
      exact ⟨hpU, idxOf_eq_of_mem hdisj hpi (by rw [hr.2]; exact hpU)⟩
  · intro _ _; rfl

open scoped Classical in
lemma card_Dset_filter_union {Pstar : Finset ℕ} {D : ℝ} {k : ℕ} {U : Finset ℕ}
    (hU_sub : U ⊆ Pstar) (hU_le : (val U : ℝ) ≤ D) :
    (((Dset Pstar D k).filter (fun r => unionOf r = U)).card : ℝ) = (k : ℝ) ^ U.card := by
  have h := sum_Dset_filter_union_eq_pi (k := k) hU_sub hU_le (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_coe] at h
  exact_mod_cast h

/-- Rewriting `∏ i, psiProd i (r i) t` as a single product over `Pstar`. -/
lemma prod_psiProd_eq_prod_Pstar {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {Pstar : Finset ℕ} {D : ℝ} {r : Fin k → Finset ℕ} (hr : r ∈ Dset Pstar D k) (t : ℕ) :
    ∏ i : Fin k, psiProd Q b s i (r i) t =
      ∏ p ∈ Pstar, if hp : p ∈ unionOf r then psi Q b s (idxOf r p hp) p t else 1 := by
  have hdisj := (mem_Dset_iff.mp hr).2.1
  have hsub := unionOf_subset hr
  have h1 : ∏ p ∈ Pstar, (if hp : p ∈ unionOf r then psi Q b s (idxOf r p hp) p t else 1) =
      ∏ p ∈ unionOf r, (if hp : p ∈ unionOf r then psi Q b s (idxOf r p hp) p t else 1) := by
    symm
    apply Finset.prod_subset hsub
    intro p _ hpn
    simp [hpn]
  rw [h1]
  have hbi : ∏ p ∈ unionOf r, (if hp : p ∈ unionOf r then psi Q b s (idxOf r p hp) p t else 1) =
      ∏ i : Fin k, ∏ p ∈ r i, (if hp : p ∈ unionOf r then psi Q b s (idxOf r p hp) p t else 1) :=
    Finset.prod_biUnion (fun i _ j _ hij => hdisj i j hij)
  rw [hbi]
  apply Finset.prod_congr rfl
  intro i _
  unfold psiProd
  apply Finset.prod_congr rfl
  intro p hpi
  have hp : p ∈ unionOf r := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hpi⟩
  rw [dif_pos hp, idxOf_eq_of_mem hdisj hpi hp]

/-- Computing the normalized Gram matrix entry `M r₁ r₂`. -/
lemma gram_entry_eval {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    (hcop : ∀ p ∈ Pstar, Nat.Coprime p Q)
    (hdiff : ∀ p ∈ Pstar, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j))
    {D : ℝ} {r₁ r₂ : Fin k → Finset ℕ}
    (hr₁ : r₁ ∈ Dset Pstar D k) (hr₂ : r₂ ∈ Dset Pstar D k) :
    let Φ := fun (r : Fin k → Finset ℕ) (t : ℕ) =>
      Real.sqrt (phi (unionOf r)) * ∏ i : Fin k, psiProd Q b s i (r i) t
    avg (val Pstar) (fun t => Φ r₁ t * Φ r₂ t) =
      if hU : unionOf r₁ = unionOf r₂ then
        ∏ p ∈ (unionOf r₁).attach,
          if idxOf r₁ p.val p.property = idxOf r₂ p.val (by rw [← hU]; exact p.property)
          then (1 : ℝ) else -1 / ((p.val : ℝ) - 1)
      else 0 := by
  intro Φ
  have hU₁_sub := unionOf_subset hr₁
  have hU₂_sub := unionOf_subset hr₂
  have hU₁_P : ∀ p ∈ unionOf r₁, p.Prime := fun p hp => hP p (hU₁_sub hp)
  have hU₂_P : ∀ p ∈ unionOf r₂, p.Prime := fun p hp => hP p (hU₂_sub hp)
  let f₁ : ℕ → ℕ → ℝ := fun p t =>
    if hp : p ∈ unionOf r₁ then psi Q b s (idxOf r₁ p hp) p t else 1
  let f₂ : ℕ → ℕ → ℝ := fun p t =>
    if hp : p ∈ unionOf r₂ then psi Q b s (idxOf r₂ p hp) p t else 1
  have hrew : ∀ t, Φ r₁ t * Φ r₂ t =
      (Real.sqrt (phi (unionOf r₁)) * Real.sqrt (phi (unionOf r₂))) *
        ∏ p ∈ Pstar, (f₁ p t * f₂ p t) := by
    intro t
    dsimp [Φ, f₁, f₂]
    rw [prod_psiProd_eq_prod_Pstar Q b s hr₁ t, prod_psiProd_eq_prod_Pstar Q b s hr₂ t,
      Finset.prod_mul_distrib]
    ring
  simp_rw [hrew]
  rw [avg_const_mul]
  have hper : ∀ p ∈ Pstar, ∀ t, f₁ p (t % p) * f₂ p (t % p) = f₁ p t * f₂ p t := by
    intro p _ t
    dsimp [f₁, f₂]
    split_ifs <;> simp [psi_mod]
  rw [avg_prod_primes Pstar hP (fun p t => f₁ p t * f₂ p t) hper]
  split_ifs with hU
  · have hphi_eq : phi (unionOf r₂) = phi (unionOf r₁) := congrArg phi hU.symm
    rw [hphi_eq, Real.mul_self_sqrt (phi_pos hU₁_P).le]
    have hprod_out : ∏ p ∈ Pstar, avg p (fun t => f₁ p t * f₂ p t) =
        ∏ p ∈ unionOf r₁, avg p (fun t => f₁ p t * f₂ p t) := by
      symm
      apply Finset.prod_subset hU₁_sub
      intro p hpP hpn
      have hpn2 : p ∉ unionOf r₂ := by rwa [← hU]
      have hconst : (fun t => f₁ p t * f₂ p t) = fun _ => 1 := by
        funext t; simp [f₁, f₂, hpn, hpn2]
      rw [hconst]
      unfold avg
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hpP).ne_zero
      field_simp [hp0]
    rw [hprod_out]
    unfold phi
    rw [← Finset.prod_mul_distrib, ← Finset.prod_attach (unionOf r₁)]
    apply Finset.prod_congr rfl
    intro ⟨p, hp1⟩ _
    have hp2 : p ∈ unionOf r₂ := by rw [← hU]; exact hp1
    have hpP : p.Prime := hU₁_P p hp1
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      linarith
    have hloc := lem_local_moments Q b s hpP (hcop p (hU₁_sub hp1))
    have hfeq : (fun t => f₁ p t * f₂ p t) =
        fun t => psi Q b s (idxOf r₁ p hp1) p t * psi Q b s (idxOf r₂ p hp2) p t := by
      funext t; simp [f₁, f₂, hp1, hp2]
    rw [hfeq]
    split_ifs with hidx
    · rw [hidx]
      have hsq : (fun t => psi Q b s (idxOf r₂ p hp2) p t * psi Q b s (idxOf r₂ p hp2) p t) =
          fun t => (psi Q b s (idxOf r₂ p hp2) p t) ^ 2 := by funext t; ring
      rw [hsq, hloc.2.1]
      field_simp [hp1_ne]
    · rw [hloc.2.2 _ _ (hdiff p (hU₁_sub hp1) _ _ hidx)]
      field_simp [hp1_ne]
  · -- unionOf r₁ ≠ unionOf r₂: find a prime in symmetric difference
    have hex : ∃ p ∈ Pstar, (p ∈ unionOf r₁ ∧ p ∉ unionOf r₂) ∨ (p ∉ unionOf r₁ ∧ p ∈ unionOf r₂) := by
      by_contra hall
      push Not at hall
      apply hU
      ext p
      by_cases hpP : p ∈ Pstar
      · obtain ⟨h1, h2⟩ := hall p hpP
        exact ⟨h1, fun hp2 => by_contra fun hp1 => h2 hp1 hp2⟩
      · exact ⟨fun h => absurd (hU₁_sub h) hpP, fun h => absurd (hU₂_sub h) hpP⟩
    obtain ⟨p, hpP, hsym⟩ := hex
    have hzero : avg p (fun t => f₁ p t * f₂ p t) = 0 := by
      have hloc := (lem_local_moments Q b s (hP p hpP) (hcop p hpP)).1
      rcases hsym with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · have hfeq : (fun t => f₁ p t * f₂ p t) = psi Q b s (idxOf r₁ p hp1) p := by
          funext t; simp [f₁, f₂, hp1, hp2]
        rw [hfeq]; exact hloc _
      · have hfeq : (fun t => f₁ p t * f₂ p t) = psi Q b s (idxOf r₂ p hp2) p := by
          funext t; simp [f₁, f₂, hp1, hp2]
        rw [hfeq]; exact hloc _
    rw [Finset.prod_eq_zero hpP hzero, mul_zero]

set_option maxHeartbeats 400000 in
/-- Lemma 3.5 (Gram / second-moment estimate) on `Dset Pstar D k` for arbitrary `c`. -/
lemma lem_gram_estimate {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    (hcop : ∀ p ∈ Pstar, Nat.Coprime p Q)
    (hdiff : ∀ p ∈ Pstar, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j))
    {z : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p)
    {D : ℝ} (hD : 1 ≤ D)
    (hsmall : 2 * (k : ℝ) * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) ≤ 1)
    (c : (Fin k → Finset ℕ) → ℝ) :
    let F := fun t : ℕ => ∑ r ∈ Dset Pstar D k, c r * ∏ i : Fin k, psiProd Q b s i (r i) t
    let I := ∑ r ∈ Dset Pstar D k, (c r) ^ 2 / ∏ i : Fin k, phi (r i)
    |avg (val Pstar) (fun t => (F t) ^ 2) - I| ≤
      (6 * (k : ℝ) * Real.log D / (z : ℝ)) * I := by
  classical
  intro F I
  set DS := Dset Pstar D k
  let bCoeff : (Fin k → Finset ℕ) → ℝ := fun r => c r / Real.sqrt (phi (unionOf r))
  let Φ : (Fin k → Finset ℕ) → ℕ → ℝ := fun r t =>
    Real.sqrt (phi (unionOf r)) * ∏ i : Fin k, psiProd Q b s i (r i) t
  let M : (Fin k → Finset ℕ) → (Fin k → Finset ℕ) → ℝ := fun r₁ r₂ =>
    avg (val Pstar) (fun t => Φ r₁ t * Φ r₂ t)
  have hF_eq : ∀ t, F t = ∑ r ∈ DS, bCoeff r * Φ r t := by
    intro t
    apply Finset.sum_congr rfl
    intro r hr
    have hphi : 0 < phi (unionOf r) := phi_pos (fun p hp => hP p (unionOf_subset hr hp))
    have hsq : Real.sqrt (phi (unionOf r)) ≠ 0 := (Real.sqrt_pos.mpr hphi).ne'
    dsimp [bCoeff, Φ]
    field_simp [hsq]
  have hI_eq : I = ∑ r ∈ DS, (bCoeff r) ^ 2 := by
    apply Finset.sum_congr rfl
    intro r hr
    have hdisj := (mem_Dset_iff.mp hr).2.1
    have hphi : 0 < phi (unionOf r) := phi_pos (fun p hp => hP p (unionOf_subset hr hp))
    dsimp [bCoeff]
    rw [div_pow, Real.sq_sqrt hphi.le, phi_unionOf hdisj]
  have hM_sym : ∀ r₁ r₂, M r₁ r₂ = M r₂ r₁ := by
    intro r₁ r₂
    dsimp [M]
    congr 1; funext t; ring
  have hM_diag : ∀ r ∈ DS, M r r = 1 := by
    intro r hr
    have h := gram_entry_eval Q b s hP hcop hdiff hr hr
    simp only [↓reduceDIte, ↓reduceIte, Finset.prod_const_one] at h
    exact h
  have hdiff_eq : avg (val Pstar) (fun t => (F t) ^ 2) - I =
      ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, M r₁ r₂ * (bCoeff r₁ * bCoeff r₂) := by
    have hsq : ∀ t, (F t) ^ 2 = ∑ r₁ ∈ DS, ∑ r₂ ∈ DS, (bCoeff r₁ * bCoeff r₂) * (Φ r₁ t * Φ r₂ t) := by
      intro t
      rw [hF_eq t, sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro r₁ _
      apply Finset.sum_congr rfl; intro r₂ _
      ring
    simp_rw [hsq]
    rw [avg_sum]
    have h1 : ∀ r₁ ∈ DS, avg (val Pstar) (fun t => ∑ r₂ ∈ DS, (bCoeff r₁ * bCoeff r₂) * (Φ r₁ t * Φ r₂ t)) =
        (bCoeff r₁) ^ 2 + ∑ r₂ ∈ DS.erase r₁, M r₁ r₂ * (bCoeff r₁ * bCoeff r₂) := by
      intro r₁ hr₁
      rw [avg_sum, ← Finset.add_sum_erase _ _ hr₁]
      congr 1
      · rw [avg_const_mul, show avg (val Pstar) (fun t => Φ r₁ t * Φ r₁ t) = M r₁ r₁ from rfl,
          hM_diag r₁ hr₁]; ring
      · apply Finset.sum_congr rfl
        intro r₂ _
        rw [avg_const_mul]; dsimp [M]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, hI_eq]
    ring
  -- Bound the off-diagonal row sum for each r₁ ∈ DS
  let ρ : ℝ := 6 * (k : ℝ) * Real.log D / (z : ℝ)
  have hrow_bound : ∀ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| ≤ ρ := by
    intro r₁ hr₁
    set U := unionOf r₁
    have hU_sub : U ⊆ Pstar := unionOf_subset hr₁
    have hU_disj := (mem_Dset_iff.mp hr₁).2.1
    have hU_le : (val U : ℝ) ≤ D := by
      rw [val_unionOf hU_disj]; exact (mem_Dset_iff.mp hr₁).2.2
    -- Only r₂ with unionOf r₂ = U contribute
    have hfilt : ∑ r₂ ∈ DS, |M r₁ r₂| = ∑ r₂ ∈ DS.filter (fun r => unionOf r = U), |M r₁ r₂| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r₂ hr₂ hnot
      have hne : unionOf r₁ ≠ unionOf r₂ := fun heq => hnot (Finset.mem_filter.mpr ⟨hr₂, heq.symm⟩)
      have h := gram_entry_eval Q b s hP hcop hdiff hr₁ hr₂
      rw [dif_neg hne] at h
      have hM0 : M r₁ r₂ = 0 := h
      rw [hM0, abs_zero]
    have hfull : ∑ r₂ ∈ DS.filter (fun r => unionOf r = U), |M r₁ r₂| =
        ∏ p ∈ U, (1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)) := by
      rw [sum_Dset_filter_union_eq_pi hU_sub hU_le (fun r₂ => |M r₁ r₂|)]
      let hpFun : {p // p ∈ U} → Fin k → ℝ := fun p i =>
        if idxOf r₁ p.val p.property = i then 1 else 1 / ((p.val : ℝ) - 1)
      have hcongr : ∀ f : {p // p ∈ U} → Fin k,
          |M r₁ (tupleOf U f)| = ∏ p : {p // p ∈ U}, hpFun p (f p) := by
        intro f
        have hr₂ : tupleOf U f ∈ DS := tupleOf_mem_Dset hU_sub hU_le f
        have hev := gram_entry_eval Q b s hP hcop hdiff hr₁ hr₂
        have hUeq : unionOf r₁ = unionOf (tupleOf U f) := (unionOf_tupleOf U f).symm
        rw [dif_pos hUeq] at hev
        have hMeq : M r₁ (tupleOf U f) =
            ∏ p ∈ (unionOf r₁).attach,
              if idxOf r₁ p.val p.property = idxOf (tupleOf U f) p.val (by rw [← hUeq]; exact p.property)
              then (1 : ℝ) else -1 / ((p.val : ℝ) - 1) := hev
        rw [hMeq, Finset.abs_prod]
        have hprod_eq : ∏ p ∈ U.attach, |if idxOf r₁ p.val p.property =
            idxOf (tupleOf U f) p.val (by rw [← hUeq]; exact p.property)
            then (1 : ℝ) else -1 / ((p.val : ℝ) - 1)| =
            ∏ p ∈ U.attach, hpFun p (f p) := by
          apply Finset.prod_congr rfl
          intro p _
          have hidx := idxOf_tupleOf U f p.property (by rw [← hUeq]; exact p.property)
          rw [hidx]
          dsimp [hpFun]
          split_ifs
          · simp
          · have hpP := hP p.val (hU_sub p.property)
            have hp1 : (0 : ℝ) < (p.val : ℝ) - 1 := by
              have : (1 : ℝ) < p.val := by exact_mod_cast hpP.one_lt
              linarith
            rw [abs_div, abs_neg, abs_one, abs_of_pos hp1]
        simpa [Finset.univ_eq_attach] using hprod_eq
      simp_rw [hcongr]
      rw [← Fintype.prod_sum hpFun, Finset.univ_eq_attach]
      rw [← Finset.prod_attach U (fun p => 1 + ((k : ℝ) - 1) / ((p : ℝ) - 1))]
      apply Finset.prod_congr rfl
      intro p _
      have hi₀ : idxOf r₁ p.val p.property ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ hi₀]
      have h0 : hpFun p (idxOf r₁ p.val p.property) = 1 := by simp [hpFun]
      have hrest : ∑ i ∈ Finset.univ.erase (idxOf r₁ p.val p.property), hpFun p i =
          ((k : ℝ) - 1) / ((p.val : ℝ) - 1) := by
        have hc : ∑ i ∈ Finset.univ.erase (idxOf r₁ p.val p.property), hpFun p i =
            ∑ _i ∈ Finset.univ.erase (idxOf r₁ p.val p.property), (1 / ((p.val : ℝ) - 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hne : idxOf r₁ p.val p.property ≠ i := (Finset.mem_erase.mp hi).1.symm
          simp [hpFun, hne]
        rw [hc, Finset.sum_const, Finset.card_erase_of_mem hi₀, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (Fin.pos (idxOf r₁ p.val p.property)).ne'
        rw [Nat.cast_sub hk1, Nat.cast_one]
        ring
      rw [h0, hrest]
    have hoff_eq : ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| =
        ∏ p ∈ U, (1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)) - 1 := by
      have hsplit := Finset.add_sum_erase DS (fun r₂ => |M r₁ r₂|) hr₁
      rw [hM_diag r₁ hr₁, abs_one, hfilt, hfull] at hsplit
      linarith
    rw [hoff_eq]
    rcases U.eq_empty_or_nonempty with hUemp | hUne
    · rw [hUemp, Finset.prod_empty, sub_self]
      dsimp [ρ]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
        (Real.log_nonneg hD)) (Nat.cast_nonneg z)
    · have hk1 : 1 ≤ k := by
        obtain ⟨p, hp⟩ := hUne
        exact Nat.pos_of_ne_zero (Fin.pos (idxOf r₁ p hp)).ne'
      have hnn : ∀ p ∈ U, 0 ≤ ((k : ℝ) - 1) / ((p : ℝ) - 1) := by
        intro p hp
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
          have : (1 : ℝ) < p := by exact_mod_cast (hP p (hU_sub hp)).one_lt
          linarith
        exact div_nonneg (by linarith) hp1.le
      have hz_pos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
      have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hU_card : (U.card : ℝ) * Real.log (z : ℝ) ≤ Real.log D := by
        have h1 : (U.card : ℝ) * Real.log (z : ℝ) ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
          calc (U.card : ℝ) * Real.log (z : ℝ) = ∑ _p ∈ U, Real.log (z : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ p ∈ U, Real.log (p : ℝ) := Finset.sum_le_sum fun p hp =>
                Real.log_le_log hz_pos (by exact_mod_cast (hgt p (hU_sub hp)).le)
        have h2 : ∑ p ∈ U, Real.log (p : ℝ) = Real.log (val U : ℝ) := by
          unfold val; rw [Nat.cast_prod, Real.log_prod]
          intro p hp; exact_mod_cast (hP p (hU_sub hp)).ne_zero
        have h3 : Real.log (val U : ℝ) ≤ Real.log D :=
          Real.log_le_log (by exact_mod_cast val_pos (fun p hp => hP p (hU_sub hp))) hU_le
        linarith
      have hsum_le : ∑ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1) ≤
          2 * (k : ℝ) * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) := by
        have hterm : ∀ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1) ≤ 2 * (k : ℝ) / (z : ℝ) := by
          intro p hp
          have hpz : (z : ℝ) < (p : ℝ) := by exact_mod_cast hgt p (hU_sub hp)
          have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast (by omega : 2 ≤ z)
          have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          have hden : (z : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
          calc ((k : ℝ) - 1) / ((p : ℝ) - 1)
              ≤ (k : ℝ) / ((p : ℝ) - 1) := div_le_div_of_nonneg_right (by linarith) hp1.le
            _ ≤ (k : ℝ) / ((z : ℝ) / 2) :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by linarith) hden
            _ = 2 * (k : ℝ) / (z : ℝ) := by ring
        calc ∑ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1)
            ≤ ∑ _p ∈ U, (2 * (k : ℝ) / (z : ℝ)) := Finset.sum_le_sum hterm
          _ = (U.card : ℝ) * (2 * (k : ℝ) / (z : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Real.log D / Real.log (z : ℝ)) * (2 * (k : ℝ) / (z : ℝ)) :=
              mul_le_mul_of_nonneg_right ((le_div_iff₀ hlogz_pos).mpr hU_card) (by positivity)
          _ = 2 * (k : ℝ) * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) := by ring
      have hprod_le := prod_one_add_le_exp_sum U (fun p => ((k : ℝ) - 1) / ((p : ℝ) - 1)) hnn
      have hv_nn : 0 ≤ ∑ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1) := Finset.sum_nonneg hnn
      have hexp_le := exp_sub_one_le_of_le hv_nn (hsum_le.trans hsmall)
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have hlogz_ge1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
        have he3 : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
        have h3z : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
        have h := Real.log_le_log (Real.exp_pos 1) (he3.trans h3z)
        rwa [Real.log_exp] at h
      calc ∏ p ∈ U, (1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)) - 1
          ≤ Real.exp (∑ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1)) - 1 := by linarith
        _ ≤ Real.exp 1 * ∑ p ∈ U, ((k : ℝ) - 1) / ((p : ℝ) - 1) := hexp_le
        _ ≤ 3 * (2 * (k : ℝ) * Real.log D / ((z : ℝ) * Real.log (z : ℝ))) :=
            mul_le_mul he1 hsum_le hv_nn (by norm_num)
        _ ≤ 3 * (2 * (k : ℝ) * Real.log D / ((z : ℝ) * 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) (Real.log_nonneg hD))
              (mul_pos hz_pos zero_lt_one)
            exact mul_le_mul_of_nonneg_left hlogz_ge1 hz_pos.le
        _ = ρ := by dsimp [ρ]; ring
  -- Combine with 2|ab| ≤ a^2 + b^2 and symmetry of M
  rw [hdiff_eq]
  have h1 : |∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, M r₁ r₂ * (bCoeff r₁ * bCoeff r₂)| ≤
      ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| * (((bCoeff r₁) ^ 2 + (bCoeff r₂) ^ 2) / 2) := by
    calc |∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, M r₁ r₂ * (bCoeff r₁ * bCoeff r₂)|
        ≤ ∑ r₁ ∈ DS, |∑ r₂ ∈ DS.erase r₁, M r₁ r₂ * (bCoeff r₁ * bCoeff r₂)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂ * (bCoeff r₁ * bCoeff r₂)| :=
          Finset.sum_le_sum fun r₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| * (((bCoeff r₁) ^ 2 + (bCoeff r₂) ^ 2) / 2) := by
          apply Finset.sum_le_sum; intro r₁ _
          apply Finset.sum_le_sum; intro r₂ _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h2ab : |bCoeff r₁ * bCoeff r₂| ≤ ((bCoeff r₁) ^ 2 + (bCoeff r₂) ^ 2) / 2 := by
            rw [abs_le]
            constructor <;> nlinarith [sq_nonneg (bCoeff r₁ + bCoeff r₂), sq_nonneg (bCoeff r₁ - bCoeff r₂)]
          exact h2ab
  have h2 : ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| * (((bCoeff r₁) ^ 2 + (bCoeff r₂) ^ 2) / 2) =
      ∑ r₁ ∈ DS, (bCoeff r₁) ^ 2 * ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| := by
    have hsplit : ∀ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| * (((bCoeff r₁) ^ 2 + (bCoeff r₂) ^ 2) / 2) =
        (∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₁) ^ 2) +
        (∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₂) ^ 2) := by
      intro r₁ _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r₂ _; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hswap : ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₂) ^ 2 =
        ∑ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₁) ^ 2 := by
      have hite : ∀ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₂) ^ 2 =
          ∑ r₂ ∈ DS, if r₂ ≠ r₁ then (1 / 2) * |M r₁ r₂| * (bCoeff r₂) ^ 2 else 0 := by
        intro r₁ _; rw [← Finset.sum_filter, Finset.filter_ne']
      have hite2 : ∀ r₁ ∈ DS, ∑ r₂ ∈ DS.erase r₁, (1 / 2) * |M r₁ r₂| * (bCoeff r₁) ^ 2 =
          ∑ r₂ ∈ DS, if r₂ ≠ r₁ then (1 / 2) * |M r₁ r₂| * (bCoeff r₁) ^ 2 else 0 := by
        intro r₁ _; rw [← Finset.sum_filter, Finset.filter_ne']
      rw [Finset.sum_congr rfl hite, Finset.sum_comm, Finset.sum_congr rfl hite2]
      apply Finset.sum_congr rfl; intro r₁ _
      apply Finset.sum_congr rfl; intro r₂ _
      rw [hM_sym r₂ r₁]
      by_cases hne : r₁ ≠ r₂
      · simp [hne, hne.symm]
      · simp [hne, ne_comm.not.mp hne]
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r₁ _
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r₂ _; ring
  have h3 : ∑ r₁ ∈ DS, (bCoeff r₁) ^ 2 * ∑ r₂ ∈ DS.erase r₁, |M r₁ r₂| ≤ ρ * I := by
    rw [hI_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r₁ hr₁
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hrow_bound r₁ hr₁) (sq_nonneg _)
  exact h1.trans (h2.le.trans h3)

/- ## Part 7: Section 3.4 - Indicator Expansion and Finite Averages -/

def indDiv (d : Finset ℕ) (m : ℤ) : ℝ :=
  if (val d : ℤ) ∣ m then 1 else 0

def Jtuple {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (d : Fin k → Finset ℕ) (t : ℕ) : ℝ :=
  ∏ i : Fin k, indDiv (d i) (Lform Q b s i t)

lemma indDiv_prod_primes {d : Finset ℕ} (hd : ∀ p ∈ d, p.Prime) (m : ℤ) :
    ∏ p ∈ d, indDiv {p} m = indDiv d m := by
  have hiff : (∀ p ∈ d, (p : ℤ) ∣ m) ↔ (val d : ℤ) ∣ m := by
    constructor
    · intro hall
      have hdvd_nat : val d ∣ m.natAbs := by
        unfold val
        refine Finset.prod_primes_dvd m.natAbs (fun p hp => (hd p hp).prime) ?_
        intro p hp
        exact Int.natCast_dvd.mp (hall p hp)
      exact Int.natCast_dvd.mpr hdvd_nat
    · intro h p hp
      have hp_dvd : (p : ℤ) ∣ (val d : ℤ) := by exact_mod_cast Finset.dvd_prod_of_mem _ hp
      exact dvd_trans hp_dvd h
  by_cases h : (val d : ℤ) ∣ m
  · have hall := hiff.mpr h
    simp only [indDiv, h, ↓reduceIte]
    apply Finset.prod_eq_one
    intro p hp
    have h1 : val {p} = p := by simp [val]
    simp [h1, hall p hp]
  · simp only [indDiv, h, ↓reduceIte]
    have hnot : ¬ ∀ p ∈ d, (p : ℤ) ∣ m := fun hall => h (hiff.mp hall)
    push Not at hnot
    obtain ⟨p, hp, hnd⟩ := hnot
    apply Finset.prod_eq_zero hp
    have h1 : val {p} = p := by simp [val]
    simp [h1, hnd]

lemma psiProd_eq_sum_indDiv {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (i : Fin k)
    {r : Finset ℕ} (hr : ∀ p ∈ r, p.Prime) (t : ℕ) :
    psiProd Q b s i r t =
      (1 / phi r) * ∑ d ∈ r.powerset, (-1 : ℝ) ^ d.card * (val d : ℝ) * indDiv d (Lform Q b s i t) := by
  unfold psiProd phi
  have hfac : ∀ p ∈ r, psi Q b s i p t =
      (1 + (-(p : ℝ) * indDiv {p} (Lform Q b s i t))) / ((p : ℝ) - 1) := by
    intro p hp
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast (hr p hp).one_lt
      linarith
    have hval1 : val {p} = p := by simp [val]
    unfold psi indDiv
    rw [hval1]
    split_ifs <;> field_simp [hp1] <;> ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib, Finset.prod_one_add]
  have hterm : ∀ d ∈ r.powerset,
      ∏ p ∈ d, (-(p : ℝ) * indDiv {p} (Lform Q b s i t)) =
        (-1 : ℝ) ^ d.card * (val d : ℝ) * indDiv d (Lform Q b s i t) := by
    intro d hd
    have hdP : ∀ p ∈ d, p.Prime := fun p hp => hr p (Finset.mem_powerset.mp hd hp)
    have hrew : ∀ p ∈ d, (-(p : ℝ) * indDiv {p} (Lform Q b s i t)) =
        (-1 : ℝ) * (p : ℝ) * indDiv {p} (Lform Q b s i t) := fun p _ => by ring
    rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, indDiv_prod_primes hdP]
    simp [val]
  rw [Finset.sum_congr rfl hterm]
  ring

open scoped Classical in
noncomputable def lambdaCoeff (Pstar : Finset ℕ) (D : ℝ) {k : ℕ}
    (a : Finset ℕ → ℝ) (d : Fin k → Finset ℕ) : ℝ :=
  ∑ r ∈ (Dset Pstar D k).filter (fun r => ∀ i, d i ⊆ r i),
    ∏ i : Fin k, (a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ))

noncomputable def Rweight (Pstar : Finset ℕ) (D : ℝ) {k : ℕ}
    (a : Finset ℕ → ℝ) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (t : ℕ) : ℝ :=
  ∑ r ∈ Dset Pstar D k, ∏ i : Fin k, (a (r i) * psiProd Q b s i (r i) t)

noncomputable def Rpartial (Pstar : Finset ℕ) (D : ℝ) {k : ℕ}
    (a : Finset ℕ → ℝ) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    (J : Finset (Fin k → Finset ℕ)) (t : ℕ) : ℝ :=
  ∑ d ∈ J, lambdaCoeff Pstar D a d * Jtuple Q b s d t

lemma sub_mem_Dset {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime) {D : ℝ} {k : ℕ}
    {r d : Fin k → Finset ℕ} (hr : r ∈ Dset Pstar D k) (hd : ∀ i, d i ⊆ r i) :
    d ∈ Dset Pstar D k := by
  rw [mem_Dset_iff] at hr ⊢
  refine ⟨fun i => (hd i).trans (hr.1 i),
    fun i j hij => Disjoint.mono (hd i) (hd j) (hr.2.1 i j hij), ?_⟩
  have hle : ∏ i : Fin k, val (d i) ≤ ∏ i : Fin k, val (r i) := by
    apply Finset.prod_le_prod'
    intro i _
    have hpos : 0 < val (r i) := val_pos (fun p hp => hP p (hr.1 i hp))
    exact Nat.le_of_dvd hpos (Finset.prod_dvd_prod_of_subset _ _ _ (hd i))
  exact (Nat.cast_le.mpr hle).trans hr.2.2

lemma Rweight_eq_Rpartial_full {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime) {D : ℝ} {k : ℕ}
    (a : Finset ℕ → ℝ) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ) (t : ℕ) :
    Rweight Pstar D a Q b s t = Rpartial Pstar D a Q b s (Dset Pstar D k) t := by
  classical
  set DS := Dset Pstar D k
  unfold Rweight Rpartial lambdaCoeff Jtuple
  have hexp : ∀ r ∈ DS, ∏ i : Fin k, (a (r i) * psiProd Q b s i (r i) t) =
      ∑ d ∈ DS, if ∀ i, d i ⊆ r i then
        (∏ i : Fin k, (a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ))) *
          ∏ i : Fin k, indDiv (d i) (Lform Q b s i t)
      else 0 := by
    intro r hr
    have hsub := (mem_Dset_iff.mp hr).1
    have h1 : ∀ i : Fin k, a (r i) * psiProd Q b s i (r i) t =
        ∑ d_i ∈ (r i).powerset,
          (a (r i) / phi (r i) * (-1 : ℝ) ^ d_i.card * (val d_i : ℝ)) *
            indDiv d_i (Lform Q b s i t) := by
      intro i
      rw [psiProd_eq_sum_indDiv Q b s i (fun p hp => hP p (hsub i hp)) t, ← mul_assoc,
        Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d_i _; ring
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum]
    have hsum_eq : ∑ d ∈ Fintype.piFinset (fun i : Fin k => (r i).powerset),
        ∏ i : Fin k, ((a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ)) *
          indDiv (d i) (Lform Q b s i t)) =
        ∑ d ∈ DS, if ∀ i, d i ⊆ r i then
          (∏ i : Fin k, (a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ))) *
            ∏ i : Fin k, indDiv (d i) (Lform Q b s i t)
        else 0 := by
      rw [← Finset.sum_filter]
      have hfilt : DS.filter (fun d => ∀ i, d i ⊆ r i) =
          Fintype.piFinset (fun i : Fin k => (r i).powerset) := by
        ext d
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨sub_mem_Dset hP hr h, h⟩⟩
      rw [hfilt]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.prod_mul_distrib]
    exact hsum_eq
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_mul, ← Finset.sum_filter]

lemma sum_piFinset_prod {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Finset α) (f : ι → α → ℝ) :
    ∑ g ∈ Fintype.piFinset s, ∏ i : ι, f i (g i) = ∏ i : ι, ∑ a ∈ s i, f i a :=
  (Finset.prod_univ_sum (t := s) (f := f)).symm

lemma sum_abs_lambda_le {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {z : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p)
    {D : ℝ} (hD8 : 8 ≤ D) {k : ℕ} (hk1 : 1 ≤ k) (hkz : (k : ℝ) ^ 6 ≤ (z : ℝ))
    (hsmall : 3 * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) ≤ Real.log 2)
    (a : Finset ℕ → ℝ) (ha : ∀ t ∈ Pstar.powerset, |a t| ≤ 1) :
    ∑ d ∈ Dset Pstar D k, |lambdaCoeff Pstar D a d| ≤ D ^ ((3 : ℝ) / 2) := by
  classical
  set DS := Dset Pstar D k
  have hD_pos : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hz_pos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- Step 1: Triangle inequality and swap (d, r)
  have htri : ∑ d ∈ DS, |lambdaCoeff Pstar D a d| ≤
      ∑ r ∈ DS, ∏ p ∈ unionOf r, (1 + 2 / ((p : ℝ) - 1)) := by
    have h1 : ∑ d ∈ DS, |lambdaCoeff Pstar D a d| ≤
        ∑ d ∈ DS, ∑ r ∈ DS.filter (fun r => ∀ i, d i ⊆ r i),
          ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) := by
      apply Finset.sum_le_sum; intro d _
      unfold lambdaCoeff
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      have hr_sub := (mem_Dset_iff.mp (Finset.mem_filter.mp hr).1).1 i
      have hphi := phi_pos (fun p hp => hP p (hr_sub hp))
      have hv_abs : |(val (d i) : ℝ)| = (val (d i) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_mul, abs_mul, abs_div, abs_of_pos hphi, abs_pow, abs_neg, abs_one, one_pow,
        mul_one, hv_abs]
    have hswap : ∑ d ∈ DS, ∑ r ∈ DS.filter (fun r => ∀ i, d i ⊆ r i),
        ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) =
        ∑ r ∈ DS, ∑ d ∈ Fintype.piFinset (fun i : Fin k => (r i).powerset),
          ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) := by
      have hite : ∀ d ∈ DS, ∑ r ∈ DS.filter (fun r => ∀ i, d i ⊆ r i),
          ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) =
          ∑ r ∈ DS, if ∀ i, d i ⊆ r i then
            ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) else 0 := fun d _ => by
        rw [← Finset.sum_filter]
      rw [Finset.sum_congr rfl hite, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨sub_mem_Dset hP hr h, h⟩⟩
    have hinner : ∀ r ∈ DS,
        ∑ d ∈ Fintype.piFinset (fun i : Fin k => (r i).powerset),
          ∏ i : Fin k, (|a (r i)| / phi (r i) * (val (d i) : ℝ)) ≤
        ∏ p ∈ unionOf r, (1 + 2 / ((p : ℝ) - 1)) := by
      intro r hr
      have hr_sub := (mem_Dset_iff.mp hr).1
      have hr_disj := (mem_Dset_iff.mp hr).2.1
      rw [sum_piFinset_prod (s := fun i : Fin k => (r i).powerset)
        (f := fun i t => |a (r i)| / phi (r i) * (val t : ℝ))]
      have hfac : ∀ i : Fin k,
          ∑ d_i ∈ (r i).powerset, (|a (r i)| / phi (r i) * (val d_i : ℝ)) ≤
          ∏ p ∈ r i, (1 + 2 / ((p : ℝ) - 1)) := by
        intro i
        rw [← Finset.mul_sum]
        have hsum_val : ∑ d_i ∈ (r i).powerset, (val d_i : ℝ) = ∏ p ∈ r i, (1 + (p : ℝ)) := by
          rw [Finset.prod_one_add]
          apply Finset.sum_congr rfl; intro d_i _; simp [val]
        rw [hsum_val]
        have ha1 : |a (r i)| ≤ 1 := ha (r i) (Finset.mem_powerset.mpr (hr_sub i))
        have hphi := phi_pos (fun p hp => hP p (hr_sub i hp))
        have hprod_nn : 0 ≤ ∏ p ∈ r i, (1 + (p : ℝ)) :=
          Finset.prod_nonneg fun p _ => by positivity
        calc |a (r i)| / phi (r i) * ∏ p ∈ r i, (1 + (p : ℝ))
            ≤ 1 / phi (r i) * ∏ p ∈ r i, (1 + (p : ℝ)) :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ha1 hphi.le) hprod_nn
          _ = (∏ p ∈ r i, (1 + (p : ℝ))) / phi (r i) := by ring
          _ = ∏ p ∈ r i, ((1 + (p : ℝ)) / ((p : ℝ) - 1)) := by
              unfold phi; rw [Finset.prod_div_distrib]
          _ = ∏ p ∈ r i, (1 + 2 / ((p : ℝ) - 1)) := by
              apply Finset.prod_congr rfl; intro p hp
              have hp1 : (p : ℝ) - 1 ≠ 0 := by
                have : (1 : ℝ) < p := by exact_mod_cast (hP p (hr_sub i hp)).one_lt
                linarith
              field_simp [hp1]; ring
      calc ∏ i : Fin k, ∑ d_i ∈ (r i).powerset, (|a (r i)| / phi (r i) * (val d_i : ℝ))
          ≤ ∏ i : Fin k, ∏ p ∈ r i, (1 + 2 / ((p : ℝ) - 1)) :=
            Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun d_i _ =>
              mul_nonneg (div_nonneg (abs_nonneg _)
                (phi_pos (fun p hp => hP p (hr_sub i hp))).le) (Nat.cast_nonneg _))
              (fun i _ => hfac i)
        _ = ∏ p ∈ unionOf r, (1 + 2 / ((p : ℝ) - 1)) := by
            unfold unionOf
            exact (Finset.prod_biUnion (fun i _ j _ hij => hr_disj i j hij)).symm
    exact h1.trans (hswap.le.trans (Finset.sum_le_sum hinner))
  -- Step 2: Group r ∈ DS by U = unionOf r
  set Uset := Pstar.powerset.filter (fun U => (val U : ℝ) ≤ D)
  have hgroup : ∑ r ∈ DS, ∏ p ∈ unionOf r, (1 + 2 / ((p : ℝ) - 1)) =
      ∑ U ∈ Uset, (k : ℝ) ^ U.card * ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) := by
    have hmap : ∀ r ∈ DS, unionOf r ∈ Uset := by
      intro r hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (unionOf_subset hr), ?_⟩
      rw [val_unionOf (mem_Dset_iff.mp hr).2.1]
      exact (mem_Dset_iff.mp hr).2.2
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.mem_filter, Finset.mem_powerset] at hU
    have hcongr : ∑ r ∈ DS.filter (fun r => unionOf r = U),
        ∏ p ∈ unionOf r, (1 + 2 / ((p : ℝ) - 1)) =
        ∑ _r ∈ DS.filter (fun r => unionOf r = U), ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) :=
      Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, card_Dset_filter_union hU.1 hU.2]
  -- Step 3: Bound each U ∈ Uset and card Uset ≤ D
  have hU_term : ∀ U ∈ Uset,
      (k : ℝ) ^ U.card * ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) ≤ 2 * D ^ ((1 : ℝ) / 6) := by
    intro U hU
    rw [Finset.mem_filter, Finset.mem_powerset] at hU
    have hU_P : ∀ p ∈ U, p.Prime := fun p hp => hP p (hU.1 hp)
    have hU_card : (U.card : ℝ) * Real.log (z : ℝ) ≤ Real.log D := by
      have h1 : (U.card : ℝ) * Real.log (z : ℝ) ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
        calc (U.card : ℝ) * Real.log (z : ℝ) = ∑ _p ∈ U, Real.log (z : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ U, Real.log (p : ℝ) := Finset.sum_le_sum fun p hp =>
              Real.log_le_log hz_pos (by exact_mod_cast (hgt p (hU.1 hp)).le)
      have h2 : ∑ p ∈ U, Real.log (p : ℝ) = Real.log (val U : ℝ) := by
        unfold val; rw [Nat.cast_prod, Real.log_prod]
        intro p hp; exact_mod_cast (hU_P p hp).ne_zero
      have h3 : Real.log (val U : ℝ) ≤ Real.log D :=
        Real.log_le_log (by exact_mod_cast val_pos hU_P) hU.2
      linarith
    have hprod2 : ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) ≤ 2 := by
      have hnn : ∀ p ∈ U, 0 ≤ 2 / ((p : ℝ) - 1) := fun p hp => by
        have : (1 : ℝ) < p := by exact_mod_cast (hU_P p hp).one_lt
        exact div_nonneg (by norm_num) (by linarith)
      refine (prod_one_add_le_exp_sum U _ hnn).trans ?_
      have hsum3 : ∑ p ∈ U, 2 / ((p : ℝ) - 1) ≤ Real.log 2 := by
        have hterm : ∀ p ∈ U, 2 / ((p : ℝ) - 1) ≤ 3 / (z : ℝ) := by
          intro p hp
          have hpz : (z : ℝ) < (p : ℝ) := by exact_mod_cast hgt p (hU.1 hp)
          have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
          have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          rw [div_le_div_iff₀ hp1 hz_pos]
          linarith
        calc ∑ p ∈ U, 2 / ((p : ℝ) - 1)
            ≤ ∑ _p ∈ U, (3 / (z : ℝ)) := Finset.sum_le_sum hterm
          _ = (U.card : ℝ) * (3 / (z : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Real.log D / Real.log (z : ℝ)) * (3 / (z : ℝ)) :=
              mul_le_mul_of_nonneg_right ((le_div_iff₀ hlogz_pos).mpr hU_card) (by positivity)
          _ = 3 * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) := by ring
          _ ≤ Real.log 2 := hsmall
      calc Real.exp (∑ p ∈ U, 2 / ((p : ℝ) - 1)) ≤ Real.exp (Real.log 2) :=
            Real.exp_le_exp.mpr hsum3
        _ = 2 := Real.exp_log (by norm_num)
    have hkpow : (k : ℝ) ^ U.card ≤ D ^ ((1 : ℝ) / 6) := by
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hlogk : 6 * Real.log (k : ℝ) ≤ Real.log (z : ℝ) := by
        have h := Real.log_le_log (pow_pos hk_pos 6) hkz
        rwa [Real.log_pow] at h
      have hexp_le : (U.card : ℝ) * Real.log (k : ℝ) ≤ ((1 : ℝ) / 6) * Real.log D := by
        have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
        have h1 : (U.card : ℝ) * Real.log (k : ℝ) ≤ (U.card : ℝ) * (Real.log (z : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        linarith
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hk_pos, Real.rpow_def_of_pos hD_pos,
        mul_comm (Real.log (k : ℝ)) _, mul_comm (Real.log D) _]
      exact Real.exp_le_exp.mpr hexp_le
    have hprod_nn : 0 ≤ ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) :=
      Finset.prod_nonneg fun p hp => by
        have : (1 : ℝ) < p := by exact_mod_cast (hU_P p hp).one_lt
        have : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
        linarith
    calc (k : ℝ) ^ U.card * ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1))
        ≤ D ^ ((1 : ℝ) / 6) * 2 := mul_le_mul hkpow hprod2 hprod_nn (Real.rpow_nonneg hD_pos.le _)
      _ = 2 * D ^ ((1 : ℝ) / 6) := by ring
  have hUset_card : (Uset.card : ℝ) ≤ D := by
    have hinj : Set.InjOn val (Uset : Set (Finset ℕ)) := by
      intro U₁ hU₁ U₂ hU₂ heq
      have h1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hU₁).1
      have h2 := Finset.mem_powerset.mp (Finset.mem_filter.mp hU₂).1
      exact val_inj_on_primes (fun p hp => hP p (h1 hp)) (fun p hp => hP p (h2 hp)) heq
    have hmaps : Set.MapsTo val (Uset : Set (Finset ℕ)) ((Finset.Icc 1 ⌊D⌋₊ : Finset ℕ) : Set ℕ) := by
      intro U hU
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨val_one_le (fun p hp => hP p (hU.1 hp)), Nat.le_floor hU.2⟩
    have hcard_nat : Uset.card ≤ (Finset.Icc 1 ⌊D⌋₊).card :=
      Finset.card_le_card_of_injOn val hmaps hinj
    rw [Nat.card_Icc] at hcard_nat
    have hle : Uset.card ≤ ⌊D⌋₊ := by omega
    exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hD_pos.le)
  have h2D : 2 * D * D ^ ((1 : ℝ) / 6) ≤ D ^ ((3 : ℝ) / 2) := by
    have h2_le : (2 : ℝ) ≤ D ^ ((1 : ℝ) / 3) := by
      have h8 : (2 : ℝ) = (8 : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h8]
      exact Real.rpow_le_rpow (by norm_num) hD8 (by norm_num)
    calc 2 * D * D ^ ((1 : ℝ) / 6)
        = 2 * (D ^ (1 : ℝ) * D ^ ((1 : ℝ) / 6)) := by rw [Real.rpow_one]; ring
      _ ≤ D ^ ((1 : ℝ) / 3) * (D ^ (1 : ℝ) * D ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_right h2_le (mul_nonneg (Real.rpow_nonneg hD_pos.le _)
            (Real.rpow_nonneg hD_pos.le _))
      _ = D ^ ((3 : ℝ) / 2) := by
          rw [← Real.rpow_add hD_pos, ← Real.rpow_add hD_pos]
          congr 1; norm_num
  calc ∑ d ∈ DS, |lambdaCoeff Pstar D a d|
      ≤ ∑ U ∈ Uset, (k : ℝ) ^ U.card * ∏ p ∈ U, (1 + 2 / ((p : ℝ) - 1)) :=
        htri.trans_eq hgroup
    _ ≤ ∑ _U ∈ Uset, (2 * D ^ ((1 : ℝ) / 6)) := Finset.sum_le_sum hU_term
    _ = (Uset.card : ℝ) * (2 * D ^ ((1 : ℝ) / 6)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ D * (2 * D ^ ((1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_right hUset_card (mul_nonneg (by norm_num) (Real.rpow_nonneg hD_pos.le _))
    _ = 2 * D * D ^ ((1 : ℝ) / 6) := by ring
    _ ≤ D ^ ((3 : ℝ) / 2) := h2D

/-- CRT characterization of simultaneous prime divisibilities for distinct primes. -/
lemma crt_system_of_primes {k : ℕ} (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) (hcop : ∀ p ∈ U, Nat.Coprime p Q)
    (idx : ℕ → Fin k) :
    ∃ a₀ : ℕ, a₀ < val U ∧ ∀ t : ℕ,
      (∀ p ∈ U, (p : ℤ) ∣ Lform Q b s (idx p) t) ↔ t % val U = a₀ := by
  induction U using Finset.induction_on with
  | empty =>
    refine ⟨0, by simp [val_empty], fun t => ?_⟩
    simp [val_empty, Nat.mod_one]
  | insert q U' hq ih =>
    have hqP : q.Prime := hU q (Finset.mem_insert_self q U')
    have hU' : ∀ p ∈ U', p.Prime := fun p hp => hU p (Finset.mem_insert_of_mem hp)
    have hcop' : ∀ p ∈ U', Nat.Coprime p Q := fun p hp => hcop p (Finset.mem_insert_of_mem hp)
    obtain ⟨rq, hrq_mem, hrq_dvd, hrq_uniq⟩ :=
      exists_unique_root_Lform Q b s (idx q) hqP (hcop q (Finset.mem_insert_self q U'))
    have hrq_lt : rq < q := Finset.mem_range.mp hrq_mem
    obtain ⟨a', ha'_lt, ha'_iff⟩ := ih hU' hcop'
    have hcop_qU : Nat.Coprime q (val U') :=
      hqP.coprime_iff_not_dvd.mpr fun hdvd => hq ((mem_iff_dvd_val hU' hqP).mpr hdvd)
    let c := Nat.chineseRemainder hcop_qU rq a'
    let a₀ := c.val % (q * val U')
    have ha₀_lt : a₀ < val (insert q U') := by
      rw [val_insert hq]
      exact Nat.mod_lt _ (Nat.mul_pos hqP.pos (val_pos hU'))
    have ha₀_q : a₀ % q = rq := by
      dsimp [a₀]
      rw [Nat.mod_mod_of_dvd c.val (dvd_mul_right q (val U')),
        show c.val % q = rq % q from c.property.1, Nat.mod_eq_of_lt hrq_lt]
    have ha₀_U : a₀ % val U' = a' := by
      dsimp [a₀]
      rw [Nat.mod_mod_of_dvd c.val (dvd_mul_left (val U') q),
        show c.val % val U' = a' % val U' from c.property.2, Nat.mod_eq_of_lt ha'_lt]
    refine ⟨a₀, ha₀_lt, fun t => ?_⟩
    rw [val_insert hq]
    have hq_iff : (q : ℤ) ∣ Lform Q b s (idx q) t ↔ t % q = rq := by
      rw [← dvd_Lform_mod_iff Q b s (idx q) q t]
      constructor
      · intro h; exact hrq_uniq (t % q) (Finset.mem_range.mpr (Nat.mod_lt t hqP.pos)) h
      · intro h; rw [h]; exact hrq_dvd
    have hmod_iff : t % (q * val U') = a₀ ↔ t % q = rq ∧ t % val U' = a' := by
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · rw [← ha₀_q, ← h, Nat.mod_mod_of_dvd t (dvd_mul_right q (val U'))]
        · rw [← ha₀_U, ← h, Nat.mod_mod_of_dvd t (dvd_mul_left (val U') q)]
      · rintro ⟨hqeq, hUeq⟩
        have h1 : t ≡ a₀ [MOD q] := by rw [Nat.ModEq, hqeq, ha₀_q]
        have h2 : t ≡ a₀ [MOD val U'] := by rw [Nat.ModEq, hUeq, ha₀_U]
        have h3 : t ≡ a₀ [MOD q * val U'] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hcop_qU).mp ⟨h1, h2⟩
        rw [Nat.ModEq] at h3
        rw [h3, Nat.mod_eq_of_lt (by rwa [← val_insert hq])]
    rw [hmod_iff, ← hq_iff, ← ha'_iff]
    constructor
    · intro hall
      exact ⟨hall q (Finset.mem_insert_self q U'),
        fun p hp => hall p (Finset.mem_insert_of_mem hp)⟩
    · rintro ⟨h1, h2⟩ p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact h1
      · exact h2 p hp'

lemma avg_mod_eq_inv {P q a₀ : ℕ} (hq : 0 < q) (hdvd : q ∣ P) (hP : 0 < P) (ha : a₀ < q) :
    avg P (fun t => if t % q = a₀ then (1 : ℝ) else 0) = 1 / (q : ℝ) := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm_pos : 0 < m := Nat.pos_of_mul_pos_left hP
  have hcount : ∑ t ∈ Finset.range (q * m), (if t % q = a₀ then (1 : ℝ) else 0) = (m : ℝ) := by
    have hbij : ∑ t ∈ Finset.range (q * m), (if t % q = a₀ then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range m, ∑ r ∈ Finset.range q, (if (j * q + r) % q = a₀ then (1 : ℝ) else 0) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun t _ => (t / q, t % q)) ?_ ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_range] at ht
        refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr (Nat.mod_lt t hq)⟩
        exact (Nat.div_lt_iff_lt_mul hq).mpr (by linarith [mul_comm q m])
      · intro t₁ _ t₂ _ h
        have h1 : t₁ / q = t₂ / q := congrArg Prod.fst h
        have h2 : t₁ % q = t₂ % q := congrArg Prod.snd h
        have e1 := Nat.div_add_mod t₁ q
        have e2 := Nat.div_add_mod t₂ q
        rw [← e1, ← e2, h1, h2]
      · intro jr hjr
        obtain ⟨hj, hr⟩ := Finset.mem_product.mp hjr
        rw [Finset.mem_range] at hj hr
        refine ⟨jr.1 * q + jr.2, Finset.mem_range.mpr ?_, ?_⟩
        · nlinarith
        · apply Prod.ext
          · rw [mul_comm jr.1 q, Nat.mul_add_div hq, Nat.div_eq_of_lt hr, add_zero]
          · rw [mul_comm jr.1 q, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · intro t _
        have e : t / q * q + t % q = t := by rw [mul_comm]; exact Nat.div_add_mod t q
        rw [e]
    rw [hbij]
    have hinner : ∀ j ∈ Finset.range m,
        ∑ r ∈ Finset.range q, (if (j * q + r) % q = a₀ then (1 : ℝ) else 0) = 1 := by
      intro j _
      have hcongr : ∀ r ∈ Finset.range q,
          (if (j * q + r) % q = a₀ then (1 : ℝ) else 0) = if r = a₀ then 1 else 0 := by
        intro r hr
        rw [mul_comm j q, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hcongr]
      simp [Finset.mem_range.mpr ha]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  unfold avg
  rw [hcount]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp [hm0, hq0]

lemma Icc_mod_count_diff {T q a₀ : ℕ} (hT : 0 < T) (hq : 0 < q) (ha : a₀ < q) :
    |(1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, if t % q = a₀ then (1 : ℝ) else 0) - 1 / (q : ℝ)| ≤
      1 / (T : ℝ) := by
  let l := T / q
  let h := T % q
  have hT_eq : T = l * q + h := by dsimp [l, h]; rw [mul_comm]; exact (Nat.div_add_mod T q).symm
  have hh_lt : h < q := Nat.mod_lt T hq
  -- Split Icc 1 T into Icc 1 (l * q) and Ioc (l * q) T
  have hsplit : Finset.Icc 1 T = Finset.Icc 1 (l * q) ∪ Finset.Ioc (l * q) T := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (l * q)) (Finset.Ioc (l * q) T) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega
  -- Count on Icc 1 (l * q) equals l
  have hfull : ∑ t ∈ Finset.Icc 1 (l * q), (if t % q = a₀ then (1 : ℝ) else 0) = (l : ℝ) := by
    let a₁ := if a₀ = 0 then q - 1 else a₀ - 1
    have ha₁_lt : a₁ < q := by dsimp [a₁]; split_ifs <;> omega
    have hshift : ∑ t ∈ Finset.Icc 1 (l * q), (if t % q = a₀ then (1 : ℝ) else 0) =
        ∑ u ∈ Finset.range (q * l), (if u % q = a₁ then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun t _ => t - 1) ?_ ?_ ?_ ?_
      · intro t ht; rw [Finset.mem_Icc] at ht; rw [Finset.mem_range, mul_comm]; omega
      · intro t₁ ht₁ t₂ ht₂ heq; rw [Finset.mem_Icc] at ht₁ ht₂; omega
      · intro u hu; rw [Finset.mem_range] at hu
        exact ⟨u + 1, Finset.mem_Icc.mpr ⟨by omega, by nlinarith⟩, by omega⟩
      · intro t ht
        rw [Finset.mem_Icc] at ht
        have ht1 : t = (t - 1) + 1 := by omega
        have hiff : t % q = a₀ ↔ (t - 1) % q = a₁ := by
          have hmod_succ : ((t - 1) + 1) % q = if (t - 1) % q + 1 = q then 0 else (t - 1) % q + 1 := by
            have hlt : (t - 1) % q < q := Nat.mod_lt _ hq
            by_cases he : (t - 1) % q + 1 = q
            · rw [if_pos he]
              have hdiv : (t - 1) + 1 = q * ((t - 1) / q + 1) := by
                have := Nat.div_add_mod (t - 1) q; nlinarith
              rw [hdiv, Nat.mul_mod_right]
            · rw [if_neg he]
              have hdiv : (t - 1) + 1 = q * ((t - 1) / q) + ((t - 1) % q + 1) := by
                have := Nat.div_add_mod (t - 1) q; omega
              rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          rw [ht1, hmod_succ]
          dsimp [a₁]
          have hlt : (t - 1) % q < q := Nat.mod_lt _ hq
          split_ifs <;> omega
        simp [hiff]
    rw [hshift]
    by_cases hl0 : l = 0
    · simp [hl0]
    · have hl_pos : 0 < l := Nat.pos_of_ne_zero hl0
      have havg := avg_mod_eq_inv (P := q * l) hq (dvd_mul_right q l) (Nat.mul_pos hq hl_pos) ha₁_lt
      unfold avg at havg
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      have hl0R : (l : ℝ) ≠ 0 := by exact_mod_cast hl_pos.ne'
      push_cast at havg
      have hmul := congrArg (fun x => ((q : ℝ) * (l : ℝ)) * x) havg
      field_simp [hq0, hl0R] at hmul
      linarith
  -- Count on Ioc (l * q) T is in [0, 1]
  have hrem_nn : 0 ≤ ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hrem_le1 : ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0) ≤ 1 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard1 : ((Finset.Ioc (l * q) T).filter (fun t => t % q = a₀)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro t₁ ht₁ t₂ ht₂
      rw [Finset.mem_filter, Finset.mem_Ioc] at ht₁ ht₂
      have h1 := Nat.div_add_mod t₁ q
      have h2 := Nat.div_add_mod t₂ q
      have hdiv_eq : t₁ / q = t₂ / q := by
        have hlt1 : t₁ < t₂ + q := by omega
        have hlt2 : t₂ < t₁ + q := by omega
        nlinarith
      rw [← h1, ← h2, hdiv_eq, ht₁.2, ht₂.2]
    exact_mod_cast hcard1
  rw [hsplit, Finset.sum_union hdisj, hfull]
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have hT_eqR : (T : ℝ) = (l : ℝ) * (q : ℝ) + (h : ℝ) := by exact_mod_cast hT_eq
  have hh_ltR : (h : ℝ) < (q : ℝ) := by exact_mod_cast hh_lt
  have hh_nnR : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hTq_lo : (l : ℝ) ≤ (T : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hq_pos]; linarith
  have hTq_hi : (T : ℝ) / (q : ℝ) ≤ (l : ℝ) + 1 := by
    rw [div_le_iff₀ hq_pos]; linarith
  rw [abs_le]
  constructor
  · have h1 : -1 ≤ ((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        (T : ℝ) / (q : ℝ) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 / (T : ℝ) by positivity)
    have e : 1 / (T : ℝ) * (((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        (T : ℝ) / (q : ℝ)) =
        1 / (T : ℝ) * ((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        1 / (q : ℝ) := by field_simp [hT_pos.ne', hq_pos.ne']
    linarith
  · have h1 : ((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        (T : ℝ) / (q : ℝ) ≤ 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 / (T : ℝ) by positivity)
    have e : 1 / (T : ℝ) * (((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        (T : ℝ) / (q : ℝ)) =
        1 / (T : ℝ) * ((l : ℝ) + ∑ t ∈ Finset.Ioc (l * q) T, (if t % q = a₀ then (1 : ℝ) else 0)) -
        1 / (q : ℝ) := by field_simp [hT_pos.ne', hq_pos.ne']
    linarith

lemma avg_Jtuple_mul_diff {k : ℕ} (hk : 0 < k) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    (hcop : ∀ p ∈ Pstar, Nat.Coprime p Q)
    (hdiff : ∀ p ∈ Pstar, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j))
    {D : ℝ} {T : ℕ} (hT : 0 < T)
    {d e : Fin k → Finset ℕ} (hd : d ∈ Dset Pstar D k) (he : e ∈ Dset Pstar D k) :
    |(1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, Jtuple Q b s d t * Jtuple Q b s e t) -
      avg (val Pstar) (fun t => Jtuple Q b s d t * Jtuple Q b s e t)| ≤ 1 / (T : ℝ) := by
  classical
  by_cases hcross : ∃ i j : Fin k, i ≠ j ∧ ¬ Disjoint (d i) (e j)
  · obtain ⟨i, j, hij, hndisj⟩ := hcross
    rw [Finset.not_disjoint_iff] at hndisj
    obtain ⟨p, hpd, hpe⟩ := hndisj
    have hpP : p ∈ Pstar := (mem_Dset_iff.mp hd).1 i hpd
    have hzero : ∀ t : ℕ, Jtuple Q b s d t * Jtuple Q b s e t = 0 := by
      intro t
      by_contra hne
      have hd1 : Jtuple Q b s d t ≠ 0 := left_ne_zero_of_mul hne
      have he1 : Jtuple Q b s e t ≠ 0 := right_ne_zero_of_mul hne
      have hdi : indDiv (d i) (Lform Q b s i t) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hd1 i (Finset.mem_univ i)
      have hej : indDiv (e j) (Lform Q b s j t) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp he1 j (Finset.mem_univ j)
      have hdi_dvd : (val (d i) : ℤ) ∣ Lform Q b s i t := by
        unfold indDiv at hdi; split_ifs at hdi with h; exact h; exact absurd rfl hdi
      have hej_dvd : (val (e j) : ℤ) ∣ Lform Q b s j t := by
        unfold indDiv at hej; split_ifs at hej with h; exact h; exact absurd rfl hej
      have hp_i : (p : ℤ) ∣ Lform Q b s i t :=
        dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem _ hpd) hdi_dvd
      have hp_j : (p : ℤ) ∣ Lform Q b s j t :=
        dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem _ hpe) hej_dvd
      apply hdiff p hpP i j hij
      have e_diff : s i - s j = Lform Q b s i t - Lform Q b s j t := by unfold Lform; ring
      rw [e_diff]; exact dvd_sub hp_i hp_j
    simp_rw [hzero]
    rw [Finset.sum_const_zero, mul_zero, avg_zero, sub_self, abs_zero]
    positivity
  · push Not at hcross
    set U := unionOf d ∪ unionOf e
    have hU_sub : U ⊆ Pstar := Finset.union_subset (unionOf_subset hd) (unionOf_subset he)
    have hU_P : ∀ p ∈ U, p.Prime := fun p hp => hP p (hU_sub hp)
    have hU_cop : ∀ p ∈ U, Nat.Coprime p Q := fun p hp => hcop p (hU_sub hp)
    let idx : ℕ → Fin k := fun p =>
      if h : p ∈ unionOf d then idxOf d p h
      else if h2 : p ∈ unionOf e then idxOf e p h2
      else ⟨0, hk⟩
    have hidx_d : ∀ i : Fin k, ∀ p ∈ d i, idx p = i := by
      intro i p hpi
      have hp : p ∈ unionOf d := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hpi⟩
      simp only [idx, hp, ↓reduceDIte]
      exact idxOf_eq_of_mem (mem_Dset_iff.mp hd).2.1 hpi hp
    have hidx_e : ∀ i : Fin k, ∀ p ∈ e i, idx p = i := by
      intro i p hpi
      have hp : p ∈ unionOf e := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hpi⟩
      by_cases hpd : p ∈ unionOf d
      · simp only [idx, hpd, ↓reduceDIte]
        have hmem := mem_idxOf d hpd
        by_contra hne
        exact Finset.disjoint_left.mp (hcross _ _ hne) hmem hpi
      · simp only [idx, hpd, hp, ↓reduceDIte]
        exact idxOf_eq_of_mem (mem_Dset_iff.mp he).2.1 hpi hp
    obtain ⟨a₀, ha₀_lt, ha₀_iff⟩ := crt_system_of_primes Q b s U hU_P hU_cop idx
    have hJ_eq : ∀ t : ℕ, Jtuple Q b s d t * Jtuple Q b s e t =
        if t % val U = a₀ then 1 else 0 := by
      intro t
      have hiff : (∀ i : Fin k, (val (d i) : ℤ) ∣ Lform Q b s i t ∧ (val (e i) : ℤ) ∣ Lform Q b s i t) ↔
          (∀ p ∈ U, (p : ℤ) ∣ Lform Q b s (idx p) t) := by
        constructor
        · intro hall p hp
          rcases Finset.mem_union.mp hp with hpd | hpe
          · obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hpd
            rw [hidx_d i p hpi]
            exact dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem _ hpi) (hall i).1
          · obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hpe
            rw [hidx_e i p hpi]
            exact dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem _ hpi) (hall i).2
        · intro hall i
          have hdiP : ∀ p ∈ d i, p.Prime := fun p hp => hP p ((mem_Dset_iff.mp hd).1 i hp)
          have heiP : ∀ p ∈ e i, p.Prime := fun p hp => hP p ((mem_Dset_iff.mp he).1 i hp)
          constructor
          · have hnat : val (d i) ∣ (Lform Q b s i t).natAbs := by
              unfold val
              refine Finset.prod_primes_dvd _ (fun p hp => (hdiP p hp).prime) fun p hp => ?_
              have hpU : p ∈ U := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩)
              have hdiv := hall p hpU
              rw [hidx_d i p hp] at hdiv
              exact Int.natCast_dvd.mp hdiv
            exact Int.natCast_dvd.mpr hnat
          · have hnat : val (e i) ∣ (Lform Q b s i t).natAbs := by
              unfold val
              refine Finset.prod_primes_dvd _ (fun p hp => (heiP p hp).prime) fun p hp => ?_
              have hpU : p ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩)
              have hdiv := hall p hpU
              rw [hidx_e i p hp] at hdiv
              exact Int.natCast_dvd.mp hdiv
            exact Int.natCast_dvd.mpr hnat
      by_cases hmod : t % val U = a₀
      · rw [if_pos hmod]
        have hall := hiff.mpr ((ha₀_iff t).mpr hmod)
        unfold Jtuple
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro i _
        simp [indDiv, (hall i).1, (hall i).2]
      · rw [if_neg hmod]
        have hnot : ¬ ∀ i : Fin k, (val (d i) : ℤ) ∣ Lform Q b s i t ∧ (val (e i) : ℤ) ∣ Lform Q b s i t :=
          fun hall => hmod ((ha₀_iff t).mp (hiff.mp hall))
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        unfold Jtuple
        by_cases hdi : (val (d i) : ℤ) ∣ Lform Q b s i t
        · have hei := hi hdi
          have h0 : ∏ j : Fin k, indDiv (e j) (Lform Q b s j t) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indDiv, hei])
          rw [h0, mul_zero]
        · have h0 : ∏ j : Fin k, indDiv (d j) (Lform Q b s j t) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indDiv, hdi])
          rw [h0, zero_mul]
    simp_rw [hJ_eq]
    have hq_pos : 0 < val U := val_pos hU_P
    have hq_dvd : val U ∣ val Pstar := Finset.prod_dvd_prod_of_subset _ _ _ hU_sub
    rw [avg_mod_eq_inv hq_pos hq_dvd (val_pos hP) ha₀_lt]
    exact Icc_mod_count_diff hT hq_pos ha₀_lt

/-- Lemma 3.4 (Finite-average comparison) for any partial sum `J ⊆ Dset Pstar D k`. -/
lemma lem_finite_averages {k : ℕ} (hk : 0 < k) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    (hcop : ∀ p ∈ Pstar, Nat.Coprime p Q)
    (hdiff : ∀ p ∈ Pstar, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j))
    {z : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p)
    {D : ℝ} (hD8 : 8 ≤ D) (hkz : (k : ℝ) ^ 6 ≤ (z : ℝ))
    (hsmall : 3 * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) ≤ Real.log 2)
    {T : ℕ} (hT : 0 < T)
    (a : Finset ℕ → ℝ) (ha : ∀ t ∈ Pstar.powerset, |a t| ≤ 1)
    (J : Finset (Fin k → Finset ℕ)) (hJ : J ⊆ Dset Pstar D k) :
    |(1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, (Rpartial Pstar D a Q b s J t) ^ 2) -
      avg (val Pstar) (fun t => (Rpartial Pstar D a Q b s J t) ^ 2)| ≤
      D ^ 3 / (T : ℝ) := by
  have hsq : ∀ t, (Rpartial Pstar D a Q b s J t) ^ 2 =
      ∑ d ∈ J, ∑ e ∈ J,
        (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
          (Jtuple Q b s d t * Jtuple Q b s e t) := by
    intro t
    unfold Rpartial
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    ring
  have hLHS : (1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, (Rpartial Pstar D a Q b s J t) ^ 2) -
      avg (val Pstar) (fun t => (Rpartial Pstar D a Q b s J t) ^ 2) =
      ∑ d ∈ J, ∑ e ∈ J, (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
        ((1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, Jtuple Q b s d t * Jtuple Q b s e t) -
          avg (val Pstar) (fun t => Jtuple Q b s d t * Jtuple Q b s e t)) := by
    simp_rw [hsq]
    rw [avg_sum, Finset.sum_comm]
    have h1 : (1 / (T : ℝ)) * ∑ d ∈ J, ∑ t ∈ Finset.Icc 1 T, ∑ e ∈ J,
        (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) * (Jtuple Q b s d t * Jtuple Q b s e t) =
        ∑ d ∈ J, ∑ e ∈ J, (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
          ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, Jtuple Q b s d t * Jtuple Q b s e t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d _
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [← Finset.mul_sum]; ring
    have h2 : ∑ d ∈ J, avg (val Pstar) (fun t => ∑ e ∈ J,
        (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) * (Jtuple Q b s d t * Jtuple Q b s e t)) =
        ∑ d ∈ J, ∑ e ∈ J, (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
          avg (val Pstar) (fun t => Jtuple Q b s d t * Jtuple Q b s e t) := by
      apply Finset.sum_congr rfl; intro d _
      rw [avg_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [avg_const_mul]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro d _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro e _
    ring
  rw [hLHS]
  have hsum_lam : ∑ d ∈ J, |lambdaCoeff Pstar D a d| ≤ D ^ ((3 : ℝ) / 2) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hJ fun _ _ _ => abs_nonneg _).trans
      (sum_abs_lambda_le hP hz hgt hD8 hk hkz hsmall a ha)
  have hD_pos : 0 < D := by linarith
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  have hD3 : (D ^ ((3 : ℝ) / 2)) ^ 2 = D ^ 3 := by
    rw [sq, ← Real.rpow_add hD_pos]
    norm_num
  calc |∑ d ∈ J, ∑ e ∈ J, (lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
          ((1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, Jtuple Q b s d t * Jtuple Q b s e t) -
            avg (val Pstar) (fun t => Jtuple Q b s d t * Jtuple Q b s e t))|
      ≤ ∑ d ∈ J, ∑ e ∈ J, |(lambdaCoeff Pstar D a d * lambdaCoeff Pstar D a e) *
          ((1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, Jtuple Q b s d t * Jtuple Q b s e t) -
            avg (val Pstar) (fun t => Jtuple Q b s d t * Jtuple Q b s e t))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ J, ∑ e ∈ J, (|lambdaCoeff Pstar D a d| * |lambdaCoeff Pstar D a e|) * (1 / (T : ℝ)) := by
        apply Finset.sum_le_sum; intro d hd
        apply Finset.sum_le_sum; intro e he
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (avg_Jtuple_mul_diff hk Q b s hP hcop hdiff hT (hJ hd) (hJ he))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (1 / (T : ℝ)) * (∑ d ∈ J, |lambdaCoeff Pstar D a d|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _; ring
    _ ≤ (1 / (T : ℝ)) * (D ^ ((3 : ℝ) / 2)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hnn : 0 ≤ ∑ d ∈ J, |lambdaCoeff Pstar D a d| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        exact sq_le_sq' (by linarith [Real.rpow_nonneg hD_pos.le ((3 : ℝ) / 2)]) hsum_lam
    _ = D ^ 3 / (T : ℝ) := by rw [hD3]; ring

/- ## Part 8: Sections 3.6-3.7 - Total Weight, Uncovered Forms, and `lem_translate` -/

open scoped Classical in
noncomputable def eps (Pstar : Finset ℕ) (D : ℝ) (a : Finset ℕ → ℝ) (v : Finset ℕ) : ℝ :=
  ∑ d ∈ Pstar.powerset.filter (fun d => Disjoint d v ∧ (val d : ℝ) ≤ D / (val v : ℝ)),
    a d / phi d

open scoped Classical in
noncomputable def cUncov (Pstar : Finset ℕ) (D : ℝ) {k : ℕ} (a : Finset ℕ → ℝ) (i₀ : Fin k)
    (r : Fin k → Finset ℕ) : ℝ :=
  if r i₀ = ∅ then eps Pstar D a (unionOf r) * ∏ i ∈ Finset.univ.erase i₀, a (r i) else 0

lemma Rweight_eq_Rpartial_erase_of_uncov {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {D : ℝ} {k : ℕ} (a : Finset ℕ → ℝ) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    (i₀ : Fin k) (t : ℕ) (huncov : ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i₀ t) :
    Rweight Pstar D a Q b s t =
      Rpartial Pstar D a Q b s ((Dset Pstar D k).filter (fun d => d i₀ = ∅)) t := by
  classical
  rw [Rweight_eq_Rpartial_full hP]
  unfold Rpartial
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hne : d i₀ ≠ ∅ := fun h0 => hnot (Finset.mem_filter.mpr ⟨hd, h0⟩)
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hpP : p ∈ Pstar := (mem_Dset_iff.mp hd).1 i₀ hp
  have hnd : ¬ (val (d i₀) : ℤ) ∣ Lform Q b s i₀ t := by
    intro hdvd
    exact huncov p hpP (dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem _ hp) hdvd)
  have hJ0 : Jtuple Q b s d t = 0 := by
    unfold Jtuple
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [indDiv, hnd])
  rw [hJ0, mul_zero]

lemma Rpartial_erase_eq_sum_eps {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {D : ℝ} {k : ℕ} (a : Finset ℕ → ℝ) (Q : ℕ) (b : ℤ) (s : Fin k → ℤ)
    (i₀ : Fin k) (t : ℕ) :
    Rpartial Pstar D a Q b s ((Dset Pstar D k).filter (fun d => d i₀ = ∅)) t =
      ∑ r ∈ Dset Pstar D k, cUncov Pstar D a i₀ r * ∏ i : Fin k, psiProd Q b s i (r i) t := by
  classical
  set DS := Dset Pstar D k
  set J := DS.filter (fun d => d i₀ = ∅)
  -- Step 1: Expand Rpartial and swap (d, r)
  have h1 : Rpartial Pstar D a Q b s J t =
      ∑ r ∈ DS, (a (r i₀) / phi (r i₀)) *
        ∏ i ∈ Finset.univ.erase i₀, (a (r i) * psiProd Q b s i (r i) t) := by
    unfold Rpartial lambdaCoeff Jtuple
    have hite : ∀ d ∈ J,
        (∑ r ∈ DS.filter (fun r => ∀ i, d i ⊆ r i),
          ∏ i : Fin k, (a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ))) *
          (∏ i : Fin k, indDiv (d i) (Lform Q b s i t)) =
        ∑ r ∈ DS, if ∀ i, d i ⊆ r i then
          ∏ i : Fin k, ((a (r i) / phi (r i) * (-1 : ℝ) ^ (d i).card * (val (d i) : ℝ)) *
            indDiv (d i) (Lform Q b s i t)) else 0 := by
      intro d _
      rw [Finset.sum_mul, ← Finset.sum_filter]
      apply Finset.sum_congr rfl; intro r _
      rw [← Finset.prod_mul_distrib]
    rw [Finset.sum_congr rfl hite, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    have hr_sub := (mem_Dset_iff.mp hr).1
    rw [← Finset.sum_filter]
    have hfilt : J.filter (fun d => ∀ i, d i ⊆ r i) =
        Fintype.piFinset (fun i : Fin k => if i = i₀ then {∅} else (r i).powerset) := by
      ext d
      simp only [J, Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨⟨_, h0⟩, hsub⟩ i
        split_ifs with hi
        · subst hi; simp [h0]
        · exact Finset.mem_powerset.mpr (hsub i)
      · intro hall
        have h0 : d i₀ = ∅ := by simpa using hall i₀
        have hsub : ∀ i, d i ⊆ r i := by
          intro i
          have hi := hall i
          split_ifs at hi with h
          · subst h; rw [Finset.mem_singleton.mp hi]; exact Finset.empty_subset _
          · exact Finset.mem_powerset.mp hi
        exact ⟨⟨sub_mem_Dset hP hr hsub, h0⟩, hsub⟩
    rw [hfilt, sum_piFinset_prod (s := fun i : Fin k => if i = i₀ then {∅} else (r i).powerset)
      (f := fun i t_i => (a (r i) / phi (r i) * (-1 : ℝ) ^ t_i.card * (val t_i : ℝ)) *
        indDiv t_i (Lform Q b s i t)),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    congr 1
    · simp [val_empty, indDiv]
    · apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      rw [if_neg hne, psiProd_eq_sum_indDiv Q b s i (fun p hp => hP p (hr_sub i hp)) t,
        ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d_i _; ring
  -- Step 2: Group r ∈ DS by r' = Function.update r i₀ ∅ ∈ J
  have hmaps : ∀ r ∈ DS, Function.update r i₀ ∅ ∈ J := by
    intro r hr
    refine Finset.mem_filter.mpr ⟨sub_mem_Dset hP hr fun i => ?_, Function.update_self i₀ ∅ r⟩
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne hi]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  have hRHS : ∑ r ∈ DS, cUncov Pstar D a i₀ r * ∏ i : Fin k, psiProd Q b s i (r i) t =
      ∑ r' ∈ J, eps Pstar D a (unionOf r') *
        ∏ i ∈ Finset.univ.erase i₀, (a (r' i) * psiProd Q b s i (r' i) t) := by
    have hsub : ∑ r ∈ DS, cUncov Pstar D a i₀ r * ∏ i : Fin k, psiProd Q b s i (r i) t =
        ∑ r' ∈ J, cUncov Pstar D a i₀ r' * ∏ i : Fin k, psiProd Q b s i (r' i) t := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hr hnot
      have hne : r i₀ ≠ ∅ := fun h0 => hnot (Finset.mem_filter.mpr ⟨hr, h0⟩)
      simp [cUncov, hne]
    rw [hsub]
    apply Finset.sum_congr rfl
    intro r' hr'
    have h0 : r' i₀ = ∅ := (Finset.mem_filter.mp hr').2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    have hpsi0 : psiProd Q b s i₀ (r' i₀) t = 1 := by simp [psiProd, h0]
    rw [hpsi0, one_mul, Finset.prod_mul_distrib]
    simp only [cUncov, h0, ↓reduceIte]
    ring
  rw [hRHS]
  apply Finset.sum_congr rfl
  intro r' hr'
  have hr'_DS : r' ∈ DS := (Finset.mem_filter.mp hr').1
  have hr'_0 : r' i₀ = ∅ := (Finset.mem_filter.mp hr').2
  have hr'_sub := (mem_Dset_iff.mp hr'_DS).1
  have hr'_disj := (mem_Dset_iff.mp hr'_DS).2.1
  have hprod_eq : ∀ r ∈ DS.filter (fun r => Function.update r i₀ ∅ = r'),
      ∏ i ∈ Finset.univ.erase i₀, (a (r i) * psiProd Q b s i (r i) t) =
      ∏ i ∈ Finset.univ.erase i₀, (a (r' i) * psiProd Q b s i (r' i) t) := by
    intro r hr
    have hupd := (Finset.mem_filter.mp hr).2
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have hri : r i = r' i := by
      have := congrFun hupd i
      rwa [Function.update_of_ne hne] at this
    rw [hri]
  rw [Finset.sum_congr rfl (fun r hr => by rw [hprod_eq r hr]), ← Finset.sum_mul]
  congr 1
  -- Bijection between fiber {r ∈ DS | update r i₀ ∅ = r'} and {d ⊆ Pstar | Disjoint d (unionOf r') ∧ val d ≤ D / val (unionOf r')}
  unfold eps
  have hval_r'_pos : (0 : ℝ) < val (unionOf r') := by
    exact_mod_cast val_pos (fun p hp => hP p (unionOf_subset hr'_DS hp))
  refine Finset.sum_bij (fun r _ => r i₀) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr
    have hr_m := mem_Dset_iff.mp hr.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hr_m.1 i₀), ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro p hpi0 hpU
      obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hpU
      by_cases hji : j = i₀
      · subst hji; rw [hr'_0] at hpj; exact Finset.notMem_empty p hpj
      · have hrj : r j = r' j := by
          have := congrFun hr.2 j
          rwa [Function.update_of_ne hji] at this
        rw [← hrj] at hpj
        exact Finset.disjoint_left.mp (hr_m.2.1 i₀ j (Ne.symm hji)) hpi0 hpj
    · rw [le_div_iff₀ hval_r'_pos]
      have hmul : (val (r i₀) : ℝ) * (val (unionOf r') : ℝ) = ((∏ i : Fin k, val (r i) : ℕ) : ℝ) := by
        rw [val_unionOf hr'_disj, ← Finset.mul_prod_erase Finset.univ (fun i => val (r' i)) (Finset.mem_univ i₀),
          hr'_0, val_empty, one_mul, ← Finset.mul_prod_erase Finset.univ (fun i => val (r i)) (Finset.mem_univ i₀)]
        have hpeq : ∏ i ∈ Finset.univ.erase i₀, val (r i) = ∏ i ∈ Finset.univ.erase i₀, val (r' i) := by
          apply Finset.prod_congr rfl; intro i hi
          have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          have := congrFun hr.2 i
          rw [Function.update_of_ne hne] at this
          rw [this]
        rw [hpeq, Nat.cast_mul]
      rw [hmul]
      exact hr_m.2.2
  · intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_filter] at hr₁ hr₂
    funext i
    by_cases hi : i = i₀
    · subst hi; exact heq
    · have h1 := congrFun hr₁.2 i
      have h2 := congrFun hr₂.2 i
      rw [Function.update_of_ne hi] at h1 h2
      exact h1.trans h2.symm
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_powerset] at hd
    refine ⟨Function.update r' i₀ d, ?_, Function.update_self i₀ d r'⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_Dset_iff]
      refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
      · by_cases hi : i = i₀
        · subst hi; rw [Function.update_self]; exact hd.1
        · rw [Function.update_of_ne hi]; exact hr'_sub i
      · by_cases hi : i = i₀
        · subst hi
          rw [Function.update_self, Function.update_of_ne hij.symm]
          exact Disjoint.mono_right (Finset.subset_biUnion_of_mem r' (Finset.mem_univ j)) hd.2.1
        · by_cases hj : j = i₀
          · subst hj
            rw [Function.update_of_ne hi, Function.update_self]
            exact (Disjoint.mono_right (Finset.subset_biUnion_of_mem r' (Finset.mem_univ i)) hd.2.1).symm
          · rw [Function.update_of_ne hi, Function.update_of_ne hj]
            exact hr'_disj i j hij
      · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), Function.update_self]
        have hpeq : ∏ i ∈ Finset.univ.erase i₀, val (Function.update r' i₀ d i) = val (unionOf r') := by
          rw [val_unionOf hr'_disj,
            ← Finset.mul_prod_erase Finset.univ (fun i => val (r' i)) (Finset.mem_univ i₀),
            hr'_0, val_empty, one_mul]
          apply Finset.prod_congr rfl; intro i hi
          rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
        rw [hpeq, Nat.cast_mul]
        exact (le_div_iff₀ hval_r'_pos).mp hd.2.2
    · funext i
      by_cases hi : i = i₀
      · subst hi; simp [hr'_0]
      · simp [Function.update_of_ne hi]
  · intro _ _; rfl

lemma eps_bound {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {z : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p)
    {D β C_tilt C_p : ℝ} (hD1 : 1 ≤ D) (hβ : 0 < β) (hCp_nn : 0 ≤ C_p)
    (a : Finset ℕ → ℝ)
    (hcancel : ∑ d ∈ Pstar.powerset, a d / phi d = 0)
    (haneg : ∀ d ∈ Pstar.powerset.erase ∅, a d ≤ 0)
    (htilt : ∑ d ∈ Pstar.powerset.erase ∅, |a d| * ((val d : ℝ) ^ β) / phi d ≤ C_tilt)
    (hprime : ∀ p ∈ Pstar, ∑ d ∈ Pstar.powerset.filter (fun d => p ∈ d), |a d| / phi d ≤ C_p / (p : ℝ))
    {v : Finset ℕ} (hv_sub : v ⊆ Pstar) (hv_le : (val v : ℝ) ≤ D) :
    0 ≤ eps Pstar D a v ∧
    eps Pstar D a v ≤ C_tilt * ((val v : ℝ) / D) ^ β + C_p * Real.log D / (z : ℝ) := by
  classical
  have hv_P : ∀ p ∈ v, p.Prime := fun p hp => hP p (hv_sub hp)
  have hv_pos : (0 : ℝ) < val v := by exact_mod_cast val_pos hv_P
  have hD_pos : 0 < D := by linarith
  set Good := Pstar.powerset.filter (fun d => Disjoint d v ∧ (val d : ℝ) ≤ D / (val v : ℝ))
  set Bad := Pstar.powerset.filter (fun d => ¬ (Disjoint d v ∧ (val d : ℝ) ≤ D / (val v : ℝ)))
  have h0_good : ∅ ∈ Good := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, Finset.disjoint_empty_left v, ?_⟩
    rw [val_empty, Nat.cast_one, le_div_iff₀ hv_pos, one_mul]
    exact hv_le
  have hBad_ne : Bad ⊆ Pstar.powerset.erase ∅ := by
    intro d hd
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_filter.mp hd).1⟩
    rintro rfl
    exact (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp h0_good).2
  have heps_eq : eps Pstar D a v = ∑ d ∈ Bad, |a d| / phi d := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Pstar.powerset
      (fun d => Disjoint d v ∧ (val d : ℝ) ≤ D / (val v : ℝ)) (fun d => a d / phi d)
    change eps Pstar D a v + ∑ d ∈ Bad, a d / phi d = ∑ d ∈ Pstar.powerset, a d / phi d at hsplit
    rw [hcancel] at hsplit
    have hneg : -∑ d ∈ Bad, a d / phi d = ∑ d ∈ Bad, |a d| / phi d := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hle0 := haneg d (hBad_ne hd)
      rw [abs_of_nonpos hle0]; ring
    linarith
  have heps_nn : 0 ≤ eps Pstar D a v := by
    rw [heps_eq]
    exact Finset.sum_nonneg fun d hd =>
      div_nonneg (abs_nonneg _)
        (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1 hp))).le
  refine ⟨heps_nn, ?_⟩
  rw [heps_eq]
  set Bad1 := (Pstar.powerset.erase ∅).filter (fun d => D / (val v : ℝ) < (val d : ℝ))
  set Bad2 := v.biUnion (fun p => Pstar.powerset.filter (fun d => p ∈ d))
  have hBad_sub : Bad ⊆ Bad1 ∪ Bad2 := by
    intro d hd
    have hd_er := hBad_ne hd
    have hnot := (Finset.mem_filter.mp hd).2
    by_cases hdisj : Disjoint d v
    · have hgt_val : D / (val v : ℝ) < (val d : ℝ) := lt_of_not_ge fun hle => hnot ⟨hdisj, hle⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd_er, hgt_val⟩)
    · rw [Finset.not_disjoint_iff] at hdisj
      obtain ⟨p, hpd, hpv⟩ := hdisj
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, hpv, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, hpd⟩⟩)
  have hterm_nn : ∀ d ∈ Pstar.powerset, 0 ≤ |a d| / phi d := fun d hd =>
    div_nonneg (abs_nonneg _) (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp hd hp))).le
  have hBad1_le : ∑ d ∈ Bad1, |a d| / phi d ≤ C_tilt * ((val v : ℝ) / D) ^ β := by
    have hstep : ∀ d ∈ Bad1, |a d| / phi d ≤
        ((val v : ℝ) / D) ^ β * (|a d| * ((val d : ℝ) ^ β) / phi d) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hd_pow := (Finset.mem_erase.mp hd.1).2
      have hphi := phi_pos (fun p hp => hP p (Finset.mem_powerset.mp hd_pow hp))
      have hgt1 : 1 ≤ ((val v : ℝ) / D) * (val d : ℝ) := by
        have h1 := (div_lt_iff₀ hv_pos).mp hd.2
        have h2 : D ≤ (val v : ℝ) * (val d : ℝ) := by linarith
        rw [div_mul_eq_mul_div, one_le_div hD_pos]; exact h2
      have hpow1 : 1 ≤ ((val v : ℝ) / D) ^ β * ((val d : ℝ) ^ β) := by
        rw [← Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
        exact Real.one_le_rpow hgt1 hβ.le
      have hmul := mul_le_mul_of_nonneg_left hpow1 (div_nonneg (abs_nonneg (a d)) hphi.le)
      calc |a d| / phi d = |a d| / phi d * 1 := (mul_one _).symm
        _ ≤ |a d| / phi d * (((val v : ℝ) / D) ^ β * ((val d : ℝ) ^ β)) := hmul
        _ = ((val v : ℝ) / D) ^ β * (|a d| * ((val d : ℝ) ^ β) / phi d) := by ring
    calc ∑ d ∈ Bad1, |a d| / phi d
        ≤ ∑ d ∈ Bad1, ((val v : ℝ) / D) ^ β * (|a d| * ((val d : ℝ) ^ β) / phi d) :=
          Finset.sum_le_sum hstep
      _ ≤ ∑ d ∈ Pstar.powerset.erase ∅, ((val v : ℝ) / D) ^ β * (|a d| * ((val d : ℝ) ^ β) / phi d) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d hd _ =>
            mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (div_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp (Finset.mem_erase.mp hd).2 hp))).le)
      _ = ((val v : ℝ) / D) ^ β * ∑ d ∈ Pstar.powerset.erase ∅, |a d| * ((val d : ℝ) ^ β) / phi d := by
          rw [← Finset.mul_sum]
      _ ≤ ((val v : ℝ) / D) ^ β * C_tilt :=
          mul_le_mul_of_nonneg_left htilt (Real.rpow_nonneg (by positivity) _)
      _ = C_tilt * ((val v : ℝ) / D) ^ β := mul_comm _ _
  have hBad2_le : ∑ d ∈ Bad2, |a d| / phi d ≤ C_p * Real.log D / (z : ℝ) := by
    have hz_pos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
    have hlogz_ge1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
      have he3 : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h3z : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      have h := Real.log_le_log (Real.exp_pos 1) (he3.trans h3z)
      rwa [Real.log_exp] at h
    have hv_card : (v.card : ℝ) ≤ Real.log D := by
      have h1 : (v.card : ℝ) * 1 ≤ ∑ p ∈ v, Real.log (p : ℝ) := by
        calc (v.card : ℝ) * 1 = ∑ _p ∈ v, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ v, Real.log (p : ℝ) := Finset.sum_le_sum fun p hp =>
              hlogz_ge1.trans (Real.log_le_log hz_pos (by exact_mod_cast (hgt p (hv_sub hp)).le))
      have h2 : ∑ p ∈ v, Real.log (p : ℝ) = Real.log (val v : ℝ) := by
        unfold val; rw [Nat.cast_prod, Real.log_prod]
        intro p hp; exact_mod_cast (hv_P p hp).ne_zero
      have h3 : Real.log (val v : ℝ) ≤ Real.log D := Real.log_le_log hv_pos hv_le
      linarith
    calc ∑ d ∈ Bad2, |a d| / phi d
        ≤ ∑ p ∈ v, ∑ d ∈ Pstar.powerset.filter (fun d => p ∈ d), |a d| / phi d :=
          sum_biUnion_le v _ _ fun d hd => by
            obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hd
            exact hterm_nn d (Finset.mem_filter.mp h2).1
      _ ≤ ∑ p ∈ v, C_p / (p : ℝ) := Finset.sum_le_sum fun p hp => hprime p (hv_sub hp)
      _ ≤ ∑ _p ∈ v, C_p / (z : ℝ) := Finset.sum_le_sum fun p hp =>
          div_le_div_of_nonneg_left hCp_nn hz_pos (by exact_mod_cast (hgt p (hv_sub hp)).le)
      _ = (v.card : ℝ) * (C_p / (z : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.log D * (C_p / (z : ℝ)) := mul_le_mul_of_nonneg_right hv_card (div_nonneg hCp_nn hz_pos.le)
      _ = C_p * Real.log D / (z : ℝ) := by ring
  have hunion : ∑ d ∈ Bad1 ∪ Bad2, |a d| / phi d ≤
      ∑ d ∈ Bad1, |a d| / phi d + ∑ d ∈ Bad2, |a d| / phi d := by
    have h := Finset.sum_union_inter (s₁ := Bad1) (s₂ := Bad2) (f := fun d => |a d| / phi d)
    have hnn : 0 ≤ ∑ d ∈ Bad1 ∩ Bad2, |a d| / phi d :=
      Finset.sum_nonneg fun d hd => hterm_nn d (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hd).1).1).2
    linarith
  have hsub_le : ∑ d ∈ Bad, |a d| / phi d ≤ ∑ d ∈ Bad1 ∪ Bad2, |a d| / phi d :=
    Finset.sum_le_sum_of_subset_of_nonneg hBad_sub fun d hd _ => by
      rcases Finset.mem_union.mp hd with h1 | h2
      · exact hterm_nn d (Finset.mem_erase.mp (Finset.mem_filter.mp h1).1).2
      · obtain ⟨_, _, h2'⟩ := Finset.mem_biUnion.mp h2
        exact hterm_nn d (Finset.mem_filter.mp h2').1
  linarith

/-- Diagonal mass lower bound (Lemma 3.6 core): `A^k - I_R ≤ A^k * (exp(-u/2) + k^2 * C_p^2 / z)`. -/
lemma I_R_lower_bound {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {z y : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p) (hle_y : ∀ p ∈ Pstar, p ≤ y)
    {D β C_1 C_p : ℝ} (hD1 : 1 ≤ D) (hβ : 0 < β) (hC1 : 0 < C_1) (hCp : 0 ≤ C_p)
    {k : ℕ} (a : Finset ℕ → ℝ) (ha : ∀ t ∈ Pstar.powerset, |a t| ≤ 1)
    (hprime : ∀ p ∈ Pstar, ∑ d ∈ Pstar.powerset.filter (fun d => p ∈ d), |a d| / phi d ≤ C_p / (p : ℝ))
    (hA1 : 1 ≤ ∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t)
    (hAβ : ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ β) / phi t ≤
      (∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t) + C_1 * β)
    (hη : C_1 * (k : ℝ) * β ≤ β * Real.log D / 2) :
    let A := ∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t
    let I_R := ∑ r ∈ Dset Pstar D k, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)
    0 ≤ A ^ k - I_R ∧
    A ^ k - I_R ≤ A ^ k * (Real.exp (-(β * Real.log D) / 2) + (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ)) := by
  classical
  intro A I_R
  set Full := Fintype.piFinset (fun _ : Fin k => Pstar.powerset)
  set DS := Dset Pstar D k
  have hDS_sub : DS ⊆ Full := Finset.filter_subset _ _
  have hD_pos : 0 < D := by linarith
  have hA_pos : 0 < A := by linarith
  have hterm_nn : ∀ r ∈ Full, 0 ≤ ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) := fun r hr =>
    Finset.prod_nonneg fun i _ =>
      div_nonneg (sq_nonneg _)
        (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hr i) hp))).le
  have hfull_eq : ∑ r ∈ Full, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) = A ^ k := by
    rw [sum_piFinset_prod (s := fun _ : Fin k => Pstar.powerset) (f := fun _ t => (a t) ^ 2 / phi t),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdiff_eq : A ^ k - I_R = ∑ r ∈ Full \ DS, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) := by
    rw [← hfull_eq, Finset.sum_sdiff_eq_sub hDS_sub]
  have hdiff_nn : 0 ≤ A ^ k - I_R := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun r hr => hterm_nn r (Finset.mem_sdiff.mp hr).1
  refine ⟨hdiff_nn, ?_⟩
  rw [hdiff_eq]
  set Tail := Full.filter (fun r => D < ((∏ i : Fin k, val (r i) : ℕ) : ℝ))
  set Coll := Full.filter (fun r => ∃ i j : Fin k, i < j ∧ ¬ Disjoint (r i) (r j))
  have hcover : Full \ DS ⊆ Tail ∪ Coll := by
    intro r hr
    rw [Finset.mem_sdiff] at hr
    by_cases hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (r i) (r j)
    · have hgtD : D < ((∏ i : Fin k, val (r i) : ℕ) : ℝ) := by
        by_contra! hle
        apply hr.2
        rw [mem_Dset_iff]
        exact ⟨fun i => Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hr.1 i), hdisj, hle⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr.1, hgtD⟩)
    · push Not at hdisj
      obtain ⟨i, j, hij, hnd⟩ := hdisj
      rcases lt_or_gt_of_ne hij with hlt | hgt'
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr.1, i, j, hlt, hnd⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr.1, j, i, hgt', fun h => hnd h.symm⟩)
  -- Bound 1: Tail ≤ A^k * exp(-u/2)
  have hTail_le : ∑ r ∈ Tail, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) ≤
      A ^ k * Real.exp (-(β * Real.log D) / 2) := by
    set Aβ := ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ β) / phi t
    have hstep : ∀ r ∈ Tail, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) ≤
        D ^ (-β) * ∏ i : Fin k, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ β) / phi (r i) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      have hprod_pos : 0 < ((∏ i : Fin k, val (r i) : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun i _ =>
          val_pos (fun p hp => hP p (Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hr.1 i) hp))
      have hgt1 : 1 ≤ ((∏ i : Fin k, val (r i) : ℕ) : ℝ) / D := (one_le_div hD_pos).mpr hr.2.le
      have hpow1 : 1 ≤ D ^ (-β) * (((∏ i : Fin k, val (r i) : ℕ) : ℝ) ^ β) := by
        rw [Real.rpow_neg hD_pos.le, inv_mul_eq_div, ← Real.div_rpow hprod_pos.le hD_pos.le]
        exact Real.one_le_rpow hgt1 hβ.le
      have hrpow_prod : (((∏ i : Fin k, val (r i) : ℕ) : ℝ) ^ β) =
          ∏ i : Fin k, ((val (r i) : ℝ) ^ β) := by
        rw [Nat.cast_prod, Real.finsetProd_rpow Finset.univ (fun i => (val (r i) : ℝ))
          (fun i _ => Nat.cast_nonneg _)]
      have hmul := mul_le_mul_of_nonneg_left hpow1 (hterm_nn r hr.1)
      have heq : (∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)) *
          (D ^ (-β) * (((∏ i : Fin k, val (r i) : ℕ) : ℝ) ^ β)) =
          D ^ (-β) * ∏ i : Fin k, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ β) / phi (r i) := by
        rw [hrpow_prod, mul_left_comm, ← Finset.prod_mul_distrib]
        congr 1; apply Finset.prod_congr rfl; intro i _; ring
      linarith
    have hAβ_pow : D ^ (-β) * Aβ ^ k ≤ A ^ k * Real.exp (-(β * Real.log D) / 2) := by
      have h1 : Aβ ≤ A * Real.exp (C_1 * β) := by
        have hlin : Aβ ≤ A * (1 + C_1 * β / A) := by
          have : A * (1 + C_1 * β / A) = A + C_1 * β := by field_simp [hA_pos.ne']
          linarith [hAβ]
        have hexp : 1 + C_1 * β / A ≤ Real.exp (C_1 * β) := by
          have hdiv : C_1 * β / A ≤ C_1 * β := div_le_self (mul_nonneg hC1.le hβ.le) hA1
          linarith [Real.add_one_le_exp (C_1 * β)]
        exact hlin.trans (mul_le_mul_of_nonneg_left hexp hA_pos.le)
      have hAβ_nn : 0 ≤ Aβ := Finset.sum_nonneg fun t ht =>
        div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp ht hp))).le
      have hpow : Aβ ^ k ≤ A ^ k * Real.exp (C_1 * (k : ℝ) * β) := by
        calc Aβ ^ k ≤ (A * Real.exp (C_1 * β)) ^ k := pow_le_pow_left₀ hAβ_nn h1 k
          _ = A ^ k * (Real.exp (C_1 * β)) ^ k := mul_pow _ _ _
          _ = A ^ k * Real.exp (C_1 * (k : ℝ) * β) := by
              rw [← Real.exp_nat_mul]; congr 2; ring
      have hDneg : D ^ (-β) = Real.exp (-(β * Real.log D)) := by
        rw [Real.rpow_def_of_pos hD_pos]; congr 1; ring
      calc D ^ (-β) * Aβ ^ k
          ≤ Real.exp (-(β * Real.log D)) * (A ^ k * Real.exp (C_1 * (k : ℝ) * β)) := by
            rw [← hDneg]; exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hD_pos.le _)
        _ = A ^ k * Real.exp (-(β * Real.log D) + C_1 * (k : ℝ) * β) := by
            rw [Real.exp_add]; ring
        _ ≤ A ^ k * Real.exp (-(β * Real.log D) / 2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg hA_pos.le k)
    calc ∑ r ∈ Tail, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)
        ≤ ∑ r ∈ Tail, D ^ (-β) * ∏ i : Fin k, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ β) / phi (r i) :=
          Finset.sum_le_sum hstep
      _ ≤ ∑ r ∈ Full, D ^ (-β) * ∏ i : Fin k, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ β) / phi (r i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun r hr _ =>
            mul_nonneg (Real.rpow_nonneg hD_pos.le _) (Finset.prod_nonneg fun i _ =>
              div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hr i) hp))).le)
      _ = D ^ (-β) * Aβ ^ k := by
          rw [← Finset.mul_sum,
            sum_piFinset_prod (s := fun _ : Fin k => Pstar.powerset)
              (f := fun _ t => (a t) ^ 2 * ((val t : ℝ) ^ β) / phi t),
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ A ^ k * Real.exp (-(β * Real.log D) / 2) := hAβ_pow
  -- Bound 2: Coll ≤ A^k * (k^2 * C_p^2 / z)
  have hColl_le : ∑ r ∈ Coll, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) ≤
      A ^ k * ((k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ)) := by
    set pairs := Finset.univ.filter (fun ij : Fin k × Fin k => ij.1 < ij.2)
    have hColl_sub : Coll ⊆ pairs.biUnion (fun ij => Pstar.biUnion (fun p =>
        Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2))) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨i, j, hij, hnd⟩ := hr.2
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨p, hpi, hpj⟩ := hnd
      have hpP : p ∈ Pstar := Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hr.1 i) hpi
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_filter.mpr ⟨hr.1, hpi, hpj⟩⟩⟩
    have hpair_p : ∀ ij ∈ pairs, ∀ p ∈ Pstar,
        ∑ r ∈ Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2),
          ∏ l : Fin k, (a (r l)) ^ 2 / phi (r l) ≤ (C_p / (p : ℝ)) ^ 2 * A ^ k := by
      intro ij hij p hp
      have hne : ij.1 ≠ ij.2 := ne_of_lt (Finset.mem_filter.mp hij).2
      have hfilt : Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2) =
          Fintype.piFinset (fun l : Fin k =>
            if l = ij.1 ∨ l = ij.2 then Pstar.powerset.filter (fun t => p ∈ t) else Pstar.powerset) := by
        ext r
        simp only [Full, Finset.mem_filter, Fintype.mem_piFinset]
        constructor
        · rintro ⟨hall, h1, h2⟩ l
          split_ifs with hl
          · rcases hl with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hall _, h1⟩
            · exact Finset.mem_filter.mpr ⟨hall _, h2⟩
          · exact hall l
        · intro hall
          refine ⟨fun l => ?_, ?_, ?_⟩
          · have hl := hall l
            split_ifs at hl
            · exact (Finset.mem_filter.mp hl).1
            · exact hl
          · have h1 := hall ij.1; simp only [true_or, ↓reduceIte, Finset.mem_filter] at h1; exact h1.2
          · have h2 := hall ij.2; simp only [or_true, ↓reduceIte, Finset.mem_filter] at h2; exact h2.2
      rw [hfilt, sum_piFinset_prod
        (s := fun l : Fin k => if l = ij.1 ∨ l = ij.2 then Pstar.powerset.filter (fun t => p ∈ t) else Pstar.powerset)
        (f := fun _ t => (a t) ^ 2 / phi t)]
      let Bp := ∑ t ∈ Pstar.powerset.filter (fun t => p ∈ t), (a t) ^ 2 / phi t
      have hBp_le : Bp ≤ C_p / (p : ℝ) := by
        have h1 : Bp ≤ ∑ t ∈ Pstar.powerset.filter (fun t => p ∈ t), |a t| / phi t := by
          apply Finset.sum_le_sum; intro t ht
          have hpow := (Finset.mem_filter.mp ht).1
          have hphi := phi_pos (fun q hq => hP q (Finset.mem_powerset.mp hpow hq))
          apply div_le_div_of_nonneg_right _ hphi.le
          have ha1 := ha t hpow
          calc (a t) ^ 2 = |a t| * |a t| := by rw [← sq_abs, sq]
            _ ≤ |a t| * 1 := mul_le_mul_of_nonneg_left ha1 (abs_nonneg _)
            _ = |a t| := mul_one _
        exact h1.trans (hprime p hp)
      have hBp_nn : 0 ≤ Bp := Finset.sum_nonneg fun t ht =>
        div_nonneg (sq_nonneg _)
          (phi_pos (fun q hq => hP q (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hq))).le
      have hi1 : ij.1 ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
      have hi2 : ij.2 ∈ (Finset.univ : Finset (Fin k)).erase ij.1 :=
        Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase Finset.univ _ hi1, ← Finset.mul_prod_erase _ _ hi2]
      have hrest : ∏ l ∈ (Finset.univ.erase ij.1).erase ij.2,
          (∑ t ∈ (if l = ij.1 ∨ l = ij.2 then Pstar.powerset.filter (fun t => p ∈ t) else Pstar.powerset),
            (a t) ^ 2 / phi t) = A ^ (k - 2) := by
        have hcongr : ∀ l ∈ (Finset.univ.erase ij.1).erase ij.2,
            (∑ t ∈ (if l = ij.1 ∨ l = ij.2 then Pstar.powerset.filter (fun t => p ∈ t) else Pstar.powerset),
              (a t) ^ 2 / phi t) = A := by
          intro l hl
          have hne2 : l ≠ ij.2 := (Finset.mem_erase.mp hl).1
          have hne1 : l ≠ ij.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
          simp [hne1, hne2, A]
        rw [Finset.prod_congr rfl hcongr, Finset.prod_const,
          Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem hi1, Finset.card_univ, Fintype.card_fin]
        rfl
      rw [hrest]
      simp only [true_or, or_true, ↓reduceIte]
      have hAk : A ^ (k - 2) ≤ A ^ k := pow_le_pow_right₀ hA1 (Nat.sub_le k 2)
      have hBp2 : Bp * Bp ≤ (C_p / (p : ℝ)) ^ 2 := by
        rw [sq]; exact mul_le_mul hBp_le hBp_le hBp_nn (div_nonneg hCp (Nat.cast_nonneg p))
      calc Bp * (Bp * A ^ (k - 2)) = (Bp * Bp) * A ^ (k - 2) := by ring
        _ ≤ (C_p / (p : ℝ)) ^ 2 * A ^ k :=
            mul_le_mul hBp2 hAk (pow_nonneg hA_pos.le _) (sq_nonneg _)
    have hsum_p : ∑ p ∈ Pstar, (C_p / (p : ℝ)) ^ 2 ≤ C_p ^ 2 / (z : ℝ) := by
      have hpull : ∑ p ∈ Pstar, (C_p / (p : ℝ)) ^ 2 = C_p ^ 2 * ∑ p ∈ Pstar, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      rw [hpull]
      have hsub : Pstar ⊆ Finset.Ioc z y := fun p hp =>
        Finset.mem_Ioc.mpr ⟨hgt p hp, hle_y p hp⟩
      have hle1 : ∑ p ∈ Pstar, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ ∑ n ∈ Finset.Ioc z y, (1 : ℝ) / ((n : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have hle2 := hle1.trans (sum_inv_sq_Ioc_le (by omega : 1 ≤ z))
      calc C_p ^ 2 * ∑ p ∈ Pstar, (1 : ℝ) / ((p : ℝ) ^ 2)
          ≤ C_p ^ 2 * (1 / (z : ℝ)) := mul_le_mul_of_nonneg_left hle2 (sq_nonneg C_p)
        _ = C_p ^ 2 / (z : ℝ) := by ring
    have hpairs_card : (pairs.card : ℝ) ≤ (k : ℝ) ^ 2 := by
      have h1 : pairs.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
      have h2 : (pairs.card : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2; nlinarith
    calc ∑ r ∈ Coll, ∏ l : Fin k, (a (r l)) ^ 2 / phi (r l)
        ≤ ∑ r ∈ pairs.biUnion (fun ij => Pstar.biUnion (fun p =>
            Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2))),
            ∏ l : Fin k, (a (r l)) ^ 2 / phi (r l) :=
          Finset.sum_le_sum_of_subset_of_nonneg hColl_sub fun r hr _ => by
            obtain ⟨_, _, hr1⟩ := Finset.mem_biUnion.mp hr
            obtain ⟨_, _, hr2⟩ := Finset.mem_biUnion.mp hr1
            exact hterm_nn r (Finset.mem_filter.mp hr2).1
      _ ≤ ∑ ij ∈ pairs, ∑ r ∈ Pstar.biUnion (fun p =>
            Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2)),
            ∏ l : Fin k, (a (r l)) ^ 2 / phi (r l) :=
          sum_biUnion_le pairs _ _ fun r hr => by
            obtain ⟨_, _, hr1⟩ := Finset.mem_biUnion.mp hr
            obtain ⟨_, _, hr2⟩ := Finset.mem_biUnion.mp hr1
            exact hterm_nn r (Finset.mem_filter.mp hr2).1
      _ ≤ ∑ ij ∈ pairs, ∑ p ∈ Pstar, ∑ r ∈ Full.filter (fun r => p ∈ r ij.1 ∧ p ∈ r ij.2),
            ∏ l : Fin k, (a (r l)) ^ 2 / phi (r l) :=
          Finset.sum_le_sum fun ij _ => sum_biUnion_le Pstar _ _ fun r hr => by
            obtain ⟨_, _, hr2⟩ := Finset.mem_biUnion.mp hr
            exact hterm_nn r (Finset.mem_filter.mp hr2).1
      _ ≤ ∑ _ij ∈ pairs, ∑ p ∈ Pstar, (C_p / (p : ℝ)) ^ 2 * A ^ k :=
          Finset.sum_le_sum fun ij hij => Finset.sum_le_sum fun p hp => hpair_p ij hij p hp
      _ = (pairs.card : ℝ) * ((∑ p ∈ Pstar, (C_p / (p : ℝ)) ^ 2) * A ^ k) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
      _ ≤ (k : ℝ) ^ 2 * ((C_p ^ 2 / (z : ℝ)) * A ^ k) :=
          mul_le_mul hpairs_card (mul_le_mul_of_nonneg_right hsum_p (pow_nonneg hA_pos.le k))
            (mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_nonneg hA_pos.le k))
            (sq_nonneg _)
      _ = A ^ k * ((k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ)) := by ring
  -- Combine Tail and Coll
  have hsub_le : ∑ r ∈ Full \ DS, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) ≤
      ∑ r ∈ Tail ∪ Coll, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover fun r hr _ => by
      rcases Finset.mem_union.mp hr with h1 | h2
      · exact hterm_nn r (Finset.mem_filter.mp h1).1
      · exact hterm_nn r (Finset.mem_filter.mp h2).1
  have hunion : ∑ r ∈ Tail ∪ Coll, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) ≤
      (∑ r ∈ Tail, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)) +
      (∑ r ∈ Coll, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)) := by
    have h := Finset.sum_union_inter (s₁ := Tail) (s₂ := Coll)
      (f := fun r => ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i))
    have hnn : 0 ≤ ∑ r ∈ Tail ∩ Coll, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) :=
      Finset.sum_nonneg fun r hr => hterm_nn r (Finset.mem_filter.mp (Finset.mem_inter.mp hr).1).1
    linarith
  linarith

/-- Diagonal mass upper bound for uncovered form `i₀` (Lemma 3.7 core). -/
lemma I_uncov_upper_bound {Pstar : Finset ℕ} (hP : ∀ p ∈ Pstar, p.Prime)
    {z : ℕ} (hz : 3 ≤ z) (hgt : ∀ p ∈ Pstar, z < p)
    {D β C_tilt C_1 C_p : ℝ} (hD1 : 1 ≤ D) (hβ : 0 < β) (hC1 : 0 < C_1) (hCp : 0 ≤ C_p)
    {k : ℕ} (a : Finset ℕ → ℝ)
    (hcancel : ∑ d ∈ Pstar.powerset, a d / phi d = 0)
    (haneg : ∀ d ∈ Pstar.powerset.erase ∅, a d ≤ 0)
    (htilt : ∑ d ∈ Pstar.powerset.erase ∅, |a d| * ((val d : ℝ) ^ β) / phi d ≤ C_tilt)
    (hprime : ∀ p ∈ Pstar, ∑ d ∈ Pstar.powerset.filter (fun d => p ∈ d), |a d| / phi d ≤ C_p / (p : ℝ))
    (hA1 : 1 ≤ ∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t)
    (hA2β : ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ (2 * β)) / phi t ≤
      (∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t) + C_1 * (2 * β))
    (hη : 2 * C_1 * (k : ℝ) * β ≤ β * Real.log D) (i₀ : Fin k) :
    let A := ∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t
    ∑ r ∈ Dset Pstar D k, (cUncov Pstar D a i₀ r) ^ 2 / ∏ i : Fin k, phi (r i) ≤
      (2 * C_tilt ^ 2 * Real.exp (-(β * Real.log D)) +
       2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) * A ^ k := by
  classical
  intro A
  set DS := Dset Pstar D k
  set J := DS.filter (fun r => r i₀ = ∅)
  set A2β := ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ (2 * β)) / phi t
  have hD_pos : 0 < D := by linarith
  have hA_pos : 0 < A := by linarith
  have hsub : ∑ r ∈ DS, (cUncov Pstar D a i₀ r) ^ 2 / ∏ i : Fin k, phi (r i) =
      ∑ r ∈ J, (eps Pstar D a (unionOf r)) ^ 2 *
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) := by
    have h1 : ∑ r ∈ DS, (cUncov Pstar D a i₀ r) ^ 2 / ∏ i : Fin k, phi (r i) =
        ∑ r ∈ J, (cUncov Pstar D a i₀ r) ^ 2 / ∏ i : Fin k, phi (r i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hr hnot
      have hne : r i₀ ≠ ∅ := fun h0 => hnot (Finset.mem_filter.mpr ⟨hr, h0⟩)
      simp [cUncov, hne]
    rw [h1]
    apply Finset.sum_congr rfl
    intro r hr
    have h0 : r i₀ = ∅ := (Finset.mem_filter.mp hr).2
    simp only [cUncov, h0, ↓reduceIte]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => phi (r i)) (Finset.mem_univ i₀),
      h0, phi_empty, one_mul, mul_pow, mul_div_assoc, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  rw [hsub]
  -- Bound each term using eps_bound and (u + v)^2 ≤ 2 u^2 + 2 v^2
  have hterm : ∀ r ∈ J,
      (eps Pstar D a (unionOf r)) ^ 2 * ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) ≤
      (2 * C_tilt ^ 2 * D ^ (-(2 * β))) *
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i) +
      (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) *
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) := by
    intro r hr
    have hrDS : r ∈ DS := (Finset.mem_filter.mp hr).1
    have h0 : r i₀ = ∅ := (Finset.mem_filter.mp hr).2
    have hdisj := (mem_Dset_iff.mp hrDS).2.1
    have hv_le : (val (unionOf r) : ℝ) ≤ D := by
      rw [val_unionOf hdisj]; exact (mem_Dset_iff.mp hrDS).2.2
    obtain ⟨heps_nn, heps_le⟩ := eps_bound hP hz hgt hD1 hβ hCp a hcancel haneg htilt hprime
      (unionOf_subset hrDS) hv_le
    have heps_sq : (eps Pstar D a (unionOf r)) ^ 2 ≤
        2 * C_tilt ^ 2 * D ^ (-(2 * β)) * ((val (unionOf r) : ℝ) ^ (2 * β)) +
        2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2 := by
      have hv_pos : (0 : ℝ) < val (unionOf r) := by
        exact_mod_cast val_pos (fun p hp => hP p (unionOf_subset hrDS hp))
      have hsq1 : (eps Pstar D a (unionOf r)) ^ 2 ≤
          (C_tilt * ((val (unionOf r) : ℝ) / D) ^ β + C_p * Real.log D / (z : ℝ)) ^ 2 :=
        pow_le_pow_left₀ heps_nn heps_le 2
      have hsq2 : (C_tilt * ((val (unionOf r) : ℝ) / D) ^ β + C_p * Real.log D / (z : ℝ)) ^ 2 ≤
          2 * (C_tilt * ((val (unionOf r) : ℝ) / D) ^ β) ^ 2 +
          2 * (C_p * Real.log D / (z : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (C_tilt * ((val (unionOf r) : ℝ) / D) ^ β - C_p * Real.log D / (z : ℝ))]
      have hpow_eq : (((val (unionOf r) : ℝ) / D) ^ β) ^ 2 =
          D ^ (-(2 * β)) * ((val (unionOf r) : ℝ) ^ (2 * β)) := by
        rw [Real.div_rpow hv_pos.le hD_pos.le, div_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul hv_pos.le, ← Real.rpow_mul hD_pos.le, Real.rpow_neg hD_pos.le]
        have e : β * (2 : ℕ) = 2 * β := by push_cast; ring
        rw [e]; ring
      have hterm1 : 2 * (C_tilt * ((val (unionOf r) : ℝ) / D) ^ β) ^ 2 =
          2 * C_tilt ^ 2 * D ^ (-(2 * β)) * ((val (unionOf r) : ℝ) ^ (2 * β)) := by
        rw [mul_pow, hpow_eq]; ring
      have hterm2 : 2 * (C_p * Real.log D / (z : ℝ)) ^ 2 =
          2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2 := by ring
      linarith
    have hw_nn : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) :=
      Finset.prod_nonneg fun i _ => div_nonneg (sq_nonneg _)
        (phi_pos (fun p hp => hP p ((mem_Dset_iff.mp hrDS).1 i hp))).le
    have hmul := mul_le_mul_of_nonneg_right heps_sq hw_nn
    have hval_prod : ((val (unionOf r) : ℝ) ^ (2 * β)) *
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) =
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i) := by
      rw [val_unionOf hdisj,
        ← Finset.mul_prod_erase Finset.univ (fun i => val (r i)) (Finset.mem_univ i₀),
        h0, val_empty, one_mul, Nat.cast_prod,
        ← Real.finsetProd_rpow (Finset.univ.erase i₀) (fun i => (val (r i) : ℝ))
          (fun i _ => Nat.cast_nonneg _),
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _; ring
    calc (eps Pstar D a (unionOf r)) ^ 2 * ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i)
        ≤ (2 * C_tilt ^ 2 * D ^ (-(2 * β)) * ((val (unionOf r) : ℝ) ^ (2 * β)) +
           2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) *
          ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) := hmul
      _ = (2 * C_tilt ^ 2 * D ^ (-(2 * β))) *
            (((val (unionOf r) : ℝ) ^ (2 * β)) *
              ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i)) +
          (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) *
            ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) := by ring
      _ = _ := by rw [hval_prod]
  -- Enlarge J to Full0 = {r : Fin k → Pstar.powerset | r i₀ = ∅}
  set Full0 := Fintype.piFinset (fun i : Fin k => if i = i₀ then {∅} else Pstar.powerset)
  have hJ_sub : J ⊆ Full0 := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · subst hi; simp [hr.2]
    · exact Finset.mem_powerset.mpr ((mem_Dset_iff.mp hr.1).1 i)
  have hsum_Full0 : ∀ γ : ℝ,
      ∑ r ∈ Full0, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ γ) / phi (r i) =
      (∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ γ) / phi t) ^ (k - 1) := by
    intro γ
    have hcongr : ∀ r ∈ Full0,
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ γ) / phi (r i) =
        ∏ i : Fin k, if i = i₀ then (1 : ℝ) else (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ γ) / phi (r i) := by
      intro r _
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), if_pos rfl, one_mul]
      apply Finset.prod_congr rfl; intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [Finset.sum_congr rfl hcongr,
      sum_piFinset_prod (s := fun i : Fin k => if i = i₀ then {∅} else Pstar.powerset)
        (f := fun i t => if i = i₀ then (1 : ℝ) else (a t) ^ 2 * ((val t : ℝ) ^ γ) / phi t),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    simp only [↓reduceIte, Finset.sum_singleton, one_mul]
    have hrest : ∀ i ∈ Finset.univ.erase i₀,
        ∑ t ∈ (if i = i₀ then {∅} else Pstar.powerset),
          (if i = i₀ then (1 : ℝ) else (a t) ^ 2 * ((val t : ℝ) ^ γ) / phi t) =
        ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ γ) / phi t := by
      intro i hi
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      simp [hne]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
  have hsum1 : ∑ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i) ≤
      A2β ^ (k - 1) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hJ_sub fun r hr _ =>
      Finset.prod_nonneg fun i hi => ?_).trans_eq (hsum_Full0 (2 * β))
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have hri := Fintype.mem_piFinset.mp hr i
    rw [if_neg hne] at hri
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp hri hp))).le
  have hsum2 : ∑ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) ≤ A ^ (k - 1) := by
    have hrew : ∀ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i) =
        ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (0 : ℝ)) / phi (r i) := by
      intro r _; apply Finset.prod_congr rfl; intro i _; simp
    rw [Finset.sum_congr rfl hrew]
    have h0 := hsum_Full0 0
    have hA0_eq : (∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ (0 : ℝ)) / phi t) = A := by
      apply Finset.sum_congr rfl; intro t _; simp
    rw [hA0_eq] at h0
    refine (Finset.sum_le_sum_of_subset_of_nonneg hJ_sub fun r hr _ =>
      Finset.prod_nonneg fun i hi => ?_).trans_eq h0
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have hri := Fintype.mem_piFinset.mp hr i
    rw [if_neg hne] at hri
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp hri hp))).le
  have hD2β_A : D ^ (-(2 * β)) * A2β ^ (k - 1) ≤ A ^ k * Real.exp (-(β * Real.log D)) := by
    have h1 : A2β ≤ A * Real.exp (2 * C_1 * β) := by
      have hlin : A2β ≤ A * (1 + 2 * C_1 * β / A) := by
        have : A * (1 + 2 * C_1 * β / A) = A + C_1 * (2 * β) := by field_simp [hA_pos.ne']
        linarith [hA2β]
      have hexp : 1 + 2 * C_1 * β / A ≤ Real.exp (2 * C_1 * β) := by
        have hdiv : 2 * C_1 * β / A ≤ 2 * C_1 * β := div_le_self (by positivity) hA1
        linarith [Real.add_one_le_exp (2 * C_1 * β)]
      exact hlin.trans (mul_le_mul_of_nonneg_left hexp hA_pos.le)
    have hA2β_nn : 0 ≤ A2β := Finset.sum_nonneg fun t ht =>
      div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (phi_pos (fun p hp => hP p (Finset.mem_powerset.mp ht hp))).le
    have hpow : A2β ^ (k - 1) ≤ A ^ k * Real.exp (2 * C_1 * (k : ℝ) * β) := by
      have hk_sub : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
      calc A2β ^ (k - 1) ≤ (A * Real.exp (2 * C_1 * β)) ^ (k - 1) := pow_le_pow_left₀ hA2β_nn h1 _
        _ = A ^ (k - 1) * Real.exp (((k - 1 : ℕ) : ℝ) * (2 * C_1 * β)) := by
            rw [mul_pow, ← Real.exp_nat_mul]
        _ ≤ A ^ k * Real.exp (2 * C_1 * (k : ℝ) * β) :=
            mul_le_mul (pow_le_pow_right₀ hA1 (Nat.sub_le k 1))
              (Real.exp_le_exp.mpr (by nlinarith [mul_pos hC1 hβ]))
              (Real.exp_pos _).le (pow_nonneg hA_pos.le k)
    have hDneg : D ^ (-(2 * β)) = Real.exp (-(2 * (β * Real.log D))) := by
      rw [Real.rpow_def_of_pos hD_pos]; congr 1; ring
    calc D ^ (-(2 * β)) * A2β ^ (k - 1)
        ≤ Real.exp (-(2 * (β * Real.log D))) * (A ^ k * Real.exp (2 * C_1 * (k : ℝ) * β)) := by
          rw [← hDneg]; exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hD_pos.le _)
      _ = A ^ k * Real.exp (-(2 * (β * Real.log D)) + 2 * C_1 * (k : ℝ) * β) := by
          rw [Real.exp_add]; ring
      _ ≤ A ^ k * Real.exp (-(β * Real.log D)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg hA_pos.le k)
  have hAk_sub : A ^ (k - 1) ≤ A ^ k := pow_le_pow_right₀ hA1 (Nat.sub_le k 1)
  calc ∑ r ∈ J, (eps Pstar D a (unionOf r)) ^ 2 * ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i)
      ≤ ∑ r ∈ J, ((2 * C_tilt ^ 2 * D ^ (-(2 * β))) *
            ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i) +
          (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) *
            ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i)) := Finset.sum_le_sum hterm
    _ = (2 * C_tilt ^ 2 * D ^ (-(2 * β))) *
          (∑ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i)) +
        (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) *
          (∑ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 / phi (r i)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 * C_tilt ^ 2) * (D ^ (-(2 * β)) * A2β ^ (k - 1)) +
        (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) * A ^ (k - 1) := by
        have h1 : (2 * C_tilt ^ 2 * D ^ (-(2 * β))) *
            (∑ r ∈ J, ∏ i ∈ Finset.univ.erase i₀, (a (r i)) ^ 2 * ((val (r i) : ℝ) ^ (2 * β)) / phi (r i)) ≤
            (2 * C_tilt ^ 2) * (D ^ (-(2 * β)) * A2β ^ (k - 1)) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hsum1
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_tilt))
              (Real.rpow_nonneg hD_pos.le _))
        have h2 := mul_le_mul_of_nonneg_left hsum2
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_p))
            (sq_nonneg (Real.log D / (z : ℝ))))
        linarith
    _ ≤ (2 * C_tilt ^ 2) * (A ^ k * Real.exp (-(β * Real.log D))) +
        (2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) * A ^ k := by
        have h1 := mul_le_mul_of_nonneg_left hD2β_A
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_tilt))
        have h2 := mul_le_mul_of_nonneg_left hAk_sub
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_p))
            (sq_nonneg (Real.log D / (z : ℝ))))
        linarith
    _ = (2 * C_tilt ^ 2 * Real.exp (-(β * Real.log D)) +
         2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) * A ^ k := by ring

set_option maxHeartbeats 800000 in
/-- Core translation step with opaque `Δ` (avoids unfolding the pair product). -/
private lemma lem_translate_core {x k Δ : ℕ} {b_lo C_tilt C_1 C_p : ℝ}
    (hb_lo : 0 < b_lo) (hCtilt : 0 < C_tilt) (hC1 : 1 ≤ C_1) (hCp : 0 < C_p)
    (hx16 : 16 ≤ x) (hz16 : 16 ≤ zParam x) (hlog2 : 2 ≤ Real.log (x : ℝ))
    (hT_ge : Real.exp (x : ℝ) / 2 ≤ (TParam x : ℝ))
    (hy_le_expx : (yParam x : ℝ) ≤ Real.exp (x : ℝ))
    (hexp_x2 : (x : ℝ) ^ 2 ≤ Real.exp ((x : ℝ) / 4))
    (hx_Merr : max (16 * (C_p ^ 2 + 4)) (16 * (4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2)) < (x : ℝ))
    (hk_pos : 0 < k) (hk_le_x : k ≤ x)
    (hC1k_le : C_1 * (k : ℝ) ≤ (x : ℝ) / 8)
    (b : ℤ) (s : Fin k → ℤ)
    (hB_lo : b_lo ≤ Bstar x Δ)
    (hcancel : ∑ t ∈ (primesStar x Δ).powerset, aCoeff x Δ t / phi t = 0)
    (habs_le : ∀ t ∈ (primesStar x Δ).powerset, |aCoeff x Δ t| ≤ 1)
    (hA1 : 1 ≤ A0 x Δ)
    (htilt_fn : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * betaParam x →
      ∑ t ∈ (primesStar x Δ).powerset.erase ∅,
        |aCoeff x Δ t| * ((val t : ℝ) ^ γ) / phi t ≤ C_tilt ∧
      Aγ x Δ γ ≤ A0 x Δ + C_1 * γ)
    (hprime_fn : ∀ p ∈ primesStar x Δ,
      ∑ t ∈ (primesStar x Δ).powerset.filter (fun t => p ∈ t),
        |aCoeff x Δ t| / phi t ≤ C_p / (p : ℝ))
    (hdiff : ∀ p ∈ primesStar x Δ, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j)) :
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp (x : ℝ) ∧
      ∀ i : Fin k, ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ Real.exp (x : ℝ) ∧
        (p : ℤ) ∣ b + (primorial x : ℤ) * (t : ℤ) + s i := by
  classical
  let M_err : ℝ := max (16 * (C_p ^ 2 + 4)) (16 * (4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2))
  set Pstar := primesStar x Δ
  set D := DParam x
  set β := betaParam x
  set z := zParam x
  set y := yParam x
  set T := TParam x
  set Q := primorial x
  set a := aCoeff x Δ
  have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hx16R : (16 : ℝ) ≤ x := by exact_mod_cast hx16
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hP : ∀ p ∈ Pstar, p.Prime := fun p hp => prime_of_mem_primesStar hp
  have hgt : ∀ p ∈ Pstar, z < p := fun p hp => gt_z_of_mem_primesStar hp
  have hle_y : ∀ p ∈ Pstar, p ≤ y := fun p hp => le_y_of_mem_primesStar hp
  have hcop : ∀ p ∈ Pstar, Nat.Coprime p Q := by
    intro p hp
    have hpP := hP p hp
    refine hpP.coprime_iff_not_dvd.mpr ?_
    intro hdvd
    change p ∣ primorial x at hdvd
    rw [primorial_eq_prod_primesLE] at hdvd
    obtain ⟨q, hq, hpq⟩ := hpP.prime.dvd_finsetProd_iff id |>.mp hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq hpP (Nat.prime_of_mem_primesLE hq)).mp hpq
    have hle_x : p ≤ x := heq ▸ (Nat.mem_primesLE.mp hq).1
    have hgt_z : x ^ 6 < p := hgt p hp
    have : x ≤ x ^ 6 := Nat.le_self_pow (by norm_num) x
    omega
  have hD_log : Real.log D = (x : ℝ) / 4 := Real.log_exp _
  have hD8 : 8 ≤ D := by
    dsimp [D, DParam]
    have : (16 : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 := by nlinarith
    linarith [hexp_x2]
  have hD1 : 1 ≤ D := by linarith
  have hβ_pos : 0 < β := by dsimp [β, betaParam]; positivity
  have hu_eq : β * Real.log D = uParam x := by
    rw [hD_log]; dsimp [β, betaParam, uParam]; field_simp [hx_pos.ne']
  have hT_pos : 0 < T := by
    have : (0 : ℝ) < (T : ℝ) := lt_of_lt_of_le (by positivity) hT_ge
    exact_mod_cast this
  have hkz : (k : ℝ) ^ 6 ≤ (z : ℝ) := by
    have : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
    have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
    rw [hz_eq]; exact pow_le_pow_left₀ (Nat.cast_nonneg k) this 6
  have hz_pos : (0 : ℝ) < z := by dsimp [z, zParam]; positivity
  have hlogz_eq : Real.log (z : ℝ) = 6 * Real.log (x : ℝ) := by simp [z, zParam, Real.log_pow]
  have hlogz_ge1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by rw [hlogz_eq]; linarith
  have hx2_le_x6 : (x : ℝ) ^ 2 ≤ (x : ℝ) ^ 6 := pow_le_pow_right₀ hx1 (by norm_num : 2 ≤ 6)
  have hx3_le_x6 : (x : ℝ) ^ 3 ≤ (x : ℝ) ^ 6 := pow_le_pow_right₀ hx1 (by norm_num : 3 ≤ 6)
  have hsmall_gram : 2 * (k : ℝ) * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) ≤ 1 := by
    rw [hD_log, div_le_one (mul_pos hz_pos (by linarith))]
    have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
    have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
    calc 2 * (k : ℝ) * ((x : ℝ) / 4)
        ≤ 2 * (x : ℝ) * ((x : ℝ) / 4) := by nlinarith
      _ ≤ (x : ℝ) ^ 2 := by nlinarith
      _ ≤ (x : ℝ) ^ 6 := hx2_le_x6
      _ = (z : ℝ) := hz_eq.symm
      _ ≤ (z : ℝ) * Real.log (z : ℝ) := le_mul_of_one_le_right hz_pos.le hlogz_ge1
  have hsmall_lam : 3 * Real.log D / ((z : ℝ) * Real.log (z : ℝ)) ≤ Real.log 2 := by
    rw [hD_log, div_le_iff₀ (mul_pos hz_pos (by linarith))]
    have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
    have hlog2_gt : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    calc 3 * ((x : ℝ) / 4)
        ≤ (1 / 2 : ℝ) * (x : ℝ) ^ 2 := by nlinarith
      _ ≤ Real.log 2 * (x : ℝ) ^ 6 :=
          mul_le_mul hlog2_gt hx2_le_x6 (sq_nonneg (x : ℝ)) (by linarith)
      _ = Real.log 2 * (z : ℝ) := by rw [hz_eq]
      _ ≤ Real.log 2 * ((z : ℝ) * Real.log (z : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hz_pos.le hlogz_ge1) (by linarith)
  have hC1kβ : C_1 * (k : ℝ) * β ≤ β * Real.log D / 2 := by
    rw [hD_log]; nlinarith
  have hD3T : D ^ 3 / (T : ℝ) ≤ 2 / (x : ℝ) ^ 2 := by
    have hD3 : D ^ 3 = Real.exp (3 * (x : ℝ) / 4) := by
      dsimp [D, DParam]; rw [← Real.exp_nat_mul]; congr 1; ring
    have h1 : D ^ 3 / (T : ℝ) ≤ Real.exp (3 * (x : ℝ) / 4) / (Real.exp (x : ℝ) / 2) := by
      rw [hD3]; exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hT_ge
    have h2 : Real.exp (3 * (x : ℝ) / 4) / (Real.exp (x : ℝ) / 2) = 2 / Real.exp ((x : ℝ) / 4) := by
      have e : Real.exp (x : ℝ) = Real.exp (3 * (x : ℝ) / 4) * Real.exp ((x : ℝ) / 4) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]; field_simp [(Real.exp_pos _).ne']
    have h3 : 2 / Real.exp ((x : ℝ) / 4) ≤ 2 / (x : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hx_pos) hexp_x2
    linarith
  have hexp_u : Real.exp (-(β * Real.log D)) ≤ 1 / (x : ℝ) ^ 2 := by
    rw [hu_eq]; dsimp [uParam]
    have h2log : 2 * Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ 5 / 4 := by
      have : (8 : ℝ) ≤ (Real.log (x : ℝ)) ^ 4 := by
        have h4 : (2 : ℝ) ^ 4 ≤ (Real.log (x : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog2 4
        norm_num at h4; linarith
      have : (Real.log (x : ℝ)) ^ 5 = Real.log (x : ℝ) * (Real.log (x : ℝ)) ^ 4 := by ring
      nlinarith
    calc Real.exp (-((Real.log (x : ℝ)) ^ 5 / 4))
        ≤ Real.exp (-(2 * Real.log (x : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (x : ℝ) ^ 2 := by
          rw [Real.exp_neg, show 2 * Real.log (x : ℝ) = Real.log ((x : ℝ) ^ 2) by
            rw [Real.log_pow]; ring, Real.exp_log (sq_pos_of_pos hx_pos), one_div]
  have hexp_u2 : Real.exp (-(β * Real.log D) / 2) ≤ 1 / (x : ℝ) := by
    have hsq : (Real.exp (-(β * Real.log D) / 2)) ^ 2 = Real.exp (-(β * Real.log D)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h1 : (Real.exp (-(β * Real.log D) / 2)) ^ 2 ≤ (1 / (x : ℝ)) ^ 2 := by
      rw [hsq]; simpa [one_div, inv_pow] using hexp_u
    nlinarith [Real.exp_pos (-(β * Real.log D) / 2), show (0 : ℝ) < 1 / (x : ℝ) by positivity]
  set S₁ : ℝ := (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (Rweight Pstar D a Q b s t) ^ 2
  set S₂ : ℝ := (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
    (Rweight Pstar D a Q b s t) ^ 2 *
      ∑ i : Fin k, if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i t then (1 : ℝ) else 0
  set A := A0 x Δ
  have hA_eq : A = ∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t := by
    unfold A A0 Aγ; apply Finset.sum_congr rfl; intro t _; simp [a]
  have hA_pos : 0 < A := by linarith
  have hAk_ge1 : 1 ≤ A ^ k := one_le_pow₀ hA1
  have hS1_ge : A ^ k / 2 ≤ S₁ := by
    have hfin := lem_finite_averages hk_pos Q b s hP hcop hdiff (by omega : 3 ≤ z) hgt hD8 hkz
      hsmall_lam hT_pos a habs_le (Dset Pstar D k) Finset.Subset.rfl
    have hR_eq : ∀ t, Rpartial Pstar D a Q b s (Dset Pstar D k) t = Rweight Pstar D a Q b s t :=
      fun t => (Rweight_eq_Rpartial_full hP a Q b s t).symm
    simp_rw [hR_eq] at hfin
    have hgram := lem_gram_estimate Q b s hP hcop hdiff (by omega : 3 ≤ z) hgt hD1 hsmall_gram
      (fun r => ∏ i : Fin k, a (r i))
    have hF_eq : (fun t => ∑ r ∈ Dset Pstar D k, (∏ i : Fin k, a (r i)) *
        ∏ i : Fin k, psiProd Q b s i (r i) t) = Rweight Pstar D a Q b s := by
      funext t; unfold Rweight; apply Finset.sum_congr rfl; intro r _; rw [Finset.prod_mul_distrib]
    have hI_eq : ∑ r ∈ Dset Pstar D k, (∏ i : Fin k, a (r i)) ^ 2 / ∏ i : Fin k, phi (r i) =
        ∑ r ∈ Dset Pstar D k, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i) := by
      apply Finset.sum_congr rfl; intro r _; rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    rw [hF_eq, hI_eq] at hgram
    set I_R := ∑ r ∈ Dset Pstar D k, ∏ i : Fin k, (a (r i)) ^ 2 / phi (r i)
    have hAβ_bound : ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ β) / phi t ≤
        (∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t) + C_1 * β := by
      have h := (htilt_fn β hβ_pos.le (by linarith)).2
      rw [← hA_eq]; exact h
    have hIR := I_R_lower_bound hP (by omega : 3 ≤ z) hgt hle_y hD1 hβ_pos (by linarith) hCp.le
      a habs_le hprime_fn (hA_eq ▸ hA1) hAβ_bound hC1kβ
    rw [← hA_eq] at hIR
    have hIR_le_Ak : I_R ≤ A ^ k := by linarith [hIR.1]
    have herr_gram : 6 * (k : ℝ) * Real.log D / (z : ℝ) ≤ 2 / (x : ℝ) := by
      rw [hD_log]
      have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
      have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
      rw [hz_eq, div_le_div_iff₀ (pow_pos hx_pos 6) hx_pos]
      have hkx2 : (k : ℝ) * (x : ℝ) ≤ (x : ℝ) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hkR hx_pos.le
      calc 6 * (k : ℝ) * ((x : ℝ) / 4) * (x : ℝ)
          = (3 / 2 : ℝ) * ((k : ℝ) * (x : ℝ)) * (x : ℝ) := by ring
        _ ≤ (3 / 2 : ℝ) * ((x : ℝ) ^ 2) * (x : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkx2 (by norm_num)) hx_pos.le
        _ = (3 / 2 : ℝ) * (x : ℝ) ^ 3 := by ring
        _ ≤ 2 * (x : ℝ) ^ 6 := by linarith [hx3_le_x6, pow_pos hx_pos 3]
    have herr_coll : (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ) ≤ C_p ^ 2 / (x : ℝ) := by
      have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
      have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
      rw [hz_eq, div_le_div_iff₀ (pow_pos hx_pos 6) hx_pos]
      have hksq : (k : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 2
      have hkx : (k : ℝ) ^ 2 * (x : ℝ) ≤ (x : ℝ) ^ 3 := by
        calc (k : ℝ) ^ 2 * (x : ℝ) ≤ (x : ℝ) ^ 2 * (x : ℝ) := mul_le_mul_of_nonneg_right hksq hx_pos.le
          _ = (x : ℝ) ^ 3 := by ring
      calc (k : ℝ) ^ 2 * C_p ^ 2 * (x : ℝ)
          = C_p ^ 2 * ((k : ℝ) ^ 2 * (x : ℝ)) := by ring
        _ ≤ C_p ^ 2 * (x : ℝ) ^ 6 := mul_le_mul_of_nonneg_left (hkx.trans hx3_le_x6) (sq_nonneg C_p)
    have hsum_err : Real.exp (-(β * Real.log D) / 2) + (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ) +
        6 * (k : ℝ) * Real.log D / (z : ℝ) + 2 / (x : ℝ) ^ 2 ≤ 1 / 2 := by
      have h1 : 2 / (x : ℝ) ^ 2 ≤ 1 / (x : ℝ) := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hx_pos) hx_pos]
        have h2x : 2 * (x : ℝ) ≤ (x : ℝ) * (x : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hx_pos.le
        rw [sq]; linarith
      have h2 : (C_p ^ 2 + 4) / (x : ℝ) ≤ 1 / 2 := by
        rw [div_le_iff₀ hx_pos]
        have : 16 * (C_p ^ 2 + 4) ≤ M_err := le_max_left _ _
        linarith
      have e : 1 / (x : ℝ) + C_p ^ 2 / (x : ℝ) + 2 / (x : ℝ) + 1 / (x : ℝ) = (C_p ^ 2 + 4) / (x : ℝ) := by ring
      linarith
    have hfin_lo : avg (val Pstar) (fun t => (Rweight Pstar D a Q b s t) ^ 2) - D ^ 3 / (T : ℝ) ≤ S₁ := by
      linarith [(abs_le.mp hfin).1]
    have hgram_lo : I_R - (6 * (k : ℝ) * Real.log D / (z : ℝ)) * I_R ≤
        avg (val Pstar) (fun t => (Rweight Pstar D a Q b s t) ^ 2) := by
      linarith [(abs_le.mp hgram).1]
    have hgram_Ak : (6 * (k : ℝ) * Real.log D / (z : ℝ)) * I_R ≤
        (6 * (k : ℝ) * Real.log D / (z : ℝ)) * A ^ k :=
      mul_le_mul_of_nonneg_left hIR_le_Ak (by rw [hD_log]; positivity)
    have hD3T_Ak : D ^ 3 / (T : ℝ) ≤ (2 / (x : ℝ) ^ 2) * A ^ k := by
      calc D ^ 3 / (T : ℝ) ≤ 2 / (x : ℝ) ^ 2 := hD3T
        _ = (2 / (x : ℝ) ^ 2) * 1 := (mul_one _).symm
        _ ≤ (2 / (x : ℝ) ^ 2) * A ^ k := mul_le_mul_of_nonneg_left hAk_ge1 (by positivity)
    have htot_err : A ^ k * (Real.exp (-(β * Real.log D) / 2) + (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ)) +
        (6 * (k : ℝ) * Real.log D / (z : ℝ)) * A ^ k + (2 / (x : ℝ) ^ 2) * A ^ k ≤
        (1 / 2) * A ^ k := by
      have e : A ^ k * (Real.exp (-(β * Real.log D) / 2) + (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ)) +
          (6 * (k : ℝ) * Real.log D / (z : ℝ)) * A ^ k + (2 / (x : ℝ) ^ 2) * A ^ k =
          (Real.exp (-(β * Real.log D) / 2) + (k : ℝ) ^ 2 * C_p ^ 2 / (z : ℝ) +
            6 * (k : ℝ) * Real.log D / (z : ℝ) + 2 / (x : ℝ) ^ 2) * A ^ k := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hsum_err (pow_nonneg hA_pos.le k)
    linarith [hIR.2]
  have hS2_lt : S₂ < A ^ k / 2 := by
    have hS2_swap : S₂ = ∑ i : Fin k, (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
        (Rweight Pstar D a Q b s t) ^ 2 *
          (if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i t then (1 : ℝ) else 0) := by
      dsimp [S₂]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hS2_swap]
    have haneg : ∀ d ∈ Pstar.powerset.erase ∅, a d ≤ 0 := by
      intro d hd
      have hne : d ≠ ∅ := (Finset.mem_erase.mp hd).1
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hd).2
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hqz : z < val d := lt_of_lt_of_le (hgt q (hsub hq))
        (Nat.le_of_dvd (val_pos (fun p hp => hP p (hsub hp))) (Finset.dvd_prod_of_mem _ hq))
      have hlogd : 0 < Real.log (val d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < val d))
      have hBpos : 0 < Bstar x Δ := hb_lo.trans_le hB_lo
      simp only [a, aCoeff, hne, ↓reduceIte]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_pos hBpos hlogd).le
    have hi_bound : ∀ i₀ : Fin k,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          (Rweight Pstar D a Q b s t) ^ 2 *
            (if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i₀ t then (1 : ℝ) else 0) ≤
        ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) * A ^ k := by
      intro i₀
      set J := (Dset Pstar D k).filter (fun d => d i₀ = ∅)
      have hdom : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          (Rweight Pstar D a Q b s t) ^ 2 *
            (if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i₀ t then (1 : ℝ) else 0) ≤
          (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (Rpartial Pstar D a Q b s J t) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro t _
        split_ifs with huncov
        · rw [mul_one, Rweight_eq_Rpartial_erase_of_uncov hP a Q b s i₀ t huncov]
        · rw [mul_zero]; exact sq_nonneg _
      have hfin := lem_finite_averages hk_pos Q b s hP hcop hdiff (by omega : 3 ≤ z) hgt hD8 hkz
        hsmall_lam hT_pos a habs_le J (Finset.filter_subset _ _)
      have hgram := lem_gram_estimate Q b s hP hcop hdiff (by omega : 3 ≤ z) hgt hD1 hsmall_gram
        (cUncov Pstar D a i₀)
      have hFeq : (fun t => ∑ r ∈ Dset Pstar D k, cUncov Pstar D a i₀ r *
          ∏ i : Fin k, psiProd Q b s i (r i) t) = Rpartial Pstar D a Q b s J := by
        funext t; exact (Rpartial_erase_eq_sum_eps hP a Q b s i₀ t).symm
      rw [hFeq] at hgram
      set I_i := ∑ r ∈ Dset Pstar D k, (cUncov Pstar D a i₀ r) ^ 2 / ∏ i : Fin k, phi (r i)
      have hI_i_nn : 0 ≤ I_i := Finset.sum_nonneg fun r hr =>
        div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ =>
          (phi_pos (fun p hp => hP p ((mem_Dset_iff.mp hr).1 i hp))).le)
      have hgram_hi : avg (val Pstar) (fun t => (Rpartial Pstar D a Q b s J t) ^ 2) ≤ 2 * I_i := by
        have h1 : 6 * (k : ℝ) * Real.log D / (z : ℝ) ≤ 1 := by
          rw [hD_log, div_le_one hz_pos]
          have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
          have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
          have hkx2 : (k : ℝ) * (x : ℝ) ≤ (x : ℝ) ^ 2 := by
            rw [sq]; exact mul_le_mul_of_nonneg_right hkR hx_pos.le
          calc 6 * (k : ℝ) * ((x : ℝ) / 4)
              = (3 / 2 : ℝ) * ((k : ℝ) * (x : ℝ)) := by ring
            _ ≤ (3 / 2 : ℝ) * (x : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hkx2 (by norm_num)
            _ ≤ (x : ℝ) ^ 3 := by
                have : (3 / 2 : ℝ) * (x : ℝ) ^ 2 ≤ (x : ℝ) * (x : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
                linarith [show (x : ℝ) * (x : ℝ) ^ 2 = (x : ℝ) ^ 3 by ring]
            _ ≤ (x : ℝ) ^ 6 := hx3_le_x6
            _ = (z : ℝ) := hz_eq.symm
        have h2 := (abs_le.mp hgram).2
        have h3 := mul_le_mul_of_nonneg_right h1 hI_i_nn
        linarith
      have hA2β_bound : ∑ t ∈ Pstar.powerset, (a t) ^ 2 * ((val t : ℝ) ^ (2 * β)) / phi t ≤
          (∑ t ∈ Pstar.powerset, (a t) ^ 2 / phi t) + C_1 * (2 * β) := by
        have h := (htilt_fn (2 * β) (by positivity) le_rfl).2
        rw [← hA_eq]; exact h
      have hI_bound := I_uncov_upper_bound hP (by omega : 3 ≤ z) hgt hD1 hβ_pos (by linarith) hCp.le
        a hcancel haneg (htilt_fn β hβ_pos.le (by linarith)).1 hprime_fn
        (hA_eq ▸ hA1) hA2β_bound (by linarith [hC1kβ]) i₀
      rw [← hA_eq] at hI_bound
      have hDz2 : (Real.log D / (z : ℝ)) ^ 2 ≤ 1 / (x : ℝ) ^ 2 := by
        rw [hD_log]
        have hz_eq : (z : ℝ) = (x : ℝ) ^ 6 := by simp [z, zParam]
        have h1 : ((x : ℝ) / 4) / (z : ℝ) ≤ 1 / (x : ℝ) := by
          rw [hz_eq, div_le_div_iff₀ (pow_pos hx_pos 6) hx_pos]
          calc ((x : ℝ) / 4) * (x : ℝ) = (1 / 4 : ℝ) * (x : ℝ) ^ 2 := by ring
            _ ≤ 1 * (x : ℝ) ^ 2 := by linarith [sq_nonneg (x : ℝ)]
            _ = (x : ℝ) ^ 2 := one_mul _
            _ ≤ (x : ℝ) ^ 6 := hx2_le_x6
            _ = 1 * (x : ℝ) ^ 6 := (one_mul _).symm
        simpa [one_div, inv_pow] using pow_le_pow_left₀ (by positivity) h1 2
      have hD3T_Ak : D ^ 3 / (T : ℝ) ≤ (2 / (x : ℝ) ^ 2) * A ^ k := by
        calc D ^ 3 / (T : ℝ) ≤ 2 / (x : ℝ) ^ 2 := hD3T
          _ = (2 / (x : ℝ) ^ 2) * 1 := (mul_one _).symm
          _ ≤ (2 / (x : ℝ) ^ 2) * A ^ k := mul_le_mul_of_nonneg_left hAk_ge1 (by positivity)
      have hfin_hi : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (Rpartial Pstar D a Q b s J t) ^ 2 ≤
          avg (val Pstar) (fun t => (Rpartial Pstar D a Q b s J t) ^ 2) + D ^ 3 / (T : ℝ) := by
        linarith [(abs_le.mp hfin).2]
      have hI_simp : 2 * I_i ≤ ((4 * C_tilt ^ 2 + 4 * C_p ^ 2) / (x : ℝ) ^ 2) * A ^ k := by
        have h1 := mul_le_mul_of_nonneg_left hexp_u (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_tilt))
        have h2 := mul_le_mul_of_nonneg_left hDz2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C_p))
        have h3 : 2 * (2 * C_tilt ^ 2 * Real.exp (-(β * Real.log D)) +
            2 * C_p ^ 2 * (Real.log D / (z : ℝ)) ^ 2) ≤ (4 * C_tilt ^ 2 + 4 * C_p ^ 2) / (x : ℝ) ^ 2 := by
          have e : (4 * C_tilt ^ 2 + 4 * C_p ^ 2) / (x : ℝ) ^ 2 =
              2 * (2 * C_tilt ^ 2 * (1 / (x : ℝ) ^ 2) + 2 * C_p ^ 2 * (1 / (x : ℝ) ^ 2)) := by ring
          linarith
        have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hA_pos.le k)
        linarith [hI_bound]
      have e : ((4 * C_tilt ^ 2 + 4 * C_p ^ 2) / (x : ℝ) ^ 2) * A ^ k + (2 / (x : ℝ) ^ 2) * A ^ k =
          ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) * A ^ k := by ring
      linarith
    calc ∑ i : Fin k, (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
            (Rweight Pstar D a Q b s t) ^ 2 *
              (if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i t then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin k, ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) * A ^ k :=
          Finset.sum_le_sum fun i _ => hi_bound i
      _ = (k : ℝ) * (((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) * A ^ k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ)) * A ^ k := by
          have hkR : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk_le_x
          have h1 : (k : ℝ) * ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) ≤
              (x : ℝ) * ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hkR (by positivity)
          have h2 : (x : ℝ) * ((4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) ^ 2) =
              (4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) / (x : ℝ) := by field_simp [hx_pos.ne']
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (h1.trans_eq h2) (pow_nonneg hA_pos.le k)
      _ < (1 / 2) * A ^ k := by
          apply mul_lt_mul_of_pos_right _ (pow_pos hA_pos k)
          rw [div_lt_iff₀ hx_pos]
          have : 16 * (4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2) ≤ M_err := le_max_right _ _
          linarith
      _ = A ^ k / 2 := by ring
  have hS2_lt_S1 : S₂ < S₁ := hS2_lt.trans_le hS1_ge
  have hex_t : ∃ t ∈ Finset.Icc 1 T, ∀ i : Fin k, ∃ p ∈ Pstar, (p : ℤ) ∣ Lform Q b s i t := by
    by_contra hall
    push Not at hall
    have hge : S₁ ≤ S₂ := by
      dsimp [S₁, S₂]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨i₀, hi₀⟩ := hall t ht
      have hcnt : (1 : ℝ) ≤ ∑ i : Fin k, if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i t then (1 : ℝ) else 0 := by
        have hle := Finset.single_le_sum
          (f := fun i : Fin k => if ∀ p ∈ Pstar, ¬ (p : ℤ) ∣ Lform Q b s i t then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i₀)
        rw [if_pos hi₀] at hle
        exact hle
      calc (Rweight Pstar D a Q b s t) ^ 2
          = (Rweight Pstar D a Q b s t) ^ 2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hcnt (sq_nonneg _)
    linarith
  obtain ⟨t, ht_mem, ht_cov⟩ := hex_t
  rw [Finset.mem_Icc] at ht_mem
  refine ⟨t, ht_mem.1, (Nat.cast_le.mpr ht_mem.2).trans (Nat.floor_le (Real.exp_pos _).le), ?_⟩
  intro i
  obtain ⟨p, hpP, hpdvd⟩ := ht_cov i
  exact ⟨p, hP p hpP, (Nat.cast_le.mpr (hle_y p hpP)).trans hy_le_expx, hpdvd⟩

/-- Main Theorem of Section 3 (`lem:translate` in Radomskii, arXiv:2610.14127). -/
lemma lem_translate :
    ∃ η : ℝ, 0 < η ∧
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    ∀ (S : Finset ℤ) (b : ℤ),
      S.Nonempty →
      (S.card : ℝ) ≤ η * (x : ℝ) →
      (∀ s ∈ S, (s.natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ))) →
      ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp (x : ℝ) ∧
        ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧
          (p : ℝ) ≤ Real.exp (x : ℝ) ∧
          (p : ℤ) ∣ b + (primorial x : ℤ) * (t : ℤ) + s := by
  classical
  obtain ⟨b_lo, b_hi, c_U, hb_lo, _, hc_U, X₁, _, hdiv⟩ := lem_divisor_sums
  obtain ⟨C_tilt, C_1, C_p, hCtilt, hC1, hCp, X₂, _, hcoeff⟩ := lem_coefficient_bounds hb_lo hc_U
  let η : ℝ := min 1 (1 / (8 * C_1))
  have hη_pos : 0 < η := lt_min zero_lt_one (by positivity)
  have hη_le1 : η ≤ 1 := min_le_left _ _
  have hη_C1 : η ≤ 1 / (8 * C_1) := min_le_right _ _
  let M_err : ℝ := max (16 * (C_p ^ 2 + 4)) (16 * (4 * C_tilt ^ 2 + 4 * C_p ^ 2 + 2))
  have hx_big : ∀ᶠ x : ℕ in atTop, M_err < (x : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop M_err
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_param_bounds 16).and (hx_big.and (eventually_ge_atTop (max 384 (max X₁ X₂)))))
  refine ⟨η, hη_pos, max X₀ 384, ?_⟩
  intro x hx S b hS_ne hS_card hS_bound
  obtain ⟨⟨hx16, _, hz16, hlog2, _, _, _, _, _, hT_ge, hy_le_expx⟩,
    hx_Merr, hx384⟩ := hX₀ x ((le_max_left _ _).trans hx)
  have hx_ge384 : 384 ≤ x := (le_max_left 384 _).trans hx384
  have hx12 : max X₁ X₂ ≤ x := (le_max_right 384 _).trans hx384
  have hxX₁ : X₁ ≤ x := (le_max_left X₁ X₂).trans hx12
  have hxX₂ : X₂ ≤ x := (le_max_right X₁ X₂).trans hx12
  have hexp_x2 : (x : ℝ) ^ 2 ≤ Real.exp ((x : ℝ) / 4) := by
    have hpow := Real.pow_div_factorial_le_exp (x := (x : ℝ) / 4) (by positivity) 3
    have h384R : (384 : ℝ) ≤ x := by exact_mod_cast hx_ge384
    have e : ((x : ℝ) / 4) ^ 3 / (Nat.factorial 3 : ℝ) = (x : ℝ) ^ 3 / 384 := by
      norm_num [Nat.factorial]; ring
    rw [e] at hpow
    nlinarith [sq_nonneg (x : ℝ)]
  let k := S.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hS_ne
  have hk_le_x : k ≤ x := by
    have h1 : (k : ℝ) ≤ (x : ℝ) := hS_card.trans (mul_le_of_le_one_left (Nat.cast_nonneg x) hη_le1)
    exact_mod_cast h1
  have hC1k_le : C_1 * (k : ℝ) ≤ (x : ℝ) / 8 := by
    have hx_nn : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have h1 : C_1 * (k : ℝ) ≤ C_1 * (η * (x : ℝ)) := mul_le_mul_of_nonneg_left hS_card (by linarith)
    have h2 : C_1 * (η * (x : ℝ)) ≤ C_1 * (1 / (8 * C_1) * (x : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hη_C1 hx_nn) (by linarith)
    have e : C_1 * (1 / (8 * C_1) * (x : ℝ)) = (x : ℝ) / 8 := by
      field_simp [show C_1 ≠ 0 by linarith]
    linarith
  let eS := S.equivFin.symm
  let s : Fin k → ℤ := fun i => (eS i).val
  have hs_inj : Function.Injective s := fun i j h => eS.injective (Subtype.ext h)
  have hs_bound : ∀ i : Fin k, ((s i).natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ)) :=
    fun i => hS_bound (s i) (eS i).property
  let pairs := Finset.univ.filter (fun pq : Fin k × Fin k => pq.1 < pq.2)
  let Δ : ℕ := ∏ pq ∈ pairs, (s pq.1 - s pq.2).natAbs
  obtain ⟨hU0_le, hB_fn⟩ := hdiv x hxX₁
  obtain ⟨hB_lo, _⟩ := hB_fn k s hk_le_x hs_inj hs_bound
  obtain ⟨hcancel, habs_le, hA1, htilt_fn, hprime_fn⟩ := hcoeff x hxX₂ hU0_le Δ hB_lo
  have hdiff : ∀ p ∈ primesStar x Δ, ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (s i - s j) := by
    intro p hp i j hij hdvd
    have hndΔ : ¬ p ∣ Δ := (Finset.mem_filter.mp hp).2
    apply hndΔ
    rcases lt_or_gt_of_ne hij with hlt | hgt'
    · have hmem : (i, j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact dvd_trans (Int.natCast_dvd.mp hdvd) (Finset.dvd_prod_of_mem _ hmem)
    · have hmem : (j, i) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt'⟩
      have hdvd' : (p : ℤ) ∣ (s j - s i) := by
        have e : s j - s i = -(s i - s j) := by ring
        rw [e]; exact dvd_neg.mpr hdvd
      exact dvd_trans (Int.natCast_dvd.mp hdvd') (Finset.dvd_prod_of_mem _ hmem)
  obtain ⟨t, ht1, ht_le, hcov⟩ := lem_translate_core hb_lo hCtilt hC1 hCp hx16 hz16 hlog2
    hT_ge hy_le_expx hexp_x2 hx_Merr hk_pos hk_le_x hC1k_le b s hB_lo
    hcancel habs_le hA1 htilt_fn hprime_fn hdiff
  refine ⟨t, ht1, ht_le, fun sv hsv => ?_⟩
  let i := S.equivFin ⟨sv, hsv⟩
  have hsi : s i = sv := by simp [s, eS, i]
  simpa [hsi] using hcov i

end OMA32Rad2

namespace OMA32Rad

/- ### Section A: Exact Interface for `lem_translate` -/

/-- Exact agreed statement of Lemma 3.1 (`lem:translate`) between Part 1 and Part 2. -/
def LemTranslateStmt : Prop :=
  ∃ η : ℝ, 0 < η ∧
  ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
  ∀ (S : Finset ℤ) (b : ℤ),
    S.Nonempty →
    (S.card : ℝ) ≤ η * (x : ℝ) →
    (∀ s ∈ S, (s.natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ))) →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp (x : ℝ) ∧
      ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧
        (p : ℝ) ≤ Real.exp (x : ℝ) ∧
        (p : ℤ) ∣ b + (primorial x : ℤ) * (t : ℤ) + s

/- ### Section B: Elementary Chebyshev and Mertens Estimates -/

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have heq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma primorial_le_exp_two_mul (x : ℕ) :
    (primorial x : ℝ) ≤ Real.exp (2 * (x : ℝ)) := by
  have hpos : (0 : ℝ) < primorial x := by exact_mod_cast primorial_pos x
  have hlog : Real.log (primorial x : ℝ) ≤ 2 * (x : ℝ) := by
    have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg x)
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
    exact h.trans (mul_le_mul_of_nonneg_right log_four_le_two (Nat.cast_nonneg x))
  calc
    (primorial x : ℝ) = Real.exp (Real.log (primorial x : ℝ)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (2 * (x : ℝ)) := Real.exp_le_exp.mpr hlog

/-- Euler totient ratio for a finite product of distinct primes. -/
lemma totient_prod_primes_div (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (((∏ p ∈ P, p).totient : ℕ) : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ) =
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert q P hq ih =>
    have hqP : q.Prime := hP q (Finset.mem_insert_self q P)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcop : q.Coprime (∏ p ∈ P, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hqP (hP' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Nat.totient_mul hcop, Nat.totient_prime hqP, Finset.prod_insert hq]
    rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm, ih hP']
    congr 1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqP.pos
    rw [Nat.cast_sub hqP.one_le, Nat.cast_one]
    field_simp

lemma totient_primorial_div (x : ℕ) :
    ((primorial x).totient : ℝ) / (primorial x : ℝ) =
      ∏ p ∈ x.primesLE, (1 - 1 / (p : ℝ)) := by
  rw [primorial_eq_prod_primesLE]
  exact totient_prod_primes_div x.primesLE (fun p hp => Nat.prime_of_mem_primesLE hp)

/-- Elementary Mertens upper bound: `φ(primorial x) / primorial x ≤ C_M / log x` for large `x`. -/
lemma mertens_totient_upper :
    ∃ C_M : ℝ, 0 < C_M ∧ ∃ X_M : ℕ, 2 ≤ X_M ∧ ∀ x : ℕ, X_M ≤ x →
      ((primorial x).totient : ℝ) / (primorial x : ℝ) ≤ C_M / Real.log (x : ℝ) := by
  obtain ⟨B, hB⟩ := OMA32Rad2.exists_prime_reciprocal_limit
  have hev := hB.eventually (eventually_gt_nhds (show B - 1 < B by linarith))
  rw [eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨Real.exp (1 - B), Real.exp_pos _, max X₁ 2, le_max_right _ _, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  have hsum : B - 1 < (∑ p ∈ x.primesLE, (1 : ℝ) / p) - Real.log (Real.log (x : ℝ)) :=
    hX₁ x hx1
  rw [totient_primorial_div]
  have hprod : ∏ p ∈ x.primesLE, (1 - 1 / (p : ℝ)) ≤
      ∏ p ∈ x.primesLE, Real.exp (-(1 / (p : ℝ))) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
      have hp0 : (0 : ℝ) < p := by linarith
      exact sub_nonneg.mpr ((div_le_iff₀ hp0).mpr (by simpa using hp1))
    · linarith [Real.add_one_le_exp (-(1 / (p : ℝ)))]
  rw [← Real.exp_sum, Finset.sum_neg_distrib] at hprod
  calc
    ∏ p ∈ x.primesLE, (1 - 1 / (p : ℝ))
        ≤ Real.exp (-(∑ p ∈ x.primesLE, (1 : ℝ) / p)) := hprod
    _ ≤ Real.exp ((1 - B) - Real.log (Real.log (x : ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp (1 - B) / Real.log (x : ℝ) := by
        rw [Real.exp_sub, Real.exp_log hlogpos]

/- ### Section C: Residue Averaging and Empty Gap Lemma -/

lemma coprime_emod_iff_no_prime_dvd (a : ℤ) {Q : ℕ} (hQ : 0 < Q) :
    Nat.Coprime (a % (Q : ℤ)).toNat Q ↔
      ∀ p : ℕ, p.Prime → p ∣ Q → ¬ ((p : ℤ) ∣ a) := by
  have hQpos : (0 : ℤ) < Q := by exact_mod_cast hQ
  set m : ℕ := (a % (Q : ℤ)).toNat
  have hm : (m : ℤ) = a % (Q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg a hQpos.ne')
  have hdiv : ∀ p : ℕ, p ∣ Q → ((p : ℤ) ∣ a ↔ p ∣ m) := by
    intro p hpQ
    have hpQZ : (p : ℤ) ∣ (Q : ℤ) := Int.ofNat_dvd.mpr hpQ
    have hdecomp : a = (Q : ℤ) * (a / (Q : ℤ)) + (m : ℤ) := by
      rw [hm]
      exact (Int.mul_ediv_add_emod a (Q : ℤ)).symm
    constructor
    · intro hpa
      have hpmZ : (p : ℤ) ∣ (m : ℤ) := by
        have h1 : (p : ℤ) ∣ (Q : ℤ) * (a / (Q : ℤ)) := dvd_mul_of_dvd_left hpQZ _
        have h2 : (m : ℤ) = a - (Q : ℤ) * (a / (Q : ℤ)) := by linarith
        rw [h2]
        exact dvd_sub hpa h1
      exact Int.ofNat_dvd.mp hpmZ
    · intro hpm
      rw [hdecomp]
      exact dvd_add (dvd_mul_of_dvd_left hpQZ _) (Int.ofNat_dvd.mpr hpm)
  constructor
  · intro hcop p hp hpQ hpa
    have hpm : p ∣ m := (hdiv p hpQ).mp hpa
    exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpm hpQ)
  · intro hno
    by_contra hnc
    have hne : Nat.gcd m Q ≠ 1 := hnc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpm : p ∣ m := hpd.trans (Nat.gcd_dvd_left m Q)
    have hpQ : p ∣ Q := hpd.trans (Nat.gcd_dvd_right m Q)
    exact hno p hp hpQ ((hdiv p hpQ).mpr hpm)

lemma card_filter_coprime_shift (Q : ℕ) (hQ : 0 < Q) (s : ℤ) :
    ((Finset.range Q).filter (fun r : ℕ => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card =
      Q.totient := by
  have hQpos : (0 : ℤ) < Q := by exact_mod_cast hQ
  let f : ℕ → ℕ := fun r => (((r : ℤ) + s) % (Q : ℤ)).toNat
  have hf_mem : ∀ r ∈ Finset.range Q, f r ∈ Finset.range Q := by
    intro r _
    rw [Finset.mem_range]
    have hlt : ((r : ℤ) + s) % (Q : ℤ) < (Q : ℤ) := Int.emod_lt_of_pos _ hQpos
    have hnn : 0 ≤ ((r : ℤ) + s) % (Q : ℤ) := Int.emod_nonneg _ hQpos.ne'
    dsimp only [f]
    omega
  have hf_inj : Set.InjOn f (Finset.range Q : Set ℕ) := by
    intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hr₁ hr₂
    have h1 : 0 ≤ ((r₁ : ℤ) + s) % (Q : ℤ) := Int.emod_nonneg _ hQpos.ne'
    have h2 : 0 ≤ ((r₂ : ℤ) + s) % (Q : ℤ) := Int.emod_nonneg _ hQpos.ne'
    have hmod : ((r₁ : ℤ) + s) % (Q : ℤ) = ((r₂ : ℤ) + s) % (Q : ℤ) := by
      have hcast : ((f r₁ : ℕ) : ℤ) = ((f r₂ : ℕ) : ℤ) := by exact_mod_cast heq
      dsimp only [f] at hcast
      rwa [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcast
    have hdvd : (Q : ℤ) ∣ ((r₁ : ℤ) - (r₂ : ℤ)) :=
      ⟨((r₁ : ℤ) + s) / (Q : ℤ) - ((r₂ : ℤ) + s) / (Q : ℤ), by
        have e1 : (Q : ℤ) * (((r₁ : ℤ) + s) / (Q : ℤ)) + ((r₁ : ℤ) + s) % (Q : ℤ) = (r₁ : ℤ) + s :=
          Int.mul_ediv_add_emod _ _
        have e2 : (Q : ℤ) * (((r₂ : ℤ) + s) / (Q : ℤ)) + ((r₂ : ℤ) + s) % (Q : ℤ) = (r₂ : ℤ) + s :=
          Int.mul_ediv_add_emod _ _
        linarith⟩
    obtain ⟨k, hk⟩ := hdvd
    have hlt1 : (r₁ : ℤ) - (r₂ : ℤ) < (Q : ℤ) := by omega
    have hlt2 : -(Q : ℤ) < (r₁ : ℤ) - (r₂ : ℤ) := by omega
    have hk0 : k = 0 := by nlinarith
    rw [hk0, mul_zero] at hk
    omega
  have himg : (Finset.range Q).image f = Finset.range Q := by
    refine Finset.eq_of_subset_of_card_le (fun m hm => ?_) ?_
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
      exact hf_mem r hr
    · rw [Finset.card_image_of_injOn hf_inj]
  have hcard :
      ((Finset.range Q).filter (fun r => Nat.Coprime (f r) Q)).card =
        ((Finset.range Q).filter (fun m => Nat.Coprime m Q)).card := by
    have h1 : ((Finset.range Q).filter (fun r => Nat.Coprime (f r) Q)).image f =
        (Finset.range Q).filter (fun m => Nat.Coprime m Q) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨r, ⟨hr, hcop⟩, rfl⟩
        exact ⟨hf_mem r hr, hcop⟩
      · rintro ⟨hm, hcop⟩
        rw [← himg] at hm
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
        exact ⟨r, ⟨hr, hcop⟩, rfl⟩
    rw [← h1, Finset.card_image_of_injOn (hf_inj.mono (Finset.filter_subset _ _))]
  rw [hcard, Nat.totient]
  congr 1
  ext m
  simp [Nat.coprime_comm]

/-- Averaging over residue classes modulo `Q`: some `r < Q` leaves at most `|S₀| * φ(Q) / Q`
coprime shifts. -/
lemma exists_good_residue (Q : ℕ) (hQ : 0 < Q) (S₀ : Finset ℤ) :
    ∃ r : ℕ, r < Q ∧
      Q * (S₀.filter (fun s => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card ≤
        S₀.card * Q.totient := by
  have hsum :
      ∑ r ∈ Finset.range Q,
          (S₀.filter (fun s => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card =
        S₀.card * Q.totient := by
    calc
      ∑ r ∈ Finset.range Q,
            (S₀.filter (fun s => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card
          = ∑ r ∈ Finset.range Q, ∑ s ∈ S₀,
              if Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q then 1 else 0 := by
              simp_rw [Finset.card_filter]
      _ = ∑ s ∈ S₀, ∑ r ∈ Finset.range Q,
              if Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q then 1 else 0 :=
              Finset.sum_comm
      _ = ∑ s ∈ S₀,
              ((Finset.range Q).filter (fun r : ℕ => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card := by
              simp_rw [Finset.card_filter]
      _ = ∑ _s ∈ S₀, Q.totient := Finset.sum_congr rfl (fun s _ => card_filter_coprime_shift Q hQ s)
      _ = S₀.card * Q.totient := by simp
  by_contra! hall
  have hlt :
      ∑ _r ∈ Finset.range Q, (S₀.card * Q.totient) <
        ∑ r ∈ Finset.range Q,
          Q * (S₀.filter (fun s => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)).card := by
    refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hQ.ne') fun r hr => ?_
    exact hall r (Finset.mem_range.mp hr)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum, hsum] at hlt
  exact lt_irrefl _ hlt

/-- Elementary pigeonhole gap lemma: `T ⊆ (a, b)` leaves a subinterval `(u, v) ⊆ (a, b)`
disjoint from `T` with `(T.card + 1) * (v - u) ≥ b - a`. -/
lemma exists_empty_gap_finset :
    ∀ n : ℕ, ∀ (a b : ℕ) (T : Finset ℕ),
      T.card = n → a < b → (∀ t ∈ T, a < t ∧ t < b) →
      ∃ u v : ℕ, a ≤ u ∧ u < v ∧ v ≤ b ∧
        (∀ t ∈ T, t ≤ u ∨ v ≤ t) ∧
        b - a ≤ (T.card + 1) * (v - u) := by
  intro n
  induction n with
  | zero =>
    intro a b T hcard hab _
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨a, b, le_refl a, hab, le_refl b, ?_, ?_⟩
    · intro t ht; simp [hT] at ht
    · rw [hcard]; omega
  | succ k ih =>
    intro a b T hcard hab hT
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    let m : ℕ := T.max' hne
    have hmT : m ∈ T := Finset.max'_mem T hne
    have hma : a < m := (hT m hmT).1
    have hmb : m < b := (hT m hmT).2
    let T' : Finset ℕ := T.erase m
    have hcard' : T'.card = k := by
      rw [Finset.card_erase_of_mem hmT, hcard]; omega
    have hT' : ∀ t ∈ T', a < t ∧ t < m := by
      intro t ht
      have htT : t ∈ T := Finset.mem_of_mem_erase ht
      have hne_m : t ≠ m := Finset.ne_of_mem_erase ht
      have hle_m : t ≤ m := Finset.le_max' T t htT
      exact ⟨(hT t htT).1, lt_of_le_of_ne hle_m hne_m⟩
    obtain ⟨u₁, v₁, hau₁, huv₁, hv₁m, hdisj₁, hlen₁⟩ := ih a m T' hcard' hma hT'
    by_cases hcmp : b - m ≤ v₁ - u₁
    · refine ⟨u₁, v₁, hau₁, huv₁, hv₁m.trans hmb.le, ?_, ?_⟩
      · intro t ht
        by_cases htm : t = m
        · right; omega
        · exact hdisj₁ t (Finset.mem_erase.mpr ⟨htm, ht⟩)
      · rw [hcard'] at hlen₁
        rw [hcard]
        have h1 : (k + 1 + 1) * (v₁ - u₁) = (k + 1) * (v₁ - u₁) + (v₁ - u₁) := by ring
        omega
    · push Not at hcmp
      refine ⟨m, b, hma.le, hmb, le_refl b, ?_, ?_⟩
      · intro t ht
        left
        exact Finset.le_max' T t ht
      · rw [hcard'] at hlen₁
        rw [hcard]
        have hmul : (k + 1) * (v₁ - u₁) ≤ (k + 1) * (b - m) :=
          Nat.mul_le_mul_left (k + 1) hcmp.le
        have h1 : (k + 1 + 1) * (b - m) = (k + 1) * (b - m) + (b - m) := by ring
        omega

lemma exists_empty_gap (A : Set ℕ) [DecidablePred (· ∈ A)] (X : ℕ) (hX : 4 ≤ X) :
    ∃ u v : ℕ, X / 2 ≤ u ∧ u < v ∧ v ≤ X ∧
      (∀ a ∈ A, a ≤ u ∨ v ≤ a) ∧
      X / 2 ≤ (((Finset.Icc 0 X).filter (· ∈ A)).card + 1) * (v - u) := by
  let T : Finset ℕ := (Finset.Ioo (X / 2) X).filter (· ∈ A)
  have hlt : X / 2 < X := by omega
  have hT : ∀ t ∈ T, X / 2 < t ∧ t < X := fun t ht =>
    Finset.mem_Ioo.mp (Finset.mem_filter.mp ht).1
  obtain ⟨u, v, hu, huv, hv, hdisj, hlen⟩ :=
    exists_empty_gap_finset T.card (X / 2) X T rfl hlt hT
  have hsub : T ⊆ (Finset.Icc 0 X).filter (· ∈ A) := by
    intro t ht
    obtain ⟨hioo, ha⟩ := Finset.mem_filter.mp ht
    have ⟨h1, h2⟩ := Finset.mem_Ioo.mp hioo
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, h2.le⟩, ha⟩
  have hcard : T.card ≤ ((Finset.Icc 0 X).filter (· ∈ A)).card := Finset.card_le_card hsub
  refine ⟨u, v, hu, huv, hv, ?_, ?_⟩
  · intro a ha
    by_cases h1 : a ≤ X / 2
    · left; omega
    · by_cases h2 : X ≤ a
      · right; omega
      · exact hdisj a (Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, ha⟩)
  · have hhalf : X / 2 ≤ X - X / 2 := by omega
    have hmul : (T.card + 1) * (v - u) ≤
        (((Finset.Icc 0 X).filter (· ∈ A)).card + 1) * (v - u) :=
      Nat.mul_le_mul_right (v - u) (Nat.add_le_add_right hcard 1)
    omega

/- ### Section D: Elementary Growth Helper & Block Theorem (`H = 1`) -/

/-- Explicit growth inequality: `18 * (log X)^2 < X^(2/5)` for all `X ≥ 1801^5`. -/
lemma log_sq_lt_rpow_two_fifths (X : ℕ) (hX : 1801 ^ 5 ≤ X) :
    18 * (Real.log (X : ℝ)) ^ 2 < (X : ℝ) ^ (2 / 5 : ℝ) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by positivity)
  have hXge : ((1801 : ℝ) ^ 5) ≤ (X : ℝ) := by exact_mod_cast hX
  set t : ℝ := (X : ℝ) ^ (1 / 10 : ℝ)
  have htpos : 0 < t := Real.rpow_pos_of_pos hXpos _
  have ht2 : t ^ 2 = (X : ℝ) ^ (1 / 5 : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num
  have ht4 : t ^ 4 = (X : ℝ) ^ (2 / 5 : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num
  have hlog : Real.log (X : ℝ) = 10 * Real.log t := by
    dsimp only [t]
    rw [Real.log_rpow hXpos]
    ring
  have hlog_le : Real.log t ≤ t := by linarith [Real.log_le_sub_one_of_pos htpos]
  have hlog_nn : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hlogt_nn : 0 ≤ Real.log t := by linarith
  have hsq : (Real.log (X : ℝ)) ^ 2 ≤ 100 * t ^ 2 := by
    rw [hlog]
    nlinarith
  have ht2_gt : (1800 : ℝ) < t ^ 2 := by
    rw [ht2]
    have hpow : (1801 : ℝ) = ((1801 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hle : (1801 : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) := by
      rw [hpow]
      exact Real.rpow_le_rpow (by positivity) hXge (by norm_num)
    linarith
  have ht4_eq : t ^ 4 = t ^ 2 * t ^ 2 := by ring
  rw [← ht4, ht4_eq]
  nlinarith

lemma prime_le_of_dvd_primorial {p x : ℕ} (hp : p.Prime) (hdvd : p ∣ primorial x) : p ≤ x := by
  rw [primorial_eq_prod_primesLE] at hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
  have ⟨hqx, hqp⟩ := Nat.mem_primesLE.mp hq
  rcases (Nat.dvd_prime hqp).mp hpq with h1 | rfl
  · exact absurd h1 hp.ne_one
  · exact hqx

/-- Clean helper for placing `N = b + Q * t` inside the middle third of `(u, v)`. -/
lemma translate_interval_bounds {u v Q b t : ℕ} {E : ℝ}
    (huv : u < v) (hQ : 0 < Q) (ht1 : 1 ≤ t) (htE : (t : ℝ) ≤ E)
    (hb_ge : u + (v - u) / 3 + 1 ≤ b)
    (hb_lt : b < u + (v - u) / 3 + 1 + Q)
    (hroom : (1 : ℝ) + (Q : ℝ) + (Q : ℝ) * E < 2 * ((v - u : ℕ) : ℝ) / 3) :
    u < b + Q * t ∧ b + Q * t < v ∧
      ((v - u : ℕ) : ℝ) / 3 < ((b + Q * t : ℕ) : ℝ) - (u : ℝ) := by
  set L : ℝ := ((v - u : ℕ) : ℝ)
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNu_gt : L / 3 < ((b + Q * t : ℕ) : ℝ) - (u : ℝ) := by
    have h1 : (v - u : ℕ) < 3 * ((v - u) / 3 + 1) := by omega
    have h2 : L < 3 * ((((v - u) / 3 : ℕ) : ℝ) + 1) := by
      have h1' : ((v - u : ℕ) : ℝ) < ((3 * ((v - u) / 3 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      simpa [L, Nat.cast_mul, Nat.cast_add] using h1'
    have h3 : ((u + (v - u) / 3 + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_ge
    have h4 : (b : ℝ) < ((b + Q * t : ℕ) : ℝ) := by
      have : 0 < Q * t := Nat.mul_pos hQ (by omega)
      exact_mod_cast (show b < b + Q * t by omega)
    push_cast at h3
    linarith
  have hN_lt_v : b + Q * t < v := by
    have h1 : ((v - u) / 3 : ℕ) * 3 ≤ v - u := Nat.div_mul_le_self (v - u) 3
    have h2 : (((v - u) / 3 : ℕ) : ℝ) ≤ L / 3 := by
      have h1' : (((v - u) / 3 * 3 : ℕ) : ℝ) ≤ ((v - u : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      dsimp only [L]
      linarith
    have h3 : (b : ℝ) < ((u + (v - u) / 3 + 1 + Q : ℕ) : ℝ) := by exact_mod_cast hb_lt
    push_cast at h3
    have h5 : ((b + Q * t : ℕ) : ℝ) = (b : ℝ) + (Q : ℝ) * (t : ℝ) := by push_cast; ring
    have h6 : (Q : ℝ) * (t : ℝ) ≤ (Q : ℝ) * E := mul_le_mul_of_nonneg_left htE hQposR.le
    have h7 : (v : ℝ) = (u : ℝ) + L := by
      dsimp only [L]
      rw [Nat.cast_sub huv.le]
      ring
    have hNR : ((b + Q * t : ℕ) : ℝ) < (v : ℝ) := by linarith
    exact_mod_cast hNR
  have hNu : u < b + Q * t := by
    have hLnn : 0 ≤ L := Nat.cast_nonneg _
    have : (u : ℝ) < ((b + Q * t : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨hNu, hN_lt_v, hNu_gt⟩

/-- Section 4 (Block Theorem specialized to `H = 1`): assuming `LemTranslateStmt`,
any set `A` with `|A ∩ [0, X]| + 1 ≤ c_* log X log log X` misses at least one integer
`N ∈ [X/2, X]` in `P + A`. -/
theorem thm_block_one (h_trans : LemTranslateStmt) :
    ∃ c_star : ℝ, 0 < c_star ∧
    ∃ X_star : ℕ, ∀ (A : Set ℕ) [DecidablePred (· ∈ A)] (X : ℕ), X_star ≤ X →
      (((Finset.Icc 0 X).filter (· ∈ A)).card : ℝ) + 1 ≤
        c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) →
      ∃ N : ℕ, X / 2 ≤ N ∧ N ≤ X ∧ ∀ p : ℕ, p.Prime → ∀ a ∈ A, N ≠ p + a := by
  obtain ⟨η, hη, X₀, htrans⟩ := h_trans
  obtain ⟨C_M, hCM, X_M, hXM2, hmert⟩ := mertens_totient_upper
  let c_star : ℝ := min 1 (η / (12 * C_M))
  have hc_pos : 0 < c_star := lt_min zero_lt_one (div_pos hη (by positivity))
  have hc_le1 : c_star ≤ 1 := min_le_left _ _
  have hc_eta : 12 * C_M * c_star ≤ η := by
    have h1 : c_star ≤ η / (12 * C_M) := min_le_right _ _
    have h2 : 0 < 12 * C_M := by positivity
    exact (le_div_iff₀' h2).mp h1
  let x_min : ℕ := max (max X₀ X_M) 6
  let X_star : ℕ := max (1801 ^ 5) (Nat.ceil (Real.exp (5 * ((x_min : ℝ) + 1))))
  refine ⟨c_star, hc_pos, X_star, fun A _ X hX hM_bound => ?_⟩
  have hX1801 : 1801 ^ 5 ≤ X := (le_max_left _ _).trans hX
  have hX4 : 4 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXexp : Real.exp (5 * ((x_min : ℝ) + 1)) ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hX))
  set x : ℕ := ⌊(1 / 5 : ℝ) * Real.log (X : ℝ)⌋₊
  have hlogX_ge : 5 * ((x_min : ℝ) + 1) ≤ Real.log (X : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hXexp
    rwa [Real.log_exp] at h
  have hx_ge_min : x_min ≤ x := by
    have h1 : (x_min : ℝ) + 1 ≤ (1 / 5 : ℝ) * Real.log (X : ℝ) := by linarith
    have h2 : (x_min : ℝ) ≤ (1 / 5 : ℝ) * Real.log (X : ℝ) := by linarith
    exact Nat.le_floor h2
  have hx_X0 : X₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx_ge_min
  have hx_XM : X_M ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx_ge_min
  have hx6 : 6 ≤ x := (le_max_right _ _).trans hx_ge_min
  have hx_pos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx_le : (x : ℝ) ≤ (1 / 5 : ℝ) * Real.log (X : ℝ) :=
    Nat.floor_le (by positivity)
  have hlogX_lt : Real.log (X : ℝ) < 5 * ((x : ℝ) + 1) := by
    have h := Nat.lt_floor_add_one ((1 / 5 : ℝ) * Real.log (X : ℝ))
    linarith
  have hlogX_le6x : Real.log (X : ℝ) ≤ 6 * (x : ℝ) := by
    have : (5 : ℝ) ≤ x := by exact_mod_cast (show 5 ≤ x by omega)
    linarith
  have hX_le_exp6x : (X : ℝ) ≤ Real.exp (6 * (x : ℝ)) := by
    calc
      (X : ℝ) = Real.exp (Real.log (X : ℝ)) := (Real.exp_log hXpos).symm
      _ ≤ Real.exp (6 * (x : ℝ)) := Real.exp_le_exp.mpr hlogX_le6x
  set Q : ℕ := primorial x
  have hQpos : 0 < Q := primorial_pos x
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  set M_set : Finset ℕ := (Finset.Icc 0 X).filter (· ∈ A)
  set S₀ : Finset ℤ := M_set.image (fun a : ℕ => -(a : ℤ))
  have hS0_card : S₀.card ≤ M_set.card := Finset.card_image_le
  obtain ⟨r, hrQ, hr_avg⟩ := exists_good_residue Q hQpos S₀
  set S : Finset ℤ := S₀.filter (fun s => Nat.Coprime (((r : ℤ) + s) % (Q : ℤ)).toNat Q)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hloglog_le : Real.log (Real.log (X : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
    have hlogX_pos : 0 < Real.log (X : ℝ) := by
      have : (0 : ℝ) ≤ x_min := Nat.cast_nonneg _
      linarith
    have h1 : Real.log (Real.log (X : ℝ)) ≤ Real.log (6 * (x : ℝ)) :=
      Real.log_le_log hlogX_pos hlogX_le6x
    rw [Real.log_mul (by norm_num) hx_pos.ne'] at h1
    have h2 : Real.log 6 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx6)
    linarith
  have hScard_le : (S.card : ℝ) ≤ η * (x : ℝ) := by
    have havgR : (Q : ℝ) * (S.card : ℝ) ≤ (S₀.card : ℝ) * (Q.totient : ℝ) := by
      exact_mod_cast hr_avg
    have hdiv : (S.card : ℝ) ≤ (S₀.card : ℝ) * ((Q.totient : ℝ) / (Q : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hQposR]
      linarith
    have hm := hmert x hx_XM
    have hS0_le : (S₀.card : ℝ) ≤ (M_set.card : ℝ) := by exact_mod_cast hS0_card
    have hM_le : (M_set.card : ℝ) ≤ c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) := by
      linarith
    have htot_nn : 0 ≤ (Q.totient : ℝ) / (Q : ℝ) := by positivity
    have h1 : (S.card : ℝ) ≤ (M_set.card : ℝ) * (C_M / Real.log (x : ℝ)) :=
      hdiv.trans ((mul_le_mul_of_nonneg_right hS0_le htot_nn).trans
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)))
    have h2 : (M_set.card : ℝ) ≤ c_star * (6 * (x : ℝ)) * (2 * Real.log (x : ℝ)) := by
      have hlogX_nn : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
      have hloglog_nn : 0 ≤ Real.log (Real.log (X : ℝ)) :=
        Real.log_nonneg (by have : (0 : ℝ) ≤ x_min := Nat.cast_nonneg _; linarith)
      calc
        (M_set.card : ℝ) ≤ c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) := hM_le
        _ ≤ c_star * (6 * (x : ℝ)) * (2 * Real.log (x : ℝ)) := by
            have hA := mul_le_mul_of_nonneg_left hlogX_le6x hc_pos.le
            exact mul_le_mul hA hloglog_le hloglog_nn (by positivity)
    calc
      (S.card : ℝ) ≤ (M_set.card : ℝ) * (C_M / Real.log (x : ℝ)) := h1
      _ ≤ (c_star * (6 * (x : ℝ)) * (2 * Real.log (x : ℝ))) * (C_M / Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (12 * C_M * c_star) * (x : ℝ) := by
          field_simp [hlogx_pos.ne']
          ring
      _ ≤ η * (x : ℝ) := mul_le_mul_of_nonneg_right hc_eta hx_pos.le
  have hS_bound : ∀ s ∈ S, (s.natAbs : ℝ) ≤ Real.exp (6 * (x : ℝ)) := by
    intro s hs
    have hs0 : s ∈ S₀ := (Finset.mem_filter.mp hs).1
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs0
    have haX : a ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have habs : (-(a : ℤ)).natAbs = a := by simp
    rw [habs]
    exact (by exact_mod_cast haX : (a : ℝ) ≤ X).trans hX_le_exp6x
  obtain ⟨u, v, huX, huv, hvX, hdisj, hgap⟩ := exists_empty_gap A X hX4
  set L : ℝ := ((v - u : ℕ) : ℝ)
  have hL_lower : (X : ℝ) / (3 * (Real.log (X : ℝ)) ^ 2) ≤ L := by
    have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by
      have : (0 : ℝ) ≤ x_min := Nat.cast_nonneg _
      linarith
    have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
    have hloglog_le_log : Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hlogX_pos]
    have hM1_le : ((M_set.card : ℝ) + 1) ≤ (Real.log (X : ℝ)) ^ 2 := by
      calc
        (M_set.card : ℝ) + 1 ≤ c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) := hM_bound
        _ ≤ 1 * Real.log (X : ℝ) * Real.log (X : ℝ) := by
            have h1 : c_star * Real.log (X : ℝ) ≤ 1 * Real.log (X : ℝ) :=
              mul_le_mul_of_nonneg_right hc_le1 hlogX_pos.le
            have h2 : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hlogX_ge1
            exact mul_le_mul h1 hloglog_le_log h2 (by positivity)
        _ = (Real.log (X : ℝ)) ^ 2 := by ring
    have hgapR : ((X / 2 : ℕ) : ℝ) ≤ ((M_set.card : ℝ) + 1) * L := by
      have h := (by exact_mod_cast hgap : ((X / 2 : ℕ) : ℝ) ≤ (((M_set.card + 1) * (v - u) : ℕ) : ℝ))
      simpa [L, Nat.cast_mul, Nat.cast_add] using h
    have hX3 : (X : ℝ) / 3 ≤ ((X / 2 : ℕ) : ℝ) := by
      have h1 : X ≤ 2 * (X / 2) + 1 := by omega
      have h2 : (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
      have h3 : (4 : ℝ) ≤ X := by exact_mod_cast hX4
      linarith
    have hLnn : 0 ≤ L := Nat.cast_nonneg _
    have hmul : (X : ℝ) / 3 ≤ (Real.log (X : ℝ)) ^ 2 * L :=
      hX3.trans (hgapR.trans (mul_le_mul_of_nonneg_right hM1_le hLnn))
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hgrowth : 18 * (Real.log (X : ℝ)) ^ 2 < (X : ℝ) ^ (2 / 5 : ℝ) :=
    log_sq_lt_rpow_two_fifths X hX1801
  have hexp3x_le : Real.exp (3 * (x : ℝ)) ≤ (X : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      Real.exp (3 * (x : ℝ)) ≤ Real.exp ((3 / 5 : ℝ) * Real.log (X : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (X : ℝ) ^ (3 / 5 : ℝ) := by
        rw [Real.rpow_def_of_pos hXpos, mul_comm]
  have hQ_le : (Q : ℝ) ≤ Real.exp (2 * (x : ℝ)) := primorial_le_exp_two_mul x
  have hQex_le : (Q : ℝ) * Real.exp (x : ℝ) ≤ Real.exp (3 * (x : ℝ)) := by
    calc
      (Q : ℝ) * Real.exp (x : ℝ) ≤ Real.exp (2 * (x : ℝ)) * Real.exp (x : ℝ) :=
        mul_le_mul_of_nonneg_right hQ_le (Real.exp_pos _).le
      _ = Real.exp (3 * (x : ℝ)) := by rw [← Real.exp_add]; ring_nf
  have hroom : 2 * (X : ℝ) ^ (3 / 5 : ℝ) < L / 3 := by
    have hlogX_pos : 0 < Real.log (X : ℝ) := by
      have : (0 : ℝ) ≤ x_min := Nat.cast_nonneg _
      linarith
    have hsplit : (X : ℝ) = (X : ℝ) ^ (3 / 5 : ℝ) * (X : ℝ) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      norm_num
    have h1 : 2 * (X : ℝ) ^ (3 / 5 : ℝ) < (X : ℝ) / (9 * (Real.log (X : ℝ)) ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      have h35pos : 0 < (X : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hXpos _
      calc
        2 * (X : ℝ) ^ (3 / 5 : ℝ) * (9 * (Real.log (X : ℝ)) ^ 2)
            = (X : ℝ) ^ (3 / 5 : ℝ) * (18 * (Real.log (X : ℝ)) ^ 2) := by ring
        _ < (X : ℝ) ^ (3 / 5 : ℝ) * (X : ℝ) ^ (2 / 5 : ℝ) :=
            mul_lt_mul_of_pos_left hgrowth h35pos
        _ = (X : ℝ) := hsplit.symm
    have hdiv3 : (X : ℝ) / (9 * (Real.log (X : ℝ)) ^ 2) =
        ((X : ℝ) / (3 * (Real.log (X : ℝ)) ^ 2)) / 3 := by ring
    linarith
  have hexpx_le3 : Real.exp (x : ℝ) ≤ Real.exp (3 * (x : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hQ_le3 : (Q : ℝ) ≤ Real.exp (3 * (x : ℝ)) :=
    hQ_le.trans (Real.exp_le_exp.mpr (by linarith))
  have hexpx_lt_L3 : Real.exp (x : ℝ) < L / 3 := by linarith
  have hQ_lt_L3 : (Q : ℝ) < L / 3 := by linarith
  have h1_lt_exp : (1 : ℝ) ≤ Real.exp (x : ℝ) := Real.one_le_exp hx_pos.le
  have hroom2 : (1 : ℝ) + (Q : ℝ) + (Q : ℝ) * Real.exp (x : ℝ) < 2 * L / 3 := by linarith
  -- Choose baseline `b : ℕ` with `b ≡ r [MOD Q]` and `u + (v - u)/3 + 1 ≤ b < u + (v - u)/3 + 1 + Q`
  let target : ℕ := u + (v - u) / 3 + 1
  have hr_lt_target : r < target := by
    have hQ_lt_L3' : (Q : ℝ) < ((v - u : ℕ) : ℝ) / 3 := hQ_lt_L3
    have hQ_le_div3 : Q ≤ (v - u) / 3 := by
      have h1 : 3 * (Q : ℝ) < ((v - u : ℕ) : ℝ) := by linarith
      have h2 : 3 * Q < v - u := by exact_mod_cast h1
      omega
    omega
  let q_nat : ℕ := (target - r + Q - 1) / Q
  let b : ℕ := r + Q * q_nat
  have hb_ge : target ≤ b := by
    have hdiv : target - r + Q - 1 < Q * (q_nat + 1) := by
      have h := Nat.lt_mul_div_succ (target - r + Q - 1) hQpos
      simpa [q_nat, mul_comm] using h
    have hmul : Q * (q_nat + 1) = Q * q_nat + Q := by ring
    omega
  have hb_lt : b < target + Q := by
    have hdiv : Q * q_nat ≤ target - r + Q - 1 := by
      have h := Nat.div_mul_le_self (target - r + Q - 1) Q
      simpa [q_nat, mul_comm] using h
    omega
  -- Obtain translate `t : ℕ`
  have ht_exists : ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp (x : ℝ) ∧
      ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ Real.exp (x : ℝ) ∧
        (p : ℤ) ∣ (b : ℤ) + (Q : ℤ) * (t : ℤ) + s := by
    by_cases hSne : S.Nonempty
    · exact htrans x hx_X0 S (b : ℤ) hSne hScard_le hS_bound
    · rw [Finset.not_nonempty_iff_eq_empty] at hSne
      refine ⟨1, le_refl 1, by simp [h1_lt_exp], fun s hs => by simp [hSne] at hs⟩
  obtain ⟨t, ht1, ht_le, ht_cov⟩ := ht_exists
  obtain ⟨hNu, hN_lt_v, hNu_gt⟩ :=
    translate_interval_bounds huv hQpos ht1 ht_le hb_ge hb_lt hroom2
  let N : ℕ := b + Q * t
  refine ⟨N, by omega, by omega, fun p hp a ha hNpa => ?_⟩
  rcases hdisj a ha with hau | hva
  · -- Case `a ≤ u`: `N - a = p > L/3`, yet some prime `q ≤ exp x < L/3` divides `p`
    have haM : a ∈ M_set := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ha⟩
    have hsa : -(a : ℤ) ∈ S₀ := Finset.mem_image.mpr ⟨a, haM, rfl⟩
    have hp_gt : L / 3 < (p : ℝ) := by
      have h1 : (p : ℝ) = (N : ℝ) - (a : ℝ) := by
        have h' : (N : ℝ) = (p : ℝ) + (a : ℝ) := by exact_mod_cast hNpa
        linarith
      have h2 : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast hau
      linarith only [hNu_gt, h1, h2]
    have hq_exists : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ Real.exp (x : ℝ) ∧ (q : ℤ) ∣ (p : ℤ) := by
      by_cases hsS : -(a : ℤ) ∈ S
      · obtain ⟨q, hq, hqle, hqdvd⟩ := ht_cov (-(a : ℤ)) hsS
        have heq : (b : ℤ) + (Q : ℤ) * (t : ℤ) + -(a : ℤ) = (p : ℤ) := by
          have : (N : ℤ) = (p : ℤ) + (a : ℤ) := by exact_mod_cast hNpa
          have hNdef : (N : ℤ) = (b : ℤ) + (Q : ℤ) * (t : ℤ) := by dsimp only [N]; push_cast; ring
          omega
        rw [heq] at hqdvd
        exact ⟨q, hq, hqle, hqdvd⟩
      · have hnc : ¬ Nat.Coprime (((r : ℤ) + -(a : ℤ)) % (Q : ℤ)).toNat Q := by
          intro hcop
          exact hsS (Finset.mem_filter.mpr ⟨hsa, hcop⟩)
        rw [coprime_emod_iff_no_prime_dvd _ hQpos] at hnc
        push Not at hnc
        obtain ⟨q, hq, hqQ, hqra⟩ := hnc
        have hqx : q ≤ x := prime_le_of_dvd_primorial hq hqQ
        have hqle : (q : ℝ) ≤ Real.exp (x : ℝ) := by
          have h1 : (q : ℝ) ≤ (x : ℝ) := by exact_mod_cast hqx
          linarith [Real.add_one_le_exp (x : ℝ)]
        have hqQZ : (q : ℤ) ∣ (Q : ℤ) := Int.ofNat_dvd.mpr hqQ
        have hNr : (Q : ℤ) ∣ (N : ℤ) - (r : ℤ) := by
          have : (N : ℤ) - (r : ℤ) = (Q : ℤ) * ((q_nat : ℤ) + (t : ℤ)) := by
            dsimp only [N, b]; push_cast; ring
          exact ⟨(q_nat : ℤ) + (t : ℤ), this⟩
        have hqp : (q : ℤ) ∣ (p : ℤ) := by
          have hp_eq : (p : ℤ) = ((N : ℤ) - (r : ℤ)) + ((r : ℤ) + -(a : ℤ)) := by
            have : (N : ℤ) = (p : ℤ) + (a : ℤ) := by exact_mod_cast hNpa
            omega
          rw [hp_eq]
          exact dvd_add (hqQZ.trans hNr) hqra
        exact ⟨q, hq, hqle, hqp⟩
    obtain ⟨q, hq, hqle, hqpZ⟩ := hq_exists
    have hqp : q ∣ p := Int.ofNat_dvd.mp hqpZ
    rcases (Nat.dvd_prime hp).mp hqp with h1 | rfl
    · exact hq.ne_one h1
    · linarith only [hp_gt, hqle, hexpx_lt_L3]
  · -- Case `v ≤ a`: contradicts `N = p + a < v`
    omega

/- ### Section E: Section 5 Disproof of `Erdos32.erdos_32.variants.log_bound` -/

lemma card_Icc_zero_le (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    ((Finset.Icc 0 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (· ∈ A)).card + 1 := by
  have hs : (Finset.Icc 0 N).filter (· ∈ A) ⊆ insert 0 ((Finset.Icc 1 N).filter (· ∈ A)) := by
    intro a ha
    obtain ⟨hi, ha⟩ := Finset.mem_filter.mp ha
    have hN := (Finset.mem_Icc.mp hi).2
    rcases Nat.eq_zero_or_pos a with rfl | hp
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp, hN⟩, ha⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- Disproof of `Erdos32.erdos_32.variants.log_bound` assuming `LemTranslateStmt`. -/
theorem disproof_of_lem_translate (h_trans : LemTranslateStmt) :
    ¬ (type_of% @Erdos32.erdos_32.variants.log_bound) := by
  classical
  rintro ⟨A, hA, hO⟩
  obtain ⟨c_star, hc_pos, X_star, hblock⟩ := thm_block_one h_trans
  rw [Erdos32.IsAdditiveComplementToPrimes, eventually_atTop] at hA
  obtain ⟨n₀, hn₀⟩ := hA
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [eventually_atTop] at hC
  obtain ⟨N₁, hN₁⟩ := hC
  let C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let K : ℝ := (C' + 2) / c_star
  let X : ℕ := max (max X_star (max (2 * n₀ + 1) N₁))
    (max 3 (Nat.ceil (Real.exp (Real.exp K))))
  have hX_star : X_star ≤ X := (le_max_left _ _).trans (le_max_left _ _)
  have hX_n0 : 2 * n₀ + 1 ≤ X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hX_N1 : N₁ ≤ X :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hX_3 : 3 ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hX_exp : Real.exp (Real.exp K) ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)))
  have hlogX_ge_expK : Real.exp K ≤ Real.log (X : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hX_exp
    rwa [Real.log_exp] at h
  have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by
    have h3 : (3 : ℝ) ≤ X := by exact_mod_cast hX_3
    have hle : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) (hle.trans h3)
    rwa [Real.log_exp] at this
  have hloglogX_ge : K ≤ Real.log (Real.log (X : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos K) hlogX_ge_expK
    rwa [Real.log_exp] at h
  have hcard1 : (((Finset.Icc 1 X).filter (· ∈ A)).card : ℝ) ≤ C' * Real.log (X : ℝ) := by
    have h := hN₁ X hX_N1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (((Finset.Icc 1 X).filter (· ∈ A)).card)),
      abs_of_nonneg (Real.log_natCast_nonneg X)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (by linarith))
  have hcard0 : (((Finset.Icc 0 X).filter (· ∈ A)).card : ℝ) + 1 ≤
      c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) := by
    have h0 : (((Finset.Icc 0 X).filter (· ∈ A)).card : ℝ) ≤
        (((Finset.Icc 1 X).filter (· ∈ A)).card : ℝ) + 1 := by
      exact_mod_cast card_Icc_zero_le A X
    have h1 : (((Finset.Icc 0 X).filter (· ∈ A)).card : ℝ) + 1 ≤ (C' + 2) * Real.log (X : ℝ) := by
      linarith
    have h2 : C' + 2 ≤ c_star * Real.log (Real.log (X : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hloglogX_ge hc_pos.le
      dsimp only [K] at h
      rwa [mul_div_cancel₀ _ hc_pos.ne'] at h
    calc
      (((Finset.Icc 0 X).filter (· ∈ A)).card : ℝ) + 1 ≤ (C' + 2) * Real.log (X : ℝ) := h1
      _ ≤ (c_star * Real.log (Real.log (X : ℝ))) * Real.log (X : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = c_star * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) := by ring
  obtain ⟨N, hNX_half, _, hN_miss⟩ := hblock A X hX_star hcard0
  have hn0N : n₀ ≤ N := by omega
  obtain ⟨p, hp, a, ha, hNpa⟩ := hn₀ N hn0N
  exact hN_miss p hp a ha hNpa

end OMA32Rad

theorem OMA.disproof : ¬ (type_of% @Erdos32.erdos_32.variants.log_bound) :=
  OMA32Rad.disproof_of_lem_translate OMA32Rad2.lem_translate
