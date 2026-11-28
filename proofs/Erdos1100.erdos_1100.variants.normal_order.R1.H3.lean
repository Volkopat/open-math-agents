import OMAReductions.R_Erdos1100_erdos_1100_variants_normal_order_R1
import Mathlib

/-!
Proof of hypothesis H3 of reduction `Erdos1100.erdos_1100.variants.normal_order.R1`
(Erdős–Tenenbaum 1983, weighted middle-divisor sum).
-/

-- Step Erdos1100.erdos_1100.variants.normal_order.R1.H3:
-- hypothesis H3 of reduction Erdos1100.erdos_1100.variants.normal_order.R1
-- Credit: @yhay81
-- Mertens first/second telescoping boilerplate adapted from Erdos1100...R1.H4
-- (crediting @marcusbuffett and @senamakel).

namespace OMA.Erdos1100H3

open Filter Finset Real
open scoped Classical BigOperators Topology

/- ### Part 1: Mertens First & Second Difference Bound -/

private lemma log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

private lemma real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

private lemma log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

private lemma log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith

private lemma summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

private lemma sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private noncomputable def primePowerConst : ℝ :=
  ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

private lemma sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

private lemma sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

private lemma abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 : 0 ≤ primePowerConst := by simpa using sum_log_div_mul_sub_one_le ∅
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

private lemma mertens1Const_nonneg : 0 ≤ mertens1Const :=
  (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)

private lemma sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

private lemma recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp

private lemma abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

private noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

private lemma mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N
  set b := Real.log ((N + 1 : ℕ) : ℝ)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

private lemma mertensG_diff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const + 1) * (1 / Real.log m - 1 / Real.log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n + 1) - mertensG m|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG m)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG m| := abs_add_le _ _
      _ ≤ (mertens1Const + 1) * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) +
          (mertens1Const + 1) * (1 / Real.log m - 1 / Real.log n) :=
          add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = (mertens1Const + 1) * (1 / Real.log m - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by ring

/- ### Part 2: Smooth Log Helper `L` and Mertens Interval Difference -/

private noncomputable def L (x : ℕ) : ℝ := Real.log (max (x : ℝ) 3)

private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h := Real.log_lt_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at h

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have he : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) < 4 := by
      rw [← Real.exp_add]
      norm_num
      linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have h := Real.log_lt_log (Real.exp_pos (1 / 2 : ℝ)) he
  rw [Real.log_exp] at h
  linarith

private lemma log_two_lt_one : Real.log 2 < 1 := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := Real.log_lt_log (by norm_num) he
  rwa [Real.log_exp] at h

private lemma one_lt_L (x : ℕ) : 1 < L x := by
  unfold L
  exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) (le_max_right _ _))

private lemma L_pos (x : ℕ) : 0 < L x := by linarith [one_lt_L x]

private lemma L_mono : Monotone L := by
  intro a b hab
  unfold L
  apply Real.log_le_log (by positivity)
  exact max_le_max_right 3 (by exact_mod_cast hab)

private lemma L_eq_log {x : ℕ} (hx : 3 ≤ x) : L x = Real.log x := by
  unfold L
  have hx' : (3 : ℝ) ≤ x := by exact_mod_cast hx
  rw [max_eq_left hx']

private lemma L_pow_two_ge (k : ℕ) : ((k + 1 : ℕ) : ℝ) / 3 ≤ L (2 ^ k) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · have := one_lt_L 1; push_cast; linarith
    · have := one_lt_L 2; push_cast; linarith
  · have h2 : Real.log ((2 : ℝ) ^ k) ≤ L (2 ^ k) := by
      unfold L
      apply Real.log_le_log (by positivity)
      exact_mod_cast le_max_left ((2 ^ k : ℕ) : ℝ) 3
    rw [Real.log_pow] at h2
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hlog2 := half_le_log_two
    push_cast
    nlinarith

private noncomputable def mertensDiffConst : ℝ :=
  |mertensG 2| + (3 * mertens1Const + 1) / Real.log 2 + Real.log (Real.log 3) + 1

private lemma mertensDiffConst_nonneg : 0 ≤ mertensDiffConst := by
  unfold mertensDiffConst
  have h1 : 0 ≤ Real.log (Real.log 3) := Real.log_nonneg one_lt_log_three.le
  have h2 : 0 ≤ mertens1Const := mertens1Const_nonneg
  have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

private lemma mertens_prime_inv_diff (z X : ℕ) (hzX : z ≤ X) :
    ∑ p ∈ (Nat.primesLE X).filter (z ≤ ·), (1 : ℝ) / p ≤
      Real.log (L X / L z) + mertensDiffConst := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC1 : 0 ≤ mertens1Const := mertens1Const_nonneg
  have hlog3pos : 0 < Real.log 3 := by linarith [one_lt_log_three]
  have hloglog3 : 0 ≤ Real.log (Real.log 3) := Real.log_nonneg one_lt_log_three.le
  by_cases hX3 : X < 3
  · have hz3 : z < 3 := by omega
    have hLX : L X = Real.log 3 := by
      unfold L; rw [max_eq_right (by exact_mod_cast (by omega : X ≤ 3))]
    have hLz : L z = Real.log 3 := by
      unfold L; rw [max_eq_right (by exact_mod_cast (by omega : z ≤ 3))]
    rw [hLX, hLz, div_self hlog3pos.ne', Real.log_one, zero_add]
    have hsub : (Nat.primesLE X).filter (z ≤ ·) ⊆ Nat.primesLE 2 := by
      intro p hp
      have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact Nat.mem_primesLE.mpr ⟨by omega, hp'.2⟩
    have hsum2 : ∑ p ∈ Nat.primesLE 2, (1 : ℝ) / p = 1 / 2 := by
      have heq : Nat.primesLE 2 = {2} := by decide
      rw [heq]; simp
    have hle : ∑ p ∈ (Nat.primesLE X).filter (z ≤ ·), (1 : ℝ) / p ≤ 1 / 2 := by
      rw [← hsum2]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hCM : (1 : ℝ) ≤ mertensDiffConst := by
      unfold mertensDiffConst
      have : 0 ≤ (3 * mertens1Const + 1) / Real.log 2 := by positivity
      linarith [abs_nonneg (mertensG 2)]
    linarith
  push Not at hX3
  have hLX : L X = Real.log X := L_eq_log hX3
  have hlogX_ge : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ X))
  have hlogX_pos : 0 < Real.log X := lt_of_lt_of_le hlog2 hlogX_ge
  have hRX : |(∑ p ∈ Nat.primesLE X, Real.log p / p - Real.log X) / Real.log X| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogX_pos]
    calc |∑ p ∈ Nat.primesLE X, Real.log p / p - Real.log X| / Real.log X
        ≤ mertens1Const / Real.log X :=
          div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat X) hlogX_pos.le
      _ ≤ mertens1Const / Real.log 2 :=
          div_le_div_of_nonneg_left hC1 hlog2 hlogX_ge
  by_cases hz3 : z < 3
  · have hLz : L z = Real.log 3 := by
      unfold L; rw [max_eq_right (by exact_mod_cast (by omega : z ≤ 3))]
    have hle1 : ∑ p ∈ (Nat.primesLE X).filter (z ≤ ·), (1 : ℝ) / p ≤
        ∑ p ∈ Nat.primesLE X, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    have hGX : ∑ p ∈ Nat.primesLE X, (1 : ℝ) / p =
        Real.log (Real.log X) + mertensG 2 + (mertensG X - mertensG 2) +
        (∑ p ∈ Nat.primesLE X, Real.log p / p - Real.log X) / Real.log X := by
      unfold mertensG; ring
    have hGd : |mertensG X - mertensG 2| ≤ (mertens1Const + 1) / Real.log 2 := by
      have h := mertensG_diff 2 X le_rfl (by omega)
      have hpos : 0 ≤ 1 / Real.log X := by positivity
      calc |mertensG X - mertensG 2|
          ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log X) := by
            simpa using h
        _ ≤ (mertens1Const + 1) * (1 / Real.log 2) := by nlinarith
        _ = (mertens1Const + 1) / Real.log 2 := by ring
    have hlogdiv : Real.log (L X / L z) = Real.log (Real.log X) - Real.log (Real.log 3) := by
      rw [hLX, hLz, Real.log_div hlogX_pos.ne' hlog3pos.ne']
    have h1 := (abs_le.mp hGd).2
    have h2 := (abs_le.mp hRX).2
    have h3 : mertensG 2 ≤ |mertensG 2| := le_abs_self _
    have hfrac : (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 ≤
        (3 * mertens1Const + 1) / Real.log 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hlog2.le
    unfold mertensDiffConst
    linarith
  · push Not at hz3
    have hLz : L z = Real.log z := L_eq_log hz3
    have hlogz_ge : Real.log 2 ≤ Real.log z :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ z))
    have hlogz_pos : 0 < Real.log z := lt_of_lt_of_le hlog2 hlogz_ge
    have hsub : (Nat.primesLE X).filter (z ≤ ·) ⊆ (Nat.primesLE X \ Nat.primesLE z) ∪ {z} := by
      intro p hp
      obtain ⟨hpX, hpz⟩ := Finset.mem_filter.mp hp
      by_cases hpeq : p = z
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hpeq)
      · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hpX, ?_⟩)
        intro hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
    have hz_not : z ∉ Nat.primesLE X \ Nat.primesLE z := by
      intro hmem
      have h1 := (Finset.mem_sdiff.mp hmem).1
      have h2 := (Finset.mem_sdiff.mp hmem).2
      exact h2 (Nat.mem_primesLE.mpr ⟨le_rfl, (Nat.mem_primesLE.mp h1).2⟩)
    have hle1 : ∑ p ∈ (Nat.primesLE X).filter (z ≤ ·), (1 : ℝ) / p ≤
        (∑ p ∈ Nat.primesLE X \ Nat.primesLE z, (1 : ℝ) / p) + (1 : ℝ) / z := by
      have hsub' : (Nat.primesLE X).filter (z ≤ ·) ⊆ insert z (Nat.primesLE X \ Nat.primesLE z) := by
        intro p hp
        simpa [Finset.union_comm] using hsub hp
      calc ∑ p ∈ (Nat.primesLE X).filter (z ≤ ·), (1 : ℝ) / p
          ≤ ∑ p ∈ insert z (Nat.primesLE X \ Nat.primesLE z), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun _ _ _ => by positivity)
        _ = (1 : ℝ) / z + ∑ p ∈ Nat.primesLE X \ Nat.primesLE z, (1 : ℝ) / p :=
            Finset.sum_insert hz_not
        _ = (∑ p ∈ Nat.primesLE X \ Nat.primesLE z, (1 : ℝ) / p) + (1 : ℝ) / z := add_comm _ _
    have hsdiff : ∑ p ∈ Nat.primesLE X \ Nat.primesLE z, (1 : ℝ) / p =
        (∑ p ∈ Nat.primesLE X, (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE z, (1 : ℝ) / p := by
      have hsubz : Nat.primesLE z ⊆ Nat.primesLE X := by
        intro p hp
        have hp' := Nat.mem_primesLE.mp hp
        exact Nat.mem_primesLE.mpr ⟨hp'.1.trans hzX, hp'.2⟩
      exact Finset.sum_sdiff_eq_sub hsubz
    have hGeq : (∑ p ∈ Nat.primesLE X, (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE z, (1 : ℝ) / p =
        (Real.log (Real.log X) - Real.log (Real.log z)) + (mertensG X - mertensG z) +
        (∑ p ∈ Nat.primesLE X, Real.log p / p - Real.log X) / Real.log X -
        (∑ p ∈ Nat.primesLE z, Real.log p / p - Real.log z) / Real.log z := by
      unfold mertensG; ring
    have hGd : |mertensG X - mertensG z| ≤ (mertens1Const + 1) / Real.log 2 := by
      have h := mertensG_diff z X (by omega) hzX
      have hpos : 0 ≤ 1 / Real.log X := by positivity
      have hle_inv : 1 / Real.log z ≤ 1 / Real.log 2 :=
        one_div_le_one_div_of_le hlog2 hlogz_ge
      calc |mertensG X - mertensG z|
          ≤ (mertens1Const + 1) * (1 / Real.log z - 1 / Real.log X) := h
        _ ≤ (mertens1Const + 1) * (1 / Real.log 2) := by nlinarith
        _ = (mertens1Const + 1) / Real.log 2 := by ring
    have hRz : |(∑ p ∈ Nat.primesLE z, Real.log p / p - Real.log z) / Real.log z| ≤
        mertens1Const / Real.log 2 := by
      rw [abs_div, abs_of_pos hlogz_pos]
      calc |∑ p ∈ Nat.primesLE z, Real.log p / p - Real.log z| / Real.log z
          ≤ mertens1Const / Real.log z :=
            div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat z) hlogz_pos.le
        _ ≤ mertens1Const / Real.log 2 :=
            div_le_div_of_nonneg_left hC1 hlog2 hlogz_ge
    have hinvz : (1 : ℝ) / z ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (by omega : 0 < z))]
      exact_mod_cast (by omega : 1 ≤ z)
    have hlogdiv : Real.log (L X / L z) = Real.log (Real.log X) - Real.log (Real.log z) := by
      rw [hLX, hLz, Real.log_div hlogX_pos.ne' hlogz_pos.ne']
    have h1 := (abs_le.mp hGd).2
    have h2 := (abs_le.mp hRX).2
    have h3 := (abs_le.mp hRz).1
    have hfrac : (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 +
        mertens1Const / Real.log 2 = (3 * mertens1Const + 1) / Real.log 2 := by ring
    unfold mertensDiffConst
    linarith [abs_nonneg (mertensG 2)]

/- ### Part 3: Multiplicative Rough-Number Upper Bound -/

private def IsRough (z r : ℕ) : Prop := ∀ p ∈ r.primeFactors, z ≤ p

private noncomputable def w (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n

private lemma w_pos (n : ℕ) : 0 < w n := by
  unfold w; positivity

private lemma w_nonneg (n : ℕ) : 0 ≤ w n := (w_pos n).le

private lemma w_le_one (n : ℕ) : w n ≤ 1 := by
  unfold w
  exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma w_one : w 1 = 1 := by
  simp [w]

private lemma w_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : w (m * n) = w m * w n := by
  unfold w
  rw [ArithmeticFunction.cardFactors_mul hm hn, pow_add]

private lemma w_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : w (p ^ e) = (1 / 2 : ℝ) ^ e := by
  unfold w
  rw [ArithmeticFunction.cardFactors_apply_prime_pow hp]

private lemma isRough_one (z : ℕ) : IsRough z 1 := by
  intro p hp; simp at hp

private lemma isRough_of_dvd {z a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) (h : IsRough z b) :
    IsRough z a := by
  intro p hp
  exact h p (Nat.primeFactors_mono hab hb hp)

private lemma sum_geom_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ e ∈ Finset.range n, r ^ e ≤ (1 - r)⁻¹ := by
  have h1r : 0 < 1 - r := by linarith
  rw [inv_eq_one_div, le_div_iff₀ h1r]
  have hgeom : (∑ e ∈ Finset.range n, r ^ e) * (1 - r) = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  rw [hgeom]
  have : 0 ≤ r ^ n := pow_nonneg hr0 n
  linarith

private lemma sum_div_le_euler_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    ∑ m ∈ (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ P), w m / (m : ℝ) ≤
      ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ)))⁻¹ := by
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ ∅) ⊆ {1} := by
      intro m hm
      obtain ⟨hmI, hmp⟩ := Finset.mem_filter.mp hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
      have hnil : m.primeFactors = ∅ := Finset.subset_empty.mp hmp
      rw [Finset.mem_singleton]
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have hfac : m.minFac ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩
      rw [hnil] at hfac
      exact Finset.notMem_empty _ hfac
    calc ∑ m ∈ (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ ∅), w m / (m : ℝ)
        ≤ ∑ m ∈ ({1} : Finset ℕ), w m / (m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => div_nonneg (w_nonneg _) (Nat.cast_nonneg _))
      _ = 1 := by simp [w_one]
  | @insert p P hpP ih =>
    have hpPrime : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpP]
    set S_ins := (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ insert p P)
    set S_P := (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ P)
    let f : ℕ → ℕ × ℕ := fun m => (m.factorization p, m / p ^ (m.factorization p))
    have hf_maps : ∀ m ∈ S_ins, f m ∈ Finset.range (X + 1) ×ˢ S_P := by
      intro m hm
      obtain ⟨hmI, hmp⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hmI
      have hm0 : m ≠ 0 := by omega
      set e := m.factorization p
      have hdvd : p ^ e ∣ m := Nat.ordProj_dvd m p
      have hpe_pos : 0 < p ^ e := pow_pos hpPrime.pos e
      have hpe_le : p ^ e ≤ m := Nat.le_of_dvd (by omega) hdvd
      have he_lt : e < X + 1 := by
        have h2e : e < 2 ^ e := Nat.lt_two_pow_self
        have h2p : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hpPrime.two_le e
        omega
      have hm'_pos : 1 ≤ m / p ^ e := Nat.div_pos hpe_le hpe_pos
      have hm'_le : m / p ^ e ≤ X := (Nat.div_le_self m _).trans hmX
      have hm'_dvd : m / p ^ e ∣ m := Nat.div_dvd_of_dvd hdvd
      have hnotp : ¬ p ∣ m / p ^ e := Nat.not_dvd_ordCompl hpPrime hm0
      have hm'_pf : (m / p ^ e).primeFactors ⊆ P := by
        intro q hq
        have hqm : q ∈ m.primeFactors := Nat.primeFactors_mono hm'_dvd hm0 hq
        have hqins := hmp hqm
        rcases Finset.mem_insert.mp hqins with rfl | hqP
        · exact absurd (Nat.dvd_of_mem_primeFactors hq) hnotp
        · exact hqP
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr he_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm'_pos, hm'_le⟩, hm'_pf⟩⟩
    have hf_inj : Set.InjOn f (S_ins : Set ℕ) := by
      intro a ha b hb hab
      have h1 : a.factorization p = b.factorization p := congrArg Prod.fst hab
      have h2 : a / p ^ (a.factorization p) = b / p ^ (b.factorization p) := congrArg Prod.snd hab
      calc a = p ^ (a.factorization p) * (a / p ^ (a.factorization p)) :=
            (Nat.mul_div_cancel' (Nat.ordProj_dvd a p)).symm
        _ = p ^ (b.factorization p) * (b / p ^ (b.factorization p)) := by rw [h2, h1]
        _ = b := Nat.mul_div_cancel' (Nat.ordProj_dvd b p)
    have hf_val : ∀ m ∈ S_ins,
        w m / (m : ℝ) = ((1 / (2 * (p : ℝ))) ^ (f m).1) * (w (f m).2 / ((f m).2 : ℝ)) := by
      intro m hm
      obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
      set e := m.factorization p
      have hdvd : p ^ e ∣ m := Nat.ordProj_dvd m p
      have hpe_pos : 0 < p ^ e := pow_pos hpPrime.pos e
      have hpe_le : p ^ e ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hm'_pos : 0 < m / p ^ e := Nat.div_pos hpe_le hpe_pos
      have hmul : p ^ e * (m / p ^ e) = m := Nat.mul_div_cancel' hdvd
      have hw : w m = (1 / 2 : ℝ) ^ e * w (m / p ^ e) := by
        conv_lhs => rw [← hmul]
        rw [w_mul hpe_pos.ne' hm'_pos.ne', w_prime_pow hpPrime e]
      have hcast : (m : ℝ) = (p : ℝ) ^ e * ((m / p ^ e : ℕ) : ℝ) := by
        exact_mod_cast hmul.symm
      change w m / (m : ℝ) = ((1 / (2 * (p : ℝ))) ^ e) * (w (m / p ^ e) / ((m / p ^ e : ℕ) : ℝ))
      rw [hw, hcast]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      have hm'0 : ((m / p ^ e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm'_pos.ne'
      rw [one_div_pow, one_div_pow, mul_pow]
      field_simp
    have hstep : ∑ m ∈ S_ins, w m / (m : ℝ) ≤
        (∑ e ∈ Finset.range (X + 1), (1 / (2 * (p : ℝ))) ^ e) *
          ∑ m' ∈ S_P, w m' / (m' : ℝ) := by
      calc ∑ m ∈ S_ins, w m / (m : ℝ)
          = ∑ m ∈ S_ins, ((1 / (2 * (p : ℝ))) ^ (f m).1) * (w (f m).2 / ((f m).2 : ℝ)) :=
            Finset.sum_congr rfl hf_val
        _ = ∑ x ∈ S_ins.image f, ((1 / (2 * (p : ℝ))) ^ x.1) * (w x.2 / (x.2 : ℝ)) := by
            rw [Finset.sum_image (fun a ha b hb h => hf_inj ha hb h)]
        _ ≤ ∑ x ∈ Finset.range (X + 1) ×ˢ S_P,
              ((1 / (2 * (p : ℝ))) ^ x.1) * (w x.2 / (x.2 : ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
              exact hf_maps m hm
            · intro x _ _
              exact mul_nonneg (by positivity) (div_nonneg (w_nonneg _) (Nat.cast_nonneg _))
        _ = (∑ e ∈ Finset.range (X + 1), (1 / (2 * (p : ℝ))) ^ e) *
              ∑ m' ∈ S_P, w m' / (m' : ℝ) := by
            rw [Finset.sum_product, Finset.sum_mul]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hr0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
    have hr1 : 1 / (2 * (p : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hgeom := sum_geom_le_inv hr0 hr1 (X + 1)
    have hih := ih hP'
    have hnonneg1 : 0 ≤ ∑ m' ∈ S_P, w m' / (m' : ℝ) :=
      Finset.sum_nonneg fun _ _ => div_nonneg (w_nonneg _) (Nat.cast_nonneg _)
    have hnonneg2 : 0 ≤ (1 - 1 / (2 * (p : ℝ)))⁻¹ := by
      exact inv_nonneg.mpr (by linarith)
    exact le_trans hstep (mul_le_mul hgeom hih hnonneg1 hnonneg2)

private lemma sum_inv_sq_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  have htele : ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      push_cast
      have hsub1 : ((k : ℝ) + 1) - 1 = (k : ℝ) := by ring
      rw [hsub1]
      have h1 : (k : ℝ) ≠ 0 := by linarith
      have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
      field_simp
      ring
  set N := max 1 (P.sup id)
  have hsub : P ⊆ Finset.Icc 2 N := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hP p hp, le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)⟩
  calc ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
        have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
        exact div_le_div_of_nonneg_left zero_le_one hden (by nlinarith)
    _ ≤ ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k hk _
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have : 0 < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
        positivity
    _ = 1 - 1 / (N : ℝ) := htele N (le_max_left _ _)
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        linarith

private lemma inv_one_sub_le_exp {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    (1 - u)⁻¹ ≤ Real.exp (u + 2 * u ^ 2) := by
  have h1u : 0 < 1 - u := by linarith
  have hpoly : 1 ≤ (1 + u + 2 * u ^ 2) * (1 - u) := by
    have : (1 + u + 2 * u ^ 2) * (1 - u) - 1 = u ^ 2 * (1 - 2 * u) := by ring
    nlinarith [sq_nonneg u]
  have hinv : (1 - u)⁻¹ ≤ 1 + u + 2 * u ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1u]
    exact hpoly
  have hexp := Real.add_one_le_exp (u + 2 * u ^ 2)
  linarith

private noncomputable def eulerConst : ℝ := Real.exp ((mertensDiffConst + 1) / 2)

private lemma eulerConst_pos : 0 < eulerConst := Real.exp_pos _

private lemma sum_rough_div_le (z X : ℕ) (hzX : z ≤ X) :
    ∑ m ∈ (Finset.Icc 1 X).filter (IsRough z), w m / (m : ℝ) ≤
      eulerConst * Real.sqrt (L X / L z) := by
  set P := (Nat.primesLE X).filter (z ≤ ·)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hsub : (Finset.Icc 1 X).filter (IsRough z) ⊆
      (Finset.Icc 1 X).filter (fun m => m.primeFactors ⊆ P) := by
    intro m hm
    obtain ⟨hmI, hmr⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_filter.mpr ⟨hmI, fun p hp => ?_⟩
    have hmX : m ≤ X := (Finset.mem_Icc.mp hmI).2
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpm : p ≤ m := Nat.le_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpm.trans hmX, hpp⟩, hmr p hp⟩
  have h1 : ∑ m ∈ (Finset.Icc 1 X).filter (IsRough z), w m / (m : ℝ) ≤
      ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ)))⁻¹ :=
    le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => div_nonneg (w_nonneg _) (Nat.cast_nonneg _)))
      (sum_div_le_euler_prod P hP X)
  have h2 : ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ)))⁻¹ ≤
      ∏ p ∈ P, Real.exp ((1 / 2 : ℝ) * (1 / (p : ℝ)) + (1 / 2 : ℝ) * (1 / (p : ℝ) ^ 2)) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      have : 1 / (2 * (p : ℝ)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      have hu0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
      have hu1 : 1 / (2 * (p : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hexp := inv_one_sub_le_exp hu0 hu1
      have heq : 1 / (2 * (p : ℝ)) + 2 * (1 / (2 * (p : ℝ))) ^ 2 =
          (1 / 2 : ℝ) * (1 / (p : ℝ)) + (1 / 2 : ℝ) * (1 / (p : ℝ) ^ 2) := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        field_simp
      rwa [heq] at hexp
  have h3 : ∏ p ∈ P, Real.exp ((1 / 2 : ℝ) * (1 / (p : ℝ)) + (1 / 2 : ℝ) * (1 / (p : ℝ) ^ 2)) =
      Real.exp ((1 / 2 : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) + (1 / 2 : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)) := by
    rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hmert := mertens_prime_inv_diff z X hzX
  have hsq := sum_inv_sq_le_one P (fun p hp => (hP p hp).two_le)
  have h4 : Real.exp ((1 / 2 : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) + (1 / 2 : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log (L X / L z) + (mertensDiffConst + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h5 : Real.exp ((1 / 2 : ℝ) * Real.log (L X / L z) + (mertensDiffConst + 1) / 2) =
      eulerConst * Real.sqrt (L X / L z) := by
    have hq : 0 < L X / L z := div_pos (L_pos X) (L_pos z)
    rw [Real.exp_add, mul_comm, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
    unfold eulerConst
    congr 2
    ring
  linarith

private lemma sum_rough_log_le (z X : ℕ) :
    ∑ r ∈ (Finset.Icc 1 X).filter (IsRough z), w r * Real.log r ≤
      (Real.log 4 + 4) * (X : ℝ) * ∑ m ∈ (Finset.Icc 1 X).filter (IsRough z), w m / (m : ℝ) := by
  set R := (Finset.Icc 1 X).filter (IsRough z)
  have hrewrite : ∑ r ∈ R, w r * Real.log r =
      ∑ r ∈ R, ∑ d ∈ r.divisors, w r * ArithmeticFunction.vonMangoldt d := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  rw [hrewrite]
  let S := R.sigma (fun r => r.divisors)
  let T := R.sigma (fun m => Finset.Icc 1 (X / m))
  let φ : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.1 / x.2, x.2⟩
  have hφ_maps : ∀ x ∈ S, φ x ∈ T := by
    intro x hx
    obtain ⟨hr, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hrI, hrR⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrX⟩ := Finset.mem_Icc.mp hrI
    obtain ⟨hdr, hr0⟩ := Nat.mem_divisors.mp hd
    have hd_pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdr (by omega)
    have hd_le : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) hdr
    have hm_pos : 1 ≤ x.1 / x.2 := Nat.div_pos hd_le hd_pos
    have hm_le : x.1 / x.2 ≤ X := (Nat.div_le_self x.1 x.2).trans hrX
    have hm_dvd : x.1 / x.2 ∣ x.1 := Nat.div_dvd_of_dvd hdr
    have hmR : IsRough z (x.1 / x.2) := isRough_of_dvd hr0 hm_dvd hrR
    have hm_mul : (x.1 / x.2) * x.2 = x.1 := Nat.div_mul_cancel hdr
    have hd_le_div : x.2 ≤ X / (x.1 / x.2) := by
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm, hm_mul]
      exact hrX
    exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hmR⟩,
      Finset.mem_Icc.mpr ⟨hd_pos, hd_le_div⟩⟩
  have hφ_inj : Set.InjOn φ (S : Set (Σ _ : ℕ, ℕ)) := by
    intro a ha b hb hab
    have hda : a.2 ∣ a.1 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp ha).2).1
    have hdb : b.2 ∣ b.1 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hb).2).1
    have h1 : a.1 / a.2 = b.1 / b.2 := congrArg Sigma.fst hab
    have h2 : a.2 = b.2 := by
      have := congrArg Sigma.snd hab
      simpa [φ] using this
    have hfst : a.1 = b.1 := by
      calc a.1 = (a.1 / a.2) * a.2 := (Nat.div_mul_cancel hda).symm
        _ = (b.1 / b.2) * b.2 := by rw [h1, h2]
        _ = b.1 := Nat.div_mul_cancel hdb
    cases a; cases b
    simp only at hfst h2
    subst hfst; subst h2; rfl
  have hstep1 : ∑ r ∈ R, ∑ d ∈ r.divisors, w r * ArithmeticFunction.vonMangoldt d ≤
      ∑ m ∈ R, ∑ d ∈ Finset.Icc 1 (X / m), w m * ArithmeticFunction.vonMangoldt d := by
    have hL : ∑ x ∈ S, w x.1 * ArithmeticFunction.vonMangoldt x.2 =
        ∑ r ∈ R, ∑ d ∈ r.divisors, w r * ArithmeticFunction.vonMangoldt d := by
      simp only [S, Finset.sum_sigma]
    have hR : ∑ y ∈ T, w y.1 * ArithmeticFunction.vonMangoldt y.2 =
        ∑ m ∈ R, ∑ d ∈ Finset.Icc 1 (X / m), w m * ArithmeticFunction.vonMangoldt d := by
      simp only [T, Finset.sum_sigma]
    rw [← hL, ← hR]
    calc ∑ x ∈ S, w x.1 * ArithmeticFunction.vonMangoldt x.2
        ≤ ∑ x ∈ S, w (φ x).1 * ArithmeticFunction.vonMangoldt (φ x).2 := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨hr, hd⟩ := Finset.mem_sigma.mp hx
          have hr1 : 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
          obtain ⟨hdr, _⟩ := Nat.mem_divisors.mp hd
          have hd_pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdr (by omega)
          have hm_pos : 0 < x.1 / x.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hdr) hd_pos
          have hw_le : w x.1 ≤ w (x.1 / x.2) := by
            have hmul : (x.1 / x.2) * x.2 = x.1 := Nat.div_mul_cancel hdr
            conv_lhs => rw [← hmul]
            rw [w_mul hm_pos.ne' hd_pos.ne']
            exact mul_le_of_le_one_right (w_nonneg _) (w_le_one _)
          exact mul_le_mul_of_nonneg_right hw_le ArithmeticFunction.vonMangoldt_nonneg
      _ = ∑ y ∈ S.image φ, w y.1 * ArithmeticFunction.vonMangoldt y.2 :=
          (Finset.sum_image (f := fun y : Σ _ : ℕ, ℕ => w y.1 * ArithmeticFunction.vonMangoldt y.2)
            (fun a ha b hb h => hφ_inj ha hb h)).symm
      _ ≤ ∑ y ∈ T, w y.1 * ArithmeticFunction.vonMangoldt y.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
            exact hφ_maps x hx
          · intro y _ _
            exact mul_nonneg (w_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  calc ∑ r ∈ R, ∑ d ∈ r.divisors, w r * ArithmeticFunction.vonMangoldt d
      ≤ ∑ m ∈ R, ∑ d ∈ Finset.Icc 1 (X / m), w m * ArithmeticFunction.vonMangoldt d := hstep1
    _ = ∑ m ∈ R, w m * Chebyshev.psi ((X / m : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.mul_sum, Chebyshev.psi, Nat.floor_natCast]
        congr 1
    _ ≤ ∑ m ∈ R, w m * ((Real.log 4 + 4) * ((X / m : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m _
        exact mul_le_mul_of_nonneg_left
          (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)) (w_nonneg _)
    _ ≤ ∑ m ∈ R, w m * ((Real.log 4 + 4) * ((X : ℝ) / (m : ℝ))) := by
        apply Finset.sum_le_sum
        intro m _
        have hc : 0 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left Nat.cast_div_le hc) (w_nonneg _)
    _ = (Real.log 4 + 4) * (X : ℝ) * ∑ m ∈ R, w m / (m : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring

private noncomputable def roughConst : ℝ := (10 + 2 * Real.log 4) * eulerConst

private lemma roughConst_pos : 0 < roughConst := by
  unfold roughConst
  have h1 : 0 < 10 + 2 * Real.log 4 := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  exact mul_pos h1 eulerConst_pos

private lemma sum_half_omega_rough_le (z X : ℕ) (hzX : z ≤ X) :
    ∑ r ∈ (Finset.Icc 1 X).filter (IsRough z), w r ≤
      roughConst * (X : ℝ) / (Real.sqrt (L X) * Real.sqrt (L z)) := by
  set R := (Finset.Icc 1 X).filter (IsRough z)
  by_cases hX4 : X < 4
  · have hsum_le : ∑ r ∈ R, w r ≤ (X : ℝ) := by
      calc ∑ r ∈ R, w r
          ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum fun r _ => w_le_one r
        _ = (R.card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 X).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = (X : ℝ) := by simp [Nat.card_Icc]
    have hLX : L X ≤ 2 := by
      unfold L
      have hmax : max (X : ℝ) 3 ≤ 3 := max_le (by exact_mod_cast (by omega : X ≤ 3)) le_rfl
      have h1 : Real.log (max (X : ℝ) 3) ≤ Real.log 3 := Real.log_le_log (by positivity) hmax
      have h2 : (3 : ℝ) < Real.exp 2 := by
        have hgt := Real.exp_one_gt_d9
        have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have h3 := Real.log_lt_log (by norm_num) h2
      rw [Real.log_exp] at h3
      linarith
    have hLz : L z ≤ 2 := le_trans (L_mono hzX) hLX
    have hprod : Real.sqrt (L X) * Real.sqrt (L z) ≤ 2 := by
      have h1 : Real.sqrt (L X) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hLX
      have h2 : Real.sqrt (L z) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hLz
      have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg (L X), Real.sqrt_nonneg (L z)]
    have hC2 : (2 : ℝ) ≤ roughConst := by
      unfold roughConst eulerConst
      have he1 : 1 ≤ Real.exp ((mertensDiffConst + 1) / 2) :=
        Real.one_le_exp (by linarith [mertensDiffConst_nonneg])
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith
    have hden_pos : 0 < Real.sqrt (L X) * Real.sqrt (L z) :=
      mul_pos (Real.sqrt_pos.mpr (L_pos X)) (Real.sqrt_pos.mpr (L_pos z))
    rw [le_div_iff₀ hden_pos]
    nlinarith [Nat.cast_nonneg (α := ℝ) X]
  push Not at hX4
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hLX : L X = Real.log X := L_eq_log (by omega)
  have hlogX_pos : 0 < Real.log X := by rw [← hLX]; exact L_pos X
  set R1 := R.filter (fun r => r * r ≤ X)
  set R2 := R.filter (fun r => ¬ r * r ≤ X)
  have hsplit : ∑ r ∈ R, w r = (∑ r ∈ R1, w r) + ∑ r ∈ R2, w r :=
    (Finset.sum_filter_add_sum_filter_not R (fun r => r * r ≤ X) w).symm
  have h1mem : 1 ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, isRough_one z⟩
  have hone_le_sum : (1 : ℝ) ≤ ∑ m ∈ R, w m / (m : ℝ) := by
    have h := Finset.single_le_sum (f := fun m => w m / (m : ℝ))
      (fun _ _ => div_nonneg (w_nonneg _) (Nat.cast_nonneg _)) h1mem
    simpa [w_one] using h
  have hR1 : Real.log X * ∑ r ∈ R1, w r ≤ 2 * (X : ℝ) * ∑ m ∈ R, w m / (m : ℝ) := by
    have hsub1 : R1 ⊆ Finset.Icc 1 (Nat.sqrt X) := by
      intro r hr
      obtain ⟨hrR, hrsq⟩ := Finset.mem_filter.mp hr
      have hr1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrR).1).1
      exact Finset.mem_Icc.mpr ⟨hr1, Nat.le_sqrt.mpr hrsq⟩
    have hcard1 : ∑ r ∈ R1, w r ≤ Real.sqrt X := by
      calc ∑ r ∈ R1, w r
          ≤ ∑ _r ∈ R1, (1 : ℝ) := Finset.sum_le_sum fun r _ => w_le_one r
        _ = (R1.card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 (Nat.sqrt X)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub1
        _ = (Nat.sqrt X : ℝ) := by simp [Nat.card_Icc]
        _ ≤ Real.sqrt X := by
            apply Real.le_sqrt_of_sq_le
            rw [sq]
            exact_mod_cast Nat.sqrt_le X
    have hlog_le : Real.log X ≤ 2 * Real.sqrt X := by
      have h := Real.log_le_rpow_div (x := (X : ℝ)) hXpos.le (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have hprod_le : Real.log X * Real.sqrt X ≤ 2 * (X : ℝ) := by
      have hsq : Real.sqrt X * Real.sqrt X = (X : ℝ) := Real.mul_self_sqrt hXpos.le
      nlinarith [Real.sqrt_nonneg (X : ℝ)]
    calc Real.log X * ∑ r ∈ R1, w r
        ≤ Real.log X * Real.sqrt X := mul_le_mul_of_nonneg_left hcard1 hlogX_pos.le
      _ ≤ 2 * (X : ℝ) := hprod_le
      _ ≤ 2 * (X : ℝ) * ∑ m ∈ R, w m / (m : ℝ) := by nlinarith
  have hR2 : Real.log X * ∑ r ∈ R2, w r ≤
      2 * (Real.log 4 + 4) * (X : ℝ) * ∑ m ∈ R, w m / (m : ℝ) := by
    have hstep : Real.log X * ∑ r ∈ R2, w r ≤ 2 * ∑ r ∈ R, w r * Real.log r := by
      rw [Finset.mul_sum, Finset.mul_sum]
      calc ∑ r ∈ R2, Real.log X * w r
          ≤ ∑ r ∈ R2, 2 * (w r * Real.log r) := by
            apply Finset.sum_le_sum
            intro r hr
            obtain ⟨hrR, hnsq⟩ := Finset.mem_filter.mp hr
            have hlt : X < r * r := by omega
            have hltR : (X : ℝ) < (r : ℝ) * (r : ℝ) := by exact_mod_cast hlt
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrR).1).1
            have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
            have hlog_lt : Real.log X ≤ 2 * Real.log r := by
              have h := Real.log_le_log hXpos hltR.le
              rw [Real.log_mul hrpos.ne' hrpos.ne'] at h
              linarith
            nlinarith [w_nonneg r]
        _ ≤ ∑ r ∈ R, 2 * (w r * Real.log r) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro r hr _
            have hr1 : (1 : ℝ) ≤ r := by
              exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
            exact mul_nonneg (by norm_num) (mul_nonneg (w_nonneg r) (Real.log_nonneg hr1))
    linarith [sum_rough_log_le z X]
  have hcomb : Real.log X * ∑ r ∈ R, w r ≤
      (10 + 2 * Real.log 4) * (X : ℝ) * ∑ m ∈ R, w m / (m : ℝ) := by
    rw [hsplit, mul_add]
    linarith
  have hdiv_bound := sum_rough_div_le z X hzX
  have hc_pos : 0 ≤ (10 + 2 * Real.log 4) * (X : ℝ) := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hcomb2 : Real.log X * ∑ r ∈ R, w r ≤
      roughConst * (X : ℝ) * Real.sqrt (L X / L z) := by
    calc Real.log X * ∑ r ∈ R, w r
        ≤ (10 + 2 * Real.log 4) * (X : ℝ) * (eulerConst * Real.sqrt (L X / L z)) :=
          le_trans hcomb (mul_le_mul_of_nonneg_left hdiv_bound hc_pos)
      _ = roughConst * (X : ℝ) * Real.sqrt (L X / L z) := by unfold roughConst; ring
  have hsqrt_div : Real.sqrt (L X / L z) = Real.sqrt (L X) / Real.sqrt (L z) :=
    Real.sqrt_div (L_pos X).le (L z)
  have hsqLX : Real.sqrt (L X) * Real.sqrt (L X) = Real.log X := by
    rw [Real.mul_self_sqrt (L_pos X).le, hLX]
  have hden_pos : 0 < Real.sqrt (L X) * Real.sqrt (L z) :=
    mul_pos (Real.sqrt_pos.mpr (L_pos X)) (Real.sqrt_pos.mpr (L_pos z))
  rw [le_div_iff₀ hden_pos]
  rw [hsqrt_div] at hcomb2
  have hLz_pos : 0 < Real.sqrt (L z) := Real.sqrt_pos.mpr (L_pos z)
  have hLX_pos : 0 < Real.sqrt (L X) := Real.sqrt_pos.mpr (L_pos X)
  have hmul : (∑ r ∈ R, w r) * (Real.sqrt (L X) * Real.sqrt (L z)) * Real.sqrt (L X) ≤
      roughConst * (X : ℝ) * Real.sqrt (L X) := by
    have lhs_eq : (∑ r ∈ R, w r) * (Real.sqrt (L X) * Real.sqrt (L z)) * Real.sqrt (L X) =
        (Real.log X * ∑ r ∈ R, w r) * Real.sqrt (L z) := by
      rw [← hsqLX]; ring
    have rhs_eq : roughConst * (X : ℝ) * Real.sqrt (L X) =
        (roughConst * (X : ℝ) * (Real.sqrt (L X) / Real.sqrt (L z))) * Real.sqrt (L z) := by
      field_simp
    rw [lhs_eq, rhs_eq]
    exact mul_le_mul_of_nonneg_right hcomb2 hLz_pos.le
  exact le_of_mul_le_mul_right hmul hLX_pos

/- ### Part 4: Middle-Divisor `rho1` Decomposition & Dyadic Block Bounds -/

private def rho1 (m : ℕ) : ℕ :=
  Finset.sup (m.divisors.filter fun d => d * d ≤ m) id

private lemma rho1_mem {m : ℕ} (hm : 1 ≤ m) :
    rho1 m ∈ m.divisors.filter (fun d => d * d ≤ m) := by
  have h1 : 1 ∈ m.divisors.filter (fun d => d * d ≤ m) := by
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd m, by omega⟩, by omega⟩
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup _ ⟨1, h1⟩ id
  simpa [rho1, heq] using hd

private lemma rho1_spec {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ rho1 m ∧ rho1 m ∣ m ∧ rho1 m * rho1 m ≤ m ∧
    rho1 m ≤ m / rho1 m ∧ 2 ≤ m / rho1 m ∧
    (∀ p ∈ (m / rho1 m).primeFactors, m < (rho1 m * p) ^ 2) ∧
    m / (rho1 m) ^ 2 = (m / rho1 m) / rho1 m := by
  have hmem := rho1_mem (by omega : 1 ≤ m)
  obtain ⟨hdvd_mem, hsq⟩ := Finset.mem_filter.mp hmem
  have hdvd : rho1 m ∣ m := (Nat.mem_divisors.mp hdvd_mem).1
  have hpos : 1 ≤ rho1 m := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hmul : rho1 m * (m / rho1 m) = m := Nat.mul_div_cancel' hdvd
  have hle : rho1 m ≤ m / rho1 m := by nlinarith
  have hge2 : 2 ≤ m / rho1 m := by
    by_contra hlt
    have : m / rho1 m ≤ 1 := by omega
    nlinarith
  have hpf : ∀ p ∈ (m / rho1 m).primeFactors, m < (rho1 m * p) ^ 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ m / rho1 m := Nat.dvd_of_mem_primeFactors hp
    have hdp_dvd : rho1 m * p ∣ m := by
      conv_rhs => rw [← hmul]
      exact Nat.mul_dvd_mul_left (rho1 m) hpdvd
    by_contra hnot
    push Not at hnot
    have hdp_mem : rho1 m * p ∈ m.divisors.filter (fun d => d * d ≤ m) := by
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hdp_dvd, by omega⟩, by nlinarith⟩
    have hle_sup : rho1 m * p ≤ rho1 m := Finset.le_sup (f := id) hdp_mem
    have hp2 : 2 ≤ p := hpp.two_le
    nlinarith
  have hdiv : m / (rho1 m) ^ 2 = (m / rho1 m) / rho1 m := by
    rw [sq, Nat.div_div_eq_div_mul]
  exact ⟨hpos, hdvd, hsq, hle, hge2, hpf, hdiv⟩

private lemma inner_ge_two_bound (N m : ℕ) (hm : 2 ≤ m) :
    ∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r ≤
      roughConst * (N : ℝ) /
        ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m))) := by
  obtain ⟨hd1, _, _, _, _, _, hdiv_eq⟩ := rho1_spec hm
  set z := (m / rho1 m) / rho1 m
  set X := (N - 1) / m
  have hsub : (Finset.Icc 2 X).filter (fun r => ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2) ⊆
      (Finset.Icc 1 X).filter (IsRough z) := by
    intro r hr
    obtain ⟨hrI, hrp⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr2, hrX⟩ := Finset.mem_Icc.mp hrI
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hrX⟩, fun p hp => ?_⟩
    have hmp := hrp p hp
    have hd2_pos : 0 < (rho1 m) ^ 2 := by positivity
    rw [show z = m / (rho1 m) ^ 2 from hdiv_eq.symm]
    exact (Nat.div_le_iff_le_mul_add_pred hd2_pos).mpr (by nlinarith)
  by_cases hzX : z ≤ X
  · calc ∑ r ∈ (Finset.Icc 2 X).filter (fun r => ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r
        ≤ ∑ r ∈ (Finset.Icc 1 X).filter (IsRough z), w r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => w_nonneg _)
      _ ≤ roughConst * (X : ℝ) / (Real.sqrt (L X) * Real.sqrt (L z)) :=
          sum_half_omega_rough_le z X hzX
      _ ≤ roughConst * ((N : ℝ) / (m : ℝ)) / (Real.sqrt (L X) * Real.sqrt (L z)) := by
          have hXle : (X : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
            calc (X : ℝ) = (((N - 1) / m : ℕ) : ℝ) := rfl
              _ ≤ ((N - 1 : ℕ) : ℝ) / (m : ℝ) := Nat.cast_div_le
              _ ≤ (N : ℝ) / (m : ℝ) := by
                  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
                  exact_mod_cast Nat.sub_le N 1
          have hden_pos : 0 < Real.sqrt (L X) * Real.sqrt (L z) :=
            mul_pos (Real.sqrt_pos.mpr (L_pos X)) (Real.sqrt_pos.mpr (L_pos z))
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hXle roughConst_pos.le) hden_pos.le
      _ = roughConst * (N : ℝ) / ((m : ℝ) * Real.sqrt (L X) * Real.sqrt (L z)) := by
          ring
  · push Not at hzX
    have hemp : (Finset.Icc 2 X).filter (fun r => ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr
      have hr' := hsub hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
      have hrX : r ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
      have hfac : r.minFac ∈ r.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd r, by omega⟩
      have hz_le := (Finset.mem_filter.mp hr').2 r.minFac hfac
      have hle_r : r.minFac ≤ r := Nat.minFac_le (by omega)
      omega
    rw [hemp, Finset.sum_empty]
    positivity [roughConst_pos, L_pos X, L_pos z]

private lemma sum_r_eq_one_bound (N : ℕ) (hN : 2 ≤ N) :
    ∑ m ∈ Finset.Ico 2 N, w m ≤ roughConst * (N : ℝ) / Real.sqrt (L N) := by
  have hsub : Finset.Ico 2 N ⊆ (Finset.Icc 1 N).filter (IsRough 1) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).one_lt.le⟩
  have h1 := sum_half_omega_rough_le 1 N (by omega)
  have hL1 : (1 : ℝ) ≤ Real.sqrt (L 1) := by
    rw [Real.one_le_sqrt]; exact (one_lt_L 1).le
  calc ∑ m ∈ Finset.Ico 2 N, w m
      ≤ ∑ m ∈ (Finset.Icc 1 N).filter (IsRough 1), w m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => w_nonneg _)
    _ ≤ roughConst * (N : ℝ) / (Real.sqrt (L N) * Real.sqrt (L 1)) := h1
    _ ≤ roughConst * (N : ℝ) / Real.sqrt (L N) := by
        apply div_le_div_of_nonneg_left (mul_nonneg roughConst_pos.le (Nat.cast_nonneg N))
          (Real.sqrt_pos.mpr (L_pos N))
        nlinarith [Real.sqrt_nonneg (L N)]

private lemma L_quot_ge_of_block {N LN j k d d' : ℕ}
    (hN : 16 ≤ N) (hLN : LN = Nat.log 2 N + 1) (hdd'_pos : 0 < d * d')
    (hj : d < 2 ^ (j + 1)) (hk : d' < 2 ^ (k + 1) * d)
    (hsum : k + 2 * j < LN) :
    ((LN - k - 2 * j : ℕ) : ℝ) / 18 ≤ L ((N - 1) / (d * d')) := by
  by_cases hsmall : LN - k - 2 * j ≤ 18
  · have h1 : ((LN - k - 2 * j : ℕ) : ℝ) / 18 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      exact_mod_cast hsmall
    linarith [one_lt_L ((N - 1) / (d * d'))]
  · push Not at hsmall
    have hdd' : d * d' < 2 ^ (k + 2 * j + 3) := by
      have h1 : d * d' < d * (2 ^ (k + 1) * d) := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · simp at hk
        · exact Nat.mul_lt_mul_of_pos_left hk hd
      have h2 : d * d < 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_lt_mul'' hj hj
      have h3 : 2 ^ (k + 1) * (2 ^ (j + 1) * 2 ^ (j + 1)) = 2 ^ (k + 2 * j + 3) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h4 : d * (2 ^ (k + 1) * d) = 2 ^ (k + 1) * (d * d) := by ring
      have h5 : 2 ^ (k + 1) * (d * d) < 2 ^ (k + 1) * (2 ^ (j + 1) * 2 ^ (j + 1)) :=
        Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      omega
    have hNpow : 2 ^ (LN - 1) ≤ N := by
      have h1 : LN - 1 = Nat.log 2 N := by omega
      rw [h1]
      exact Nat.pow_log_le_self 2 (by omega)
    have hLN5 : 5 ≤ LN := by
      have : 4 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
      omega
    have hN1pow : 2 ^ (LN - 2) ≤ N - 1 := by
      have h1 : 2 ^ (LN - 1) = 2 * 2 ^ (LN - 2) := by
        rw [← pow_succ']; congr 1; omega
      have h2 : 1 ≤ 2 ^ (LN - 2) := Nat.one_le_pow _ _ (by norm_num)
      omega
    set e := LN - k - 2 * j - 5
    have hquot : 2 ^ e ≤ (N - 1) / (d * d') := by
      rw [Nat.le_div_iff_mul_le hdd'_pos]
      have h1 : 2 ^ e * (d * d') ≤ 2 ^ e * 2 ^ (k + 2 * j + 3) :=
        Nat.mul_le_mul_left _ hdd'.le
      have h2 : 2 ^ e * 2 ^ (k + 2 * j + 3) = 2 ^ (LN - 2) := by
        rw [← pow_add]; congr 1; omega
      omega
    have hLge : ((e + 1 : ℕ) : ℝ) / 3 ≤ L ((N - 1) / (d * d')) :=
      le_trans (L_pow_two_ge e) (L_mono hquot)
    have hnat : LN - k - 2 * j ≤ 6 * (e + 1) := by omega
    have hreal : ((LN - k - 2 * j : ℕ) : ℝ) ≤ 6 * ((e + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith

private lemma prime_ge_pow_half {k p : ℕ} (h : 2 ^ k < p ^ 2) : 2 ^ (k / 2) ≤ p := by
  by_contra hlt
  push Not at hlt
  have h1 : p ^ 2 < (2 ^ (k / 2)) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h2 : (2 ^ (k / 2)) ^ 2 = 2 ^ (2 * (k / 2)) := by rw [← pow_mul]; ring_nf
  have h3 : 2 ^ (2 * (k / 2)) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private lemma block_d'_sum_le (j k d : ℕ) (hd_lo : 2 ^ j ≤ d) :
    ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
        w d' / (d' : ℝ) ≤
      (2 * Real.sqrt 18 * roughConst) /
        (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by positivity) hd_lo
  have hkd_pos : (0 : ℝ) < (2 ^ k * d : ℕ) := by exact_mod_cast (by positivity : 0 < 2 ^ k * d)
  have hsub : (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))) ⊆
      (Finset.Icc 1 (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))) := by
    intro x hx
    obtain ⟨hxI, hxR⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hxI
    have h1' : 1 ≤ x := by
      have hpos : 0 < 2 ^ k * d := by positivity
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1', h2.le⟩, hxR⟩
  have hle_zX : 2 ^ (k / 2) ≤ 2 ^ (k + 1) * d := by
    calc 2 ^ (k / 2) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (k + 1) * d := Nat.le_mul_of_pos_right _ hd_pos
  have h1 : ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
        w d' / (d' : ℝ) ≤
      (∑ d' ∈ (Finset.Icc 1 (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))), w d') /
        ((2 ^ k * d : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    calc ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
          w d' / (d' : ℝ)
        ≤ ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
          w d' / ((2 ^ k * d : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro d' hd'
          have hlo : 2 ^ k * d ≤ d' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hd').1).1
          exact div_le_div_of_nonneg_left (w_nonneg d') hkd_pos (by exact_mod_cast hlo)
      _ ≤ ∑ d' ∈ (Finset.Icc 1 (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
          w d' / ((2 ^ k * d : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => div_nonneg (w_nonneg _) hkd_pos.le)
  have h2 := sum_half_omega_rough_le (2 ^ (k / 2)) (2 ^ (k + 1) * d) hle_zX
  have hL1 : ((k + j + 1 : ℕ) : ℝ) / 3 ≤ L (2 ^ (k + 1) * d) := by
    have hpow : 2 ^ (k + j) ≤ 2 ^ (k + 1) * d := by
      calc 2 ^ (k + j) = 2 ^ k * 2 ^ j := pow_add 2 k j
        _ ≤ 2 ^ (k + 1) * d := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) hd_lo
    exact le_trans (L_pow_two_ge (k + j)) (L_mono hpow)
  have hL2 : ((k + 1 : ℕ) : ℝ) / 6 ≤ L (2 ^ (k / 2)) := by
    have h := L_pow_two_ge (k / 2)
    have hnat : k + 1 ≤ 2 * (k / 2 + 1) := by omega
    have hreal : ((k + 1 : ℕ) : ℝ) ≤ 2 * ((k / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hden_ge : Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 18 ≤
      Real.sqrt (L (2 ^ (k + 1) * d)) * Real.sqrt (L (2 ^ (k / 2))) := by
    have hs1 : Real.sqrt (((k + j + 1 : ℕ) : ℝ) / 3) ≤ Real.sqrt (L (2 ^ (k + 1) * d)) :=
      Real.sqrt_le_sqrt hL1
    have hs2 : Real.sqrt (((k + 1 : ℕ) : ℝ) / 6) ≤ Real.sqrt (L (2 ^ (k / 2))) :=
      Real.sqrt_le_sqrt hL2
    rw [Real.sqrt_div (Nat.cast_nonneg _)] at hs1
    rw [Real.sqrt_div (Nat.cast_nonneg _)] at hs2
    have h18 : Real.sqrt 3 * Real.sqrt 6 = Real.sqrt 18 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    calc Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 18
        = (Real.sqrt ((k + j + 1 : ℕ) : ℝ) / Real.sqrt 3) *
          (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 6) := by
          rw [← h18]; ring
      _ ≤ Real.sqrt (L (2 ^ (k + 1) * d)) * Real.sqrt (L (2 ^ (k / 2))) :=
          mul_le_mul hs1 hs2 (by positivity) (Real.sqrt_nonneg _)
  have hratio : ((2 ^ (k + 1) * d : ℕ) : ℝ) / ((2 ^ k * d : ℕ) : ℝ) = 2 := by
    push_cast
    rw [pow_succ]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  calc ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
        w d' / (d' : ℝ)
      ≤ (roughConst * ((2 ^ (k + 1) * d : ℕ) : ℝ) /
          (Real.sqrt (L (2 ^ (k + 1) * d)) * Real.sqrt (L (2 ^ (k / 2))))) /
          ((2 ^ k * d : ℕ) : ℝ) :=
        le_trans h1 (div_le_div_of_nonneg_right h2 hkd_pos.le)
    _ = 2 * roughConst / (Real.sqrt (L (2 ^ (k + 1) * d)) * Real.sqrt (L (2 ^ (k / 2)))) := by
        rw [div_right_comm, mul_div_assoc, hratio]; ring
    _ ≤ 2 * roughConst /
          (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 18) := by
        apply div_le_div_of_nonneg_left (by positivity [roughConst_pos]) (by positivity) hden_ge
    _ = (2 * Real.sqrt 18 * roughConst) /
          (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
        field_simp

private lemma block_d_sum_le (j : ℕ) :
    ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), w d / (d : ℝ) ≤
      (2 * Real.sqrt 3 * roughConst) / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
  have h2j_pos : (0 : ℝ) < (2 ^ j : ℕ) := by exact_mod_cast (by positivity : 0 < 2 ^ j)
  have hsub : Finset.Ico (2 ^ j) (2 ^ (j + 1)) ⊆ (Finset.Icc 1 (2 ^ (j + 1))).filter (IsRough 1) := by
    intro d hd
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans (Nat.one_le_pow _ _ (by norm_num)) h1, h2.le⟩,
      fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le⟩
  have h1 : ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), w d / (d : ℝ) ≤
      (∑ d ∈ (Finset.Icc 1 (2 ^ (j + 1))).filter (IsRough 1), w d) / ((2 ^ j : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    calc ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), w d / (d : ℝ)
        ≤ ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), w d / ((2 ^ j : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          exact div_le_div_of_nonneg_left (w_nonneg d) h2j_pos
            (by exact_mod_cast (Finset.mem_Ico.mp hd).1)
      _ ≤ ∑ d ∈ (Finset.Icc 1 (2 ^ (j + 1))).filter (IsRough 1), w d / ((2 ^ j : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => div_nonneg (w_nonneg _) h2j_pos.le)
  have h2 := sum_half_omega_rough_le 1 (2 ^ (j + 1)) (Nat.one_le_pow _ _ (by norm_num))
  have hL : ((j + 1 : ℕ) : ℝ) / 3 ≤ L (2 ^ (j + 1)) :=
    le_trans (L_pow_two_ge j) (L_mono (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hL1 : (1 : ℝ) ≤ Real.sqrt (L 1) := by
    rw [Real.one_le_sqrt]; exact (one_lt_L 1).le
  have hden_ge : Real.sqrt ((j + 1 : ℕ) : ℝ) / Real.sqrt 3 ≤
      Real.sqrt (L (2 ^ (j + 1))) * Real.sqrt (L 1) := by
    have hs := Real.sqrt_le_sqrt hL
    rw [Real.sqrt_div (Nat.cast_nonneg _)] at hs
    nlinarith [Real.sqrt_nonneg (L (2 ^ (j + 1)))]
  have hratio : ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) = 2 := by
    push_cast; rw [pow_succ]; field_simp
  calc ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), w d / (d : ℝ)
      ≤ (roughConst * ((2 ^ (j + 1) : ℕ) : ℝ) /
          (Real.sqrt (L (2 ^ (j + 1))) * Real.sqrt (L 1))) / ((2 ^ j : ℕ) : ℝ) :=
        le_trans h1 (div_le_div_of_nonneg_right h2 h2j_pos.le)
    _ = 2 * roughConst / (Real.sqrt (L (2 ^ (j + 1))) * Real.sqrt (L 1)) := by
        rw [div_right_comm, mul_div_assoc, hratio]; ring
    _ ≤ 2 * roughConst / (Real.sqrt ((j + 1 : ℕ) : ℝ) / Real.sqrt 3) :=
        div_le_div_of_nonneg_left (by positivity [roughConst_pos]) (by positivity) hden_ge
    _ = (2 * Real.sqrt 3 * roughConst) / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
        field_simp

/- ### Part 5: Finite Integer Double-Sum Bound -/

private lemma sum_inv_sqrt_le (M : ℕ) :
    ∑ t ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (M : ℝ) := by
  induction M with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hstep : (1 : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) := by
      have hs1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := by positivity
      have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
      have hdiff : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
          (Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ)) = 1 := by
        have h1 : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = (k : ℝ) + 1 := by
          rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
        have h2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
        nlinarith
      rw [div_le_iff₀ hs1]
      nlinarith
    linarith

private lemma sum_inv_range_le (L : ℕ) (_hL : 1 ≤ L) :
    ∑ k ∈ Finset.range L, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 + Real.log L := by
  have h1 : ∑ k ∈ Finset.range L, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) = (harmonic L : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_nbij' (fun k => k + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi; simp only [Finset.mem_Icc] at hi; exact Finset.mem_range.mpr (by omega)
    · intro k _; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro k _; simp [one_div]
  rw [h1]
  exact harmonic_le_one_add_log L

private lemma inner_j_sum_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ j ∈ Finset.range ((M + 1) / 2),
        (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) ≤ 7 := by
  set J := Finset.range ((M + 1) / 2)
  set J1 := J.filter (fun j => 4 * j < M)
  set J2 := J.filter (fun j => ¬ 4 * j < M)
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => 4 * j < M)]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hJ1 : ∑ j ∈ J1,
      (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) ≤ 2 * Real.sqrt 2 := by
    have hstep : ∑ j ∈ J1,
        (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) ≤
        (Real.sqrt 2 / Real.sqrt (M : ℝ)) * ∑ j ∈ J1, (1 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have h4j : 4 * j < M := (Finset.mem_filter.mp hj).2
      have h2j : (M : ℝ) / 2 ≤ ((M - 2 * j : ℕ) : ℝ) := by
        have : M ≤ 2 * (M - 2 * j) := by omega
        have : (M : ℝ) ≤ 2 * ((M - 2 * j : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hs : Real.sqrt (M : ℝ) / Real.sqrt 2 ≤ Real.sqrt ((M - 2 * j : ℕ) : ℝ) := by
        rw [← Real.sqrt_div hMpos.le]
        exact Real.sqrt_le_sqrt h2j
      have hs_pos : 0 < Real.sqrt (M : ℝ) / Real.sqrt 2 := by positivity
      have hj_pos : 0 < Real.sqrt ((j + 1 : ℕ) : ℝ) := by positivity
      calc (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ))
          ≤ (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * (Real.sqrt (M : ℝ) / Real.sqrt 2)) :=
            div_le_div_of_nonneg_left zero_le_one (mul_pos hj_pos hs_pos)
              (mul_le_mul_of_nonneg_left hs hj_pos.le)
        _ = (Real.sqrt 2 / Real.sqrt (M : ℝ)) * ((1 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
            field_simp
    have hsum1 : ∑ j ∈ J1, (1 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (M : ℝ) := by
      calc ∑ j ∈ J1, (1 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)
          = ∑ t ∈ J1.image (fun j : ℕ => j + 1), (1 : ℝ) / Real.sqrt (t : ℝ) := by
            rw [Finset.sum_image (fun a _ b _ h => by omega)]
        _ ≤ ∑ t ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (t : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
              have hlt : j < (M + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · intro _ _ _; positivity
        _ ≤ 2 * Real.sqrt (M : ℝ) := sum_inv_sqrt_le M
    calc ∑ j ∈ J1, (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ))
        ≤ (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (M : ℝ)) :=
          le_trans hstep (mul_le_mul_of_nonneg_left hsum1 (by positivity))
      _ = 2 * Real.sqrt 2 := by field_simp
  have hJ2 : ∑ j ∈ J2,
      (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) ≤ 4 := by
    have hstep : ∑ j ∈ J2,
        (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) ≤
        (2 / Real.sqrt (M : ℝ)) * ∑ j ∈ J2, (1 : ℝ) / Real.sqrt ((M - 2 * j : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have h4j : M ≤ 4 * j := by have := (Finset.mem_filter.mp hj).2; omega
      have hlt : j < (M + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hpos : 0 < M - 2 * j := by omega
      have hj1 : (M : ℝ) / 4 ≤ ((j + 1 : ℕ) : ℝ) := by
        have : M ≤ 4 * (j + 1) := by omega
        have : (M : ℝ) ≤ 4 * ((j + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hs : Real.sqrt (M : ℝ) / 2 ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) := by
        have h := Real.sqrt_le_sqrt hj1
        rw [Real.sqrt_div hMpos.le, show Real.sqrt 4 = 2 by norm_num] at h
        exact h
      have hs_pos : 0 < Real.sqrt (M : ℝ) / 2 := by positivity
      have hm_pos : 0 < Real.sqrt ((M - 2 * j : ℕ) : ℝ) := by
        exact Real.sqrt_pos.mpr (by exact_mod_cast hpos)
      calc (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ))
          ≤ (1 : ℝ) / ((Real.sqrt (M : ℝ) / 2) * Real.sqrt ((M - 2 * j : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_left zero_le_one (mul_pos hs_pos hm_pos)
              (mul_le_mul_of_nonneg_right hs hm_pos.le)
        _ = (2 / Real.sqrt (M : ℝ)) * ((1 : ℝ) / Real.sqrt ((M - 2 * j : ℕ) : ℝ)) := by
            field_simp
    have hinj : Set.InjOn (fun j => M - 2 * j) (J2 : Set ℕ) := by
      intro a ha b hb hab
      have ha' : a < (M + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb' : b < (M + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      dsimp only at hab
      omega
    have hsum2 : ∑ j ∈ J2, (1 : ℝ) / Real.sqrt ((M - 2 * j : ℕ) : ℝ) ≤ 2 * Real.sqrt (M : ℝ) := by
      calc ∑ j ∈ J2, (1 : ℝ) / Real.sqrt ((M - 2 * j : ℕ) : ℝ)
          = ∑ t ∈ J2.image (fun j => M - 2 * j), (1 : ℝ) / Real.sqrt (t : ℝ) := by
            rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
        _ ≤ ∑ t ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (t : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
              have hlt : j < (M + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · intro _ _ _; positivity
        _ ≤ 2 * Real.sqrt (M : ℝ) := sum_inv_sqrt_le M
    calc ∑ j ∈ J2, (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((M - 2 * j : ℕ) : ℝ))
        ≤ (2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (M : ℝ)) :=
          le_trans hstep (mul_le_mul_of_nonneg_left hsum2 (by positivity))
      _ = 4 := by field_simp; ring
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

private lemma finite_double_sum_le (LN : ℕ) (hL : 1 ≤ LN) :
    ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
        (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
          Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤
      (8 * Real.sqrt 3) * (1 + Real.log LN) ^ 2 / Real.sqrt (LN : ℝ) := by
  have hLpos : (0 : ℝ) < LN := by exact_mod_cast hL
  have hlog_ge0 : 0 ≤ Real.log (LN : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have h1log : 1 ≤ 1 + Real.log (LN : ℝ) := by linarith
  have hterm : ∀ k ∈ Finset.range LN, ∀ j ∈ Finset.range ((LN - k + 1) / 2),
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
        Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤
      (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) +
      (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
          Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
    intro k hk j hj
    have hkL : k < LN := Finset.mem_range.mp hk
    have hjL : j < (LN - k + 1) / 2 := Finset.mem_range.mp hj
    have hrem_pos : 0 < LN - k - 2 * j := by omega
    by_cases hcase : 3 * (k + j + 1) < LN
    · have hrem_ge : (LN : ℝ) / 3 ≤ ((LN - k - 2 * j : ℕ) : ℝ) := by
        have : LN ≤ 3 * (LN - k - 2 * j) := by omega
        have : (LN : ℝ) ≤ 3 * ((LN - k - 2 * j : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hs_rem : Real.sqrt (LN : ℝ) / Real.sqrt 3 ≤ Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) := by
        rw [← Real.sqrt_div hLpos.le]; exact Real.sqrt_le_sqrt hrem_ge
      have hsqj : ((j + 1 : ℕ) : ℝ) ≤
          Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) := by
        have h1 : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt ((k + j + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast (by omega : j + 1 ≤ k + j + 1))
        have h2 : Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
        nlinarith [Real.sqrt_nonneg ((j + 1 : ℕ) : ℝ)]
      have hden_ge : ((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) * (Real.sqrt (LN : ℝ) / Real.sqrt 3) ≤
          ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) := by
        have hA : ((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hsqj (Nat.cast_nonneg _)
        exact mul_le_mul hA hs_rem (by positivity) (by positivity)
      have hle1 : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤
          (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
            ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) := by
        calc _ ≤ (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) *
                (Real.sqrt (LN : ℝ) / Real.sqrt 3)) :=
              div_le_div_of_nonneg_left zero_le_one (by positivity) hden_ge
          _ = (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
                ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) := by
              field_simp
      linarith [show 0 ≤ (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
          Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) by positivity]
    · push Not at hcase
      have hkj_ge : (LN : ℝ) / 3 ≤ ((k + j + 1 : ℕ) : ℝ) := by
        have : (LN : ℝ) ≤ 3 * ((k + j + 1 : ℕ) : ℝ) := by exact_mod_cast hcase
        linarith
      have hs_kj : Real.sqrt (LN : ℝ) / Real.sqrt 3 ≤ Real.sqrt ((k + j + 1 : ℕ) : ℝ) := by
        rw [← Real.sqrt_div hLpos.le]; exact Real.sqrt_le_sqrt hkj_ge
      have hrem_posR : 0 < Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast hrem_pos)
      have hden_ge : ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            (Real.sqrt (LN : ℝ) / Real.sqrt 3) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) := by
        have h1 : ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) * (Real.sqrt (LN : ℝ) / Real.sqrt 3) ≤
            ((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hs_kj (by positivity)
        exact mul_le_mul_of_nonneg_right h1 hrem_posR.le
      have hle2 : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤
          (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
            ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
              Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
        calc _ ≤ (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
                (Real.sqrt (LN : ℝ) / Real.sqrt 3) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) :=
              div_le_div_of_nonneg_left zero_le_one (by positivity) hden_ge
          _ = (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
                ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
                  Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
              field_simp
      linarith [show 0 ≤ (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) by positivity]
  have hsum_split :
      ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
        (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
          Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤
      (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        (∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
          (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) +
      (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
        (∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
          (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
    calc _ ≤ ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
            ((Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
              ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))) +
            (Real.sqrt 3 / Real.sqrt (LN : ℝ)) *
              ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
                Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)))) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun j hj => hterm k hk j hj
      _ = _ := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS1 : ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ≤ (1 + Real.log LN) ^ 2 := by
    calc ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
          (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range LN,
            (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            simp only [Finset.mem_range] at hj ⊢; omega
          · intro _ _ _; positivity
      _ = (∑ k ∈ Finset.range LN, (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          (∑ j ∈ Finset.range LN, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (1 + Real.log LN) * (1 + Real.log LN) :=
          mul_le_mul (sum_inv_range_le LN hL) (sum_inv_range_le LN hL)
            (Finset.sum_nonneg fun _ _ => by positivity) (by linarith)
      _ = (1 + Real.log LN) ^ 2 := (sq _).symm
  have hS2 : ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
        Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) ≤ 7 * (1 + Real.log LN) ^ 2 := by
    calc ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
          (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
            Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))
        = ∑ k ∈ Finset.range LN, ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) *
            ∑ j ∈ Finset.range ((LN - k + 1) / 2),
              (1 : ℝ) / (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ∑ k ∈ Finset.range LN, ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) * 7 := by
          apply Finset.sum_le_sum
          intro k hk
          have hMk : 1 ≤ LN - k := by have := Finset.mem_range.mp hk; omega
          have := inner_j_sum_le (LN - k) hMk
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 7 * ∑ k ∈ Finset.range LN, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 7 * (1 + Real.log LN) := by linarith [sum_inv_range_le LN hL]
      _ ≤ 7 * (1 + Real.log LN) ^ 2 := by nlinarith
  have hfactor : 0 ≤ Real.sqrt 3 / Real.sqrt (LN : ℝ) := by positivity
  calc _ ≤ (Real.sqrt 3 / Real.sqrt (LN : ℝ)) * (1 + Real.log LN) ^ 2 +
          (Real.sqrt 3 / Real.sqrt (LN : ℝ)) * (7 * (1 + Real.log LN) ^ 2) :=
        le_trans hsum_split (add_le_add (mul_le_mul_of_nonneg_left hS1 hfactor)
          (mul_le_mul_of_nonneg_left hS2 hfactor))
    _ = (8 * Real.sqrt 3) * (1 + Real.log LN) ^ 2 / Real.sqrt (LN : ℝ) := by ring

/- ### Part 6: Assembly of `S(N)` Bound and Asymptotic Conclusion -/

private noncomputable def totalConst : ℝ :=
  roughConst + 8 * Real.sqrt 3 * (216 * roughConst ^ 3)

private lemma main_sum_bound (N : ℕ) (hN : 16 ≤ N) :
    (∑ m ∈ Finset.Ico 2 N,
      ∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors,
          m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2),
      ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r))) ≤
    totalConst * (N : ℝ) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
  set LN := Nat.log 2 N + 1
  have hLN5 : 5 ≤ LN := by
    have : 4 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
    omega
  have hlogN_ge2 : (2 : ℝ) ≤ Real.log N := by
    have h1 : Real.exp 2 < 16 := by
      have hgt := Real.exp_one_lt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have hN16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : Real.log (Real.exp 2) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h2
  have hlogN_pos : 0 < Real.log N := by linarith
  have hLN_ge : Real.log N ≤ (LN : ℝ) := by
    have hlt : N < 2 ^ LN := Nat.lt_pow_succ_log_self (by norm_num) N
    have h1 : Real.log (N : ℝ) ≤ Real.log ((2 : ℝ) ^ LN) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hlt.le)
    rw [Real.log_pow] at h1
    have := log_two_lt_one
    nlinarith
  have hLN_le : (LN : ℝ) ≤ 3 * Real.log N := by
    have hle : 2 ^ (LN - 1) ≤ N := by
      have : LN - 1 = Nat.log 2 N := by omega
      rw [this]; exact Nat.pow_log_le_self 2 (by omega)
    have h1 : Real.log ((2 : ℝ) ^ (LN - 1)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hle)
    rw [Real.log_pow] at h1
    have hcast : ((LN - 1 : ℕ) : ℝ) = (LN : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at h1
    have := half_le_log_two
    have hLN1 : (0 : ℝ) ≤ (LN : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (LN : ℝ) := by exact_mod_cast (by omega : 1 ≤ LN)
      linarith
    nlinarith
  -- Step 1: Split r = 1 vs r ≥ 2
  have hsplit_r : ∀ m ∈ Finset.Ico 2 N,
      (∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2),
        ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r))) ≤
      w m + w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r) := by
    intro m hm
    have hm_lt : m < N := (Finset.mem_Ico.mp hm).2
    have hm_pos : 1 ≤ (N - 1) / m := Nat.div_pos (by omega) (by have := (Finset.mem_Ico.mp hm).1; omega)
    have hfactor : ∀ r, (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r) =
        w m * w r := fun r => by unfold w; rw [pow_add]
    simp_rw [hfactor]
    rw [← Finset.mul_sum]
    have hIcc : Finset.Icc 1 ((N - 1) / m) = insert 1 (Finset.Icc 2 ((N - 1) / m)) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.filter_insert]
    have h1ok : ∀ p ∈ (1 : ℕ).primeFactors, m ≤ p * (rho1 m) ^ 2 := by
      intro p hp; simp at hp
    rw [if_pos h1ok, Finset.sum_insert (by simp), w_one, mul_add, mul_one]
  -- Bound the r = 1 sum
  have hpart1 : ∑ m ∈ Finset.Ico 2 N, w m ≤ roughConst * (N : ℝ) / Real.sqrt (Real.log N) := by
    have h := sum_r_eq_one_bound N (by omega)
    rwa [L_eq_log (by omega)] at h
  -- Step 2: Bound the r ≥ 2 sum via (d, d') and dyadic blocks (k, j)
  let M2 := (Finset.Ico 2 N).filter (fun m => 2 ≤ (N - 1) / m)
  have hpart2_reduce :
      ∑ m ∈ Finset.Ico 2 N,
        w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
          ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r) ≤
      ∑ m ∈ M2,
        w m * (roughConst * (N : ℝ) /
          ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m)))) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 N) (fun m => 2 ≤ (N - 1) / m)]
    have hzero : ∑ m ∈ (Finset.Ico 2 N).filter (fun m => ¬ 2 ≤ (N - 1) / m),
        w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
          ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hlt : (N - 1) / m < 2 := by have := (Finset.mem_filter.mp hm).2; omega
      have hemp : Finset.Icc 2 ((N - 1) / m) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro r hr; simp only [Finset.mem_Icc] at hr; omega
      simp [hemp]
    rw [hzero, add_zero]
    apply Finset.sum_le_sum
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
    exact mul_le_mul_of_nonneg_left (inner_ge_two_bound N m hm2) (w_nonneg m)
  -- Group M2 by (k, j) where j = log_2(rho1 m), k = log_2((m/rho1 m)/rho1 m)
  let Kset := (Finset.range LN).sigma (fun k => Finset.range ((LN - k + 1) / 2))
  let blk (kj : Σ _ : ℕ, ℕ) : Finset ℕ :=
    M2.filter (fun m => Nat.log 2 ((m / rho1 m) / rho1 m) = kj.1 ∧ Nat.log 2 (rho1 m) = kj.2)
  have hM2_cover : ∀ m ∈ M2,
      (⟨Nat.log 2 ((m / rho1 m) / rho1 m), Nat.log 2 (rho1 m)⟩ : Σ _ : ℕ, ℕ) ∈ Kset := by
    intro m hm
    have hmI := (Finset.mem_filter.mp hm).1
    obtain ⟨hm2, hmN⟩ := Finset.mem_Ico.mp hmI
    obtain ⟨hd1, hdvd, _, hdle, _, _, _⟩ := rho1_spec hm2
    set d := rho1 m
    set d' := m / d
    set j := Nat.log 2 d
    set k := Nat.log 2 (d' / d)
    have hq1 : 1 ≤ d' / d := Nat.div_pos hdle hd1
    have h2j : 2 ^ j ≤ d := Nat.pow_log_le_self 2 (by omega)
    have h2k : 2 ^ k ≤ d' / d := Nat.pow_log_le_self 2 (by omega)
    have hpow_lt : 2 ^ (k + 2 * j) < 2 ^ LN := by
      have h1 : 2 ^ (k + 2 * j) = 2 ^ k * 2 ^ j * 2 ^ j := by rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : 2 ^ k * 2 ^ j ≤ d' := by
        calc 2 ^ k * 2 ^ j ≤ (d' / d) * d := Nat.mul_le_mul h2k h2j
          _ ≤ d' := Nat.div_mul_le_self d' d
      have h3 : 2 ^ k * 2 ^ j * 2 ^ j ≤ d' * d := Nat.mul_le_mul h2 h2j
      have h4 : d' * d = m := by rw [mul_comm]; exact Nat.mul_div_cancel' hdvd
      have h5 : N < 2 ^ LN := Nat.lt_pow_succ_log_self (by norm_num) N
      omega
    have hsum_lt : k + 2 * j < LN := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
    simp only [Kset, Finset.mem_sigma, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have hM2_eq : M2 = Kset.biUnion blk := by
    ext m
    simp only [Finset.mem_biUnion, blk, Finset.mem_filter]
    constructor
    · intro hm
      exact ⟨⟨Nat.log 2 ((m / rho1 m) / rho1 m), Nat.log 2 (rho1 m)⟩, hM2_cover m hm, hm, rfl, rfl⟩
    · rintro ⟨_, _, hm, _, _⟩
      exact hm
  have hdisj : Set.PairwiseDisjoint (Kset : Set (Σ _ : ℕ, ℕ)) blk := by
    intro a _ b _ hab
    change Disjoint (blk a) (blk b)
    rw [Finset.disjoint_left]
    intro m hma hmb
    have ha := (Finset.mem_filter.mp hma).2
    have hb := (Finset.mem_filter.mp hmb).2
    apply hab
    cases a; cases b
    simp only at ha hb
    congr
    · exact ha.1.symm.trans hb.1
    · exact ha.2.symm.trans hb.2
  -- Bound each block (k, j)
  have hblk_bound : ∀ kj ∈ Kset,
      ∑ m ∈ blk kj,
        w m * (roughConst * (N : ℝ) /
          ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m)))) ≤
      (216 * roughConst ^ 3) * (N : ℝ) *
        ((1 : ℝ) / (((kj.1 + 1 : ℕ) : ℝ) * Real.sqrt ((kj.2 + 1 : ℕ) : ℝ) *
          Real.sqrt ((kj.1 + kj.2 + 1 : ℕ) : ℝ) * Real.sqrt ((LN - kj.1 - 2 * kj.2 : ℕ) : ℝ))) := by
    intro kj hkj
    obtain ⟨k, j⟩ := kj
    obtain ⟨hkL, hjL⟩ := Finset.mem_sigma.mp hkj
    have hk_lt : k < LN := Finset.mem_range.mp hkL
    have hj_lt : j < (LN - k + 1) / 2 := Finset.mem_range.mp hjL
    have hsum_lt : k + 2 * j < LN := by omega
    have hrem_pos : 0 < LN - k - 2 * j := by omega
    -- First pull out the constant factor depending only on (k, j, N)
    set Ckj : ℝ :=
      roughConst * (N : ℝ) * Real.sqrt 18 * Real.sqrt 3 /
        (Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ))
    have hstep1 : ∑ m ∈ blk ⟨k, j⟩,
        w m * (roughConst * (N : ℝ) /
          ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m)))) ≤
        Ckj * ∑ m ∈ blk ⟨k, j⟩, w m / (m : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hmM2, hkm, hjm⟩ := Finset.mem_filter.mp hm
      dsimp only at hkm hjm
      have hm2 : 2 ≤ m := (Finset.mem_Ico.mp (Finset.mem_filter.mp hmM2).1).1
      obtain ⟨hd1, hdvd, _, hdle, hd'2, _, _⟩ := rho1_spec hm2
      set d := rho1 m
      set d' := m / d
      have hq1 : 1 ≤ d' / d := Nat.div_pos hdle hd1
      have hd_lt : d < 2 ^ (j + 1) := by
        rw [← hjm]; exact Nat.lt_pow_succ_log_self (by norm_num) d
      have hq_lt : d' / d < 2 ^ (k + 1) := by
        rw [← hkm]; exact Nat.lt_pow_succ_log_self (by norm_num) (d' / d)
      have hd'_lt : d' < 2 ^ (k + 1) * d := (Nat.div_lt_iff_lt_mul hd1).mp hq_lt
      have hmul : d * d' = m := Nat.mul_div_cancel' hdvd
      have hLquot : ((LN - k - 2 * j : ℕ) : ℝ) / 18 ≤ L ((N - 1) / m) := by
        rw [← hmul]
        exact L_quot_ge_of_block hN rfl (Nat.mul_pos hd1 (by omega)) hd_lt hd'_lt hsum_lt
      have hLk : ((k + 1 : ℕ) : ℝ) / 3 ≤ L (d' / d) := by
        have h2k : 2 ^ k ≤ d' / d := by
          rw [← hkm]; exact Nat.pow_log_le_self 2 (by omega)
        exact le_trans (L_pow_two_ge k) (L_mono h2k)
      have hs1 : Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) / Real.sqrt 18 ≤ Real.sqrt (L ((N - 1) / m)) := by
        rw [← Real.sqrt_div (Nat.cast_nonneg _)]; exact Real.sqrt_le_sqrt hLquot
      have hs2 : Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 3 ≤ Real.sqrt (L (d' / d)) := by
        rw [← Real.sqrt_div (Nat.cast_nonneg _)]; exact Real.sqrt_le_sqrt hLk
      have hm_posR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hremR : 0 < Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast hrem_pos)
      have hprod_ge :
          (Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) / Real.sqrt 18) *
          (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 3) ≤
          Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d)) :=
        mul_le_mul hs1 hs2 (by positivity) (Real.sqrt_nonneg _)
      have hmain : roughConst * (N : ℝ) /
            ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d))) ≤
          Ckj / (m : ℝ) := by
        have hlhs : roughConst * (N : ℝ) /
              ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d))) =
            (roughConst * (N : ℝ) / (Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d)))) / (m : ℝ) := by
          ring
        rw [hlhs]
        apply div_le_div_of_nonneg_right _ hm_posR.le
        calc roughConst * (N : ℝ) / (Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d)))
            ≤ roughConst * (N : ℝ) /
                ((Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ) / Real.sqrt 18) *
                 (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt 3)) :=
              div_le_div_of_nonneg_left (mul_nonneg roughConst_pos.le (Nat.cast_nonneg N))
                (by positivity) hprod_ge
          _ = Ckj := by unfold Ckj; field_simp
      calc w m * (roughConst * (N : ℝ) /
              ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L (d' / d))))
          ≤ w m * (Ckj / (m : ℝ)) := mul_le_mul_of_nonneg_left hmain (w_nonneg m)
        _ = Ckj * (w m / (m : ℝ)) := by ring
    -- Next bound ∑ m ∈ blk ⟨k, j⟩, w m / m via (d, d')
    let Dset := Finset.Ico (2 ^ j) (2 ^ (j + 1))
    let PairSet := Dset.sigma (fun d =>
      (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))))
    let ψ : ℕ → Σ _ : ℕ, ℕ := fun m => ⟨rho1 m, m / rho1 m⟩
    have hψ_maps : ∀ m ∈ blk ⟨k, j⟩, ψ m ∈ PairSet := by
      intro m hm
      obtain ⟨hmM2, hkm, hjm⟩ := Finset.mem_filter.mp hm
      dsimp only at hkm hjm
      have hm2 : 2 ≤ m := (Finset.mem_Ico.mp (Finset.mem_filter.mp hmM2).1).1
      obtain ⟨hd1, hdvd, _, hdle, _, hpf, _⟩ := rho1_spec hm2
      set d := rho1 m
      set d' := m / d
      have hq1 : 1 ≤ d' / d := Nat.div_pos hdle hd1
      have hd_lo : 2 ^ j ≤ d := by rw [← hjm]; exact Nat.pow_log_le_self 2 (by omega)
      have hd_hi : d < 2 ^ (j + 1) := by rw [← hjm]; exact Nat.lt_pow_succ_log_self (by norm_num) d
      have hq_lo : 2 ^ k ≤ d' / d := by rw [← hkm]; exact Nat.pow_log_le_self 2 (by omega)
      have hq_hi : d' / d < 2 ^ (k + 1) := by
        rw [← hkm]; exact Nat.lt_pow_succ_log_self (by norm_num) (d' / d)
      have hd'_lo : 2 ^ k * d ≤ d' := le_trans (Nat.mul_le_mul_right d hq_lo) (Nat.div_mul_le_self d' d)
      have hd'_hi : d' < 2 ^ (k + 1) * d := (Nat.div_lt_iff_lt_mul hd1).mp hq_hi
      have hmul : d * d' = m := Nat.mul_div_cancel' hdvd
      have hd'_rough : IsRough (2 ^ (k / 2)) d' := by
        intro p hp
        have hlt := hpf p hp
        have h1 : d * d' < d * (d * p ^ 2) := by
          calc d * d' = m := hmul
            _ < (d * p) ^ 2 := hlt
            _ = d * (d * p ^ 2) := by ring
        have h2 : d' < d * p ^ 2 := Nat.lt_of_mul_lt_mul_left h1
        have h3 : 2 ^ k < p ^ 2 := by
          have : 2 ^ k * d < d * p ^ 2 := lt_of_le_of_lt hd'_lo h2
          rw [mul_comm d] at this
          exact Nat.lt_of_mul_lt_mul_right this
        exact prime_ge_pow_half h3
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Ico.mpr ⟨hd_lo, hd_hi⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hd'_lo, hd'_hi⟩, hd'_rough⟩⟩
    have hψ_inj : Set.InjOn ψ (blk ⟨k, j⟩ : Set ℕ) := by
      intro a ha b hb hab
      have ha2 : 2 ≤ a := (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1
      have hb2 : 2 ≤ b := (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
      have hda : rho1 a ∣ a := (rho1_spec ha2).2.1
      have hdb : rho1 b ∣ b := (rho1_spec hb2).2.1
      have h1 : rho1 a = rho1 b := congrArg Sigma.fst hab
      have h2 : a / rho1 a = b / rho1 b := by
        have := congrArg Sigma.snd hab
        simpa [ψ] using this
      calc a = rho1 a * (a / rho1 a) := (Nat.mul_div_cancel' hda).symm
        _ = rho1 b * (b / rho1 b) := by rw [h2, h1]
        _ = b := Nat.mul_div_cancel' hdb
    have hstep2 : ∑ m ∈ blk ⟨k, j⟩, w m / (m : ℝ) ≤
        (4 * Real.sqrt 18 * Real.sqrt 3 * roughConst ^ 2) /
          (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) *
            Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
      have hmap_sum : ∑ m ∈ blk ⟨k, j⟩, w m / (m : ℝ) ≤
          ∑ x ∈ PairSet, (w x.1 / (x.1 : ℝ)) * (w x.2 / (x.2 : ℝ)) := by
        have heq : ∑ m ∈ blk ⟨k, j⟩, w m / (m : ℝ) =
            ∑ m ∈ blk ⟨k, j⟩, (w (ψ m).1 / ((ψ m).1 : ℝ)) * (w (ψ m).2 / ((ψ m).2 : ℝ)) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm2 : 2 ≤ m := (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
          obtain ⟨hd1, hdvd, _, _, hd'2, _, _⟩ := rho1_spec hm2
          have hmul : rho1 m * (m / rho1 m) = m := Nat.mul_div_cancel' hdvd
          have hw : w m = w (rho1 m) * w (m / rho1 m) := by
            conv_lhs => rw [← hmul]
            rw [w_mul (by omega) (by omega)]
          have hcast : (m : ℝ) = (rho1 m : ℝ) * ((m / rho1 m : ℕ) : ℝ) := by
            exact_mod_cast hmul.symm
          dsimp only [ψ]
          rw [hw, hcast]
          ring
        have himg : ∑ x ∈ (blk ⟨k, j⟩).image ψ, (w x.1 / (x.1 : ℝ)) * (w x.2 / (x.2 : ℝ)) =
            ∑ m ∈ blk ⟨k, j⟩, (w (ψ m).1 / ((ψ m).1 : ℝ)) * (w (ψ m).2 / ((ψ m).2 : ℝ)) :=
          Finset.sum_image (fun a ha b hb h => hψ_inj ha hb h)
        rw [heq, ← himg]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
          exact hψ_maps m hm
        · intro x _ _
          exact mul_nonneg (div_nonneg (w_nonneg _) (Nat.cast_nonneg _))
            (div_nonneg (w_nonneg _) (Nat.cast_nonneg _))
      calc ∑ m ∈ blk ⟨k, j⟩, w m / (m : ℝ)
          ≤ ∑ d ∈ Dset, (w d / (d : ℝ)) *
              ∑ d' ∈ (Finset.Ico (2 ^ k * d) (2 ^ (k + 1) * d)).filter (IsRough (2 ^ (k / 2))),
                w d' / (d' : ℝ) := by
            rw [Finset.sum_sigma] at hmap_sum
            refine le_trans hmap_sum (le_of_eq ?_)
            refine Finset.sum_congr rfl fun d _ => ?_
            dsimp only
            exact (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ d ∈ Dset, (w d / (d : ℝ)) *
              ((2 * Real.sqrt 18 * roughConst) /
                (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
            apply Finset.sum_le_sum
            intro d hd
            exact mul_le_mul_of_nonneg_left
              (block_d'_sum_le j k d (Finset.mem_Ico.mp hd).1)
              (div_nonneg (w_nonneg d) (Nat.cast_nonneg d))
        _ = (∑ d ∈ Dset, w d / (d : ℝ)) *
              ((2 * Real.sqrt 18 * roughConst) /
                (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ))) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ ((2 * Real.sqrt 3 * roughConst) / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
              ((2 * Real.sqrt 18 * roughConst) /
                (Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_right (block_d_sum_le j) (by positivity [roughConst_pos])
        _ = (4 * Real.sqrt 18 * Real.sqrt 3 * roughConst ^ 2) /
              (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) *
                Real.sqrt ((k + 1 : ℕ) : ℝ)) := by ring
    have hCkj_nn : 0 ≤ Ckj := by unfold Ckj; positivity [roughConst_pos]
    have hsqk : Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    calc ∑ m ∈ blk ⟨k, j⟩,
          w m * (roughConst * (N : ℝ) /
            ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m))))
        ≤ Ckj * ((4 * Real.sqrt 18 * Real.sqrt 3 * roughConst ^ 2) /
            (Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) *
              Real.sqrt ((k + 1 : ℕ) : ℝ))) :=
          le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 hCkj_nn)
      _ = (4 * (Real.sqrt 18 * Real.sqrt 18) * (Real.sqrt 3 * Real.sqrt 3) * roughConst ^ 3) *
            (N : ℝ) *
            ((1 : ℝ) / ((Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) *
              Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((k + j + 1 : ℕ) : ℝ) *
              Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
          unfold Ckj; ring
      _ = (216 * roughConst ^ 3) * (N : ℝ) *
            ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
              Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ))) := by
          rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 18),
              Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqk]
          ring
  have hpart2 :
      ∑ m ∈ Finset.Ico 2 N,
        w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
          ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r) ≤
      (8 * Real.sqrt 3 * (216 * roughConst ^ 3)) * (N : ℝ) *
        (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
    have hlogLN_le : 1 + Real.log (LN : ℝ) ≤ 1 + Real.log (3 * Real.log N) := by
      gcongr
    have hlogLN_ge1 : (1 : ℝ) ≤ 1 + Real.log (LN : ℝ) := by
      have : (0 : ℝ) ≤ Real.log (LN : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ LN))
      linarith
    have hsqrt_le : Real.sqrt (Real.log N) ≤ Real.sqrt (LN : ℝ) := Real.sqrt_le_sqrt hLN_ge
    have hquot_le :
        (1 + Real.log (LN : ℝ)) ^ 2 / Real.sqrt (LN : ℝ) ≤
        (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
      calc (1 + Real.log (LN : ℝ)) ^ 2 / Real.sqrt (LN : ℝ)
          ≤ (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (LN : ℝ) := by
            apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
            exact pow_le_pow_left₀ (by linarith) hlogLN_le 2
        _ ≤ (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
            apply div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr hlogN_pos) hsqrt_le
    calc ∑ m ∈ Finset.Ico 2 N,
            w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
              ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r)
        ≤ ∑ m ∈ M2,
            w m * (roughConst * (N : ℝ) /
              ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m)))) :=
          hpart2_reduce
      _ = ∑ kj ∈ Kset, ∑ m ∈ blk kj,
            w m * (roughConst * (N : ℝ) /
              ((m : ℝ) * Real.sqrt (L ((N - 1) / m)) * Real.sqrt (L ((m / rho1 m) / rho1 m)))) := by
          rw [hM2_eq, Finset.sum_biUnion hdisj]
      _ ≤ ∑ kj ∈ Kset,
            (216 * roughConst ^ 3) * (N : ℝ) *
              ((1 : ℝ) / (((kj.1 + 1 : ℕ) : ℝ) * Real.sqrt ((kj.2 + 1 : ℕ) : ℝ) *
                Real.sqrt ((kj.1 + kj.2 + 1 : ℕ) : ℝ) * Real.sqrt ((LN - kj.1 - 2 * kj.2 : ℕ) : ℝ))) :=
          Finset.sum_le_sum hblk_bound
      _ = (216 * roughConst ^ 3) * (N : ℝ) *
            ∑ k ∈ Finset.range LN, ∑ j ∈ Finset.range ((LN - k + 1) / 2),
              (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) *
                Real.sqrt ((k + j + 1 : ℕ) : ℝ) * Real.sqrt ((LN - k - 2 * j : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_sigma]
      _ ≤ (216 * roughConst ^ 3) * (N : ℝ) *
            ((8 * Real.sqrt 3) * (1 + Real.log (LN : ℝ)) ^ 2 / Real.sqrt (LN : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (finite_double_sum_le LN (by omega))
          positivity [roughConst_pos]
      _ ≤ (216 * roughConst ^ 3) * (N : ℝ) *
            ((8 * Real.sqrt 3) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity [roughConst_pos])
          have h1 : (8 * Real.sqrt 3) * (1 + Real.log (LN : ℝ)) ^ 2 / Real.sqrt (LN : ℝ) =
              (8 * Real.sqrt 3) * ((1 + Real.log (LN : ℝ)) ^ 2 / Real.sqrt (LN : ℝ)) := by ring
          have h2 : (8 * Real.sqrt 3) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) =
              (8 * Real.sqrt 3) * ((1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N)) := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hquot_le (by positivity)
      _ = (8 * Real.sqrt 3 * (216 * roughConst ^ 3)) * (N : ℝ) *
            (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by ring
  have hsq_ge1 : (1 : ℝ) ≤ (1 + Real.log (3 * Real.log N)) ^ 2 := by
    have hlog3_pos : 0 ≤ Real.log (3 * Real.log N) := Real.log_nonneg (by linarith)
    nlinarith
  have hpart1' : ∑ m ∈ Finset.Ico 2 N, w m ≤
      roughConst * (N : ℝ) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
    calc ∑ m ∈ Finset.Ico 2 N, w m
        ≤ roughConst * (N : ℝ) / Real.sqrt (Real.log N) := hpart1
      _ = (roughConst * (N : ℝ) / Real.sqrt (Real.log N)) * 1 := (mul_one _).symm
      _ ≤ (roughConst * (N : ℝ) / Real.sqrt (Real.log N)) * (1 + Real.log (3 * Real.log N)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_ge1 (by positivity [roughConst_pos])
      _ = roughConst * (N : ℝ) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by ring
  calc (∑ m ∈ Finset.Ico 2 N,
          ∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
            ∀ p ∈ r.primeFactors,
              m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2),
          ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r)))
      ≤ ∑ m ∈ Finset.Ico 2 N,
          (w m + w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
            ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r)) :=
        Finset.sum_le_sum hsplit_r
    _ = (∑ m ∈ Finset.Ico 2 N, w m) +
        (∑ m ∈ Finset.Ico 2 N,
          w m * (∑ r ∈ (Finset.Icc 2 ((N - 1) / m)).filter (fun r =>
            ∀ p ∈ r.primeFactors, m ≤ p * (rho1 m) ^ 2), w r)) :=
        Finset.sum_add_distrib
    _ ≤ roughConst * (N : ℝ) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) +
        (8 * Real.sqrt 3 * (216 * roughConst ^ 3)) * (N : ℝ) *
          (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) :=
        add_le_add hpart1' hpart2
    _ = totalConst * (N : ℝ) * (1 + Real.log (3 * Real.log N)) ^ 2 / Real.sqrt (Real.log N) := by
        unfold totalConst; ring

end OMA.Erdos1100H3

theorem OMA.solution : OMA.R_Erdos1100_erdos_1100_variants_normal_order_R1.H3 := by
  intro δ hδ
  rw [Filter.eventually_atTop]
  set α : ℝ := δ / 4
  have hα : 0 < α := by positivity
  have htot_pos : 0 < OMA.Erdos1100H3.totalConst := by
    unfold OMA.Erdos1100H3.totalConst
    positivity [OMA.Erdos1100H3.roughConst_pos]
  set C : ℝ := OMA.Erdos1100H3.totalConst * (1 + (3 : ℝ) ^ α / α) ^ 2
  have hC_pos : 0 < C := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max 16 (Real.exp (max 1 (C ^ (2 / δ)))))
  refine ⟨max 16 N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_left _ _) hN
  have hN_ge_exp : Real.exp (max 1 (C ^ (2 / δ))) ≤ (N : ℝ) := by
    have h1 : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hN)
    exact le_trans (le_max_right _ _) (le_trans hN₀ h1)
  set x : ℝ := Real.log (N : ℝ)
  have hx_ge_max : max 1 (C ^ (2 / δ)) ≤ x := by
    have h := Real.log_le_log (Real.exp_pos _) hN_ge_exp
    rwa [Real.log_exp] at h
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx_ge_max
  have hx0 : 0 < x := by linarith
  have hx_ge_C : C ^ (2 / δ) ≤ x := le_trans (le_max_right _ _) hx_ge_max
  have hC_le_rpow : C ≤ x ^ (δ / 2) := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hC_pos.le _) hx_ge_C (by positivity : 0 ≤ δ / 2)
    rw [← Real.rpow_mul hC_pos.le] at hpow
    have hexp1 : (2 / δ) * (δ / 2) = 1 := by field_simp
    rwa [hexp1, Real.rpow_one] at hpow
  have hlog_bound : Real.log (3 * x) ≤ ((3 : ℝ) ^ α / α) * x ^ α := by
    have h3x_pos : 0 < 3 * x := by linarith
    have h1 : Real.log ((3 * x) ^ α) ≤ (3 * x) ^ α := by
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h3x_pos α)
      linarith
    rw [Real.log_rpow h3x_pos] at h1
    have h2 : Real.log (3 * x) ≤ (3 * x) ^ α / α := (le_div_iff₀ hα).mpr (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h2
    calc Real.log (3 * x) ≤ (3 : ℝ) ^ α * x ^ α / α := h2
      _ = ((3 : ℝ) ^ α / α) * x ^ α := by ring
  have h1_le_xα : (1 : ℝ) ≤ x ^ α := Real.one_le_rpow hx1 hα.le
  have h1_add_log : 1 + Real.log (3 * x) ≤ (1 + (3 : ℝ) ^ α / α) * x ^ α := by
    linarith
  have hsq_bound : (1 + Real.log (3 * x)) ^ 2 ≤ (1 + (3 : ℝ) ^ α / α) ^ 2 * x ^ (δ / 2) := by
    have h0 : 0 ≤ 1 + Real.log (3 * x) := by
      have : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
      linarith
    have hsq := pow_le_pow_left₀ h0 h1_add_log 2
    rw [mul_pow, ← Real.rpow_natCast (x ^ α) 2, ← Real.rpow_mul hx0.le] at hsq
    have h2α : α * ((2 : ℕ) : ℝ) = δ / 2 := by unfold α; push_cast; ring
    rwa [h2α] at hsq
  have hnum_bound : OMA.Erdos1100H3.totalConst * (1 + Real.log (3 * x)) ^ 2 ≤ x ^ δ := by
    calc OMA.Erdos1100H3.totalConst * (1 + Real.log (3 * x)) ^ 2
        ≤ OMA.Erdos1100H3.totalConst * ((1 + (3 : ℝ) ^ α / α) ^ 2 * x ^ (δ / 2)) :=
          mul_le_mul_of_nonneg_left hsq_bound htot_pos.le
      _ = C * x ^ (δ / 2) := by unfold C; ring
      _ ≤ x ^ (δ / 2) * x ^ (δ / 2) :=
          mul_le_mul_of_nonneg_right hC_le_rpow (Real.rpow_nonneg hx0.le _)
      _ = x ^ δ := by
          rw [← Real.rpow_add hx0]
          congr 1; ring
  have hmain := OMA.Erdos1100H3.main_sum_bound N hN16
  calc (∑ m ∈ Finset.Ico 2 N,
          ∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
            ∀ p ∈ r.primeFactors,
              m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2),
          ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r)))
      ≤ OMA.Erdos1100H3.totalConst * (N : ℝ) * (1 + Real.log (3 * x)) ^ 2 / Real.sqrt x := hmain
    _ = (N : ℝ) * ((OMA.Erdos1100H3.totalConst * (1 + Real.log (3 * x)) ^ 2) / Real.sqrt x) := by ring
    _ ≤ (N : ℝ) * (x ^ δ / Real.sqrt x) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
        exact div_le_div_of_nonneg_right hnum_bound (Real.sqrt_nonneg x)
    _ = (N : ℝ) * x ^ (-(1 / 2 : ℝ) + δ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0]
        congr 2; ring
