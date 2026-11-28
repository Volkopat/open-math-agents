import OMAReductions.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1
import Mathlib

-- Step H3 of reduction Erdos694.erdos_694.variants.inf_unique.R1.H1.R1.
-- Proof: a Selberg upper-bound sieve for q, s q + 1, a q + 1 (library of Steven Enamakel, adapted).


/-!
Mertens' theorems.

Elementary proofs, over the reals, of the three theorems of Mertens (1874):

* `OMALib694.Mertens.abs_sum_log_div_sub_log_le` (first theorem):
  `|∑_{p ≤ x} log p / p - log x| ≤ mertens1Const + log 2` for `x ≥ 1`;
* `OMALib694.Mertens.abs_sum_inv_sub_log_log_le` (second theorem):
  `|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const` for `x ≥ 2`;
* `OMALib694.Mertens.prod_one_sub_inv_bounds` (third theorem, product form):
  `exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp mertens2Const / log z` for `z ≥ 2`;

with existential forms `mertens1`, `mertens2`, `mertens3`. Sums over primes `p ≤ x` are written
`∑ p ∈ Nat.primesLE ⌊x⌋₊`, as in `Mathlib.NumberTheory.Chebyshev`.

The first theorem follows from Legendre's formula for `log N!`, the bounds
`N log N - N ≤ log N! ≤ N log N` and Chebyshev's bound `θ(N) ≤ N log 4`. The second follows
from the first by discrete summation by parts, run as an induction on `N`. The third follows from
the second and `-t / (1 - t) ≤ log (1 - t) ≤ -t`.
-/

open scoped Classical

namespace OMALib694.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
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

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
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
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
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

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
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


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
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


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
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

/-- Running sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
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

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring


/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩

theorem log_one_sub_inv_bounds {p : ℕ} (hp : p.Prime) :
    -(1 / (p : ℝ)) - Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        Real.log (1 - 1 / (p : ℝ)) ∧
      Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 := by
      rw [div_div, div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

/-- **Mertens' third theorem**, explicit form. For real `z ≥ 2`,
`exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp (mertens2Const) / log z`
with `c = mertens2Const + primePowerConst / log 2`. -/
theorem prod_one_sub_inv_bounds (z : ℝ) (hz : 2 ≤ z) :
    Real.exp (-(mertens2Const + primePowerConst / Real.log 2)) / Real.log z ≤
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ Real.exp mertens2Const / Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    intro h; linarith
  have hPpos : 0 < ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP := Real.log_prod (s := Nat.primesLE ⌊z⌋₊) (f := fun p => (1 - 1 / (p : ℝ))) hne
  have hup : Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) ≤
      -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p := by
    rw [hlogP, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).2
  have hlo : -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p - primePowerConst / Real.log 2 ≤
      Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) := by
    rw [hlogP]
    have hK := sum_log_div_mul_sub_one_le (Nat.primesLE ⌊z⌋₊)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK' : ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        primePowerConst / Real.log 2 := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hK hl2.le
    have hs := Finset.sum_le_sum (s := Nat.primesLE ⌊z⌋₊) fun p hp =>
      (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).1
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    linarith
  have hM := abs_sum_inv_sub_log_log_le z hz
  rw [abs_le] at hM
  have hexp : ∀ t : ℝ, Real.exp t / Real.log z = Real.exp (t - Real.log (Real.log z)) := by
    intro t
    rw [Real.exp_sub, Real.exp_log hlz]
  rw [hexp, hexp, ← Real.exp_log hPpos]
  constructor
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]

/-- **Mertens' third theorem**, existential form: there are constants `0 < c₁` and `c₂` with
`c₁ / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ c₂ / log z` for all real `z ≥ 2`. -/
theorem mertens3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℝ, 2 ≤ z →
    c₁ / Real.log z ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ c₂ / Real.log z :=
  ⟨_, _, Real.exp_pos _, Real.exp_pos _, prod_one_sub_inv_bounds⟩


end OMALib694.Mertens


open scoped Classical
open Finset

namespace OMALib694.Sieve

variable {ι : Type*} [DecidableEq ι]

/-- The Selberg function `h(p) = g(p)/(1 - g(p))` attached to a local density `g`. -/
noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

/-- Selberg's normaliser `G = Σ_{S ∈ D} Π_{p ∈ S} h(p)` for a support family `D`. -/
noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

/-- The optimal Selberg weights
`λ_S = (-1)^{|S|} (Π_{p∈S} g(p)⁻¹) G⁻¹ Σ_{T ∈ D, S ⊆ T} Π_{p∈T} h(p)`. -/
noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

/-- Inclusion-exclusion over an interval `[U, T]` of the subset lattice. -/
theorem sum_interval_neg_one_pow {U T : Finset ι} (hUT : U ⊆ T) :
    ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card = if T = U then (-1) ^ U.card else 0 := by
  have h1 : ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card
      = ∑ V ∈ (T \ U).powerset, (-1 : ℝ) ^ U.card * (-1) ^ V.card := by
    refine Finset.sum_nbij' (fun S => S \ U) (fun V => U ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS ⊢
      exact sdiff_subset_sdiff hS.1 le_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hV ⊢
      refine ⟨union_subset hUT (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset, mem_coe] at hV
      have : Disjoint U V := by
        rw [disjoint_iff_ne]; intro a ha b hb hab; subst hab
        have := hV hb; simp at this; exact this.2 ha
      exact union_sdiff_cancel_left this
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      rw [← pow_add, add_comm, card_sdiff_add_card_eq_card hS.2]
  have h2 : ∑ V ∈ (T \ U).powerset, ((-1 : ℝ)) ^ V.card = if T \ U = ∅ then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := T \ U))
    push_cast at this
    rw [this]
  rw [h1, ← mul_sum, h2]
  have : T \ U = ∅ ↔ T = U := by
    constructor
    · intro h; exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h) hUT
    · intro h; subst h; simp
  by_cases hT : T = U
  · simp [hT]
  · rw [if_neg (by rwa [this]), if_neg hT, mul_zero]

section Abstract

variable {Q : Finset ι} {g : ι → ℝ} {D : Finset (Finset ι)}

theorem hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {p : ι} (hp : p ∈ Q) :
    0 < hFun g p := div_pos (hg0 p hp) (by linarith [hg1 p hp])

theorem prod_hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S : Finset ι}
    (hS : S ⊆ Q) : 0 < ∏ p ∈ S, hFun g p :=
  prod_pos fun p hp => hFun_pos hg0 hg1 (hS hp)

/-- `G ≥ 1`, since the empty set contributes `1`. -/
theorem one_le_selbergG (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : 1 ≤ selbergG g D := by
  unfold selbergG
  have := single_le_sum (f := fun S => ∏ p ∈ S, hFun g p)
    (fun S hS => (prod_hFun_pos hg0 hg1 (hDQ S hS)).le) hemp
  simpa using this

theorem selbergWeight_mul_prod (hg0 : ∀ p ∈ Q, 0 < g p) {S : Finset ι} (hS : S ⊆ Q) :
    selbergWeight g D S * ∏ p ∈ S, g p
      = (-1) ^ S.card / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p := by
  unfold selbergWeight
  have h : (∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp => inv_mul_cancel₀ (hg0 p (hS hp)).ne'
  calc _ = (-1) ^ S.card / selbergG g D * (∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p) *
        ((∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p) := by ring
    _ = _ := by rw [h, mul_one]

/-- The diagonalising variables `y_U = Σ_{S ∈ D, U ⊆ S} λ_S g(S)` of the Selberg weights. -/
theorem selbergY (hg0 : ∀ p ∈ Q, 0 < g p) (hDQ : ∀ S ∈ D, S ⊆ Q)
    (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (U : Finset ι) :
    ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / selbergG g D else 0 := by
  set G := selbergG g D
  set hS : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have e1 : ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = ∑ S ∈ D, ∑ T ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun S hSD => ?_
    by_cases hU : U ⊆ S
    · rw [if_pos hU, selbergWeight_mul_prod hg0 (hDQ S hSD), mul_sum, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      by_cases hST : S ⊆ T <;> simp [hU, hST, hS, G]
    · rw [if_neg hU]; symm
      exact sum_eq_zero fun T _ => by simp [hU]
  rw [e1, sum_comm]
  have e2 : ∀ T ∈ D, (∑ S ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0)
      = if T = U then (-1) ^ U.card / G * hS U else 0 := by
    intro T hT
    rw [← sum_filter]
    by_cases hUT : U ⊆ T
    · have hf : D.filter (fun S => U ⊆ S ∧ S ⊆ T) = T.powerset.filter (fun S => U ⊆ S) := by
        ext S; simp only [mem_filter, mem_powerset]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩; exact ⟨hdown T hT S h2, h1, h2⟩
      rw [hf, ← sum_mul, ← sum_div, sum_interval_neg_one_pow hUT]
      by_cases hTU : T = U
      · subst hTU; simp
      · simp [hTU]
    · have hTU : T ≠ U := by rintro rfl; exact hUT le_rfl
      rw [if_neg hTU]
      refine sum_eq_zero fun S hS' => ?_
      simp only [mem_filter] at hS'
      exact absurd (hS'.2.1.trans hS'.2.2) hUT
  rw [sum_congr rfl e2, sum_ite_eq']
  split_ifs <;> ring

theorem prod_union_eq (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S₁ S₂ : Finset ι}
    (h₁ : S₁ ⊆ Q) (h₂ : S₂ ⊆ Q) :
    ∏ p ∈ S₁ ∪ S₂, g p = (∏ p ∈ S₁, g p) * (∏ p ∈ S₂, g p) *
      ∑ U ∈ Q.powerset, if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0 := by
  have hinv : (∏ p ∈ S₁ ∩ S₂, g p)⁻¹ = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← prod_inv_distrib]
    have : ∀ p ∈ S₁ ∩ S₂, (g p)⁻¹ = 1 + (hFun g p)⁻¹ := by
      intro p hp
      have hp' : p ∈ Q := h₁ (mem_inter.mp hp).1
      have a := hg0 p hp'; have b := hg1 p hp'
      unfold hFun; rw [inv_div]; field_simp; ring
    rw [prod_congr rfl this, prod_one_add]
    exact sum_congr rfl fun U _ => by rw [prod_inv_distrib]
  have hsum : ∑ U ∈ Q.powerset, (if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0)
      = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_filter, mem_powerset, subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans h₁, h⟩
  have hne : (∏ p ∈ S₁ ∩ S₂, g p) ≠ 0 :=
    (prod_pos fun p hp => hg0 p (h₁ (mem_inter.mp hp).1)).ne'
  rw [hsum, ← hinv, ← prod_union_inter (s₁ := S₁) (s₂ := S₂)]
  field_simp

/-- The Selberg quadratic form evaluated at the optimal weights equals `1 / G`. -/
theorem selberg_mainTerm (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D) :
    ∑ S₁ ∈ D, ∑ S₂ ∈ D, selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
      = 1 / selbergG g D := by
  set G := selbergG g D with hG
  set a : Finset ι → ℝ := fun S => selbergWeight g D S * ∏ p ∈ S, g p
  set w : Finset ι → ℝ := fun U => (∏ p ∈ U, hFun g p)⁻¹
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have e1 : ∀ S₁ ∈ D, ∀ S₂ ∈ D,
      selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
        = ∑ U ∈ Q.powerset, w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0)) := by
    intro S₁ h₁ S₂ h₂
    rw [prod_union_eq hg0 hg1 (hDQ _ h₁) (hDQ _ h₂), mul_sum, mul_sum]
    refine sum_congr rfl fun U _ => ?_
    by_cases u1 : U ⊆ S₁ <;> by_cases u2 : U ⊆ S₂ <;> simp [u1, u2, a, w] <;> ring
  rw [sum_congr rfl fun S₁ h₁ => sum_congr rfl fun S₂ h₂ => e1 S₁ h₁ S₂ h₂]
  have eswap : ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∑ U ∈ Q.powerset,
      w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0))
      = ∑ U ∈ Q.powerset, w U * ((∑ S ∈ D with U ⊆ S, a S) * (∑ S ∈ D with U ⊆ S, a S)) := by
    simp_rw [sum_filter, sum_mul_sum, mul_sum]
    conv_lhs => arg 2; ext S₁; rw [sum_comm]
    rw [sum_comm]
  rw [eswap]
  have hy : ∀ U, ∑ S ∈ D with U ⊆ S, a S
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0 :=
    selbergY hg0 hDQ hdown
  simp_rw [hy]
  have e3 : ∀ U ∈ Q.powerset, w U * ((if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0) *
      (if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0))
      = if U ∈ D then (∏ p ∈ U, hFun g p) / G ^ 2 else 0 := by
    intro U hU
    split_ifs with hUD
    · have hpos := prod_hFun_pos hg0 hg1 (hDQ U hUD)
      simp only [w]
      field_simp
      rw [← pow_mul, mul_comm (U.card) 2, pow_mul]; simp
    · simp
  rw [sum_congr rfl e3, ← sum_filter]
  have : Q.powerset.filter (fun U => U ∈ D) = D := by
    ext U; simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hDQ U h, h⟩⟩
  rw [this, ← sum_div]
  change G / G ^ 2 = 1 / G
  field_simp

/-- The optimal Selberg weights satisfy `|λ_S| ≤ 1`. -/
theorem abs_selbergWeight_le (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    {S : Finset ι} (hS : S ∈ D) : |selbergWeight g D S| ≤ 1 := by
  set G := selbergG g D with hG
  set hp : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have hSQ := hDQ S hS
  have hnn : ∀ T ⊆ Q, 0 ≤ hp T := fun T hT => (prod_hFun_pos hg0 hg1 hT).le
  have hginv : 0 < ∏ p ∈ S, (g p)⁻¹ := prod_pos fun p h => inv_pos.mpr (hg0 p (hSQ h))
  have habs : |selbergWeight g D S|
      = (∏ p ∈ S, (g p)⁻¹) * (∑ T ∈ D with S ⊆ T, hp T) / G := by
    unfold selbergWeight
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hginv, abs_of_pos (by linarith : (0:ℝ) < G),
      abs_of_nonneg (sum_nonneg fun T hT => hnn T (hDQ T (mem_filter.mp hT).1))]
    ring
  rw [habs, div_le_one (by linarith)]
  have key : ∀ T ∈ D.filter (fun T => S ⊆ T),
      (∏ p ∈ S, (g p)⁻¹) * hp T = ∑ W ∈ S.powerset, hp (W ∪ (T \ S)) := by
    intro T hT
    have hST := (mem_filter.mp hT).2
    have h1 : hp T = hp S * hp (T \ S) := by
      simp only [hp]; rw [mul_comm, prod_sdiff hST]
    have h2 : (∏ p ∈ S, (g p)⁻¹) * hp S = ∏ p ∈ S, (1 + hFun g p) := by
      simp only [hp]; rw [← prod_mul_distrib]
      refine prod_congr rfl fun p h => ?_
      have a := hg0 p (hSQ h); have b := hg1 p (hSQ h)
      have c : 1 - g p ≠ 0 := by linarith
      unfold hFun; field_simp; ring
    rw [h1, ← mul_assoc, h2, prod_one_add, sum_mul]
    refine sum_congr rfl fun W hW => ?_
    simp only [hp]
    rw [prod_union]
    exact disjoint_of_subset_left (mem_powerset.mp hW) disjoint_sdiff
  rw [mul_sum, sum_congr rfl key, sum_comm, ← sum_product']
  rw [← sum_image (s := S.powerset ×ˢ D.filter (fun T => S ⊆ T)) (g := fun x => x.1 ∪ (x.2 \ S))
    (f := hp)]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      simp only [mem_image, mem_product, mem_powerset, mem_filter] at hU
      obtain ⟨⟨W, T⟩, ⟨hW, hT, _⟩, rfl⟩ := hU
      exact hdown T hT _ (union_subset (hW.trans (by assumption)) sdiff_subset)
    · intro U hU _
      exact hnn U (hDQ U hU)
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powerset, mem_filter] at hx hy
    simp only at hxy
    have e1 : x.1 = (x.1 ∪ (x.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hx.1]
    have e2 : y.1 = (y.1 ∪ (y.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hy.1]
    have f1 : x.2 = S ∪ (x.1 ∪ (x.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hx.1, union_sdiff_of_subset hx.2.2]
    have f2 : y.2 = S ∪ (y.1 ∪ (y.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hy.1, union_sdiff_of_subset hy.2.2]
    exact Prod.ext (by rw [e1, e2, hxy]) (by rw [f1, f2, hxy])

theorem selbergWeight_empty (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : selbergWeight g D ∅ = 1 := by
  have hG1 : 1 ≤ selbergG g D := one_le_selbergG hg0 hg1 hDQ hemp
  unfold selbergWeight
  simp only [card_empty, pow_zero, prod_empty, one_mul, empty_subset, filter_true_of_mem,
    implies_true]
  change 1 / selbergG g D * selbergG g D = 1
  field_simp

/-- **Selberg's upper-bound sieve, abstract form.**

`A` is a finite family of objects, `E a` is the set of primes dividing `a`, `Q` is the finite
set of sieving primes, and `D` is any down-closed family of subsets of `Q` containing `∅` (the
support of the Selberg weights; for the classical sieve, the sets of primes with product `< z`).
If for every `S ⊆ Q` the number of `a` divisible by all of `S` is `X * Π_{p∈S} g p + r S`, with
`0 < g p < 1`, then the number of `a` free of all primes of `Q` is at most
`X / G + Σ_{S₁, S₂ ∈ D} |r (S₁ ∪ S₂)|`, where `G = selbergG g D`. -/
theorem selberg_sieve_abstract {α : Type*} (A : Finset α) (E : α → Finset ι)
    (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    (X : ℝ) (r : Finset ι → ℝ)
    (hr : ∀ S ⊆ Q, ((A.filter (fun a => S ⊆ E a)).card : ℝ) = X * ∏ p ∈ S, g p + r S) :
    ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
  set lam := selbergWeight g D
  have step1 : ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2 := by
    rw [card_filter]; push_cast
    refine sum_le_sum fun a _ => ?_
    split_ifs with hd
    · have : (∑ S ∈ D, if S ⊆ E a then lam S else 0) = lam ∅ := by
        have e := sum_ite_eq' D ∅ lam
        rw [if_pos hemp] at e
        rw [← e]
        refine sum_congr rfl fun S hS => ?_
        by_cases hS0 : S = ∅
        · subst hS0; simp
        · have : ¬ S ⊆ E a := by
            intro h
            apply hS0
            exact subset_empty.mp fun x hx =>
              (disjoint_left.mp hd (hDQ S hS hx) (h hx)).elim
          simp [this, hS0, Ne.symm hS0]
      have e1 : lam ∅ = 1 := selbergWeight_empty hg0 hg1 hDQ hemp
      rw [this, e1]; norm_num
    · positivity
  have step2 : ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2
      = ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ) := by
    simp_rw [sq, sum_mul_sum, card_filter]
    push_cast
    rw [sum_comm]
    refine sum_congr rfl fun S₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : S₁ ⊆ E a <;> by_cases h2 : S₂ ⊆ E a <;> simp [h1, h2, union_subset_iff]
  have step3 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ)
      = X * (∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * ∏ p ∈ S₁ ∪ S₂, g p)
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₁ h₁ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₂ h₂ => ?_
    rw [hr _ (union_subset (hDQ _ h₁) (hDQ _ h₂))]; ring
  have step4 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂)
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have a1 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₁
    have a2 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₂
    calc lam S₁ * lam S₂ * r (S₁ ∪ S₂) ≤ |lam S₁ * lam S₂ * r (S₁ ∪ S₂)| := le_abs_self _
      _ = |lam S₁| * |lam S₂| * |r (S₁ ∪ S₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |r (S₁ ∪ S₂)| := by gcongr
      _ = _ := by ring
  rw [selberg_mainTerm hg0 hg1 hDQ hdown hemp] at step3
  calc _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
      rw [mul_one_div]; linarith

end Abstract

/-! ## Counting residue conditions -/


theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2 <;> (ext; simp)
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/-! ## Selberg's sieve for residue conditions -/

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

/-- The classical Selberg support: sets of primes from `Q` whose product is `< z`. -/
noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

/-- **Selberg's sieve for residue conditions.** For each prime `p ∈ Q` let `C p` be a
`p`-periodic condition on `ℕ` holding for `ω(p)` residues, with `0 < ω(p) < p`. Then the number
of `n < N` satisfying no condition `C p`, `p ∈ Q`, is at most
`N / G + Σ_{S₁,S₂ ∈ D} Π_{p ∈ S₁ ∪ S₂} ω(p)`, with `G = selbergG (ω/p) D`, for any down-closed
support family `D ∋ ∅` of subsets of `Q`. -/
theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast (hQ p hp).pos)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    simp only [g]; rw [div_lt_one this]; exact_mod_cast hω1 p hp
  set E : ℕ → Finset ℕ := fun n => Q.filter (fun p => C p n)
  set r : Finset ℕ → ℝ := fun S =>
    (((range N).filter (fun n => S ⊆ E n)).card : ℝ) - N * ∏ p ∈ S, g p
  have key := selberg_sieve_abstract (range N) E hg0 hg1 hDQ hdown hemp (N : ℝ) r
    (fun S _ => by simp only [r]; rw [add_sub_cancel])
  have hrem : ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)|
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset (hDQ _ h₁) (hDQ _ h₂)
    have hc : ((range N).filter (fun n => S₁ ∪ S₂ ⊆ E n)).card
        = ((range N).filter (fun n => ∀ p ∈ S₁ ∪ S₂, C p n)).card := by
      congr 1; ext n
      simp only [E, mem_filter, subset_iff]
      exact ⟨fun h => ⟨h.1, fun p hp => (h.2 hp).2⟩, fun h => ⟨h.1, fun p hp => ⟨hSQ hp, h.2 p hp⟩⟩⟩
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp)) N
    simp only [r]; rw [hc]
    exact this
  have k2 := key.trans (add_le_add le_rfl hrem)
  have hc : ((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card
      = ((range N).filter (fun n => Disjoint Q (E n))).card := by
    congr 1; ext n
    simp only [E, disjoint_left, mem_filter, not_and]
    exact ⟨fun h => ⟨h.1, fun p hp _ => h.2 p hp⟩, fun h => ⟨h.1, fun p hp => h.2 hp hp⟩⟩
  have hc' : (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      = (((range N).filter (fun n => Disjoint Q (E n))).card : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  exact k2

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => (hQ p (hS.1 hp)).one_lt.le

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

/-- **Selberg's sieve at level `z`, with a crude explicit remainder.** With the classical support
`levelFamily Q z` (products of primes `< z`), the number of `n < N` meeting no condition `C p`,
`p ∈ Q`, is at most `N / G + z ^ 4`. -/
theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have key := selberg_residue N Q hQ C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
    (levelFamily_down hQ) (empty_mem_levelFamily hz)
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ S₁ ∈ levelFamily Q z, ∀ S₂ ∈ levelFamily Q z,
      ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ (z : ℝ) ^ 2 := by
    intro S₁ h₁ S₂ h₂
    have h₁' := h₁; have h₂' := h₂
    simp only [levelFamily, mem_filter, mem_powerset] at h₁' h₂'
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset h₁'.1 h₂'.1
    have a : ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ ∏ p ∈ S₁ ∪ S₂, (p : ℝ) :=
      prod_le_prod (fun p _ => by positivity)
        (fun p hp => by exact_mod_cast (hω1 p (hSQ hp)).le)
    have b : ∏ p ∈ S₁ ∪ S₂, p ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
      rw [← prod_union_inter]
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hQ p (h₁'.1 (mem_inter.mp hp).1)).pos)
    have c : (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ≤ z * z :=
      Nat.mul_le_mul h₁'.2.le h₂'.2.le
    have : ((∏ p ∈ S₁ ∪ S₂, p : ℕ) : ℝ) ≤ (z : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast b.trans c
    push_cast at this
    linarith
  calc ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ)
      ≤ ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, (z : ℝ) ^ 2 :=
        sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => hterm S₁ h₁ S₂ h₂
    _ = ((levelFamily Q z).card : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

/-- `selbergG` only depends on `g` on the primes of `Q`. -/
theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]

/-! ## Prime pairs `p, p + d` -/

/-- The number of residues removed modulo `p` in the prime-pair sieve:
`1` if `p ∣ d`, otherwise `2`. -/
def pairOmega (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

/-- Selberg's `G(z)` for the prime-pair sieve with difference `d`:
`G_d(z) = Σ_{m < z, m ∣ P(z)} Π_{p ∣ m} ω_d(p)/(p - ω_d(p))`, written over sets of primes
`< z` with product `< z`. -/
noncomputable def pairG (d z : ℕ) : ℝ :=
  selbergG (fun p => (pairOmega d p : ℝ) / p) (levelFamily (Nat.primesBelow z) z)

theorem pairOmega_pos (d p : ℕ) : 0 < pairOmega d p := by
  unfold pairOmega; split_ifs <;> norm_num

theorem pairOmega_lt {d p : ℕ} (hd : Even d) (hp : p.Prime) : pairOmega d p < p := by
  unfold pairOmega
  split_ifs with h
  · exact hp.one_lt
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have := hp.two_le; omega

/-- The singular-series factor `Π_{p ∣ d, p > 2} (1 + 1/p)` of the prime-pair bound. -/
noncomputable def pairSingularProduct (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors with 2 < p, (1 + 1 / (p : ℝ))

theorem one_le_pairSingularProduct (d : ℕ) : 1 ≤ pairSingularProduct d := by
  unfold pairSingularProduct
  have := prod_le_prod (s := d.primeFactors.filter (fun p => 2 < p)) (f := fun _ : ℕ => (1 : ℝ))
    (g := fun p : ℕ => 1 + 1 / (p : ℝ)) (fun _ _ => zero_le_one)
    (fun p _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  simpa using this

/-- **Mertens-type input for the prime-pair sieve** (an explicit hypothesis, to be discharged
by a Mertens library): `c log² z ≤ G_d(z) · Π_{p ∣ d, p > 2} (1 + 1/p)` for all even `d > 0`
and all `z ≥ 2`. Classically this holds for some absolute `c > 0`. -/
def PairGLowerBound (c : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → Even d → ∀ z : ℕ, 2 ≤ z →
    c * Real.log z ^ 2 ≤ pairG d z * pairSingularProduct d

/-! ## Brun–Titchmarsh -/

/-! ## A lower bound for `G` (Rankin's trick) -/

/-- **Rankin lower bound for Selberg's `G`.** If `Q ⊆ Qbig` consists of primes and `h ≥ 0`
on `Qbig`, then for every `ε ≥ 0`,
`Π_{p∈Q} (1 + h p) - z^{-ε} Π_{p∈Q} (1 + h p · p^ε) ≤ G` (support `levelFamily Qbig z`). -/
theorem selbergG_ge_rankin (g : ℕ → ℝ) (Q Qbig : Finset ℕ) (hQQ : Q ⊆ Qbig)
    (hQ : ∀ p ∈ Q, p.Prime) (hh : ∀ p ∈ Qbig, 0 ≤ hFun g p) (z : ℕ) (hz : 1 ≤ z)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∏ p ∈ Q, (1 + hFun g p) - (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + hFun g p * (p : ℝ) ^ ε)
      ≤ selbergG g (levelFamily Qbig z) := by
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hnn : ∀ S ∈ Q.powerset, 0 ≤ ∏ p ∈ S, hFun g p := fun S hS =>
    prod_nonneg fun p hp => hh p (hQQ (mem_powerset.mp hS hp))
  rw [prod_one_add, prod_one_add]
  rw [← sum_filter_add_sum_filter_not Q.powerset (fun S => ∏ p ∈ S, p < z)]
  have h1 : ∑ S ∈ Q.powerset with ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ selbergG g (levelFamily Qbig z) := by
    unfold selbergG
    apply sum_le_sum_of_subset_of_nonneg
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      simp only [levelFamily, mem_filter, mem_powerset]
      exact ⟨hS.1.trans hQQ, hS.2⟩
    · intro S hS _
      simp only [levelFamily, mem_filter, mem_powerset] at hS
      exact prod_nonneg fun p hp => hh p (hS.1 hp)
  have h2 : ∑ S ∈ Q.powerset with ¬ ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ (z : ℝ) ^ (-ε) * ∑ S ∈ Q.powerset, ∏ p ∈ S, hFun g p * (p : ℝ) ^ ε := by
    rw [mul_sum]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset (fun S : Finset ℕ => ¬ ∏ p ∈ S, p < z) Q.powerset) ?_).trans' ?_
    · intro S hS _
      have := hnn S hS
      rw [prod_mul_distrib]
      exact mul_nonneg (Real.rpow_nonneg hz0.le _)
        (mul_nonneg this (prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _))
    · refine sum_le_sum fun S hS => ?_
      simp only [mem_filter, not_lt] at hS
      have hpos := hnn S hS.1
      rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      have hge : (z : ℝ) ^ ε ≤ (∏ p ∈ S, (p : ℝ)) ^ ε := by
        apply Real.rpow_le_rpow hz0.le _ hε
        have := hS.2
        rw [← Nat.cast_prod]; exact_mod_cast this
      have hzz : (z : ℝ) ^ (-ε) * (z : ℝ) ^ ε = 1 := by
        rw [Real.rpow_neg hz0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hz0 ε).ne']
      have : 1 ≤ (z : ℝ) ^ (-ε) * (∏ p ∈ S, (p : ℝ)) ^ ε := by
        rw [← hzz]
        exact mul_le_mul_of_nonneg_left hge (Real.rpow_nonneg hz0.le _)
      nlinarith
  linarith

/-- Weierstrass product inequality: `Π (1 - a i) ≥ 1 - Σ a i` for `0 ≤ a i ≤ 1`. -/
theorem one_sub_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have a0 := h0 j (mem_insert_self j s); have a1 := h1 j (mem_insert_self j s)
    have hP : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

theorem sum_Icc_three_inv_sq_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `Π_{p ∣ d, p > 2} (1 - 1/p) · Π_{p ∣ d, p > 2} (1 + 1/p) ≥ 1/2`. -/
theorem prod_odd_one_sub_mul_ge (d : ℕ) (hd : 0 < d) :
    1 / 2 ≤ (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
  unfold pairSingularProduct
  set T := d.primeFactors.filter (fun p => 2 < p)
  rw [← prod_mul_distrib]
  have e : ∀ p ∈ T, (1 - 1 / (p : ℝ)) * (1 + 1 / p) = 1 - 1 / (p : ℝ) ^ 2 := by
    intro p _; ring
  rw [prod_congr rfl e]
  have hT : ∀ p ∈ T, 3 ≤ p := fun p hp => (mem_filter.mp hp).2
  refine le_trans ?_ (one_sub_sum_le_prod T _ (fun p _ => by positivity) (fun p hp => by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hT p hp
    rw [div_le_one (by positivity)]; nlinarith))
  have hsub : T ⊆ Icc 3 d := fun p hp => by
    have h1 := hT p hp
    have h2 : p ≤ d := Nat.le_of_dvd hd (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
    exact mem_Icc.mpr ⟨h1, h2⟩
  have hle : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ n ∈ Icc 3 d, (1 : ℝ) / (n : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rcases lt_or_ge d 2 with h | h
  · have : T = ∅ := by
      ext p; simp only [notMem_empty, iff_false]; intro hp
      have := hsub hp; simp at this; omega
    simp [this]; norm_num
  · have := sum_Icc_three_inv_sq_le d h
    have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
    linarith

theorem pair_hFun (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p
      = (pairOmega d p : ℝ) / ((p : ℝ) - pairOmega d p) := by
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold hFun
  have : (p : ℝ) - pairOmega d p ≠ 0 := by linarith
  field_simp

theorem pair_hFun_nonneg (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    0 ≤ hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem pair_hFun_le (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p ≤ 6 / p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold pairOmega
  split_ifs with h
  · push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

theorem pair_one_add_hFun_ge (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1)
      ≤ 1 + hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div]
  unfold pairOmega
  split_ifs with h
  · push_cast
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; nlinarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [mul_one, div_pow, div_le_iff₀ (by nlinarith)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    rw [show (1 : ℝ) + 2 / ((p : ℝ) - 2) = p / ((p : ℝ) - 2) by field_simp; ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Rankin step for the prime-pair sieve: with `Y ≤ z^{1/37}`, `G_d(z) ≥ ½ Π_{p ≤ Y} (1 + h(p))`. -/
theorem pair_rankin_half (d z Y : ℕ) (hd : Even d) (hY3 : 3 ≤ Y) (hYz : Y < z)
    (hlYup : Real.log Y ≤ Real.log z / 37)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4) :
    (1 / 2) * ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p)
      ≤ pairG d z := by
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)

  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hQQ : Q ⊆ Nat.primesBelow z := fun p hp => by
    have := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, this.2⟩
  set ε : ℝ := 1 / Real.log Y
  have hε : 0 ≤ ε := by positivity
  have hrank := selbergG_ge_rankin g Q (Nat.primesBelow z) hQQ hQp
    (fun p hp => pair_hFun_nonneg d hd (Nat.mem_primesBelow.mp hp).2) z (by omega) hε
  change _ ≤ pairG d z at hrank
  set H : ℕ → ℝ := fun p => hFun g p
  have hH0 : ∀ p ∈ Q, 0 ≤ H p := fun p hp => pair_hFun_nonneg d hd (hQp p hp)
  -- the Rankin tail
  have hpe : ∀ p ∈ Q, (p : ℝ) ^ ε - 1 ≤ 2 * (Real.log p / Real.log Y) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlpY : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by linarith) (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
    have ht : |Real.log p * ε| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simp only [ε]; rw [mul_one_div, div_le_one hlY]; exact hlpY
    rw [Real.rpow_def_of_pos (by linarith)]
    have := (abs_le.mp (Real.abs_exp_sub_one_le ht)).2
    rw [abs_of_nonneg (by positivity)] at this
    have e : Real.log p * ε = Real.log p / Real.log Y := by simp only [ε]; ring
    rw [← e]; exact this
  have hsumtail : ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1) ≤ 36 := by
    calc ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)
        ≤ ∑ p ∈ Q, (6 / (p : ℝ)) * (2 * (Real.log p / Real.log Y)) := by
          refine sum_le_sum fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have : (0 : ℝ) ≤ (p : ℝ) ^ ε - 1 := by
            have := Real.one_le_rpow hp1 hε; linarith
          exact mul_le_mul (pair_hFun_le d hd (hQp p hp)) (hpe p hp) this (by positivity)
      _ = (12 / Real.log Y) * ∑ p ∈ Q, Real.log p / p := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      _ ≤ (12 / Real.log Y) * (Real.log Y + Real.log 4) :=
          mul_le_mul_of_nonneg_left (hM1 Y) (by positivity)
      _ ≤ 36 := by
          have h4 : Real.log 4 ≤ 2 * Real.log Y := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
            linarith
          rw [div_mul_eq_mul_div, div_le_iff₀ hlY]; nlinarith
  have hprod_tail : ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 := by
    calc ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ ∏ p ∈ Q, ((1 + H p) * Real.exp (H p * ((p : ℝ) ^ ε - 1))) := by
          refine prod_le_prod (fun p hp => by
            have := hH0 p hp; positivity) fun p hp => ?_
          have h0 := hH0 p hp
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have hb : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε
          have := Real.add_one_le_exp (H p * ((p : ℝ) ^ ε - 1))
          nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ (p : ℝ) ^ ε - 1)]
      _ = (∏ p ∈ Q, (1 + H p)) * Real.exp (∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)) := by
          rw [prod_mul_distrib, Real.exp_sum]
      _ ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsumtail)
            (prod_nonneg fun p hp => by have := hH0 p hp; linarith)
  have hzeps : (z : ℝ) ^ (-ε) ≤ Real.exp (-37) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    simp only [ε]
    rw [mul_neg, mul_one_div, neg_le_neg_iff, le_div_iff₀ hlY]; linarith
  have hP0 : 0 ≤ ∏ p ∈ Q, (1 + H p) := prod_nonneg fun p hp => by have := hH0 p hp; linarith
  have hhalf : (1 / 2) * ∏ p ∈ Q, (1 + H p) ≤ pairG d z := by
    have he : Real.exp (-37) * Real.exp 36 ≤ 1 / 2 := by
      rw [← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    have ht : (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := by
      calc (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
          ≤ Real.exp (-37) * ((∏ p ∈ Q, (1 + H p)) * Real.exp 36) :=
            mul_le_mul hzeps hprod_tail (prod_nonneg fun p hp => by
              have := hH0 p hp; positivity) (Real.exp_pos _).le
        _ = (Real.exp (-37) * Real.exp 36) * ∏ p ∈ Q, (1 + H p) := by ring
        _ ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := mul_le_mul_of_nonneg_right he hP0
    linarith
  exact hhalf

/-- Euler-product lower bound: `Π_{p ≤ Y} (1 + h(p)) ≥ (Π_{p ≤ Y} (1 - 1/p))⁻² Π_{p ∣ d} (1 - 1/p)`. -/
theorem pair_euler_ge (d Y : ℕ) (hd0 : 0 < d) (hd : Even d) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p) := by
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun (fun p => (pairOmega d p : ℝ) / p) p

  -- Mertens lower bound for the Euler product
  have hE : ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Q, (1 + H p) := by
    have hf : ∀ p ∈ Q, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have step1 : ∏ p ∈ Q, ((1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1))
        ≤ ∏ p ∈ Q, (1 + H p) :=
      prod_le_prod (fun p hp => by
        have := hf p hp
        split_ifs <;> positivity) fun p hp => pair_one_add_hFun_ge d hd (hQp p hp)
    rw [prod_mul_distrib, prod_pow, prod_inv_distrib] at step1
    refine le_trans ?_ step1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← prod_filter]
    have hsub : Q.filter (fun p => p ∣ d) ⊆ d.primeFactors := fun p hp => by
      simp only [mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hQp p hp.1, hp.2, hd0.ne'⟩
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ p ∈ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) :=
      prod_nonneg fun p hp => hf p (mem_filter.mp hp).1
    have h1 : ∏ p ∈ d.primeFactors \ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) ≤ 1 := by
      refine prod_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    nlinarith
  exact hE

/-- **Discharging `PairGLowerBound` from Mertens' theorems.** The inputs are Mertens' first
theorem (upper half) and the upper half of Mertens' product theorem, in exactly the form proved
in `OMALib694.Mertens` (`sum_log_div_le_nat`, `prod_one_sub_inv_bounds`). -/
theorem pairGLowerBound_of_mertens {M : ℝ} (hM : 0 < M)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4)
    (hM3 : ∀ N : ℕ, 2 ≤ N → ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) ≤ M / Real.log N) :
    PairGLowerBound (min (1 / 2700) (1 / (43808 * M ^ 2))) := by
  intro d hd0 hd z hz
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hgQ0 : ∀ p ∈ Nat.primesBelow z, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast pairOmega_pos d p)
      (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos)
  have hgQ1 : ∀ p ∈ Nat.primesBelow z, g p < 1 := fun p hp => by
    have hp' := (Nat.mem_primesBelow.mp hp).2
    simp only [g]; rw [div_lt_one (by exact_mod_cast hp'.pos)]; exact_mod_cast pairOmega_lt hd hp'
  have hG1 : 1 ≤ pairG d z :=
    one_le_selbergG hgQ0 hgQ1 levelFamily_subset (empty_mem_levelFamily hz)
  have hPP := one_le_pairSingularProduct d
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin1 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / 2700 := min_le_left _ _
  have hmin2 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / (43808 * M ^ 2) := min_le_right _ _
  have hmin0 : 0 < min (1 / 2700) (1 / (43808 * M ^ 2)) := lt_min (by norm_num) (by positivity)
  set c := min (1 / 2700) (1 / (43808 * M ^ 2))
  have hGP : 1 ≤ pairG d z * pairSingularProduct d := by nlinarith
  by_cases hbig : 74 * Real.log 2 ≤ Real.log z
  swap
  · push_neg at hbig
    have : Real.log z ^ 2 ≤ 2700 := by nlinarith
    calc c * Real.log z ^ 2 ≤ (1 / 2700) * 2700 := by
          apply mul_le_mul hmin1 this (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
      _ ≤ _ := hGP
  -- large z
  set y : ℝ := (z : ℝ) ^ ((1 : ℝ) / 37) with hydef
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hlogy : Real.log y = Real.log z / 37 := by
    rw [hydef, Real.log_rpow (by linarith)]; ring
  have hy4 : Real.log 4 ≤ Real.log y := by
    rw [hlogy, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hy4' : 4 ≤ y := by
    have := Real.exp_le_exp.mpr hy4
    rwa [Real.exp_log (by norm_num), Real.exp_log hy0] at this
  set Y := ⌊y⌋₊
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hYgt : y < Y + 1 := Nat.lt_floor_add_one y
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) < Y := by linarith
    exact_mod_cast this.le
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlYup : Real.log Y ≤ Real.log z / 37 := by
    rw [← hlogy]; exact Real.log_le_log (by linarith) hYle
  have hlYlo : Real.log z / 74 ≤ Real.log Y := by
    have h1 : Real.log (y / 2) ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div hy0.ne' (by norm_num), hlogy] at h1
    linarith
  have hYz : Y < z := by
    have h1 : Real.log Y < Real.log z := by linarith
    have := (Real.log_lt_log_iff (by linarith) (by linarith)).mp h1
    exact_mod_cast this
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun g p
  have hhalf := pair_rankin_half d z Y hd hY3 hYz hlYup hM1
  have hE := pair_euler_ge d Y hd0 hd
  have hM3Y := hM3 Y (by omega)
  have hQpos : 0 < ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hinv : Real.log Y / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hQpos, inv_div]; exact hM3Y
  -- the factor at the primes dividing d
  have h2d : 2 ∈ d.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, even_iff_two_dvd.mp hd, hd0.ne'⟩
  have hsplit2 : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      = (1 / 2) * ∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ)) := by
    have : d.primeFactors.filter (fun p => 2 < p) = d.primeFactors.erase 2 := by
      ext p; simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, by have := (Nat.prime_of_mem_primeFactors h2).two_le; omega⟩
    rw [this, ← mul_prod_erase _ _ h2d]; norm_num
  have hodd := prod_odd_one_sub_mul_ge d hd0
  have hD : 1 / 4 ≤ (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
    rw [hsplit2]
    have : 1 / 2 * (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d
        = 1 / 2 * ((∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d) := by
      ring
    linarith
  -- assemble
  have hY2 : (Real.log z / 74) ^ 2 / M ^ 2 ≤ ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 := by
    have : Real.log z / 74 / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ :=
      le_trans (div_le_div_of_nonneg_right hlYlo hM.le) hinv
    rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) this 2
  have hDpos : 0 ≤ ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hfinal : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) ≤ pairG d z * pairSingularProduct d := by
    set A := (Real.log z / 74) ^ 2 / M ^ 2
    set P := ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
    set E := ∏ p ∈ Q, (1 + H p)
    set PP := pairSingularProduct d
    have hA0 : 0 ≤ A := by positivity
    have hPP0 : 0 ≤ PP := by linarith
    have a1 : A * P ≤ E := le_trans (mul_le_mul_of_nonneg_right hY2 hDpos) hE
    have a2 : A * (1 / 4) ≤ A * (P * PP) := mul_le_mul_of_nonneg_left hD hA0
    have a3 : A * P * PP ≤ E * PP := mul_le_mul_of_nonneg_right a1 hPP0
    have a4 : 1 / 2 * E * PP ≤ pairG d z * PP := mul_le_mul_of_nonneg_right hhalf hPP0
    have e1 : A * P * PP = A * (P * PP) := by ring
    have e2 : 1 / 2 * E * PP = 1 / 2 * (E * PP) := by ring
    linarith
  have hc : c * Real.log z ^ 2 ≤ (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) := by
    have : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) = (1 / (43808 * M ^ 2)) * Real.log z ^ 2 := by
      field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hmin2 (sq_nonneg _)
  linarith

end OMALib694.Sieve


/-!
Unconditional prime-pair bound: `Sieve.lean` combined with `Mertens.lean`.

This file is meant to be appended after the contents of `Mertens.lean` (namespace
`OMALib694.Mertens`) and `Sieve.lean` (namespace `OMALib694.Sieve`); it uses
`OMALib694.Mertens.sum_log_div_le_nat` and `OMALib694.Mertens.prod_one_sub_inv_bounds` to discharge
the Mertens-type hypothesis `OMALib694.Sieve.PairGLowerBound`.
-/

open scoped Classical
open Finset

namespace OMALib694.Sieve

/-- The Mertens-type input `PairGLowerBound c` holds for an explicit absolute `c > 0`. -/
theorem exists_pairGLowerBound : ∃ c : ℝ, 0 < c ∧ PairGLowerBound c := by
  set M := Real.exp OMALib694.Mertens.mertens2Const
  have hM : 0 < M := Real.exp_pos _
  refine ⟨min (1 / 2700) (1 / (43808 * M ^ 2)), lt_min (by norm_num) (by positivity),
    pairGLowerBound_of_mertens hM OMALib694.Mertens.sum_log_div_le_nat ?_⟩
  intro N hN
  have h := (OMALib694.Mertens.prod_one_sub_inv_bounds (N : ℝ) (by exact_mod_cast hN)).2
  rwa [Nat.floor_natCast] at h

end OMALib694.Sieve

/-! ## Triples `q`, `s q + 1`, `a q + 1` -/

open scoped Classical BigOperators
open Finset Filter

namespace OMALib694.Triple

open OMALib694.Sieve

/-- The modulus `s a |a - s|` of the triple sieve (natural subtraction, one of the two
differences vanishes). -/
def tripleM (s a : ℕ) : ℕ := s * a * ((a - s) + (s - a))

/-- The local condition of the triple sieve: `p ∣ q (s q + 1) (a q + 1)`. -/
def tripleCond (s a : ℕ) (p q : ℕ) : Prop := p ∣ q * (s * q + 1) * (a * q + 1)

/-- The sieving primes: primes `p < z` with `3 < p` and `p ∤ s a |a - s|`. -/
noncomputable def triplePrimes (s a z : ℕ) : Finset ℕ :=
  (Nat.primesBelow z).filter (fun p => 3 < p ∧ ¬ p ∣ tripleM s a)

/-- Selberg's `G` for the triple sieve, with density `3 / p` on every sieving prime. -/
noncomputable def tripleG (s a z : ℕ) : ℝ :=
  selbergG (fun p : ℕ => (3 : ℝ) / p) (levelFamily (triplePrimes s a z) z)

theorem mem_triplePrimes {s a z p : ℕ} :
    p ∈ triplePrimes s a z ↔ p < z ∧ p.Prime ∧ 3 < p ∧ ¬ p ∣ tripleM s a := by
  simp [triplePrimes, Nat.mem_primesBelow, and_assoc]

theorem tripleCond_periodic (s a p q : ℕ) : tripleCond s a p q ↔ tripleCond s a p (q % p) := by
  unfold tripleCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

/-- TASK 1. For a prime `p > 3` not dividing `s a |a - s|`, exactly three residues modulo `p`
are removed: `0`, `-1/s` and `-1/a`. -/
theorem omega_tripleCond {s a p : ℕ} (hp : p.Prime) (h3 : 3 < p) (hm : ¬ p ∣ tripleM s a) :
    omega (tripleCond s a) p = 3 := by
  have := Fact.mk hp
  unfold tripleM at hm
  have hs : ¬ p ∣ s := fun h => hm (Dvd.dvd.mul_right (Dvd.dvd.mul_right h a) _)
  have ha : ¬ p ∣ a := fun h => hm (Dvd.dvd.mul_right (Dvd.dvd.mul_left h s) _)
  have hd : ¬ p ∣ (a - s) + (s - a) := fun h => hm (Dvd.dvd.mul_left h _)
  have hsZ : (s : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hs
  have haZ : (a : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact ha
  have hasZ : (a : ZMod p) ≠ (s : ZMod p) := by
    intro h
    apply hd
    rcases le_total s a with hsa | hsa
    · have : ((a - s : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hsa, h, sub_self]
      rw [ZMod.natCast_eq_zero_iff] at this
      rw [Nat.sub_eq_zero_of_le hsa, add_zero]; exact this
    · have : ((s - a : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hsa, h, sub_self]
      rw [ZMod.natCast_eq_zero_iff] at this
      rw [Nat.sub_eq_zero_of_le hsa, zero_add]; exact this
  have hu0 : -(s : ZMod p)⁻¹ ≠ 0 := by simp [hsZ]
  have hv0 : -(a : ZMod p)⁻¹ ≠ 0 := by simp [haZ]
  have huv : -(s : ZMod p)⁻¹ ≠ -(a : ZMod p)⁻¹ := by
    intro h
    apply hasZ
    have : (s : ZMod p)⁻¹ = (a : ZMod p)⁻¹ := neg_inj.mp h
    exact (inv_inj.mp this).symm
  have e1 : ∀ c : ℕ, (c : ZMod p) ≠ 0 → ∀ x : ZMod p,
      (c : ZMod p) * x + 1 = 0 ↔ x = -(c : ZMod p)⁻¹ := by
    intro c hc x
    constructor
    · intro h
      have h' : (c : ZMod p) * x = -1 := eq_neg_of_add_eq_zero_left h
      calc x = (c : ZMod p)⁻¹ * ((c : ZMod p) * x) := (inv_mul_cancel_left₀ hc x).symm
        _ = -(c : ZMod p)⁻¹ := by rw [h']; ring
    · rintro rfl
      rw [mul_neg, mul_inv_cancel₀ hc]; ring
  have hval : ∀ r < p, ∀ w : ZMod p, (r : ZMod p) = w ↔ r = w.val := by
    intro r hr w
    constructor
    · rintro rfl; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
    · rintro rfl; exact ZMod.natCast_zmod_val w
  have key : ∀ r < p, tripleCond s a p r ↔
      r = 0 ∨ r = (-(s : ZMod p)⁻¹).val ∨ r = (-(a : ZMod p)⁻¹).val := by
    intro r hr
    unfold tripleCond
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [mul_eq_zero, e1 s hsZ, e1 a haZ, hval r hr, ZMod.val_zero, or_assoc]
  have hfilt : (range p).filter (tripleCond s a p)
      = {0, (-(s : ZMod p)⁻¹).val, (-(a : ZMod p)⁻¹).val} := by
    ext r
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hr, h⟩; exact (key r hr).mp h
    · intro h
      have hr : r < p := by
        rcases h with rfl | rfl | rfl
        · exact hp.pos
        · exact ZMod.val_lt _
        · exact ZMod.val_lt _
      exact ⟨hr, (key r hr).mpr h⟩
  unfold omega
  rw [hfilt]
  have h1 : (-(s : ZMod p)⁻¹).val ≠ (-(a : ZMod p)⁻¹).val :=
    fun h => huv (ZMod.val_injective p h)
  have h2 : 0 ≠ (-(s : ZMod p)⁻¹).val := fun h => hu0 ((ZMod.val_eq_zero _).mp h.symm)
  have h3' : 0 ≠ (-(a : ZMod p)⁻¹).val := fun h => hv0 ((ZMod.val_eq_zero _).mp h.symm)
  rw [card_insert_of_notMem (by simp [h2, h3']), card_insert_of_notMem (by simp [h1]),
    card_singleton]

/-- Selberg upper bound for the triple, explicit form. -/
theorem triple_card_le_sieve (s a Y z : ℕ) (hs : 0 < s) (ha : 0 < a) (hz : 2 ≤ z) :
    (((Icc 1 Y).filter fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime).card : ℝ)
      ≤ z + (Y + 1) / tripleG s a z + (z : ℝ) ^ 4 := by
  set Q := triplePrimes s a z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (mem_triplePrimes.mp hp).2.1
  have hsub : (Icc 1 Y).filter (fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime)
      ⊆ range z ∪ (range (Y + 1)).filter (fun n => ∀ p ∈ Q, ¬ tripleCond s a p n) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    simp only [mem_union, mem_range, mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨by omega, fun q hq hdiv => ?_⟩
      have hq' := mem_triplePrimes.mp hq
      unfold tripleCond at hdiv
      rcases (hq'.2.1.dvd_mul).mp hdiv with h | h
      · rcases (hq'.2.1.dvd_mul).mp h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hq'.2.1 hn.2.1).mp h; omega
        · have := (Nat.prime_dvd_prime_iff_eq hq'.2.1 hn.2.2.1).mp h
          have : n ≤ s * n := Nat.le_mul_of_pos_left n hs
          omega
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2.1 hn.2.2.2).mp h
        have : n ≤ a * n := Nat.le_mul_of_pos_left n ha
        omega
  have hω : ∀ p ∈ Q, omega (tripleCond s a) p = 3 := fun p hp => by
    obtain ⟨-, h1, h2, h3⟩ := mem_triplePrimes.mp hp
    exact omega_tripleCond h1 h2 h3
  have hω0 : ∀ p ∈ Q, 0 < omega (tripleCond s a) p := fun p hp => by rw [hω p hp]; norm_num
  have hω1 : ∀ p ∈ Q, omega (tripleCond s a) p < p := fun p hp => by
    rw [hω p hp]; exact (mem_triplePrimes.mp hp).2.2.1
  have hsieve := selberg_residue_level (Y + 1) z hz Q hQ (tripleCond s a)
    (tripleCond_periodic s a) hω0 hω1
  have hG : selbergG (fun p => (omega (tripleCond s a) p : ℝ) / p) (levelFamily Q z)
      = tripleG s a z :=
    selbergG_congr levelFamily_subset fun p hp => by rw [hω p hp]; norm_num
  rw [hG] at hsieve
  push_cast at hsieve
  have hcard := card_le_card hsub
  have hu := card_union_le (range z)
    ((range (Y + 1)).filter (fun n => ∀ p ∈ Q, ¬ tripleCond s a p n))
  rw [card_range] at hu
  have : (((Icc 1 Y).filter (fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime)).card : ℝ)
      ≤ z + (((range (Y + 1)).filter (fun n => ∀ p ∈ Q, ¬ tripleCond s a p n)).card : ℝ) := by
    exact_mod_cast hcard.trans hu
  linarith

/-- TASK 2. Rankin step for the triple sieve: with `3 ≤ Y < z` and `Y ≤ z^{1/73}`,
`G ≥ ½ Π_{p ≤ Y, p > 3, p ∤ m} (1 + h(p))`. Adapt `pair_rankin_half`
(here `h(p) = 3/(p-3) ≤ 12/p`, the tail sum is at most `72`). -/
theorem triple_rankin_half (s a z Y : ℕ) (hY3 : 3 ≤ Y) (hYz : Y < z)
    (hlYup : Real.log Y ≤ Real.log z / 73)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4) :
    (1 / 2) * ∏ p ∈ triplePrimes s a (Y + 1), (1 + hFun (fun p : ℕ => (3 : ℝ) / p) p)
      ≤ tripleG s a z := by
  set g : ℕ → ℝ := fun p => (3 : ℝ) / p
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)
  set Q := triplePrimes s a (Y + 1)
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (mem_triplePrimes.mp hp).2.1
  have hQ3 : ∀ p ∈ Q, 3 < p := fun p hp => (mem_triplePrimes.mp hp).2.2.1
  have hQY : ∀ p ∈ Q, p ≤ Y := fun p hp => by have := (mem_triplePrimes.mp hp).1; omega
  have hQQ : Q ⊆ triplePrimes s a z := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_triplePrimes.mp hp
    exact mem_triplePrimes.mpr ⟨by omega, h2, h3, h4⟩
  have hHfun : ∀ p : ℕ, 3 < p → hFun g p = 3 / ((p : ℝ) - 3) := by
    intro p hp
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast hp
    have hp3 : (p : ℝ) - 3 ≠ 0 := by intro h; linarith
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have e : 1 - 3 / (p : ℝ) = ((p : ℝ) - 3) / p := by field_simp
    simp only [hFun, g]
    rw [e, div_div_div_cancel_right₀ hp0]
  have hH0' : ∀ p : ℕ, 3 < p → 0 ≤ hFun g p := fun p hp => by
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast hp
    rw [hHfun p hp]; exact div_nonneg (by norm_num) (by linarith)
  have hHle : ∀ p : ℕ, 3 < p → hFun g p ≤ 12 / p := fun p hp => by
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast hp
    rw [hHfun p hp, div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  set ε : ℝ := 1 / Real.log Y
  have hε : 0 ≤ ε := by positivity
  have hrank := selbergG_ge_rankin g Q (triplePrimes s a z) hQQ hQp
    (fun p hp => hH0' p (mem_triplePrimes.mp hp).2.2.1) z (by omega) hε
  change _ ≤ tripleG s a z at hrank
  set H : ℕ → ℝ := fun p => hFun g p
  have hH0 : ∀ p ∈ Q, 0 ≤ H p := fun p hp => hH0' p (hQ3 p hp)
  -- the Rankin tail
  have hpe : ∀ p ∈ Q, (p : ℝ) ^ ε - 1 ≤ 2 * (Real.log p / Real.log Y) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlpY : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by linarith) (by exact_mod_cast hQY p hp)
    have ht : |Real.log p * ε| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simp only [ε]; rw [mul_one_div, div_le_one hlY]; exact hlpY
    rw [Real.rpow_def_of_pos (by linarith)]
    have := (abs_le.mp (Real.abs_exp_sub_one_le ht)).2
    rw [abs_of_nonneg (by positivity)] at this
    have e : Real.log p * ε = Real.log p / Real.log Y := by simp only [ε]; ring
    rw [← e]; exact this
  have hQsub : Q ⊆ Nat.primesLE Y := fun p hp => Nat.mem_primesLE.mpr ⟨hQY p hp, hQp p hp⟩
  have hsumQ : ∑ p ∈ Q, Real.log p / p ≤ ∑ p ∈ Nat.primesLE Y, Real.log p / p :=
    sum_le_sum_of_subset_of_nonneg hQsub fun p hp _ => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
      have := Real.log_nonneg this
      positivity
  have hsumtail : ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1) ≤ 72 := by
    calc ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)
        ≤ ∑ p ∈ Q, (12 / (p : ℝ)) * (2 * (Real.log p / Real.log Y)) := by
          refine sum_le_sum fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have : (0 : ℝ) ≤ (p : ℝ) ^ ε - 1 := by
            have := Real.one_le_rpow hp1 hε; linarith
          exact mul_le_mul (hHle p (hQ3 p hp)) (hpe p hp) this (by positivity)
      _ = (24 / Real.log Y) * ∑ p ∈ Q, Real.log p / p := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      _ ≤ (24 / Real.log Y) * (Real.log Y + Real.log 4) :=
          mul_le_mul_of_nonneg_left (hsumQ.trans (hM1 Y)) (by positivity)
      _ ≤ 72 := by
          have h4 : Real.log 4 ≤ 2 * Real.log Y := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
            linarith
          rw [div_mul_eq_mul_div, div_le_iff₀ hlY]; nlinarith
  have hprod_tail : ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 72 := by
    calc ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ ∏ p ∈ Q, ((1 + H p) * Real.exp (H p * ((p : ℝ) ^ ε - 1))) := by
          refine prod_le_prod (fun p hp => by
            have := hH0 p hp; positivity) fun p hp => ?_
          have h0 := hH0 p hp
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have hb : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε
          have := Real.add_one_le_exp (H p * ((p : ℝ) ^ ε - 1))
          nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ (p : ℝ) ^ ε - 1)]
      _ = (∏ p ∈ Q, (1 + H p)) * Real.exp (∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)) := by
          rw [prod_mul_distrib, Real.exp_sum]
      _ ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 72 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsumtail)
            (prod_nonneg fun p hp => by have := hH0 p hp; linarith)
  have hzeps : (z : ℝ) ^ (-ε) ≤ Real.exp (-73) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    simp only [ε]
    rw [mul_neg, mul_one_div, neg_le_neg_iff, le_div_iff₀ hlY]; linarith
  have hP0 : 0 ≤ ∏ p ∈ Q, (1 + H p) := prod_nonneg fun p hp => by have := hH0 p hp; linarith
  have he : Real.exp (-73) * Real.exp 72 ≤ 1 / 2 := by
    rw [← Real.exp_add]; norm_num
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
  have ht : (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := by
    calc (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ Real.exp (-73) * ((∏ p ∈ Q, (1 + H p)) * Real.exp 72) :=
          mul_le_mul hzeps hprod_tail (prod_nonneg fun p hp => by
            have := hH0 p hp; positivity) (Real.exp_pos _).le
      _ = (Real.exp (-73) * Real.exp 72) * ∏ p ∈ Q, (1 + H p) := by ring
      _ ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := mul_le_mul_of_nonneg_right he hP0
  have hhalf : (1 / 2) * ∏ p ∈ Q, (1 + H p) ≤ tripleG s a z := by linarith
  exact hhalf

/-- TASK 3. Euler-product lower bound: `1 + h(p) = p/(p-3) ≥ (1 - 1/p)⁻³`, and the primes
`p ≤ Y` missing from the sieve all divide `6 m`. Adapt `pair_euler_ge`. -/
theorem triple_euler_ge (s a Y : ℕ) (hm : 0 < tripleM s a) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 3 *
        (∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ))) ^ 3
      ≤ ∏ p ∈ triplePrimes s a (Y + 1), (1 + hFun (fun p : ℕ => (3 : ℝ) / p) p) := by
  set P := Nat.primesLE Y
  set Q := triplePrimes s a (Y + 1)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hQP : Q ⊆ P := fun p hp => by
    obtain ⟨h1, h2, -, -⟩ := mem_triplePrimes.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, h2⟩
  have hf : ∀ p : ℕ, p.Prime → 0 < 1 - 1 / (p : ℝ) := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hf1 : ∀ p : ℕ, 1 - 1 / (p : ℝ) ≤ 1 := fun p => by
    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hsd : P \ Q ⊆ (6 * tripleM s a).primeFactors := by
    intro p hp
    obtain ⟨hpP, hpQ⟩ := mem_sdiff.mp hp
    have hpp := hP p hpP
    have hpY := (Nat.mem_primesLE.mp hpP).1
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, by omega⟩
    by_cases h3 : 3 < p
    · have : p ∣ tripleM s a := by
        by_contra hnd
        exact hpQ (mem_triplePrimes.mpr ⟨by omega, hpp, h3, hnd⟩)
      exact Dvd.dvd.mul_left this 6
    · have : p = 2 ∨ p = 3 := by have := hpp.two_le; omega
      rcases this with rfl | rfl
      · exact Dvd.dvd.mul_right (by norm_num) _
      · exact Dvd.dvd.mul_right (by norm_num) _
  set B := ∏ p ∈ Q, (1 - 1 / (p : ℝ))
  set C := ∏ p ∈ P \ Q, (1 - 1 / (p : ℝ))
  set D := ∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ))
  have hB : 0 < B := prod_pos fun p hp => hf p (hP p (hQP hp))
  have hC : 0 < C := prod_pos fun p hp => hf p (hP p (mem_sdiff.mp hp).1)
  have hD0 : 0 ≤ D := prod_nonneg fun p hp => (hf p (Nat.prime_of_mem_primeFactors hp)).le
  have hA : ∏ p ∈ P, (1 - 1 / (p : ℝ)) = C * B := (prod_sdiff hQP).symm
  have hDC : D ≤ C := by
    have e := prod_sdiff hsd (f := fun p : ℕ => 1 - 1 / (p : ℝ))
    have h1 : ∏ p ∈ (6 * tripleM s a).primeFactors \ (P \ Q), (1 - 1 / (p : ℝ)) ≤ 1 :=
      prod_le_one (fun p hp => (hf p (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1)).le)
        (fun p _ => hf1 p)
    have h2 : D = (∏ p ∈ (6 * tripleM s a).primeFactors \ (P \ Q), (1 - 1 / (p : ℝ))) * C :=
      e.symm
    rw [h2]; nlinarith
  have hloc : ∀ p ∈ Q, (1 - 1 / (p : ℝ))⁻¹ ^ 3 ≤ 1 + hFun (fun p : ℕ => (3 : ℝ) / p) p := by
    intro p hp
    obtain ⟨-, hpp, h3, -⟩ := mem_triplePrimes.mp hp
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast h3
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp3 : (p : ℝ) - 3 ≠ 0 := by intro h; linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    simp only [hFun]
    have e1 : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
    have e2 : 1 + (3 / (p : ℝ)) / (1 - 3 / p) = p / ((p : ℝ) - 3) := by
      have : 1 - 3 / (p : ℝ) = ((p : ℝ) - 3) / p := by field_simp
      rw [this]; field_simp; ring
    rw [e1, e2, inv_div, div_pow, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p) (by linarith : (0 : ℝ) ≤ 3 * p - 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p) (by linarith : (0 : ℝ) ≤ p))
        (by linarith : (0 : ℝ) ≤ 3 * p - 1)]
  have hprod : (B⁻¹) ^ 3 ≤ ∏ p ∈ Q, (1 + hFun (fun p : ℕ => (3 : ℝ) / p) p) := by
    calc (B⁻¹) ^ 3 = ∏ p ∈ Q, (1 - 1 / (p : ℝ))⁻¹ ^ 3 := by
          rw [prod_pow, prod_inv_distrib]
      _ ≤ _ := prod_le_prod (fun p hp => by have := hf p (hP p (hQP hp)); positivity) hloc
  rw [hA]
  calc ((C * B)⁻¹) ^ 3 * D ^ 3 = (D / (C * B)) ^ 3 := by ring
    _ ≤ (B⁻¹) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        calc D ≤ C := hDC
          _ = B⁻¹ * (C * B) := by field_simp
    _ ≤ _ := hprod

/-- TASK 4. Lower bound for the triple `G`, from Tasks 2, 3 and Mertens. Adapt
`pairGLowerBound_of_mertens` and `exists_pairGLowerBound`. -/
theorem tripleG_lower : ∃ c : ℝ, 0 < c ∧ ∀ s a z : ℕ, 0 < tripleM s a → 2 ≤ z →
    c * Real.log z ^ 3 * (∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ))) ^ 3
      ≤ tripleG s a z := by
  set M := Real.exp OMALib694.Mertens.mertens2Const
  have hM : 0 < M := Real.exp_pos _
  have hM3 : ∀ N : ℕ, 2 ≤ N → ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) ≤ M / Real.log N := by
    intro N hN
    have h := (OMALib694.Mertens.prod_one_sub_inv_bounds (N : ℝ) (by exact_mod_cast hN)).2
    rwa [Nat.floor_natCast] at h
  refine ⟨min (1 / 1100000) (1 / (2 * 146 ^ 3 * M ^ 3)), lt_min (by norm_num) (by positivity), ?_⟩
  intro s a z hm hz
  have hc1 : min (1 / 1100000) (1 / (2 * 146 ^ 3 * M ^ 3)) ≤ 1 / 1100000 := min_le_left _ _
  have hc2 : min (1 / 1100000) (1 / (2 * 146 ^ 3 * M ^ 3)) ≤ 1 / (2 * 146 ^ 3 * M ^ 3) :=
    min_le_right _ _
  have hc0 : 0 < min (1 / 1100000) (1 / (2 * 146 ^ 3 * M ^ 3)) :=
    lt_min (by norm_num) (by positivity)
  set c := min (1 / 1100000) (1 / (2 * 146 ^ 3 * M ^ 3))
  set g : ℕ → ℝ := fun p => (3 : ℝ) / p
  have hg0 : ∀ p ∈ triplePrimes s a z, 0 < g p := fun p hp =>
    div_pos (by norm_num) (by exact_mod_cast (mem_triplePrimes.mp hp).2.1.pos)
  have hg1 : ∀ p ∈ triplePrimes s a z, g p < 1 := fun p hp => by
    have h3 : (3 : ℝ) < p := by exact_mod_cast (mem_triplePrimes.mp hp).2.2.1
    simp only [g]; rw [div_lt_one (by linarith)]; exact h3
  have hG1 : 1 ≤ tripleG s a z :=
    one_le_selbergG hg0 hg1 levelFamily_subset (empty_mem_levelFamily hz)
  set P := ∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ))
  have hP0 : 0 ≤ P := prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hP1 : P ≤ 1 := prod_le_one (fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this) (fun p _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have hP3 : P ^ 3 ≤ 1 := pow_le_one₀ hP0 hP1
  have hP3' : 0 ≤ P ^ 3 := by positivity
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hbig : 146 * Real.log 2 ≤ Real.log z
  swap
  · rw [not_le] at hbig
    have h3 : Real.log z ^ 3 ≤ 1100000 := by
      have : Real.log z ≤ 102 := by linarith
      calc Real.log z ^ 3 ≤ 102 ^ 3 := pow_le_pow_left₀ hlz.le this 3
        _ ≤ 1100000 := by norm_num
    have hcz : c * Real.log z ^ 3 ≤ 1 := by
      calc c * Real.log z ^ 3 ≤ (1 / 1100000) * 1100000 :=
            mul_le_mul hc1 h3 (by positivity) (by norm_num)
        _ = 1 := by norm_num
    have : 0 ≤ c * Real.log z ^ 3 := by positivity
    calc c * Real.log z ^ 3 * P ^ 3 ≤ 1 * 1 := mul_le_mul hcz hP3 hP3' (by norm_num)
      _ = 1 := by norm_num
      _ ≤ _ := hG1
  -- large z
  set y : ℝ := (z : ℝ) ^ ((1 : ℝ) / 73) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hlogy : Real.log y = Real.log z / 73 := by
    rw [hydef, Real.log_rpow (by linarith)]; ring
  have hy4 : Real.log 4 ≤ Real.log y := by
    rw [hlogy, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hy4' : 4 ≤ y := by
    have := Real.exp_le_exp.mpr hy4
    rwa [Real.exp_log (by norm_num), Real.exp_log hy0] at this
  set Y := ⌊y⌋₊
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hYgt : y < Y + 1 := Nat.lt_floor_add_one y
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) < Y := by linarith
    exact_mod_cast this.le
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlYup : Real.log Y ≤ Real.log z / 73 := by
    rw [← hlogy]; exact Real.log_le_log (by linarith) hYle
  have hlYlo : Real.log z / 146 ≤ Real.log Y := by
    have h1 : Real.log (y / 2) ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div hy0.ne' (by norm_num), hlogy] at h1
    linarith
  have hYz : Y < z := by
    have h1 : Real.log Y < Real.log z := by linarith
    have := (Real.log_lt_log_iff (by linarith) (by linarith)).mp h1
    exact_mod_cast this
  have hhalf := triple_rankin_half s a z Y hY3 hYz hlYup OMALib694.Mertens.sum_log_div_le_nat
  have hE := triple_euler_ge s a Y hm
  have hM3Y := hM3 Y (by omega)
  have hQpos : 0 < ∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hinv : Real.log Y / M ≤ (∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hQpos, inv_div]; exact hM3Y
  have hY3' : (Real.log z / 146 / M) ^ 3
      ≤ ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (le_trans (div_le_div_of_nonneg_right hlYlo hM.le) hinv) 3
  have a1 : (Real.log z / 146 / M) ^ 3 * P ^ 3
      ≤ ∏ p ∈ triplePrimes s a (Y + 1), (1 + hFun g p) :=
    le_trans (mul_le_mul_of_nonneg_right hY3' hP3') hE
  have hc' : c * Real.log z ^ 3 ≤ (1 / 2) * (Real.log z / 146 / M) ^ 3 := by
    have e : (1 / 2) * (Real.log z / 146 / M) ^ 3
        = (1 / (2 * 146 ^ 3 * M ^ 3)) * Real.log z ^ 3 := by
      field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  calc c * Real.log z ^ 3 * P ^ 3 ≤ (1 / 2) * (Real.log z / 146 / M) ^ 3 * P ^ 3 :=
        mul_le_mul_of_nonneg_right hc' hP3'
    _ = (1 / 2) * ((Real.log z / 146 / M) ^ 3 * P ^ 3) := by ring
    _ ≤ (1 / 2) * ∏ p ∈ triplePrimes s a (Y + 1), (1 + hFun g p) := by linarith
    _ ≤ tripleG s a z := hhalf

/-- TASK 5. `m / φ(m) ≪ log L` as soon as `log₂ m ≤ L`. Split the primes of `m` at `L`:
the small ones by Mertens' product theorem, the large ones (fewer than `L/2` of them, each
`> L`) by `Π (1 - a i) ≥ 1 - Σ a i`. -/
theorem inv_prod_primeFactors_le : ∃ A : ℝ, 0 < A ∧ ∀ m L : ℕ, 0 < m → 4 ≤ L →
    Nat.log 2 m ≤ L → (∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)))⁻¹ ≤ A * Real.log L := by
  set c₀ := OMALib694.Mertens.mertens2Const + OMALib694.Mertens.primePowerConst / Real.log 2
  refine ⟨2 * Real.exp c₀, by positivity, fun m L hm hL hlog => ?_⟩
  have hf : ∀ p : ℕ, p.Prime → 0 < 1 - 1 / (p : ℝ) := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hf1 : ∀ p : ℕ, 1 - 1 / (p : ℝ) ≤ 1 := fun p => by
    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hmL : m < 2 ^ (L + 1) := by
    calc m < 2 ^ (Nat.log 2 m).succ := Nat.lt_pow_succ_log_self (by norm_num) m
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set S := m.primeFactors.filter (fun p => p ≤ L)
  set T := m.primeFactors.filter (fun p => ¬ p ≤ L)
  have hsplit : ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
      = (∏ p ∈ S, (1 - 1 / (p : ℝ))) * ∏ p ∈ T, (1 - 1 / (p : ℝ)) :=
    (prod_filter_mul_prod_filter_not _ _ _).symm
  have hSsub : S ⊆ Nat.primesLE L := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨h2, Nat.prime_of_mem_primeFactors h1⟩
  have hSge : ∏ p ∈ Nat.primesLE L, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    rw [← prod_sdiff hSsub]
    have h0 : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp =>
      (hf p (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).le
    have h1 : ∏ p ∈ Nat.primesLE L \ S, (1 - 1 / (p : ℝ)) ≤ 1 :=
      prod_le_one (fun p hp => (hf p (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2).le)
        (fun p _ => hf1 p)
    nlinarith
  have hLR : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hlL : 0 < Real.log L := Real.log_pos (by linarith)
  have hmert : Real.exp (-c₀) / Real.log L ≤ ∏ p ∈ Nat.primesLE L, (1 - 1 / (p : ℝ)) := by
    have h := (OMALib694.Mertens.prod_one_sub_inv_bounds (L : ℝ) (by linarith)).1
    rwa [Nat.floor_natCast] at h
  have hTcard : 2 * T.card ≤ L := by
    have h1 : (∏ p ∈ T, p) ∣ m :=
      (prod_dvd_prod_of_subset T m.primeFactors (fun p => p) (filter_subset _ _)).trans
        (Nat.prod_primeFactors_dvd m)
    have h2 : ∏ p ∈ T, p ≤ m := Nat.le_of_dvd hm h1
    have h3 : 4 ^ T.card ≤ ∏ p ∈ T, p := Finset.pow_card_le_prod T (fun p => p) 4
      (fun p hp => by have := (mem_filter.mp hp).2; omega)
    have h4 : 2 ^ (2 * T.card) < 2 ^ (L + 1) := by
      rw [pow_mul]; exact lt_of_le_of_lt (by norm_num; exact h3.trans h2) hmL
    by_contra hc
    have h5 : 2 ^ (L + 1) ≤ 2 ^ (2 * T.card) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hTsum : ∑ p ∈ T, 1 / (p : ℝ) ≤ 1 / 2 := by
    have hb : ∀ p ∈ T, 1 / (p : ℝ) ≤ 1 / ((L : ℝ) + 1) := fun p hp => by
      have h1 : L + 1 ≤ p := by have := (mem_filter.mp hp).2; omega
      have h2 : (L : ℝ) + 1 ≤ p := by exact_mod_cast h1
      exact one_div_le_one_div_of_le (by positivity) h2
    calc ∑ p ∈ T, 1 / (p : ℝ) ≤ ∑ p ∈ T, 1 / ((L : ℝ) + 1) := sum_le_sum hb
      _ = T.card / ((L : ℝ) + 1) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : (2 * T.card : ℝ) ≤ L := by exact_mod_cast hTcard
        linarith
  have hTge : 1 / 2 ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ)) := by
    have := OMALib694.Sieve.one_sub_sum_le_prod T (fun p => 1 / (p : ℝ))
      (fun p _ => by positivity) (fun p hp => by
        have : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).one_lt.le
        rw [div_le_one (by linarith)]; exact this)
    linarith
  have hS0 : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) (hmert.trans hSge)
  have hprod : Real.exp (-c₀) / Real.log L * (1 / 2) ≤ ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [hsplit]; exact mul_le_mul (hmert.trans hSge) hTge (by norm_num) hS0.le
  have hpos : 0 < Real.exp (-c₀) / Real.log L * (1 / 2) := by positivity
  calc (∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)))⁻¹
        ≤ (Real.exp (-c₀) / Real.log L * (1 / 2))⁻¹ := inv_anti₀ hpos hprod
    _ = 2 * Real.exp c₀ * Real.log L := by
        rw [Real.exp_neg]
        field_simp

/-- The triple bound with all the sieve constants collected. -/
theorem triple_bound : ∃ K : ℝ, 0 < K ∧ ∀ s a Y z L : ℕ, 0 < s → 0 < a → 0 < tripleM s a →
    2 ≤ z → 4 ≤ L → Nat.log 2 (6 * tripleM s a) ≤ L →
    (((Icc 1 Y).filter fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime).card : ℝ)
      ≤ z + (z : ℝ) ^ 4 + K * (Y + 1) * Real.log L ^ 3 / Real.log z ^ 3 := by
  obtain ⟨c, hc, hG⟩ := tripleG_lower
  obtain ⟨A, hA, hP⟩ := inv_prod_primeFactors_le
  refine ⟨A ^ 3 / c, by positivity, fun s a Y z L hs ha hm hz hL hlog => ?_⟩
  have hcard := triple_card_le_sieve s a Y z hs ha hz
  have hP0 : 0 < ∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ)) :=
    prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
      linarith
  set P := ∏ p ∈ (6 * tripleM s a).primeFactors, (1 - 1 / (p : ℝ))
  have hPi := hP (6 * tripleM s a) L (by omega) hL hlog
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hLR : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hlL : 0 < Real.log L := Real.log_pos (by linarith)
  have hGz := hG s a z hm hz
  have hGpos : 0 < tripleG s a z := lt_of_lt_of_le (by positivity) hGz
  have hinv3 : (P⁻¹) ^ 3 ≤ (A * Real.log L) ^ 3 := pow_le_pow_left₀ (by positivity) hPi 3
  have h1 : 1 / tripleG s a z ≤ A ^ 3 / c * Real.log L ^ 3 / Real.log z ^ 3 := by
    rw [div_le_iff₀ hGpos]
    calc (1 : ℝ) = (c * Real.log z ^ 3 * P ^ 3) * ((P⁻¹) ^ 3 / (c * Real.log z ^ 3)) := by
          field_simp
      _ ≤ tripleG s a z * ((A * Real.log L) ^ 3 / (c * Real.log z ^ 3)) :=
          mul_le_mul hGz (div_le_div_of_nonneg_right hinv3 (by positivity)) (by positivity)
            hGpos.le
      _ = A ^ 3 / c * Real.log L ^ 3 / Real.log z ^ 3 * tripleG s a z := by
          field_simp
  have hY : (0 : ℝ) ≤ Y + 1 := by positivity
  have h2 : ((Y : ℝ) + 1) / tripleG s a z
      ≤ A ^ 3 / c * (Y + 1) * Real.log L ^ 3 / Real.log z ^ 3 := by
    calc ((Y : ℝ) + 1) / tripleG s a z = (Y + 1) * (1 / tripleG s a z) := by ring
      _ ≤ (Y + 1) * (A ^ 3 / c * Real.log L ^ 3 / Real.log z ^ 3) :=
          mul_le_mul_of_nonneg_left h1 hY
      _ = _ := by ring
  linarith

/-- Eventually `(log k)^3 ≤ ε k`. -/
theorem eventually_log_cube_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, Real.log k ^ 3 ≤ ε * k := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 3)).def hε
  have h2 := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2] with k hk
  simp only [id, Real.norm_eq_abs] at hk
  rw [Nat.abs_cast] at hk
  exact (le_abs_self _).trans hk

/-- The target statement. -/
theorem h3 : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
  let X : ℕ := 2^(k^10)
  ∀ s a : ℕ, 0 < s → s^2 ≤ X → a ∈ (n*s).divisors → a ≠ s →
    (((Icc 1 (X/s)).filter fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime).card:ℝ)
 ≤ C*X/((s:ℝ)*(k:ℝ)^29) := by
  intro n hn
  obtain ⟨K, hK, hbound⟩ := triple_bound
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [eventually_log_cube_le (1 / (4 * 1331 * 262144 * K)) (by positivity),
    eventually_ge_atTop (12 * n ^ 2 + 3)] with k hlog hk
  intro X s a hs hsX ha hne
  have hX : X = 2 ^ (k ^ 10) := rfl
  have hk3 : 3 ≤ k := by omega
  have ht3 : 19683 * k ≤ k ^ 10 := by
    have : 3 ^ 9 ≤ k ^ 9 := Nat.pow_le_pow_left hk3 9
    calc 19683 * k = 3 ^ 9 * k := by norm_num
      _ ≤ k ^ 9 * k := Nat.mul_le_mul_right k this
      _ = k ^ 10 := by ring
  set t := k ^ 10 with ht
  have hXpos : 0 < X := by rw [hX]; positivity
  have hsX1 : s ≤ X := le_trans (by nlinarith) hsX
  have haN : a ≤ n * s := Nat.divisor_le ha
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hm : 0 < tripleM s a := by
    unfold tripleM
    have : 0 < (a - s) + (s - a) := by omega
    positivity
  set z : ℕ := 2 ^ (t / 16) with hz
  set L : ℕ := k ^ 11 with hL
  have hz2 : 2 ≤ z := by
    have : 1 ≤ t / 16 := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t / 16) := Nat.pow_le_pow_right (by norm_num) this
  have hLt : 3 * t ≤ L := by
    calc 3 * t ≤ k * k ^ 10 := Nat.mul_le_mul_right _ hk3
      _ = k ^ 11 := by ring
  have hL4 : 4 ≤ L := by omega
  have hlogm : Nat.log 2 (6 * tripleM s a) ≤ L := by
    have hm1 : tripleM s a ≤ s * (n * s) * (2 * (n * s)) := by
      unfold tripleM
      have h1 : (a - s) + (s - a) ≤ 2 * (n * s) := by
        have : s ≤ n * s := Nat.le_mul_of_pos_left s hn
        omega
      exact Nat.mul_le_mul (Nat.mul_le_mul_left s haN) h1
    have hm2 : 6 * tripleM s a ≤ 12 * n ^ 2 * (X * X) := by
      have e : s * (n * s) * (2 * (n * s)) = 2 * n ^ 2 * (s * s ^ 2) := by ring
      have h3' : s * s ^ 2 ≤ X * X := Nat.mul_le_mul hsX1 hsX
      calc 6 * tripleM s a ≤ 6 * (s * (n * s) * (2 * (n * s))) := Nat.mul_le_mul_left 6 hm1
        _ = 12 * n ^ 2 * (s * s ^ 2) := by rw [e]; ring
        _ ≤ 12 * n ^ 2 * (X * X) := Nat.mul_le_mul_left _ h3'
    have hm3 : 12 * n ^ 2 * (X * X) ≤ 2 ^ L := by
      have hn2 : 12 * n ^ 2 ≤ 2 ^ t := by
        have : k < 2 ^ k := Nat.lt_two_pow_self
        have : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 12 * n ^ 2 * (X * X) ≤ 2 ^ t * (2 ^ t * 2 ^ t) := by
            rw [hX]; exact Nat.mul_le_mul_right _ hn2
        _ = 2 ^ (3 * t) := by rw [← pow_add, ← pow_add]; ring_nf
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hLt
    calc Nat.log 2 (6 * tripleM s a) ≤ Nat.log 2 (2 ^ L) := Nat.log_mono_right (hm2.trans hm3)
      _ = L := Nat.log_pow (by norm_num) L
  have key := hbound s a (X / s) z L hs ha0 hm hz2 hL4 hlogm
  -- real estimates
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hxpos : 0 < (X : ℝ) / s := by positivity
  have hY : ((X / s : ℕ) : ℝ) ≤ (X : ℝ) / s := Nat.cast_div_le
  have hx1 : 1 ≤ (X : ℝ) / s := by
    rw [le_div_iff₀ hsR, one_mul]; exact_mod_cast hsX1
  have hx2 : (X : ℝ) ≤ ((X : ℝ) / s) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have : (s : ℝ) ^ 2 ≤ X := by exact_mod_cast hsX
    nlinarith
  -- the remainder z + z^4
  have hrem : (z : ℝ) + (z : ℝ) ^ 4 ≤ (X : ℝ) / s / (2 * (k : ℝ) ^ 29) := by
    have hN : 16 * k ^ 58 * z ^ 8 ≤ X := by
      have e0 : k ^ 58 < (2 ^ k) ^ 58 := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
      have e1 : 16 * k ^ 58 < 2 ^ (4 + 58 * k) := by
        rw [pow_add, mul_comm 58 k, pow_mul]; norm_num; linarith
      have e2 : 4 + 58 * k ≤ t / 2 := by omega
      have e3 : z ^ 8 ≤ 2 ^ (t / 2) := by
        rw [hz, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 16 * k ^ 58 * z ^ 8 ≤ 2 ^ (t / 2) * 2 ^ (t / 2) :=
            Nat.mul_le_mul (e1.le.trans (Nat.pow_le_pow_right (by norm_num) e2)) e3
        _ = 2 ^ (t / 2 + t / 2) := (pow_add ..).symm
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = X := hX.symm
    have hNR : 16 * (k : ℝ) ^ 58 * (z : ℝ) ^ 8 ≤ ((X : ℝ) / s) ^ 2 :=
      le_trans (by exact_mod_cast hN) hx2
    have h4 : 4 * (z : ℝ) ^ 4 * (k : ℝ) ^ 29 ≤ (X : ℝ) / s := by
      have h0 : 0 ≤ 4 * (z : ℝ) ^ 4 * (k : ℝ) ^ 29 := by positivity
      have : (4 * (z : ℝ) ^ 4 * (k : ℝ) ^ 29) ^ 2 ≤ ((X : ℝ) / s) ^ 2 := by
        calc (4 * (z : ℝ) ^ 4 * (k : ℝ) ^ 29) ^ 2 = 16 * (k : ℝ) ^ 58 * (z : ℝ) ^ 8 := by ring
          _ ≤ _ := hNR
      exact (pow_le_pow_iff_left₀ h0 hxpos.le two_ne_zero).mp this
    have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    have hzz : (z : ℝ) ≤ (z : ℝ) ^ 4 := le_self_pow₀ hz1 (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right (show (z : ℝ) + (z : ℝ) ^ 4 ≤ 2 * (z : ℝ) ^ 4 by linarith)
      (show (0 : ℝ) ≤ 2 * (k : ℝ) ^ 29 by positivity)
    nlinarith
  -- the main term
  have hmain : K * (((X / s : ℕ) : ℝ) + 1) * Real.log L ^ 3 / Real.log z ^ 3
      ≤ (X : ℝ) / s / (2 * (k : ℝ) ^ 29) := by
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
    have hLlog : Real.log L = 11 * Real.log k := by
      rw [hL, Nat.cast_pow, Real.log_pow]; norm_num
    have htR : ((t : ℕ) : ℝ) = (k : ℝ) ^ 10 := by rw [ht]; push_cast; ring
    have hzlog : (k : ℝ) ^ 10 / 64 ≤ Real.log z := by
      rw [hz, Nat.cast_pow, Real.log_pow]
      have h16 : t ≤ 32 * (t / 16) := by omega
      have h16R : ((t : ℕ) : ℝ) ≤ 32 * ((t / 16 : ℕ) : ℝ) := by exact_mod_cast h16
      rw [htR] at h16R
      have := Real.log_two_gt_d9
      have : (0 : ℝ) ≤ ((t / 16 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hKl : K * Real.log k ^ 3 ≤ (k : ℝ) / (4 * 1331 * 262144) := by
      have := mul_le_mul_of_nonneg_left hlog hK.le
      calc K * Real.log k ^ 3 ≤ K * (1 / (4 * 1331 * 262144 * K) * k) := this
        _ = (k : ℝ) / (4 * 1331 * 262144) := by field_simp
    have hYx : ((X / s : ℕ) : ℝ) + 1 ≤ 2 * ((X : ℝ) / s) := by linarith
    have hlz0 : 0 < Real.log z := lt_of_lt_of_le (by positivity) hzlog
    have hlz3 : ((k : ℝ) ^ 10 / 64) ^ 3 ≤ Real.log z ^ 3 :=
      pow_le_pow_left₀ (by positivity) hzlog 3
    rw [div_le_div_iff₀ (by positivity) (by positivity), hLlog]
    have s1 : K * (((X / s : ℕ) : ℝ) + 1) * (11 * Real.log k) ^ 3 * (2 * (k : ℝ) ^ 29)
        ≤ K * (2 * ((X : ℝ) / s)) * (11 * Real.log k) ^ 3 * (2 * (k : ℝ) ^ 29) := by
      gcongr
    have s2 : K * (2 * ((X : ℝ) / s)) * (11 * Real.log k) ^ 3 * (2 * (k : ℝ) ^ 29)
        = (4 * 1331) * ((X : ℝ) / s) * (k : ℝ) ^ 29 * (K * Real.log k ^ 3) := by ring
    have s3 : (4 * 1331) * ((X : ℝ) / s) * (k : ℝ) ^ 29 * (K * Real.log k ^ 3)
        ≤ (4 * 1331) * ((X : ℝ) / s) * (k : ℝ) ^ 29 * ((k : ℝ) / (4 * 1331 * 262144)) := by
      gcongr
    have s4 : (4 * 1331) * ((X : ℝ) / s) * (k : ℝ) ^ 29 * ((k : ℝ) / (4 * 1331 * 262144))
        = (X : ℝ) / s * ((k : ℝ) ^ 10 / 64) ^ 3 := by ring
    have s5 : (X : ℝ) / s * ((k : ℝ) ^ 10 / 64) ^ 3 ≤ (X : ℝ) / s * Real.log z ^ 3 :=
      mul_le_mul_of_nonneg_left hlz3 hxpos.le
    linarith
  have hsplit : 1 * (X : ℝ) / ((s : ℝ) * (k : ℝ) ^ 29)
      = (X : ℝ) / s / (2 * (k : ℝ) ^ 29) + (X : ℝ) / s / (2 * (k : ℝ) ^ 29) := by
    field_simp; ring
  rw [hsplit]
  linarith

end OMALib694.Triple

theorem OMA.solution : OMA.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1.H3 :=
  OMALib694.Triple.h3
