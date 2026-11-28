import OMAReductions.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1
import Mathlib

/-!
# The lower bound in the Erdős–Tenenbaum density estimate

Credit: @deepqntm. The prime cutoff and its large-deviation exponent follow the earlier
desk analysis by @MechaNuggan. The Mertens estimates are from the checked repository
proof of Romanoff's theorem (`Erdos16.erdos_16.variant.romanoff`). Periodic counting
follows the checked `Erdos470` positive-density reduction.

`density_power_lower` proves the lower bound at every sufficiently small positive threshold.
-/

open scoped Classical
namespace OMALib.Mertens

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

/-- Partial sums used in the proof of Mertens' second theorem. -/
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


end OMALib.Mertens

open Filter Finset Topology Erdos448

namespace OMA.Erdos448Bound

-- Periodic counting adapted from the checked Erdos470 weird_pos_density reduction.
private lemma periodic_hasDensity {p : ℕ → Prop} {d : ℕ}
    [DecidablePred p] (hd : 0 < d) (hp : Function.Periodic p d) :
    {n : ℕ | p n}.HasDensity ((Nat.count p d : ℝ) / d) := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 ≤ density := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n := by
    change Nat.count (fun i ↦ p (i + d)) n = Nat.count p n
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * d + r) = (q + 1) * count d + count r
      rw [Nat.succ_mul, add_right_comm (q * d) d r, Nat.count_add', hshift]
      change count (q * d + r) + count d = (q + 1) * count d + count r
      rw [ih, Nat.succ_mul, add_right_comm]
  have hncard (n : ℕ) : ({m : ℕ | p m} ∩ Set.Iio n).ncard = count n := by
    rw [show {m : ℕ | p m} ∩ Set.Iio n =
        (↑((Finset.range n).filter p) : Set ℕ) by ext m; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(count n : ℝ) / (n : ℝ) - density| ≤ (d : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let r := n % d
    let q := n / d
    have hsplit : q * d + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n d
    have hcount : q * count d + count r = count n := (hblocks q r).symm.trans (congrArg count hsplit)
    have hsplit' : (q : ℝ) * (d : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    have hcount' : (q : ℝ) * (count d : ℝ) + (count r : ℝ) = (count n : ℝ) := by
      exact_mod_cast hcount
    have hd_mul : (d : ℝ) * density = (count d : ℝ) :=
      mul_div_cancel₀ _ hd'.ne'
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hr : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt n hd).le
    have hcount_r : (count r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.count_le (p := p)
    have herror : (count n : ℝ) / (n : ℝ) - density =
        ((count r : ℝ) - (r : ℝ) * density) / (n : ℝ) := by
      apply (eq_div_iff hn'.ne').mpr
      calc
        _ = (count n : ℝ) - (n : ℝ) * density := by field_simp
        _ = _ := by rw [← hcount', ← hsplit', add_mul, mul_assoc, hd_mul]; ring
    rw [herror, abs_div, abs_of_pos hn']
    apply div_le_div_of_nonneg_right _ hn'.le
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left hdensity_le (Nat.cast_nonneg r)
      linarith [Nat.cast_nonneg (α := ℝ) (count r)]
    · have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hdensity
      linarith
  have ht : Tendsto (fun n : ℕ ↦ (count n : ℝ) / (n : ℝ) - density) atTop (𝓝 0) := by
    have hu := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    have hl : Tendsto (fun n : ℕ ↦ -((d : ℝ) / n)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hu.neg
    refine hl.squeeze' hu ?_ ?_
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).1
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).2
  simpa [Set.HasDensity, Set.partialDensity, hncard] using ht.add_const density

/-- Each divisor of the second factor contributes at most `log₂ a + 2` dyadic blocks. -/
theorem tauPlus_mul_le (a b : ℕ) :
    tauPlus (a * b) ≤ b.divisors.card * (Nat.log 2 a + 2) := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp [tauPlus]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [tauPlus]
  let bins := fun x : ℕ × ℕ => Nat.log 2 x.1 + x.2
  change ((a * b).divisors.image (Nat.log 2)).card ≤ _
  calc
    _ ≤ ((b.divisors ×ˢ range (Nat.log 2 a + 2)).image bins).card := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hj
      obtain ⟨u, v, hu, hv, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hd)
      have hu0 := Nat.pos_of_dvd_of_pos hu (Nat.pos_of_ne_zero ha)
      have hv0 := Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hb)
      have hlow : Nat.log 2 v ≤ Nat.log 2 (u * v) :=
        Nat.log_mono_right (Nat.le_mul_of_pos_left _ hu0)
      have hhigh : Nat.log 2 (u * v) < Nat.log 2 v + (Nat.log 2 a + 2) := by
        apply Nat.log_lt_of_lt_pow (Nat.mul_pos hu0 hv0).ne'
        calc
          u * v < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 v + 1) :=
            Nat.mul_lt_mul_of_lt_of_lt
              ((Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hu).trans_lt (Nat.lt_pow_succ_log_self (by decide) a))
              (Nat.lt_pow_succ_log_self (by decide) v)
          _ = _ := by rw [← pow_add]; congr 1; omega
      apply mem_image.mpr
      refine ⟨(v, Nat.log 2 (u * v) - Nat.log 2 v),
        mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hv, hb⟩, mem_range.mpr (by omega)⟩, ?_⟩
      dsimp [bins]
      omega
    _ ≤ _ := Finset.card_image_le.trans_eq (by simp)

/-- The integers with selected factor `a` and remaining factor coprime to `M`. -/
def exactFactor (M a : ℕ) : Set ℕ := {n | (a * M).gcd n = a}

theorem exactFactor_hasDensity {M a : ℕ} (hM : 0 < M) (ha : 0 < a) :
    (exactFactor M a).HasDensity ((M.totient : ℝ) / M * (a : ℝ)⁻¹) := by
  let P := fun n => (a * M).gcd n = a
  have hper : Function.Periodic P (a * M) := fun n => by
    simp only [P, Nat.gcd_add_self_right]
  have h := periodic_hasDensity (Nat.mul_pos ha hM) hper
  have hc : (Nat.count P (a * M)) = M.totient := by
    rw [Nat.count_eq_card_filter_range]
    have hφ := Nat.totient_div_of_dvd (dvd_mul_right a M)
    simpa [P, ha] using hφ.symm
  rw [hc] at h
  simpa [exactFactor, P, Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem exactFactor_iff {M a n : ℕ} (ha : 0 < a) :
    n ∈ exactFactor M a ↔ ∃ b, n = a * b ∧ M.Coprime b := by
  change (a * M).gcd n = a ↔ _
  constructor
  · intro h
    have had : a ∣ n := h ▸ Nat.gcd_dvd_right (a * M) n
    obtain ⟨b, rfl⟩ := had
    refine ⟨b, rfl, ?_⟩
    simpa [Nat.gcd_mul_left, ha.ne', Nat.Coprime] using h
  · rintro ⟨b, rfl, hb⟩
    rw [Nat.gcd_mul_left, hb.gcd_eq_one, mul_one]

theorem le_upperDensity_of_subset {S T : Set ℕ} {d : ℝ} (hS : S.HasDensity d) (hST : S ⊆ T) :
    d ≤ T.upperDensity := by
  rw [← hS.limsup_eq]
  refine Filter.limsup_le_limsup (.of_forall fun n => ?_)
    (isCoboundedUnder_le_of_le atTop (x := (0 : ℝ)) fun n => by positivity)
    (isBoundedUnder_of_eventually_le (.of_forall fun n => Set.partialDensity_le_one T Set.univ n))
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ hST)

theorem hasDensity_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y : ι → Set ℕ) (d : ι → ℝ)
    (hY : ∀ i ∈ s, (Y i).HasDensity (d i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Y i) (Y j)) :
    (⋃ i ∈ s, Y i).HasDensity (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hk]
    have hD : Disjoint (Y k) (⋃ j ∈ s, Y j) := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun j hj => hdisj k (mem_insert_self _ _) j (mem_insert_of_mem hj) (by rintro rfl; exact hk hj)
    have hsum := (hY k (mem_insert_self k s)).add
      (ih (fun i hi => hY i (mem_insert_of_mem hi))
        (fun i hi j hj => hdisj i (mem_insert_of_mem hi) j (mem_insert_of_mem hj)))
    refine hsum.congr fun n => ?_
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, ← add_div,
      Set.union_inter_distrib_right, Set.ncard_union_eq (hD.mono Set.inter_subset_left Set.inter_subset_left)
        ((Set.finite_Iio n).inter_of_right _) ((Set.finite_Iio n).inter_of_right _), Nat.cast_add]

def smallRatio (ε : ℝ) : Set ℕ := {n | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}

theorem exactFactor_subset_smallRatio {M a : ℕ} {ε : ℝ} (hM : 1 < M) (ha : a ∣ M)
    (hsmall : (Nat.log 2 a : ℝ) + 2 < ε * (a.divisors.card : ℝ)) :
    exactFactor M a ⊆ smallRatio ε := by
  have ha0 := Nat.pos_of_dvd_of_pos ha (by omega : 0 < M)
  intro n hn
  obtain ⟨b, rfl, hMb⟩ := (exactFactor_iff ha0).mp hn
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hMb
    omega
  have hτ : (0 : ℝ) < b.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hb0⟩
  change (tauPlus (a * b) : ℝ) < _
  rw [(hMb.of_dvd_left ha).card_divisors_mul, Nat.cast_mul]
  calc
    (tauPlus (a * b) : ℝ) ≤ ((Nat.log 2 a : ℝ) + 2) * b.divisors.card := by
      exact_mod_cast (tauPlus_mul_le a b).trans_eq (Nat.mul_comm _ _)
    _ < (ε * a.divisors.card) * b.divisors.card := mul_lt_mul_of_pos_right hsmall hτ
    _ = _ := mul_assoc _ _ _

/-- Sum the exact densities for any collection of suitable divisors of a modulus. -/
theorem density_lower_from_divisors {M : ℕ} (hM : 1 < M) (A : Finset ℕ) {ε : ℝ}
    (hA : ∀ a ∈ A, a ∣ M)
    (hε : ∀ a ∈ A, (Nat.log 2 a : ℝ) + 2 < ε * (a.divisors.card : ℝ)) :
    (M.totient : ℝ) / M * (∑ a ∈ A, (a : ℝ)⁻¹) ≤ (smallRatio ε).upperDensity := by
  rw [mul_sum]
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => Nat.pos_of_dvd_of_pos (hA a ha) (by omega)
  apply le_upperDensity_of_subset (hasDensity_biUnion A (exactFactor M) _
    (fun a ha => exactFactor_hasDensity (by omega) (hpos a ha)) ?_)
  · exact Set.iUnion₂_subset fun a ha => exactFactor_subset_smallRatio hM (hA a ha) (hε a ha)
  · intro a ha c hc hac
    rw [Set.disjoint_left]
    intro n hn hn'
    have hg {v : ℕ} (hv : v ∈ A) (hnv : n ∈ exactFactor M v) : M.gcd n = v := by
      obtain ⟨b, rfl, hb⟩ := (exactFactor_iff (hpos v hv)).mp hnv
      rw [hb.symm.gcd_mul_right_cancel_right, Nat.gcd_eq_right (hA v hv)]
    exact hac ((hg ha hn).symm.trans (hg hc hn'))

end OMA.Erdos448Bound

open Filter Finset Real Topology
namespace OMA.Erdos448Bound

/-- Total reciprocal weight of the products of `k` distinct primes of `Q`. -/
noncomputable def symWeight (Q : Finset ℕ) (k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ A ∈ Q.powersetCard k, ∏ p ∈ A, w p

/-- Count the ways to add one new prime to a product. -/
theorem symWeight_step (Q : Finset ℕ) (k : ℕ) (w : ℕ → ℝ) :
    (k + 1 : ℝ) * symWeight Q (k + 1) w =
      ∑ A ∈ Q.powersetCard k, (∏ p ∈ A, w p) * ∑ p ∈ Q \ A, w p := by
  classical
  calc
    _ = ∑ A ∈ Q.powersetCard (k+1), ∑ _p ∈ A, ∏ q ∈ A, w q := by
      unfold symWeight
      rw [mul_sum]
      refine sum_congr rfl fun A hA => ?_
      simp [(mem_powersetCard.mp hA).2]
    _ = ∑ A ∈ Q.powersetCard k, ∑ p ∈ Q \ A, (∏ q ∈ A, w q) * w p := by
      rw [sum_sigma', sum_sigma']
      apply sum_nbij' (fun u : (Σ _A : Finset ℕ, ℕ) => ⟨u.1.erase u.2, u.2⟩)
        (fun u => ⟨insert u.2 u.1, u.2⟩)
      · rintro ⟨A, p⟩ h
        simp only [mem_sigma, mem_powersetCard, Finset.mem_sdiff] at h ⊢
        exact ⟨⟨(erase_subset _ _).trans h.1.1, by rw [card_erase_of_mem h.2, h.1.2]; omega⟩,
          h.1.1 h.2, notMem_erase _ _⟩
      · rintro ⟨A, p⟩ h
        simp only [mem_sigma, mem_powersetCard, Finset.mem_sdiff] at h ⊢
        exact ⟨⟨insert_subset h.2.1 h.1.1, by rw [card_insert_of_notMem h.2.2, h.1.2]⟩,
          mem_insert_self _ _⟩
      · rintro ⟨A,p⟩ h
        simp only [mem_sigma] at h
        simp [insert_erase h.2]
      · rintro ⟨A,p⟩ h
        simp only [mem_sigma, Finset.mem_sdiff] at h
        simp [erase_insert h.2.2]
      · rintro ⟨A,p⟩ h
        simp only [mem_sigma] at h
        exact (prod_erase_mul _ _ h.2).symm
    _ = _ := by simp only [mul_sum]

/-- Lower bound an elementary symmetric sum by selecting the primes successively. -/
theorem pow_le_factorial_mul_symWeight (Q : Finset ℕ) (w : ℕ → ℝ) (k : ℕ)
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hw : ∀ p ∈ Q, 0 ≤ w p ∧ w p ≤ B) (hroom : L + k * B ≤ ∑ p ∈ Q, w p) :
    L ^ k ≤ (k.factorial : ℝ) * symWeight Q k w := by
  induction k with
  | zero => simp [symWeight]
  | succ k ih =>
    have hstep : L + k * B ≤ ∑ p ∈ Q, w p := by push_cast at hroom; nlinarith
    have hrec : symWeight Q k w * L ≤ (k + 1 : ℝ) * symWeight Q (k+1) w := by
      rw [symWeight_step]
      unfold symWeight
      rw [sum_mul]
      refine sum_le_sum fun A hA => mul_le_mul_of_nonneg_left ?_
        (prod_nonneg fun p hp => (hw _ ((mem_powersetCard.mp hA).1 hp)).1)
      rw [sum_sdiff_eq_sub (mem_powersetCard.mp hA).1]
      have hA' : ∑ p ∈ A, w p ≤ k * B := calc
        _ ≤ ∑ _p ∈ A, B := sum_le_sum fun p hp => (hw _ ((mem_powersetCard.mp hA).1 hp)).2
        _ = _ := by simp [(mem_powersetCard.mp hA).2]
      linarith
    calc
      L ^ (k+1) = L^k * L := pow_succ _ _
      _ ≤ (k.factorial : ℝ) * (symWeight Q k w * L) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (ih hstep) hL
      _ ≤ k.factorial * ((k + 1 : ℝ) * symWeight Q (k+1) w) :=
        mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.factorial_succ]; push_cast; ring

def primeProduct (D : Finset ℕ) : ℕ := ∏ p ∈ D, p

theorem primeProduct_divisors (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    (primeProduct D).divisors.card = 2^D.card := by
  induction D using Finset.induction_on with
  | empty => simp [primeProduct]
  | insert p D hp ih =>
    have hp' := hD p (mem_insert_self _ _)
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (primeProduct D) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp' (hD' q hq)).mpr (fun e => hp (e ▸ hq))
    rw [show primeProduct (insert p D) = p * primeProduct D from prod_insert hp,
      hcop.card_divisors_mul, ih hD', hp'.divisors, card_insert_of_notMem hp, pow_succ]
    simp [Ne.symm hp'.ne_one, mul_comm]

/-- A quantitative lower bound for the upper density, using `k` primes up to `y`. -/
theorem prime_subset_density {M : ℕ} (hM : 1 < M) (Q : Finset ℕ) (k : ℕ) {y ε : ℝ}
    (_hy : 0 < y) (hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ y) (hMQ : primeProduct Q ∣ M)
    (hsmall : k * Real.log y / Real.log 2 + 2 < ε * (2 : ℝ)^k) :
    (M.totient : ℝ) / M * symWeight Q k (fun p => (p : ℝ)⁻¹) ≤ (smallRatio ε).upperDensity := by
  let A := (Q.powersetCard k).image primeProduct
  have hpD {D : Finset ℕ} (hD : D ∈ Q.powersetCard k) : ∀ p ∈ D, p.Prime :=
    fun p hp => (hQ p ((mem_powersetCard.mp hD).1 hp)).1
  have heq : symWeight Q k (fun p => (p : ℝ)⁻¹) = ∑ a ∈ A, (a : ℝ)⁻¹ := by
    dsimp [A, symWeight]
    rw [sum_image]
    · simp [primeProduct, prod_inv_distrib]
    · intro D hD E hE h
      simpa [primeProduct, Nat.primeFactors_prod (hpD hD), Nat.primeFactors_prod (hpD hE)] using
        congrArg Nat.primeFactors h
  rw [heq]
  apply density_lower_from_divisors hM A
  · intro a ha
    obtain ⟨D,hD,rfl⟩ := mem_image.mp ha
    exact (prod_dvd_prod_of_subset D Q id (mem_powersetCard.mp hD).1).trans hMQ
  · intro a ha
    obtain ⟨D,hD,rfl⟩ := mem_image.mp ha
    have hpos : 0 < primeProduct D := prod_pos fun p hp => (hpD hD p hp).pos
    have hle : (primeProduct D : ℝ) ≤ y ^ k := by
      unfold primeProduct
      push_cast
      rw [← (mem_powersetCard.mp hD).2]
      exact (prod_le_prod (fun p _ => Nat.cast_nonneg (α := ℝ) p)
        (fun p hp => (hQ p ((mem_powersetCard.mp hD).1 hp)).2)).trans_eq (by simp)
    have hlog := Real.log_le_log (by exact_mod_cast hpos) hle
    rw [Real.log_pow] at hlog
    have hnat := Real.natLog_le_logb (primeProduct D) 2
    simp only [Real.logb, Nat.cast_ofNat] at hnat
    rw [primeProduct_divisors D (hpD hD), (mem_powersetCard.mp hD).2, Nat.cast_pow, Nat.cast_ofNat]
    exact lt_of_le_of_lt (add_le_add (hnat.trans
      (div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num)).le)) le_rfl) hsmall

end OMA.Erdos448Bound

open Filter Finset Real Topology
namespace OMA.Erdos448Bound

private theorem totient_ratio (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ((primeProduct Q).totient : ℝ) / primeProduct Q = ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors (primeProduct Q))
  push_cast at h
  have hpos : 0 < primeProduct Q := prod_pos fun p hp => (hQ p hp).pos
  rw [div_eq_iff (by exact_mod_cast hpos.ne')]
  simpa only [primeProduct, Nat.primeFactors_prod hQ, one_div, mul_comm] using h

/-- Mertens' bounds at the cutoff `exp (exp (k/2))`. Discarding finitely many
small primes changes the reciprocal sum by a bounded amount. -/
private theorem primes_for_grid (α : ℝ) (hα : 0 < α) (hα' : α < 1/2) :
    ∃ c > 0, ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ,
      k * exp (k/2) / log 2 + 2 < ε * (2:ℝ)^k →
      c / exp (k/2) * ((α*k)^k / (k.factorial : ℝ)) ≤ (smallRatio ε).upperDensity := by
  obtain ⟨B, hB⟩ := exists_nat_gt ((1/2 - α)⁻¹)
  have hB0 : (0 : ℝ) < B := lt_trans (inv_pos.mpr (sub_pos.mpr hα')) hB
  have hBinv : (B:ℝ)⁻¹ < 1/2 - α := (inv_lt_comm₀ hB0 (sub_pos.mpr hα')).mpr hB
  obtain ⟨C, hC⟩ := OMALib.Mertens.mertens2
  obtain ⟨c, c₂, hc, _hc₂, hprod⟩ := OMALib.Mertens.mertens3
  refine ⟨c, hc, ?_⟩
  let boundary := ∑ p ∈ range B, (p:ℝ)⁻¹
  have hgap : 0 < (1/2 - α - (B : ℝ)⁻¹) := by linarith
  have hlarge := ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hgap).eventually
    (eventually_ge_atTop (C + boundary))
  filter_upwards [hlarge] with k hk
  intro ε hε
  let y : ℝ := exp (exp (k/2))
  have hly : log y = exp (k/2) := Real.log_exp _
  have hy : 2 ≤ y := by
    have hone : 1 ≤ exp ((k : ℝ)/2) := Real.one_le_exp (by positivity)
    dsimp [y]
    linarith [Real.add_one_le_exp (exp ((k : ℝ)/2))]
  let P := Nat.primesLE ⌊y⌋₊
  let Q := P.filter (B ≤ ·)
  let w := fun p : ℕ => (p : ℝ)⁻¹
  have hPQ : Q ⊆ P := filter_subset _ _
  have hpP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE hp
  have hM : 1 < primeProduct P := by
    have h2 : 2 ∈ P := Nat.mem_primesLE.mpr ⟨Nat.le_floor hy, Nat.prime_two⟩
    exact lt_of_lt_of_le (by decide : 1 < 2) (Finset.single_le_prod' (f := id)
      (fun p hp => (hpP p hp).one_le) h2)
  have hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ y := by
    intro p hp
    exact ⟨hpP _ (hPQ hp), (Nat.cast_le.mpr (Nat.le_of_mem_primesLE (hPQ hp))).trans
      (Nat.floor_le (by linarith))⟩
  have hw : ∀ p ∈ Q, 0 ≤ w p ∧ w p ≤ (B : ℝ)⁻¹ := by
    intro p hp
    exact ⟨by dsimp [w]; positivity, inv_anti₀ hB0 (by exact_mod_cast (mem_filter.mp hp).2)⟩
  have hdiscard : ∑ p ∈ P \ Q, w p ≤ boundary := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => by dsimp [w]; positivity)
    intro p hp
    have h := mem_sdiff.mp hp
    exact mem_range.mpr (lt_of_not_ge fun hh => h.2 (mem_filter.mpr ⟨h.1, hh⟩))
  have hS : (k:ℝ)/2 - C ≤ ∑ p ∈ P, w p := by
    have h := (abs_le.mp (hC y hy)).1
    rw [hly, Real.log_exp] at h
    simpa only [w, P, one_div] using (by linarith :
      (k:ℝ)/2 - C ≤ ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1:ℝ) / p)
  have hadd := sum_sdiff (f := w) hPQ
  have hroom : α*k + k*(B:ℝ)⁻¹ ≤ ∑ p ∈ Q, w p := by
    change C + boundary ≤ (k : ℝ) * (1/2 - α - (B:ℝ)⁻¹) at hk
    linarith
  have hsym : (α*k)^k / (k.factorial : ℝ) ≤ symWeight Q k w := by
    rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos k)]
    simpa only [mul_comm] using pow_le_factorial_mul_symWeight Q w k (by positivity) (by positivity) hw hroom
  have hcoef : c / exp (k/2) ≤ ((primeProduct P).totient : ℝ) / primeProduct P := by
    rw [totient_ratio P hpP]
    simpa only [P, hly] using (hprod y hy).1
  refine (mul_le_mul hcoef hsym (by positivity) (by positivity)).trans ?_
  apply prime_subset_density hM Q k (y := y) (by linarith) hQ
    (prod_dvd_prod_of_subset Q P id hPQ)
  simpa only [hly] using hε

private theorem eventually_linear_lt_exp (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, A * k + B < exp (δ * k) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) * exp (-(δ*k))) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ hδ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h0 : Tendsto (fun k : ℕ => exp (-(δ*k))) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 δ hδ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun k : ℕ => (A*k+B) / exp (δ*k)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, ← Real.exp_neg, add_mul, mul_assoc] using (h1.const_mul A).add (h0.const_mul B)
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with k hk
  exact (div_lt_one (Real.exp_pos _)).mp hk

private theorem factorial_upper : ∃ C > 0, ∀ k : ℕ, 0 < k →
    (k.factorial : ℝ) ≤ C*k * ((k:ℝ) / exp 1)^k := by
  refine ⟨2 * Stirling.stirlingSeq 1, mul_pos (by norm_num) (Stirling.stirlingSeq'_pos 0), ?_⟩
  rintro (_ | n) h
  · omega
  let k := n+1
  have hk : (1:ℝ) ≤ k := by exact_mod_cast Nat.succ_pos n
  have hst : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le n)
  have hd : 0 < sqrt (2 * k : ℝ) * ((k:ℝ) / exp 1)^k := by positivity
  have hh := (div_le_iff₀ hd).mp hst
  have hsqrt : sqrt (2*k : ℝ) ≤ 2*k := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  change (k.factorial : ℝ) ≤ _
  calc
    _ ≤ Stirling.stirlingSeq 1 * (sqrt (2*k : ℝ) * ((k:ℝ) / exp 1)^k) := hh
    _ ≤ Stirling.stirlingSeq 1 * (2*k * ((k:ℝ) / exp 1)^k) := by
      gcongr
      exact (Stirling.stirlingSeq'_pos 0).le
    _ = _ := by change _ = 2 * Stirling.stirlingSeq 1 * (k : ℝ) * _; ring

noncomputable def rate : ℝ := log 2 - 1/2

theorem rate_pos : 0 < rate := by unfold rate; linarith [Real.log_two_gt_d9]

/-- At threshold `exp (-s k)` the exceptional set has upper density at least
`exp (-u k)`, for every `s < log 2 - 1/2 < u`. -/
theorem grid_lower {s u : ℝ} (hs : s < rate) (hu : rate < u) :
    ∀ᶠ k : ℕ in atTop, exp (-u * k) ≤ (smallRatio (exp (-s*k))).upperDensity := by
  let δ := (u - rate)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let α := exp (-log 2 - δ)
  have hα' : α < 1/2 := by
    have h : α < exp (-log 2) := Real.exp_lt_exp.mpr (by linarith)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2), one_div] using h
  obtain ⟨c, hc, hpacket⟩ := primes_for_grid α (Real.exp_pos _) hα'
  obtain ⟨C, hC, hfac⟩ := factorial_upper
  filter_upwards [hpacket, eventually_gt_atTop 0,
    eventually_linear_lt_exp (1/log 2) 2 (sub_pos.mpr hs),
    eventually_linear_lt_exp (C/c) 0 hδ] with k hpack hk hthreshold hloss
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hth : (k:ℝ) * exp (k/2) / log 2 + 2 < exp (-s*k) * 2^k := by
    have h1 : 1 ≤ exp ((k:ℝ)/2) := Real.one_le_exp (by positivity)
    calc
      _ ≤ ((1/log 2)*k+2) * exp (k/2) := by
        rw [add_mul, show 1/log 2 * (k:ℝ) * exp (k/2) = k * exp (k/2) / log 2 by ring]
        linarith
      _ < exp ((rate-s)*k) * exp (k/2) := mul_lt_mul_of_pos_right hthreshold (exp_pos _)
      _ = _ := by
        have htwo : (2:ℝ)^k = exp (k * log 2) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
        rw [htwo, ← Real.exp_add, ← Real.exp_add]
        congr 1; unfold rate; ring
  refine le_trans ?_ (hpack _ hth)
  have hfacpos : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hexp : (α * exp 1)^k = exp ((1 - log 2 - δ)*k) := by
    dsimp [α]
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1; ring
  have hratio : (α * exp 1)^k / (C*k) ≤ (α*k)^k / (k.factorial : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos hC hk') hfacpos]
    calc
      _ ≤ (α * exp 1)^k * (C*k * ((k:ℝ) / exp 1)^k) :=
        mul_le_mul_of_nonneg_left (hfac k hk) (by positivity)
      _ = _ := by rw [mul_left_comm, ← mul_pow, show α * exp 1 * (↑k / exp 1) = α*k by field_simp, mul_comm (C*k)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hratio (by positivity))
  rw [hexp]
  have he : exp ((1-log 2-δ)*k) = exp (-u*k) * exp (k/2) * exp (δ*k) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [δ, rate]; ring
  rw [he]
  have hck : C*k ≤ c * exp (δ*k) := by
    have : (C*k)/c < exp (δ*k) := by convert hloss using 1; ring
    exact le_of_lt (by simpa [mul_comm] using (div_lt_iff₀ hc).mp this)
  calc
    exp (-u*k) ≤ exp (-u*k) * (c * exp (δ*k) / (C*k)) := by
      apply le_mul_of_one_le_right (exp_pos _).le
      exact (one_le_div (mul_pos hC hk')).mpr hck
    _ = _ := by field_simp

end OMA.Erdos448Bound

open Filter Finset Real Topology Erdos448
namespace OMA.Erdos448Bound

private theorem smallRatio_upperDensity_mono : Monotone fun ε => (smallRatio ε).upperDensity := by
  intro a b hab
  have hsub : smallRatio a ⊆ smallRatio b := fun n hn =>
    lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))
  refine Filter.limsup_le_limsup (.of_forall fun n => ?_)
    (isCoboundedUnder_le_of_le atTop (x := (0:ℝ)) fun n => by positivity)
    (isBoundedUnder_of_eventually_le (.of_forall fun n => Set.partialDensity_le_one _ Set.univ n))
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ hsub)

/-- The full lower half of the Erdős–Tenenbaum exponent, for every sufficiently small
positive real threshold. -/
theorem density_power_lower {p : ℝ} (hp : 1 < p) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε^p ≤ (smallRatio ε).upperDensity := by
  have hp0 : 0 < p := by linarith
  have hdiv : rate/p < rate := (div_lt_iff₀ hp0).mpr (by nlinarith [rate_pos])
  obtain ⟨s, hs₁, hs₂⟩ := exists_between hdiv
  have hs : 0 < s := lt_trans (div_pos rate_pos hp0) hs₁
  obtain ⟨u, hu₁, hu₂⟩ := exists_between ((div_lt_iff₀ hp0).mp hs₁)
  have hu : 0 < u := rate_pos.trans hu₁
  let t := fun ε : ℝ => -log ε / s
  have ht : Tendsto t (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).atTop_div_const hs
  have hg := (tendsto_nat_ceil_atTop.comp ht).eventually (grid_lower hs₂ hu₁)
  have hlarge := (ht.atTop_mul_const (sub_pos.mpr hu₂)).eventually (eventually_ge_atTop u)
  filter_upwards [self_mem_nhdsWithin, hg, hlarge, ht.eventually (eventually_ge_atTop 0)]
    with ε hε hgrid hbig ht0
  change 0 < ε at hε
  let k := ⌈t ε⌉₊
  have hk₁ : t ε ≤ k := Nat.le_ceil _
  have hk₂ : (k:ℝ) < t ε + 1 := Nat.ceil_lt_add_one ht0
  have hts : t ε * s = -log ε := div_mul_cancel₀ _ hs.ne'
  have hexp : exp (-s*k) ≤ ε := by
    rw [← Real.le_log_iff_exp_le hε]
    nlinarith [mul_le_mul_of_nonneg_right hk₁ hs.le]
  calc
    ε^p = exp (log ε * p) := Real.rpow_def_of_pos hε _
    _ ≤ exp (-u*k) := by
      apply Real.exp_le_exp.mpr
      change u ≤ t ε * (s*p-u) at hbig
      nlinarith [mul_lt_mul_of_pos_right hk₂ hu, congrArg (· * p) hts]
    _ ≤ (smallRatio (exp (-s*k))).upperDensity := hgrid
    _ ≤ _ := smallRatio_upperDensity_mono hexp

end OMA.Erdos448Bound

theorem OMA.solution : OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1.H1 := by
  intro p hp
  exact OMA.Erdos448Bound.density_power_lower hp
