import OMAReductions.R_BalancedPrimes_balanced_primes_R1
import Mathlib

-- Step BalancedPrimes.balanced_primes.R1.H2: hypothesis H2 of reduction BalancedPrimes.balanced_primes.R1 (upper-bound sieve for prime quadruples).
-- Credit: @ivillar. The Mertens theorems (namespace OMALib.Mertens), the Selberg sieve for residue
-- conditions and the Rankin lower bound (namespace OMALib.Sieve) are reused unchanged from the merged
-- proof proofs/Erdos16.erdos_16.variant.romanoff.R1.H1.lean (PR 2471; see
-- the credit text). New here: the four-dimensional sieve for n, n + 6, n + 12, n + c and the assembly.

section BPLib

/-!
Mertens' theorems.

Elementary proofs, over the reals, of the three theorems of Mertens (1874):

* `OMALib.Mertens.abs_sum_log_div_sub_log_le` (first theorem):
  `|∑_{p ≤ x} log p / p - log x| ≤ mertens1Const + log 2` for `x ≥ 1`;
* `OMALib.Mertens.abs_sum_inv_sub_log_log_le` (second theorem):
  `|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const` for `x ≥ 2`;
* `OMALib.Mertens.prod_one_sub_inv_bounds` (third theorem, product form):
  `exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp mertens2Const / log z` for `z ≥ 2`;

with existential forms `mertens1`, `mertens2`, `mertens3`. Sums over primes `p ≤ x` are written
`∑ p ∈ Nat.primesLE ⌊x⌋₊`, as in `Mathlib.NumberTheory.Chebyshev`.

The first theorem follows from Legendre's formula for `log N!`, the bounds
`N log N - N ≤ log N! ≤ N log N` and Chebyshev's bound `θ(N) ≤ N log 4`. The second follows
from the first by discrete partial summation, run as an induction on `N`. The third follows from
the second and `-t / (1 - t) ≤ log (1 - t) ≤ -t`.
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


/-- Upper half of Mertens' second theorem for any subset of the primes, for instance the primes
in a residue class: `∑_{p ≤ x, P p} 1 / p ≤ log log x + mertens2Const` for real `x ≥ 2`. -/
theorem sum_inv_filter_le (P : ℕ → Prop) [DecidablePred P] (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      Real.log (Real.log x) + mertens2Const := by
  have h := abs_sum_inv_sub_log_log_le x hx
  rw [abs_le] at h
  have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith [h.2]

end OMALib.Mertens


open scoped Classical
open Finset

namespace OMALib.Sieve

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


/-! ## Prime quadruples `n, n + 6, n + 12, n + c` -/

/-- The local condition of the quadruple sieve: `p ∣ n (n + 6) (n + 12) (n + c)`. -/
def quadCond (c : ℕ) (p n : ℕ) : Prop := p ∣ n * (n + 6) * (n + 12) * (n + c)

theorem quadCond_periodic (c p n : ℕ) : quadCond c p n ↔ quadCond c p (n % p) := by
  unfold quadCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

/-- Selberg's `G(z)` for the quadruple sieve. -/
noncomputable def quadG (c z : ℕ) : ℝ :=
  selbergG (fun p => (omega (quadCond c) p : ℝ) / p) (levelFamily (Nat.primesBelow z) z)

theorem card_root_le_one (p a : ℕ) (hp : 0 < p) :
    ((range p).filter (fun r => p ∣ r + a)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [mem_filter, mem_range] at hx hy
  have h1 : (x + a) % p = (y + a) % p := by
    rw [Nat.mod_eq_zero_of_dvd hx.2, Nat.mod_eq_zero_of_dvd hy.2]
  have h2 : x % p = y % p := Nat.ModEq.add_right_cancel' a h1
  rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h2

theorem omega_quad_le (c p : ℕ) (hp : p.Prime) : omega (quadCond c) p ≤ 4 := by
  unfold omega
  have hsub : (range p).filter (quadCond c p) ⊆
      (((range p).filter (fun r => p ∣ r + 0) ∪ (range p).filter (fun r => p ∣ r + 6)) ∪
        (range p).filter (fun r => p ∣ r + 12)) ∪ (range p).filter (fun r => p ∣ r + c) := by
    intro r hr
    simp only [mem_filter, mem_range, mem_union, quadCond] at hr ⊢
    obtain ⟨hr, hd⟩ := hr
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hr, by simpa using h⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hr, h⟩))
      · exact Or.inl (Or.inr ⟨hr, h⟩)
    · exact Or.inr ⟨hr, h⟩
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have h0 := card_root_le_one p 0 hp.pos
  have h6 := card_root_le_one p 6 hp.pos
  have h12 := card_root_le_one p 12 hp.pos
  have hc := card_root_le_one p c hp.pos
  have := card_union_le ((range p).filter (fun r => p ∣ r + 0) ∪
    (range p).filter (fun r => p ∣ r + 6)) ((range p).filter (fun r => p ∣ r + 12))
  have := card_union_le ((range p).filter (fun r => p ∣ r + 0))
    ((range p).filter (fun r => p ∣ r + 6))
  omega

theorem omega_quad_pos (c p : ℕ) (hp : p.Prime) : 0 < omega (quadCond c) p := by
  unfold omega
  apply Finset.card_pos.mpr
  exact ⟨0, mem_filter.mpr ⟨mem_range.mpr hp.pos, by simp [quadCond]⟩⟩

theorem omega_lt_of_not (C : ℕ → ℕ → Prop) (p r : ℕ) (hr : r < p) (hC : ¬ C p r) :
    omega C p < p := by
  unfold omega
  have hsub : (range p).filter (C p) ⊆ (range p).erase r := by
    intro x hx
    simp only [mem_filter, mem_range] at hx
    refine mem_erase.mpr ⟨fun h => hC (h ▸ hx.2), mem_range.mpr hx.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (mem_range.mpr hr), card_range] at this
  omega

theorem omega_quad_lt (c p : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hp : p.Prime) :
    omega (quadCond c) p < p := by
  by_cases h5 : 5 ≤ p
  · have := omega_quad_le c p hp; omega
  have hp2 := hp.two_le
  have h : p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases h with rfl | rfl | rfl
  · apply omega_lt_of_not _ 2 1 (by norm_num)
    unfold quadCond
    rcases hc with rfl | rfl | rfl | rfl <;> decide
  · rcases hc with rfl | rfl | rfl | rfl
    · exact omega_lt_of_not _ 3 2 (by norm_num) (by unfold quadCond; decide)
    · exact omega_lt_of_not _ 3 1 (by norm_num) (by unfold quadCond; decide)
    · exact omega_lt_of_not _ 3 2 (by norm_num) (by unfold quadCond; decide)
    · exact omega_lt_of_not _ 3 1 (by norm_num) (by unfold quadCond; decide)
  · exact absurd hp (by norm_num)

theorem omega_quad_ge (c p : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hp13 : 13 ≤ p) :
    4 ≤ omega (quadCond c) p := by
  unfold omega
  have hc12 : c < 12 := by omega
  have hsub : ({0, p - 6, p - 12, p - c} : Finset ℕ) ⊆ (range p).filter (quadCond c p) := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    unfold quadCond
    rcases hr with rfl | rfl | rfl | rfl
    · simp
    · rw [show p - 6 + 6 = p by omega]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_mul_left p _) _) _
    · rw [show p - 12 + 12 = p by omega]
      exact Dvd.dvd.mul_right (dvd_mul_left p _) _
    · rw [show p - c + c = p by omega]
      exact dvd_mul_left p _
  have hcard : ({0, p - 6, p - 12, p - c} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp only [mem_singleton]; omega
    · simp only [mem_insert, mem_singleton]; omega
    · simp only [mem_insert, mem_singleton]; omega
  have := card_le_card hsub
  omega

theorem quad_hFun (c : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) {p : ℕ} (hp : p.Prime) :
    hFun (fun p => (omega (quadCond c) p : ℝ) / p) p
      = (omega (quadCond c) p : ℝ) / ((p : ℝ) - omega (quadCond c) p) := by
  have hlt : (omega (quadCond c) p : ℝ) < p := by exact_mod_cast omega_quad_lt c p hc hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold hFun
  have : (p : ℝ) - omega (quadCond c) p ≠ 0 := by linarith
  field_simp

theorem quad_hFun_nonneg (c : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) {p : ℕ}
    (hp : p.Prime) : 0 ≤ hFun (fun p => (omega (quadCond c) p : ℝ) / p) p := by
  rw [quad_hFun c hc hp]
  have hlt : (omega (quadCond c) p : ℝ) < p := by exact_mod_cast omega_quad_lt c p hc hp
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem quad_hFun_le (c : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) {p : ℕ} (hp : p.Prime) :
    hFun (fun p => (omega (quadCond c) p : ℝ) / p) p ≤ 20 / p := by
  rw [quad_hFun c hc hp]
  have hlt := omega_quad_lt c p hc hp
  have hle := omega_quad_le c p hp
  have hp2 := hp.two_le
  have key : omega (quadCond c) p * (p + 20) ≤ 20 * p := by
    by_cases h5 : 5 ≤ p
    · nlinarith
    · have : p = 2 ∨ p = 3 ∨ p = 4 := by omega
      rcases this with rfl | rfl | rfl <;> omega
  have key' : (omega (quadCond c) p : ℝ) * ((p : ℝ) + 20) ≤ 20 * p := by exact_mod_cast key
  have hltR : (omega (quadCond c) p : ℝ) < p := by exact_mod_cast hlt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [div_le_div_iff₀ (by linarith) hp0]
  nlinarith

theorem quad_one_add_hFun_ge (c : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) {p : ℕ}
    (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 4 * (if p < 13 then 1 / 16 else 1)
      ≤ 1 + hFun (fun p => (omega (quadCond c) p : ℝ) / p) p := by
  have hH := quad_hFun_nonneg c hc hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div]
  split_ifs with h13
  · have h1 : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h0 : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := div_nonneg hp0.le (by linarith)
    have h2 : ((p : ℝ) / ((p : ℝ) - 1)) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith
  · push_neg at h13
    have h4 : omega (quadCond c) p = 4 :=
      le_antisymm (omega_quad_le c p hp) (omega_quad_ge c p hc h13)
    rw [quad_hFun c hc hp, h4]
    have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast h13
    push_cast
    have hp4 : (p : ℝ) - 4 ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [mul_one, show (1 : ℝ) + 4 / ((p : ℝ) - 4) = p / ((p : ℝ) - 4) by
      field_simp; ring]
    rw [div_pow, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [sq_nonneg ((p : ℝ) - 1), sq_nonneg (p : ℝ), mul_pos hp0 hp0]

/-- Euler-product lower bound for the quadruple sieve. -/
theorem quad_euler_ge (c Y : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 4 * (1 / 16) ^ 5
      ≤ ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (omega (quadCond c) p : ℝ) / p) p) := by
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hf : ∀ p ∈ Q, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have step1 : ∏ p ∈ Q, ((1 - 1 / (p : ℝ))⁻¹ ^ 4 * (if p < 13 then 1 / 16 else 1))
      ≤ ∏ p ∈ Q, (1 + hFun (fun p => (omega (quadCond c) p : ℝ) / p) p) :=
    prod_le_prod (fun p hp => by
      have := hf p hp
      split_ifs <;> positivity) fun p hp => quad_one_add_hFun_ge c hc (hQp p hp)
  rw [prod_mul_distrib, prod_pow, prod_inv_distrib] at step1
  refine le_trans ?_ step1
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  have hcard : (Q.filter (fun p => p < 13)).card ≤ 5 := by
    have hsub : Q.filter (fun p => p < 13) ⊆ ({2, 3, 5, 7, 11} : Finset ℕ) := by
      intro p hp
      simp only [mem_filter] at hp
      have hpp := hQp p hp.1
      have h13 := hp.2
      simp only [mem_insert, mem_singleton]
      interval_cases p <;> first | (norm_num at hpp; done) | simp
    exact (card_le_card hsub).trans (by decide)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard

/-- Rankin step for the quadruple sieve: with `log Y ≤ log z / 121`,
`G(z) ≥ ½ Π_{p ≤ Y} (1 + h(p))`. -/
theorem quad_rankin_half (c z Y : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hY3 : 3 ≤ Y)
    (hYz : Y < z) (hlYup : Real.log Y ≤ Real.log z / 121)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4) :
    (1 / 2) * ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (omega (quadCond c) p : ℝ) / p) p)
      ≤ quadG c z := by
  set g : ℕ → ℝ := fun p => (omega (quadCond c) p : ℝ) / p
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
    (fun p hp => quad_hFun_nonneg c hc (Nat.mem_primesBelow.mp hp).2) z (by omega) hε
  change _ ≤ quadG c z at hrank
  set H : ℕ → ℝ := fun p => hFun g p
  have hH0 : ∀ p ∈ Q, 0 ≤ H p := fun p hp => quad_hFun_nonneg c hc (hQp p hp)
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
  have hsumtail : ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1) ≤ 120 := by
    calc ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)
        ≤ ∑ p ∈ Q, (20 / (p : ℝ)) * (2 * (Real.log p / Real.log Y)) := by
          refine sum_le_sum fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have : (0 : ℝ) ≤ (p : ℝ) ^ ε - 1 := by
            have := Real.one_le_rpow hp1 hε; linarith
          exact mul_le_mul (quad_hFun_le c hc (hQp p hp)) (hpe p hp) this (by positivity)
      _ = (40 / Real.log Y) * ∑ p ∈ Q, Real.log p / p := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      _ ≤ (40 / Real.log Y) * (Real.log Y + Real.log 4) :=
          mul_le_mul_of_nonneg_left (hM1 Y) (by positivity)
      _ ≤ 120 := by
          have h4 : Real.log 4 ≤ 2 * Real.log Y := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
            linarith
          rw [div_mul_eq_mul_div, div_le_iff₀ hlY]; nlinarith
  have hprod_tail : ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 120 := by
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
      _ ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 120 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsumtail)
            (prod_nonneg fun p hp => by have := hH0 p hp; linarith)
  have hzeps : (z : ℝ) ^ (-ε) ≤ Real.exp (-121) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    simp only [ε]
    rw [mul_neg, mul_one_div, neg_le_neg_iff, le_div_iff₀ hlY]; linarith
  have hP0 : 0 ≤ ∏ p ∈ Q, (1 + H p) := prod_nonneg fun p hp => by have := hH0 p hp; linarith
  have he : Real.exp (-121) * Real.exp 120 ≤ 1 / 2 := by
    rw [← Real.exp_add]; norm_num
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
  have ht : (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := by
    calc (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ Real.exp (-121) * ((∏ p ∈ Q, (1 + H p)) * Real.exp 120) :=
          mul_le_mul hzeps hprod_tail (prod_nonneg fun p hp => by
            have := hH0 p hp; positivity) (Real.exp_pos _).le
      _ = (Real.exp (-121) * Real.exp 120) * ∏ p ∈ Q, (1 + H p) := by ring
      _ ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := mul_le_mul_of_nonneg_right he hP0
  linarith

/-- The sieve bound for prime quadruples `n, n + 6, n + 12, n + c` with `n < X`. -/
theorem card_quad_le_sieve (c X z : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hz : 2 ≤ z) :
    (((range X).filter (fun n => n.Prime ∧ (n + 6).Prime ∧ (n + 12).Prime ∧
        (n + c).Prime)).card : ℝ) ≤ z + X / quadG c z + (z : ℝ) ^ 4 := by
  set Q := Nat.primesBelow z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hsub : (range X).filter (fun n => n.Prime ∧ (n + 6).Prime ∧ (n + 12).Prime ∧
        (n + c).Prime)
      ⊆ range z ∪ (range X).filter (fun n => ∀ p ∈ Q, ¬ quadCond c p n) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [mem_union, mem_range, mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      obtain ⟨hnX, h0, h6, h12, hcc⟩ := hn
      refine ⟨hnX, fun q hq hdiv => ?_⟩
      have hq' := Nat.mem_primesBelow.mp hq
      unfold quadCond at hdiv
      rcases (hq'.2.dvd_mul).mp hdiv with h | h
      · rcases (hq'.2.dvd_mul).mp h with h | h
        · rcases (hq'.2.dvd_mul).mp h with h | h
          · have := (Nat.prime_dvd_prime_iff_eq hq'.2 h0).mp h; omega
          · have := (Nat.prime_dvd_prime_iff_eq hq'.2 h6).mp h; omega
        · have := (Nat.prime_dvd_prime_iff_eq hq'.2 h12).mp h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2 hcc).mp h; omega
  have hω0 : ∀ p ∈ Q, 0 < omega (quadCond c) p := fun p hp => omega_quad_pos c p (hQ p hp)
  have hω1 : ∀ p ∈ Q, omega (quadCond c) p < p := fun p hp => omega_quad_lt c p hc (hQ p hp)
  have hsieve := selberg_residue_level X z hz Q hQ (quadCond c) (quadCond_periodic c) hω0 hω1
  change _ ≤ (X : ℝ) / quadG c z + _ at hsieve
  have hcard := card_le_card hsub
  have hu := card_union_le (range z) ((range X).filter (fun n => ∀ p ∈ Q, ¬ quadCond c p n))
  rw [card_range] at hu
  have : (((range X).filter (fun n => n.Prime ∧ (n + 6).Prime ∧ (n + 12).Prime ∧
        (n + c).Prime)).card : ℝ)
      ≤ z + (((range X).filter (fun n => ∀ p ∈ Q, ¬ quadCond c p n)).card : ℝ) := by
    exact_mod_cast hcard.trans hu
  linarith

end OMALib.Sieve

end BPLib

namespace OMABP

open Finset OMALib.Sieve

/-- Mertens' constant in the product form used below. -/
noncomputable def MC : ℝ := Real.exp OMALib.Mertens.mertens2Const

theorem MC_pos : 0 < MC := Real.exp_pos _

theorem mertens3_nat (N : ℕ) (hN : 2 ≤ N) :
    ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) ≤ MC / Real.log N := by
  have h := (OMALib.Mertens.prod_one_sub_inv_bounds (N : ℝ) (by exact_mod_cast hN)).2
  rwa [Nat.floor_natCast] at h

theorem log_two_pow (n : ℕ) : Real.log ((2 ^ n : ℕ) : ℝ) = n * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- Lower bound for the quadruple sieve's `G` at the level `z = 2 ^ a`. -/
theorem quadG_ge (c a b : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hb : 2 ≤ b)
    (hab : 121 * b ≤ a) :
    (1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4 ≤ quadG c (2 ^ a) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4b : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hY3 : 3 ≤ 2 ^ b := by omega
  have hYz : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlY : Real.log ((2 ^ b : ℕ) : ℝ) = b * Real.log 2 := log_two_pow b
  have hlz : Real.log ((2 ^ a : ℕ) : ℝ) = a * Real.log 2 := log_two_pow a
  have hlYup : Real.log ((2 ^ b : ℕ) : ℝ) ≤ Real.log ((2 ^ a : ℕ) : ℝ) / 121 := by
    rw [hlY, hlz]
    have : (121 : ℝ) * b ≤ a := by exact_mod_cast hab
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hhalf := quad_rankin_half c (2 ^ a) (2 ^ b) hc hY3 hYz hlYup
    OMALib.Mertens.sum_log_div_le_nat
  have hE := quad_euler_ge c (2 ^ b) hc
  have hM3 := mertens3_nat (2 ^ b) (by omega)
  set Q := Nat.primesLE (2 ^ b)
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hQpos : 0 < ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlYpos : 0 < Real.log ((2 ^ b : ℕ) : ℝ) := by rw [hlY]; positivity
  have hinv : Real.log ((2 ^ b : ℕ) : ℝ) / MC ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [le_inv_comm₀ (by have := MC_pos; positivity) hQpos, inv_div]; exact hM3
  rw [hlY] at hinv
  have h4 : ((b * Real.log 2) / MC) ^ 4 ≤ ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 4 :=
    pow_le_pow_left₀ (by have := MC_pos; positivity) hinv 4
  have h5 : ((b * Real.log 2) / MC) ^ 4 * (1 / 16) ^ 5
      ≤ ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 4 * (1 / 16) ^ 5 :=
    mul_le_mul_of_nonneg_right h4 (by norm_num)
  linarith

/-- Growth: `8 (8 a + 8) ^ 4 ≤ 16 ^ a` for `a ≥ 10`. -/
theorem poly_le_exp (a : ℕ) (ha : 10 ≤ a) : 8 * (8 * a + 8) ^ 4 ≤ 16 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    have h1 : 8 * (a + 1) + 8 ≤ 2 * (8 * a + 8) := by omega
    have h2 : (8 * (a + 1) + 8) ^ 4 ≤ (2 * (8 * a + 8)) ^ 4 := Nat.pow_le_pow_left h1 4
    rw [mul_pow] at h2
    calc 8 * (8 * (a + 1) + 8) ^ 4 ≤ 8 * (2 ^ 4 * (8 * a + 8) ^ 4) := Nat.mul_le_mul_left 8 h2
      _ = 16 * (8 * (8 * a + 8) ^ 4) := by ring
      _ ≤ 16 * 16 ^ a := Nat.mul_le_mul_left 16 ih
      _ = 16 ^ (a + 1) := by ring

theorem card_quad_le (c X a b : ℕ) (hc : c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 10) (hb : 2 ≤ b)
    (hab : 121 * b ≤ a) :
    (((range X).filter (fun n => n.Prime ∧ (n + 6).Prime ∧ (n + 12).Prime ∧
        (n + c).Prime)).card : ℝ)
      ≤ 2 ^ a + X / ((1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4) + (2 ^ a) ^ 4 := by
  have hz : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := card_quad_le_sieve c X (2 ^ a) hc hz
  have hG := quadG_ge c a b hc hb hab
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hGmin : 0 < (1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4 := by
    have := MC_pos; positivity
  have hdiv : (X : ℝ) / quadG c (2 ^ a) ≤
      X / ((1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hGmin hG
  push_cast at h
  linarith

theorem main_H2 : OMA.R_BalancedPrimes_balanced_primes_R1.H2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C0 : ℝ := 16 ^ 6 * MC ^ 4 * 1936 ^ 4 / Real.log 2 ^ 4 with hC0
  have hC0pos : 0 < C0 := by have := MC_pos; positivity
  refine ⟨⌈1 + C0⌉₊, 1936, fun k hk => ?_⟩
  set a := k / 8 with ha
  set b := a / 121 with hb
  have ha8 : 8 * a ≤ k := by omega
  have hk8 : k < 8 * a + 8 := by omega
  have hb2 : 2 ≤ b := by omega
  have hab : 121 * b ≤ a := by omega
  have hkb : k ≤ 1936 * b := by omega
  set X := 2 ^ (k + 1) with hX
  set W := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 12) ∧
        ((Finset.Ioo p (p + 12)).filter (fun q => q ≠ p + 6 ∧ Nat.Prime q)).Nonempty) with hW
  set T : ℕ → Finset ℕ := fun c => (range X).filter
      (fun n => n.Prime ∧ (n + 6).Prime ∧ (n + 12).Prime ∧ (n + c).Prime) with hT
  have hsub : W ⊆ ((T 2 ∪ T 4) ∪ T 8) ∪ T 10 := by
    intro p hp
    simp only [hW, mem_filter, mem_Ico] at hp
    obtain ⟨⟨hlo, hhi⟩, hp0, hp6, hp12, ⟨q, hq⟩⟩ := hp
    simp only [mem_filter, mem_Ioo] at hq
    obtain ⟨⟨hq1, hq2⟩, hq6, hqp⟩ := hq
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpodd : p % 2 = 1 := by
      rcases hp0.eq_two_or_odd with h | h
      · omega
      · exact h
    have hqodd : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hpX : p < X := hhi
    have : q = p + 2 ∨ q = p + 4 ∨ q = p + 8 ∨ q = p + 10 := by omega
    simp only [hT, mem_union, mem_filter, mem_range]
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨hpX, hp0, hp6, hp12, hqp⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hpX, hp0, hp6, hp12, hqp⟩))
    · exact Or.inl (Or.inr ⟨hpX, hp0, hp6, hp12, hqp⟩)
    · exact Or.inr ⟨hpX, hp0, hp6, hp12, hqp⟩
  have hcardW : W.card ≤ (T 2).card + (T 4).card + (T 8).card + (T 10).card := by
    refine (card_le_card hsub).trans ?_
    have e1 := card_union_le ((T 2 ∪ T 4) ∪ T 8) (T 10)
    have e2 := card_union_le (T 2 ∪ T 4) (T 8)
    have e3 := card_union_le (T 2) (T 4)
    omega
  have hT2 := card_quad_le 2 X a b (by norm_num) hb2 hab
  have hT4 := card_quad_le 4 X a b (by norm_num) hb2 hab
  have hT8 := card_quad_le 8 X a b (by norm_num) hb2 hab
  have hT10 := card_quad_le 10 X a b (by norm_num) hb2 hab
  have hMC := MC_pos
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hGm0 : (0 : ℝ) < (1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4 := by positivity
  have hWR : (W.card : ℝ) ≤ 4 * ((2 : ℝ) ^ a +
      X / ((1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4) + ((2 : ℝ) ^ a) ^ 4) := by
    have : (W.card : ℝ) ≤ (T 2).card + (T 4).card + (T 8).card + (T 10).card := by
      exact_mod_cast hcardW
    simp only [hT] at this
    linarith
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkbR : (k : ℝ) ≤ 1936 * b := by exact_mod_cast hkb
  have hpoly : 8 * (8 * a + 8) ^ 4 ≤ 16 ^ a := poly_le_exp a (by omega)
  have hk4 : (0 : ℝ) ≤ (k : ℝ) ^ 4 := by positivity
  have hpart1 : (k : ℝ) ^ 4 * (4 * ((2 : ℝ) ^ a + ((2 : ℝ) ^ a) ^ 4)) ≤ (2 : ℝ) ^ k := by
    have h1 : (k : ℝ) ^ 4 ≤ (8 * (a : ℝ) + 8) ^ 4 := by
      have : (k : ℝ) ≤ 8 * a + 8 := by exact_mod_cast hk8.le
      exact pow_le_pow_left₀ hkR this 4
    have h4 : ((2 : ℝ) ^ a) ^ 4 = (16 : ℝ) ^ a := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2 : (2 : ℝ) ^ a ≤ (16 : ℝ) ^ a := pow_le_pow_left₀ (by norm_num) (by norm_num) a
    have h3 : (16 : ℝ) ^ a * (16 : ℝ) ^ a ≤ (2 : ℝ) ^ k := by
      have : (2 : ℝ) ^ (8 * a) ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) ha8
      calc (16 : ℝ) ^ a * (16 : ℝ) ^ a = (2 : ℝ) ^ (8 * a) := by
            rw [← mul_pow, show (16 : ℝ) * 16 = 2 ^ 8 by norm_num, ← pow_mul]
        _ ≤ (2 : ℝ) ^ k := this
    have hpolyR : (8 : ℝ) * (8 * (a : ℝ) + 8) ^ 4 ≤ (16 : ℝ) ^ a := by exact_mod_cast hpoly
    have h16 : (0 : ℝ) ≤ (16 : ℝ) ^ a := by positivity
    have e1 : 4 * ((2 : ℝ) ^ a + ((2 : ℝ) ^ a) ^ 4) ≤ 8 * (16 : ℝ) ^ a := by rw [h4]; linarith
    calc (k : ℝ) ^ 4 * (4 * ((2 : ℝ) ^ a + ((2 : ℝ) ^ a) ^ 4))
        ≤ (k : ℝ) ^ 4 * (8 * (16 : ℝ) ^ a) := mul_le_mul_of_nonneg_left e1 hk4
      _ ≤ (8 * (a : ℝ) + 8) ^ 4 * (8 * (16 : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((8 : ℝ) * (8 * (a : ℝ) + 8) ^ 4) * (16 : ℝ) ^ a := by ring
      _ ≤ (16 : ℝ) ^ a * (16 : ℝ) ^ a := mul_le_mul_of_nonneg_right hpolyR h16
      _ ≤ (2 : ℝ) ^ k := h3
  have hpart2 : (k : ℝ) ^ 4 * (4 * ((X : ℝ) / ((1 / 2) * (1 / 16) ^ 5 *
      ((b * Real.log 2) / MC) ^ 4))) ≤ C0 * (2 : ℝ) ^ k := by
    have hXR : (X : ℝ) = 2 * (2 : ℝ) ^ k := by simp only [hX]; push_cast; ring
    rw [hXR, hC0]
    have hb4 : (k : ℝ) ^ 4 ≤ 1936 ^ 4 * (b : ℝ) ^ 4 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hkR hkbR 4
    have hbpos : (0 : ℝ) < b := by linarith
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have e : (k : ℝ) ^ 4 * (4 * (2 * (2 : ℝ) ^ k / ((1 / 2) * (1 / 16) ^ 5 *
        ((b * Real.log 2) / MC) ^ 4))) =
        ((k : ℝ) ^ 4 / (b : ℝ) ^ 4) * (16 ^ 6 * MC ^ 4 / Real.log 2 ^ 4) * (2 : ℝ) ^ k := by
      field_simp
      ring
    have e2 : 16 ^ 6 * MC ^ 4 * 1936 ^ 4 / Real.log 2 ^ 4 * (2 : ℝ) ^ k =
        (1936 : ℝ) ^ 4 * (16 ^ 6 * MC ^ 4 / Real.log 2 ^ 4) * (2 : ℝ) ^ k := by ring
    rw [e, e2]
    have hq : (k : ℝ) ^ 4 / (b : ℝ) ^ 4 ≤ 1936 ^ 4 := by
      rw [div_le_iff₀ (by positivity)]; exact hb4
    have hpos : (0 : ℝ) ≤ 16 ^ 6 * MC ^ 4 / Real.log 2 ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hpos) h2k.le
  have hfinal : (k : ℝ) ^ 4 * W.card ≤ (1 + C0) * (2 : ℝ) ^ k := by
    have h1 := mul_le_mul_of_nonneg_left hWR hk4
    have hsplit : (k : ℝ) ^ 4 * (4 * ((2 : ℝ) ^ a +
        X / ((1 / 2) * (1 / 16) ^ 5 * ((b * Real.log 2) / MC) ^ 4) + ((2 : ℝ) ^ a) ^ 4)) =
        (k : ℝ) ^ 4 * (4 * ((2 : ℝ) ^ a + ((2 : ℝ) ^ a) ^ 4)) +
        (k : ℝ) ^ 4 * (4 * ((X : ℝ) / ((1 / 2) * (1 / 16) ^ 5 *
          ((b * Real.log 2) / MC) ^ 4))) := by ring
    linarith
  have hceil : (1 + C0) ≤ (⌈1 + C0⌉₊ : ℝ) := Nat.le_ceil _
  have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  have : (k : ℝ) ^ 4 * W.card ≤ (⌈1 + C0⌉₊ : ℝ) * (2 : ℝ) ^ k :=
    hfinal.trans (mul_le_mul_of_nonneg_right hceil h2k)
  exact_mod_cast this

end OMABP

theorem OMA.solution : OMA.R_BalancedPrimes_balanced_primes_R1.H2 := OMABP.main_H2
