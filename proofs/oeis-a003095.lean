import OMAStatements.S_oeis_a003095
import Mathlib

/-!
# OEIS A003095: eventual periods of `a (n+1) = a n ^ 2 + 1` modulo `2^k`, `10^k`, `20^k`

Write `f x = x ^ 2 + 1`, so `a (n+1) = f (a n)` and `a 0 = 0`.

**Residues.** By induction `a n ≡ n (mod 2)`, and `a n mod 5` runs through `0, 1, 2, 0, 1, 2, …`.

**Contraction.** Since `f x - f y = (x - y)(x + y)`,

* `a (m+4) - a (m+2) = (a (m+2) - a m) (a (m+2) + a m) (a (m+3) + a (m+1))`, and the middle
  factor is even. So each step of two indices gains a factor `2`: for every `k`,
  `2^k ∣ a (n+2) - a n` for all large `n`.
* `a (m+6) - a (m+3) = (a (m+3) - a m) (a (m+3) + a m) (a (m+4) + a (m+1)) (a (m+5) + a (m+2))`,
  and one of the three sums is a sum of two multiples of `5`. So for every `k`,
  `5^k ∣ a (n+3) - a n` for all large `n`.

Hence `2` is an eventual period modulo `2^k`, and `6` is one modulo `10^k = 2^k 5^k` and modulo
`20^k = 2^(2k) 5^k`.

**Minimality.** An odd shift changes the parity, and a shift not divisible by `3` changes the
residue modulo `5`. So no odd number is an eventual period modulo an even number, and `2`, `4`
are not eventual periods modulo a multiple of `5`.
-/

open OMA.S_oeis_a003095

namespace OMA.A003095

lemma a_succ (n : ℕ) : a (n + 1) = a n ^ 2 + 1 := rfl

lemma a_succ_int (n : ℕ) : ((a (n + 1) : ℕ) : ℤ) = (a n : ℤ) ^ 2 + 1 := by
  rw [a_succ]; push_cast; ring

/-- `a n` has the parity of `n`. -/
lemma a_mod_two (n : ℕ) : a n % 2 = n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a_succ, Nat.add_mod, Nat.pow_mod, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> omega

/-- Modulo `5` the sequence is `0, 1, 2, 0, 1, 2, …`. -/
lemma a_mod_five (n : ℕ) : a n % 5 = n % 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a_succ, Nat.add_mod, Nat.pow_mod, ih]
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] <;> omega

/-! ### The two contraction identities -/

lemma diff_two (m : ℕ) : ((a (m + 4) : ℤ) - a (m + 2))
    = ((a (m + 2) : ℤ) - a m) * ((a (m + 2) : ℤ) + a m) * ((a (m + 3) : ℤ) + a (m + 1)) := by
  have e4 : ((a (m + 4) : ℕ) : ℤ) = (a (m + 3) : ℤ) ^ 2 + 1 := a_succ_int (m + 3)
  have e3 : ((a (m + 3) : ℕ) : ℤ) = (a (m + 2) : ℤ) ^ 2 + 1 := a_succ_int (m + 2)
  have e2 : ((a (m + 2) : ℕ) : ℤ) = (a (m + 1) : ℤ) ^ 2 + 1 := a_succ_int (m + 1)
  have e1 : ((a (m + 1) : ℕ) : ℤ) = (a m : ℤ) ^ 2 + 1 := a_succ_int m
  linear_combination e4 - e2 + ((a (m + 3) : ℤ) + a (m + 1)) * (e3 - e1)

lemma diff_three (m : ℕ) : ((a (m + 6) : ℤ) - a (m + 3))
    = ((a (m + 3) : ℤ) - a m)
      * (((a (m + 3) : ℤ) + a m) * ((a (m + 4) : ℤ) + a (m + 1)) * ((a (m + 5) : ℤ) + a (m + 2))) := by
  have e6 : ((a (m + 6) : ℕ) : ℤ) = (a (m + 5) : ℤ) ^ 2 + 1 := a_succ_int (m + 5)
  have e5 : ((a (m + 5) : ℕ) : ℤ) = (a (m + 4) : ℤ) ^ 2 + 1 := a_succ_int (m + 4)
  have e4 : ((a (m + 4) : ℕ) : ℤ) = (a (m + 3) : ℤ) ^ 2 + 1 := a_succ_int (m + 3)
  have e3 : ((a (m + 3) : ℕ) : ℤ) = (a (m + 2) : ℤ) ^ 2 + 1 := a_succ_int (m + 2)
  have e2 : ((a (m + 2) : ℕ) : ℤ) = (a (m + 1) : ℤ) ^ 2 + 1 := a_succ_int (m + 1)
  have e1 : ((a (m + 1) : ℕ) : ℤ) = (a m : ℤ) ^ 2 + 1 := a_succ_int m
  linear_combination e6 - e3 + ((a (m + 5) : ℤ) + a (m + 2)) * (e5 - e2)
    + ((a (m + 5) : ℤ) + a (m + 2)) * ((a (m + 4) : ℤ) + a (m + 1)) * (e4 - e1)

/-- For every `k`, eventually `2 ^ k ∣ a (n + 2) - a n`. -/
lemma pow_two_dvd (k : ℕ) : ∃ N, ∀ n ≥ N, ((2 : ℤ) ^ k) ∣ (a (n + 2) : ℤ) - a n := by
  induction k with
  | zero => exact ⟨0, fun n _ => by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + 2, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h1 := hN m (by omega)
    have h2 : (2 : ℤ) ∣ (a (m + 2) : ℤ) + a m := by
      have := a_mod_two (m + 2)
      have := a_mod_two m
      omega
    have hgoal : ((2 : ℤ) ^ (k + 1)) ∣ (a (m + 4) : ℤ) - a (m + 2) := by
      rw [diff_two, pow_succ]
      exact Dvd.dvd.mul_right (mul_dvd_mul h1 h2) _
    exact hgoal

/-- For every `k`, eventually `5 ^ k ∣ a (n + 3) - a n`. -/
lemma pow_five_dvd (k : ℕ) : ∃ N, ∀ n ≥ N, ((5 : ℤ) ^ k) ∣ (a (n + 3) : ℤ) - a n := by
  induction k with
  | zero => exact ⟨0, fun n _ => by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + 3, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h1 := hN m (by omega)
    -- one of the three sums is a sum of two multiples of `5`
    have h5 : (5 : ℤ) ∣ ((a (m + 3) : ℤ) + a m) * ((a (m + 4) : ℤ) + a (m + 1))
        * ((a (m + 5) : ℤ) + a (m + 2)) := by
      have r0 := a_mod_five m
      have r1 := a_mod_five (m + 1)
      have r2 := a_mod_five (m + 2)
      have r3 := a_mod_five (m + 3)
      have r4 := a_mod_five (m + 4)
      have r5 := a_mod_five (m + 5)
      have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases h3 with h | h | h
      · have : (5 : ℤ) ∣ (a (m + 3) : ℤ) + a m := by omega
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
      · have : (5 : ℤ) ∣ (a (m + 5) : ℤ) + a (m + 2) := by omega
        exact Dvd.dvd.mul_left this _
      · have : (5 : ℤ) ∣ (a (m + 4) : ℤ) + a (m + 1) := by omega
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left this _) _
    have hgoal : ((5 : ℤ) ^ (k + 1)) ∣ (a (m + 6) : ℤ) - a (m + 3) := by
      rw [diff_three, pow_succ]
      exact mul_dvd_mul h1 h5
    exact hgoal

/-! ### Eventual periods -/

lemma period_two (k : ℕ) : ∃ N, ∀ n ≥ N, a (n + 2) ≡ a n [MOD 2 ^ k] := by
  obtain ⟨N, hN⟩ := pow_two_dvd k
  refine ⟨N, fun n hn => ?_⟩
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  push_cast
  exact hN n hn

/-- `6` is an eventual period modulo any `M = 2 ^ i * 5 ^ j`. -/
lemma period_six (M i j : ℕ) (hM : (M : ℤ) = 2 ^ i * 5 ^ j) :
    ∃ N, ∀ n ≥ N, a (n + 6) ≡ a n [MOD M] := by
  obtain ⟨N2, h2⟩ := pow_two_dvd i
  obtain ⟨N5, h5⟩ := pow_five_dvd j
  refine ⟨max N2 N5, fun n hn => ?_⟩
  have hn2 : N2 ≤ n := le_trans (le_max_left _ _) hn
  have hn5 : N5 ≤ n := le_trans (le_max_right _ _) hn
  -- three steps of size two
  have a1 : ((2 : ℤ) ^ i) ∣ (a (n + 6) : ℤ) - a (n + 4) := h2 (n + 4) (by omega)
  have a2 : ((2 : ℤ) ^ i) ∣ (a (n + 4) : ℤ) - a (n + 2) := h2 (n + 2) (by omega)
  have a3 : ((2 : ℤ) ^ i) ∣ (a (n + 2) : ℤ) - a n := h2 n hn2
  have d2 : ((2 : ℤ) ^ i) ∣ (a (n + 6) : ℤ) - a n := by
    have h := dvd_add (dvd_add a1 a2) a3
    have e : ((a (n + 6) : ℤ) - a (n + 4)) + ((a (n + 4) : ℤ) - a (n + 2))
        + ((a (n + 2) : ℤ) - a n) = (a (n + 6) : ℤ) - a n := by ring
    rwa [e] at h
  -- two steps of size three
  have b1 : ((5 : ℤ) ^ j) ∣ (a (n + 6) : ℤ) - a (n + 3) := h5 (n + 3) (by omega)
  have b2 : ((5 : ℤ) ^ j) ∣ (a (n + 3) : ℤ) - a n := h5 n hn5
  have d5 : ((5 : ℤ) ^ j) ∣ (a (n + 6) : ℤ) - a n := by
    have h := dvd_add b1 b2
    have e : ((a (n + 6) : ℤ) - a (n + 3)) + ((a (n + 3) : ℤ) - a n)
        = (a (n + 6) : ℤ) - a n := by ring
    rwa [e] at h
  have hcop : IsCoprime ((2 : ℤ) ^ i) ((5 : ℤ) ^ j) :=
    IsCoprime.pow ⟨-2, 1, by norm_num⟩
  rw [Nat.modEq_iff_dvd, dvd_sub_comm, hM]
  exact hcop.mul_dvd d2 d5

/-! ### Minimality -/

/-- An odd shift is never an eventual period modulo an even number. -/
lemma no_odd_period {M q : ℕ} (hM : 2 ∣ M) (hq : q % 2 = 1) :
    ¬ ∃ N, ∀ n ≥ N, a (n + q) ≡ a n [MOD M] := by
  rintro ⟨N, h⟩
  have h2 : a (N + q) % 2 = a N % 2 := (h N le_rfl).of_dvd hM
  rw [a_mod_two, a_mod_two] at h2
  omega

/-- A shift not divisible by `3` is never an eventual period modulo a multiple of `5`. -/
lemma no_period_mod_three {M q : ℕ} (hM : 5 ∣ M) (hq : q % 3 ≠ 0) :
    ¬ ∃ N, ∀ n ≥ N, a (n + q) ≡ a n [MOD M] := by
  rintro ⟨N, h⟩
  have h5 : a (N + q) % 5 = a N % 5 := (h N le_rfl).of_dvd hM
  rw [a_mod_five, a_mod_five] at h5
  omega

/-- No `0 < q < 6` is an eventual period modulo a multiple of `10`. -/
lemma no_small_period {M q : ℕ} (h2 : 2 ∣ M) (h5 : 5 ∣ M) (hq0 : 0 < q) (hq6 : q < 6) :
    ¬ ∃ N, ∀ n ≥ N, a (n + q) ≡ a n [MOD M] := by
  by_cases hodd : q % 2 = 1
  · exact no_odd_period h2 hodd
  · exact no_period_mod_three h5 (by omega)

end OMA.A003095

open OMA.A003095 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003095.main := by
  intro k hk
  refine ⟨⟨period_two k, ?_⟩, ⟨period_six (10 ^ k) k k ?_, ?_⟩, ⟨period_six (20 ^ k) (2 * k) k ?_, ?_⟩⟩
  · intro q hq0 hq2
    exact no_odd_period (dvd_pow_self 2 hk.ne') (by omega)
  · push_cast
    rw [← mul_pow]
    norm_num
  · intro q hq0 hq6
    exact no_small_period (dvd_pow (by norm_num) hk.ne') (dvd_pow (by norm_num) hk.ne') hq0 hq6
  · push_cast
    rw [pow_mul, ← mul_pow]
    norm_num
  · intro q hq0 hq6
    exact no_small_period (dvd_pow (by norm_num) hk.ne') (dvd_pow (by norm_num) hk.ne') hq0 hq6
