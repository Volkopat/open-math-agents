import OMAReductions.R_OeisA110835_conjecture_R2

-- Step OeisA110835.conjecture.R2.H1: for 1 ≤ m ≤ 7 and m < n there is a prime in [n m, n (m + 1)].
-- Proof: a prime in (x, 8x/7] for every x ≥ 33, from explicit Chebyshev-type bounds on ψ
-- (weights on divisors of 420, one bootstrap round; Nagura 1952 and the 7/6 case are proved on
-- the way), a chain of 138 primes below 1.6·10^9, and decide tables for small windows.


/-!
# Nagura's theorem (1952): for every natural `x ≥ 25` there is a prime `p` with `x < p ≤ 6x/5`.

Proof route: Chebyshev's identity `log N! = ∑_{n ≤ N} Λ(n) ⌊N/n⌋`, Chebyshev's weights
`1, -1/2, -1/3, -1/5, +1/30`, and one bootstrap step (the weight is also `1` on `[7, 10)`),
which improves Chebyshev's upper constant `6A/5` to `(1026/875) A < 6A/5`.
-/

open Real Finset ArithmeticFunction

namespace Nagura

/-- `T N = log N!`. -/
noncomputable def T (N : ℕ) : ℝ := Real.log (N.factorial : ℝ)

/-- `S N = ψ(N) = ∑_{0 < n ≤ N} Λ n`. -/
noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, Λ n

theorem psi_nat (N : ℕ) : Chebyshev.psi N = S N := by
  simp [Chebyshev.psi, S]

theorem S_nonneg (N : ℕ) : 0 ≤ S N :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

theorem divisors_eq_filter (m : ℕ) (hm : m ≠ 0) :
    m.divisors = (Ioc 0 m).filter (· ∣ m) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hm), Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h⟩, h⟩
  · rintro ⟨-, h⟩
    exact ⟨h, hm⟩

/-- Chebyshev's identity: `log N! = ∑_{n ≤ N} Λ(n) ⌊N/n⌋`. -/
theorem T_eq (N : ℕ) : T N = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  induction N with
  | zero => simp [T]
  | succ N ih =>
    have h1 : T (N + 1) = Real.log ((N + 1 : ℕ) : ℝ) + T N := by
      simp only [T, Nat.factorial_succ, Nat.cast_mul]
      rw [Real.log_mul (by positivity) (by positivity)]
    have h2 : ∀ n ∈ Ioc 0 (N + 1), Λ n * (((N + 1) / n : ℕ) : ℝ)
        = Λ n * ((N / n : ℕ) : ℝ) + (if n ∣ N + 1 then Λ n else 0) := by
      intro n _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [h1, ih, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_filter,
      ← divisors_eq_filter (N + 1) (Nat.succ_ne_zero N), ArithmeticFunction.vonMangoldt_sum,
      Finset.sum_Ioc_succ_top (Nat.zero_le N), Nat.div_eq_of_lt (Nat.lt_succ_self N)]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    ring

theorem T_div (N d : ℕ) (hd : 0 < d) :
    T (N / d) = ∑ n ∈ Ioc 0 N, Λ n * (((N / n) / d : ℕ) : ℝ) := by
  rw [T_eq]
  have hc : ∀ n, (N / d) / n = (N / n) / d := by
    intro n; rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hc]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (Nat.div_le_self N d)⟩
  · intro n hn hn'
    simp only [Finset.mem_Ioc, not_and, not_le] at hn hn'
    have : N / d < n := hn' hn.1
    rw [← hc, Nat.div_eq_of_lt this]
    simp

/-- Chebyshev's weight function. -/
def fC (k : ℕ) : ℤ := (k : ℤ) - ((k / 2 : ℕ) : ℤ) - ((k / 3 : ℕ) : ℤ) - ((k / 5 : ℕ) : ℤ)
  + ((k / 30 : ℕ) : ℤ)

theorem fC_nonneg (k : ℕ) : 0 ≤ fC k := by unfold fC; omega
theorem fC_le_one (k : ℕ) : fC k ≤ 1 := by unfold fC; omega
theorem fC_eq_one_a (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 5) : fC k = 1 := by unfold fC; omega
theorem fC_eq_one_b (k : ℕ) (h1 : 7 ≤ k) (h2 : k ≤ 9) : fC k = 1 := by unfold fC; omega

theorem fC_cast (k : ℕ) : ((fC k : ℤ) : ℝ) = (k : ℝ) - ((k / 2 : ℕ) : ℝ) - ((k / 3 : ℕ) : ℝ)
    - ((k / 5 : ℕ) : ℝ) + ((k / 30 : ℕ) : ℝ) := by
  unfold fC
  rw [Int.cast_add, Int.cast_sub, Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]

/-- Chebyshev's combination. -/
noncomputable def C (N : ℕ) : ℝ := T N - T (N / 2) - T (N / 3) - T (N / 5) + T (N / 30)

theorem C_eq (N : ℕ) : C N = ∑ n ∈ Ioc 0 N, Λ n * (fC (N / n) : ℝ) := by
  rw [C, T_eq N, T_div N 2 (by norm_num), T_div N 3 (by norm_num), T_div N 5 (by norm_num),
    T_div N 30 (by norm_num), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [fC_cast]
  simp only [Nat.div_div_eq_div_mul]
  ring

theorem C_le_S (N : ℕ) : C N ≤ S N := by
  rw [C_eq, S]
  apply Finset.sum_le_sum
  intro n _
  have h1 : (fC (N / n) : ℝ) ≤ 1 := by exact_mod_cast fC_le_one (N / n)
  have h2 : 0 ≤ Λ n := vonMangoldt_nonneg
  nlinarith

theorem sum_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc a c, f n = ∑ n ∈ Ioc a b, f n + ∑ n ∈ Ioc b c, f n :=
  (Finset.sum_Ioc_consecutive f hab hbc).symm

theorem S_sub (a b : ℕ) (hab : a ≤ b) : S b - S a = ∑ n ∈ Ioc a b, Λ n := by
  rw [S, S, sum_split 0 a b (Nat.zero_le a) hab]; ring

/-- The telescoping comparison used for the upper bounds. -/
theorem S_upper_aux (N : ℕ) : (S N - S (N / 6)) + (S (N / 7) - S (N / 10)) ≤ C N := by
  have h10_7 : N / 10 ≤ N / 7 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have h7_6 : N / 7 ≤ N / 6 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have h6 : N / 6 ≤ N := Nat.div_le_self N 6
  rw [S_sub _ _ h6, S_sub _ _ h10_7, C_eq, sum_split 0 (N / 10) N (Nat.zero_le _) (h10_7.trans (h7_6.trans h6)),
    sum_split (N / 10) (N / 7) N h10_7 (h7_6.trans h6), sum_split (N / 7) (N / 6) N h7_6 h6]
  have hA : 0 ≤ ∑ n ∈ Ioc 0 (N / 10), Λ n * (fC (N / n) : ℝ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by exact_mod_cast fC_nonneg _)
  have hC : 0 ≤ ∑ n ∈ Ioc (N / 7) (N / 6), Λ n * (fC (N / n) : ℝ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by exact_mod_cast fC_nonneg _)
  have hB : ∑ n ∈ Ioc (N / 10) (N / 7), Λ n * (fC (N / n) : ℝ) = ∑ n ∈ Ioc (N / 10) (N / 7), Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have k1 : 7 ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr (by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 7)).mp hn.2; linarith)
    have k2 : N / n < 10 := (Nat.div_lt_iff_lt_mul hn0).mpr (by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).mp hn.1; linarith)
    rw [fC_eq_one_b _ k1 (by omega)]; simp
  have hD : ∑ n ∈ Ioc (N / 6) N, Λ n * (fC (N / n) : ℝ) = ∑ n ∈ Ioc (N / 6) N, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have k1 : 1 ≤ N / n := Nat.div_pos hn.2 hn0
    have k2 : N / n < 6 := (Nat.div_lt_iff_lt_mul hn0).mpr (by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).mp hn.1; linarith)
    rw [fC_eq_one_a _ k1 (by omega)]; simp
  rw [hB, hD]
  linarith

theorem S_upper_aux1 (N : ℕ) : S N - S (N / 6) ≤ C N := by
  have := S_upper_aux N
  have : 0 ≤ S (N / 7) - S (N / 10) := by
    rw [S_sub _ _ (Nat.div_le_div_left (by norm_num) (by norm_num))]
    exact Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  linarith

end Nagura

namespace Nagura

/-- `g y = y log y - y`. -/
noncomputable def g (y : ℝ) : ℝ := y * Real.log y - y

/-- Tangent-line inequality for the convex function `g`. -/
theorem g_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : g a + Real.log a * (b - a) ≤ g b := by
  unfold g
  rcases hb.eq_or_lt with rfl | hb
  · simp; nlinarith [Real.log_le_sub_one_of_pos ha]
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne', inv_div] at h
    have h2 : b * (1 - a / b) = b - a := by field_simp
    have h3 : b * (1 - a / b) ≤ b * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_left h hb.le
    nlinarith

theorem g_ge_neg_one (y : ℝ) (hy : 0 ≤ y) : -1 ≤ g y := by
  have := g_tangent (a := 1) one_pos hy
  simp [g] at this ⊢; linarith

theorem T_zero : T 0 = 0 := by simp [T]

theorem T_ge (M : ℕ) : g M ≤ T M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [g, T]
  · have h := Stirling.le_log_factorial_stirling (Nat.pos_iff_ne_zero.mp hM)
    have h1 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.two_le_pi])
    unfold g T; linarith

theorem T_le (M : ℕ) (hM : 1 ≤ M) : T M ≤ g M + Real.log M / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at h
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [Real.log_mul (by norm_num) hk.ne', Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  unfold g T
  push_cast at h ⊢
  linarith

theorem log_nat_mono {m N : ℕ} (h : m ≤ N) : Real.log m ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

theorem T_div_ge (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    g ((N : ℝ) / d) - Real.log N ≤ T (N / d) := by
  set y : ℝ := (N : ℝ) / d with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyN : y ≤ N := by
    rw [hy]; exact div_le_self (by positivity) (by exact_mod_cast hd)
  have hMle : ((N / d : ℕ) : ℝ) ≤ y := Nat.cast_div_le
  have hMge : y - 1 < ((N / d : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor y
    rwa [hy, Nat.floor_div_eq_div] at this
  have ht := g_tangent hy0 (Nat.cast_nonneg (N / d))
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have key : -Real.log N ≤ Real.log y * (((N / d : ℕ) : ℝ) - y) := by
    rcases le_or_gt 1 y with h1 | h1
    · have hl : 0 ≤ Real.log y := Real.log_nonneg h1
      have hl2 : Real.log y ≤ Real.log N := Real.log_le_log hy0 hyN
      nlinarith
    · have hl : Real.log y < 0 := Real.log_neg hy0 h1
      nlinarith
  have := T_ge (N / d)
  linarith

theorem T_div_le (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    T (N / d) ≤ g ((N : ℝ) / d) + Real.log N / 2 + 1 := by
  set y : ℝ := (N : ℝ) / d with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hMle : ((N / d : ℕ) : ℝ) ≤ y := Nat.cast_div_le
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
  · rw [h0, T_zero]
    have := g_ge_neg_one y hy0.le
    linarith
  · have hM : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hpos
    have ht := g_tangent hM hy0.le
    have hl : 0 ≤ Real.log ((N / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
    have hl2 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N d)
    have h1 := T_le (N / d) hpos
    nlinarith

/-- Chebyshev's constant `A = log(2^{1/2} 3^{1/3} 5^{1/5} / 30^{1/30}) ≈ 0.92129`. -/
noncomputable def A : ℝ := 7 / 15 * Real.log 2 + 3 / 10 * Real.log 3 + 1 / 6 * Real.log 5

theorem g_comb (N : ℝ) (hN : 0 < N) :
    g N - g (N / 2) - g (N / 3) - g (N / 5) + g (N / 30) = A * N := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold g A
  rw [Real.log_div hN.ne' (by norm_num), Real.log_div hN.ne' (by norm_num),
    Real.log_div hN.ne' (by norm_num), Real.log_div hN.ne' (by norm_num), h30]
  ring

theorem C_ge (N : ℕ) (hN : 1 ≤ N) : A * N - 5 / 2 * Real.log N - 3 ≤ C N := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e := g_comb N h0
  have a1 := T_ge N
  have a2 := T_div_le N 2 hN (by norm_num)
  have a3 := T_div_le N 3 hN (by norm_num)
  have a5 := T_div_le N 5 hN (by norm_num)
  have a30 := T_div_ge N 30 hN (by norm_num)
  push_cast at a2 a3 a5 a30
  unfold C
  linarith

theorem C_le (N : ℕ) (hN : 1 ≤ N) : C N ≤ A * N + 4 * Real.log N + 2 := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e := g_comb N h0
  have a1 := T_le N hN
  have a2 := T_div_ge N 2 hN (by norm_num)
  have a3 := T_div_ge N 3 hN (by norm_num)
  have a5 := T_div_ge N 5 hN (by norm_num)
  have a30 := T_div_le N 30 hN (by norm_num)
  push_cast at a2 a3 a5 a30
  unfold C
  linarith

/-- Chebyshev's lower bound, explicit: `ψ(N) ≥ A N - (5/2) log N - 3`. -/
theorem S_ge (N : ℕ) : A * N - 5 / 2 * Real.log N - 3 ≤ S N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  · exact (C_ge N hN).trans (C_le_S N)

end Nagura

namespace Nagura

theorem log2_gt : (0.6931 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
theorem log2_lt : Real.log 2 < (0.6932 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)

theorem log3_ge : 19 / 12 * Real.log 2 ≤ Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 19) ≤ Real.log ((3 : ℝ) ^ 12) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log3_le : Real.log 3 ≤ 65 / 41 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 41) ≤ Real.log ((2 : ℝ) ^ 65) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log5_ge : 65 / 28 * Real.log 2 ≤ Real.log 5 := by
  have h : Real.log ((2 : ℝ) ^ 65) ≤ Real.log ((5 : ℝ) ^ 28) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log5_le : Real.log 5 ≤ 7 / 3 * Real.log 2 := by
  have h : Real.log ((5 : ℝ) ^ 3) ≤ Real.log ((2 : ℝ) ^ 7) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem A_ge : (0.92 : ℝ) ≤ A := by
  unfold A; nlinarith [log2_gt, log3_ge, log5_ge]

theorem A_le : A ≤ (0.93 : ℝ) := by
  unfold A; nlinarith [log2_lt, log3_le, log5_le, log2_gt]

theorem A_nonneg : 0 ≤ A := le_trans (by norm_num) A_ge

theorem sqrt_le_mul (m : ℝ) (N : ℝ) (k : ℝ) (hk : 0 ≤ k) (h : m ≤ k ^ 2 * N) :
    Real.sqrt m ≤ k * Real.sqrt N := by
  rcases le_or_gt 0 N with hN | hN
  · rw [show k * Real.sqrt N = Real.sqrt (k ^ 2 * N) by
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]]
    exact Real.sqrt_le_sqrt h
  · have : m ≤ 0 := by nlinarith [sq_nonneg k]
    rw [Real.sqrt_eq_zero'.mpr this]
    exact mul_nonneg hk (Real.sqrt_nonneg _)

theorem log_le_two_sqrt (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ 2 * (Real.sqrt N - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsq : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0.le).symm
  have := Real.log_le_sub_one_of_pos hs
  calc Real.log N = Real.log (Real.sqrt N ^ 2) := by rw [← hsq]
    _ = 2 * Real.log (Real.sqrt N) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ 2 * (Real.sqrt N - 1) := by linarith

theorem cast_div_le' (N d : ℕ) : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le

theorem cast_div_gt (N d : ℕ) : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
  have := Nat.sub_one_lt_floor ((N : ℝ) / d)
  rwa [Nat.floor_div_eq_div] at this

/-- Chebyshev's upper bound, explicit: `ψ(N) ≤ (6/5) A N + 14 √N`. -/
theorem S_le_U1 (N : ℕ) : S N ≤ 6 / 5 * A * N + 14 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have hc := C_le N hN
  have hs := S_upper_aux1 N
  have hm : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := cast_div_le' N 6; push_cast at this; exact this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ 41 / 100 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlog := log_le_two_sqrt N hN
  have hA := mul_le_mul_of_nonneg_left hm A_nonneg
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

/-- Bootstrapped upper bound: `ψ(N) ≤ (1026/875) A N + 30 √N`, and `1026/875 < 6/5`. -/
theorem S_le_U2 (N : ℕ) : S N ≤ 1026 / 875 * A * N + 30 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have hl7 := S_ge (N / 7)
  have hu10 := S_le_U1 (N / 10)
  have hc := C_le N hN
  have hs := S_upper_aux N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := cast_div_le' N 6; push_cast at this; exact this
  have m7 : (N : ℝ) / 7 - 1 < ((N / 7 : ℕ) : ℝ) := by
    have := cast_div_gt N 7; push_cast at this; exact this
  have m10 : ((N / 10 : ℕ) : ℝ) ≤ (N : ℝ) / 10 := by
    have := cast_div_le' N 10; push_cast at this; exact this
  have sq6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ 41 / 100 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have sq10 : Real.sqrt ((N / 10 : ℕ) : ℝ) ≤ 317 / 1000 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have l7 : Real.log ((N / 7 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 7)
  have hlog := log_le_two_sqrt N hN
  have a6 := mul_le_mul_of_nonneg_left m6 A_nonneg
  have a7 := mul_le_mul_of_nonneg_left m7.le A_nonneg
  have a10 := mul_le_mul_of_nonneg_left m10 A_nonneg
  have hAle := A_le
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

theorem theta_eq_of_no_prime (N M : ℕ) (hNM : N ≤ M) (h : ∀ p, p.Prime → N < p → M < p) :
    Chebyshev.theta M = Chebyshev.theta N := by
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, hpM⟩, hp⟩
    refine ⟨⟨h0, ?_⟩, hp⟩
    by_contra hc
    push_neg at hc
    exact absurd hpM (not_le.mpr (h p hp hc))
  · rintro ⟨⟨h0, hpN⟩, hp⟩
    exact ⟨⟨h0, hpN.trans hNM⟩, hp⟩

/-- Nagura's theorem for large `N` (`N ≥ 9 · 10^6`). -/
theorem nagura_large (N : ℕ) (hN : 9000000 ≤ N) : ∃ p, p.Prime ∧ N < p ∧ 5 * p ≤ 6 * N := by
  by_contra hcon
  push_neg at hcon
  set M := 6 * N / 5 with hMdef
  have hNM : N ≤ M := by omega
  have hth : Chebyshev.theta M = Chebyshev.theta N :=
    theta_eq_of_no_prime N M hNM (fun p hp hlt => by have := hcon p hp hlt; omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have h1 := Chebyshev.psi_sub_theta_le hM1
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  rw [psi_nat] at h1 h2
  have hL := S_ge M
  have hU := S_le_U2 N
  -- real-number bookkeeping
  have hN0 : (9000000 : ℝ) ≤ N := by exact_mod_cast hN
  set s := Real.sqrt (N : ℝ) with hs
  have hsN : (N : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hs3 : (3000 : ℝ) ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hMle : (M : ℝ) ≤ 6 / 5 * N := by
    have : 5 * M ≤ 6 * N := by omega
    have : (5 : ℝ) * M ≤ 6 * N := by exact_mod_cast this
    linarith
  have hMge : (6 * N - 4 : ℝ) / 5 ≤ M := by
    have : 6 * N ≤ 5 * M + 4 := by omega
    have : (6 : ℝ) * N ≤ 5 * M + 4 := by exact_mod_cast this
    linarith
  have hsqM : Real.sqrt (M : ℝ) ≤ 10955 / 10000 * s :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  -- log M ≤ log 2 + 2 log s ≤ 0.7 + 2 (log 3000 + s/3000 - 1)
  have hlogM2 : Real.log M ≤ Real.log 2 + Real.log N := by
    have : M ≤ 2 * N := by omega
    have h := log_nat_mono this
    push_cast at h
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  have hspos : 0 < s := by linarith
  have hlogN : Real.log N = 2 * Real.log s := by
    rw [hsN, Real.log_pow]; push_cast; ring
  have hlog3000 : Real.log 3000 ≤ 12 * Real.log 2 := by
    have h : Real.log (3000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 12) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at h
  have hlogs : Real.log s ≤ Real.log 3000 + (s / 3000 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 3000 by positivity)
    rw [Real.log_div hspos.ne' (by norm_num)] at h
    linarith
  have hlogMb : Real.log M ≤ 1534 / 100 + s / 1500 := by
    have := log2_lt
    nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt (M : ℝ) * Real.log M ≤ (10955 / 10000 * s) * (1534 / 100 + s / 1500) :=
    mul_le_mul hsqM hlogMb hlogM0 (by positivity)
  have hAM := mul_le_mul_of_nonneg_left hMge A_nonneg
  have hA := A_ge
  have hAN : 0.92 * (N : ℝ) ≤ A * N := mul_le_mul_of_nonneg_right hA (by linarith)
  have hss : 3000 * s ≤ s * s := by nlinarith
  rw [hsN] at hAN hAM hU
  nlinarith

end Nagura

namespace Nagura

/-- `Good x`: there is a prime `p` with `x < p ≤ 6x/5`. -/
def Good (x : ℕ) : Prop := ∃ p, p.Prime ∧ x < p ∧ 5 * p ≤ 6 * x

/-- `chainOK a l`: each element of `l` is at most `6/5` of its predecessor (starting from `a`). -/
def chainOK : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: t => decide (5 * b ≤ 6 * a) && chainOK b t

theorem chain_cover (l : List ℕ) : ∀ a : ℕ, (∀ p ∈ l, p.Prime) → chainOK a l = true →
    ∀ x, a ≤ x → (∃ p ∈ l, x < p) → Good x := by
  induction l with
  | nil => intro a _ _ x _ ⟨p, hp, _⟩; simp at hp
  | cons b t ih =>
    intro a hpr hch x hax hex
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hch
    by_cases hxb : x < b
    · exact ⟨b, hpr b (by simp), hxb, by omega⟩
    · push_neg at hxb
      apply ih b (fun p hp => hpr p (by simp [hp])) hch.2 x hxb
      obtain ⟨p, hp, hxp⟩ := hex
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact ⟨p, hp, hxp⟩

/-- The chain of primes `29, 31, 37, …, 10485721`, each at most `6/5` of the previous. -/
def primeChain : List ℕ := [29, 31, 37, 43, 47, 53, 61, 73, 83, 97, 113, 131, 157, 181, 211, 251, 293, 349, 409, 487, 577, 691, 829, 991, 1187, 1423, 1699, 2029, 2423, 2903, 3469, 4159, 4987, 5981, 7177, 8609, 10321, 12379, 14851, 17807, 21347, 25609, 30727, 36871, 44221, 53051, 63659, 76387, 91639, 109961, 131947, 158329, 189989, 227977, 273569, 328277, 393931, 472711, 567209, 680633, 816743, 980081, 1176089, 1411297, 1693553, 2032253, 2438693, 2926421, 3511693, 4214009, 5056781, 6068137, 7281751, 8738101, 10485721]

theorem primeChain_prime : ∀ p ∈ primeChain, p.Prime := by
  simp only [primeChain, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

theorem primeChain_chain : chainOK 25 primeChain = true := by decide

theorem nagura_small (x : ℕ) (h1 : 25 ≤ x) (h2 : x < 9000000) : Good x :=
  chain_cover primeChain 25 primeChain_prime primeChain_chain x h1
    ⟨10485721, by simp [primeChain], by omega⟩

/-- **Nagura (1952).** For every natural number `x ≥ 25` there is a prime `p`
with `x < p` and `5 p ≤ 6 x`, i.e. `x < p ≤ 6x/5`. -/
theorem nagura (x : ℕ) (hx : 25 ≤ x) : ∃ p, p.Prime ∧ x < p ∧ 5 * p ≤ 6 * x := by
  rcases lt_or_ge x 9000000 with h | h
  · exact nagura_small x hx h
  · exact nagura_large x h

end Nagura

/-! ## Generic Chebyshev-type weight systems (for intervals `(x, (1+1/k) x]` with `k > 5`) -/

namespace Nagura

/-- A weight system: a list of pairs `(d, c)`, meaning `∑ c ⌊t/d⌋`. -/
abbrev Weights := List (ℕ × ℤ)

def fW : Weights → ℕ → ℤ
  | [], _ => 0
  | p :: W, k => p.2 * ((k / p.1 : ℕ) : ℤ) + fW W k

noncomputable def CW : Weights → ℕ → ℝ
  | [], _ => 0
  | p :: W, N => (p.2 : ℝ) * T (N / p.1) + CW W N

theorem CW_eq (W : Weights) (hW : ∀ p ∈ W, 0 < p.1) (N : ℕ) :
    CW W N = ∑ n ∈ Ioc 0 N, Λ n * (fW W (N / n) : ℝ) := by
  induction W with
  | nil => simp [CW, fW]
  | cons p W ih =>
    rw [CW, ih (fun q hq => hW q (List.mem_cons_of_mem _ hq)), T_div N p.1 (hW p (by simp)),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [fW, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring

/-- Runs: a list of triples `(α, β, w)`, meaning `w · 1[α ≤ t < β]`. -/
abbrev Runs := List (ℕ × ℕ × ℕ)

def hR : Runs → ℕ → ℤ
  | [], _ => 0
  | r :: R, k => (if r.1 ≤ k ∧ k < r.2.1 then (r.2.2 : ℤ) else 0) + hR R k

noncomputable def SR : Runs → ℕ → ℝ
  | [], _ => 0
  | r :: R, N => (r.2.2 : ℝ) * (S (N / r.1) - S (N / r.2.1)) + SR R N

theorem run_sum (α β N : ℕ) (h1 : 1 ≤ α) (h2 : α ≤ β) :
    ∑ n ∈ Ioc 0 N, Λ n * (if α ≤ N / n ∧ N / n < β then (1 : ℝ) else 0) = S (N / α) - S (N / β) := by
  rw [S_sub _ _ (Nat.div_le_div_left h2 (by omega))]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hα, hβ⟩
      refine ⟨?_, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr
          (by have := (Nat.div_lt_iff_lt_mul hn0).mp hβ; linarith)
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr
          (by have := (Nat.le_div_iff_mul_le hn0).mp hα; linarith)
    · rintro ⟨hlo, hhi⟩
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlo
      have hnN : n ≤ N := hhi.trans (Nat.div_le_self N α)
      refine ⟨⟨hn0, hnN⟩, ?_, ?_⟩
      · exact (Nat.le_div_iff_mul_le hn0).mpr
          (by have := (Nat.le_div_iff_mul_le (by omega)).mp hhi; linarith)
      · exact (Nat.div_lt_iff_lt_mul hn0).mpr
          (by have := (Nat.div_lt_iff_lt_mul (by omega)).mp hlo; linarith)

theorem SR_eq (R : Runs) (hR1 : ∀ r ∈ R, 1 ≤ r.1 ∧ r.1 ≤ r.2.1) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n * (hR R (N / n) : ℝ) = SR R N := by
  induction R with
  | nil => simp [hR, SR]
  | cons r R ih =>
    have hr := hR1 r (by simp)
    rw [SR, ← ih (fun q hq => hR1 q (List.mem_cons_of_mem _ hq)),
      ← run_sum r.1 r.2.1 N hr.1 hr.2, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [hR, Int.cast_add]
    split_ifs <;> push_cast <;> ring

/-- Lower-bound structure: if `fW + hR ≤ Q` pointwise, then `CW + SR ≤ Q ψ`. -/
theorem lower_struct (W : Weights) (R : Runs) (Q : ℕ) (hW : ∀ p ∈ W, 0 < p.1)
    (hR1 : ∀ r ∈ R, 1 ≤ r.1 ∧ r.1 ≤ r.2.1) (hpt : ∀ k, 1 ≤ k → fW W k + hR R k ≤ Q) (N : ℕ) :
    CW W N + SR R N ≤ Q * S N := by
  rw [CW_eq W hW, ← SR_eq R hR1, ← Finset.sum_add_distrib, S, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_Ioc] at hn
  have h := hpt (N / n) (Nat.div_pos hn.2 hn.1)
  have h' : (fW W (N / n) : ℝ) + (hR R (N / n) : ℝ) ≤ Q := by exact_mod_cast h
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  nlinarith

/-- Upper-bound structure: if `hR ≤ fW` pointwise, then `SR ≤ CW`. -/
theorem upper_struct (W : Weights) (R : Runs) (hW : ∀ p ∈ W, 0 < p.1)
    (hR1 : ∀ r ∈ R, 1 ≤ r.1 ∧ r.1 ≤ r.2.1) (hpt : ∀ k, 1 ≤ k → hR R k ≤ fW W k) (N : ℕ) :
    SR R N ≤ CW W N := by
  rw [CW_eq W hW, ← SR_eq R hR1]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_Ioc] at hn
  have h := hpt (N / n) (Nat.div_pos hn.2 hn.1)
  have h' : (hR R (N / n) : ℝ) ≤ (fW W (N / n) : ℝ) := by exact_mod_cast h
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  nlinarith

/-! ### Periodicity: pointwise conditions from finitely many checks -/

theorem fW_add (W : Weights) (P : ℕ) (hP : ∀ p ∈ W, p.1 ∣ P) (k : ℕ) :
    fW W (P + k) = fW W P + fW W k := by
  induction W with
  | nil => simp [fW]
  | cons p W ih =>
    simp only [fW]
    rw [ih (fun q hq => hP q (List.mem_cons_of_mem _ hq)),
      Nat.add_div_of_dvd_right (hP p (by simp))]
    push_cast; ring

theorem fW_periodic (W : Weights) (P : ℕ) (hP : ∀ p ∈ W, p.1 ∣ P) (h0 : fW W P = 0) (k : ℕ) :
    fW W k = fW W (k % P) := by
  have key : ∀ q r, fW W (P * q + r) = fW W r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show P * (q + 1) + r = P + (P * q + r) by ring, fW_add W P hP, h0, zero_add, ih]
  conv_lhs => rw [← Nat.div_add_mod k P]
  exact key _ _

theorem hR_eq_zero (R : Runs) (B : ℕ) (hB : ∀ r ∈ R, r.2.1 ≤ B) (k : ℕ) (hk : B ≤ k) :
    hR R k = 0 := by
  induction R with
  | nil => simp [hR]
  | cons r R ih =>
    simp only [hR]
    rw [ih (fun q hq => hB q (List.mem_cons_of_mem _ hq))]
    have := hB r (by simp)
    rw [if_neg (by omega)]; simp

/-- Lower pointwise condition from a finite certificate. -/
theorem lower_pt (W : Weights) (R : Runs) (Q P B : ℕ) (hP0 : 0 < P) (hP : ∀ p ∈ W, p.1 ∣ P)
    (h0 : fW W P = 0)
    (hB : ∀ r ∈ R, r.2.1 ≤ B) (hsmall : ∀ k < B, 1 ≤ k → fW W k + hR R k ≤ Q)
    (hper : ∀ k < P, fW W k ≤ Q) : ∀ k, 1 ≤ k → fW W k + hR R k ≤ Q := by
  intro k hk
  rcases lt_or_ge k B with h | h
  · exact hsmall k h hk
  · rw [hR_eq_zero R B hB k h, add_zero, fW_periodic W P hP h0]
    exact hper _ (Nat.mod_lt _ hP0)

/-- Upper pointwise condition from a finite certificate. -/
theorem upper_pt (W : Weights) (R : Runs) (P B : ℕ) (hP0 : 0 < P) (hP : ∀ p ∈ W, p.1 ∣ P)
    (h0 : fW W P = 0) (hB : ∀ r ∈ R, r.2.1 ≤ B) (hsmall : ∀ k < B, 1 ≤ k → hR R k ≤ fW W k)
    (hper : ∀ k < P, 0 ≤ fW W k) : ∀ k, 1 ≤ k → hR R k ≤ fW W k := by
  intro k hk
  rcases lt_or_ge k B with h | h
  · exact hsmall k h hk
  · rw [hR_eq_zero R B hB k h, fW_periodic W P hP h0]
    exact hper _ (Nat.mod_lt _ hP0)

end Nagura

namespace Nagura

noncomputable def gW : Weights → ℝ → ℝ
  | [], _ => 0
  | p :: W, N => (p.2 : ℝ) * g (N / p.1) + gW W N

noncomputable def meanW : Weights → ℝ
  | [] => 0
  | p :: W => (p.2 : ℝ) / p.1 + meanW W

noncomputable def KW : Weights → ℝ
  | [] => 0
  | p :: W => -((p.2 : ℝ) * Real.log p.1 / p.1) + KW W

noncomputable def absW : Weights → ℝ
  | [] => 0
  | p :: W => |(p.2 : ℝ)| + absW W

theorem absW_nonneg (W : Weights) : 0 ≤ absW W := by
  induction W with
  | nil => simp [absW]
  | cons p W ih => simp only [absW]; positivity

theorem gW_eq (W : Weights) (hW : ∀ p ∈ W, 0 < p.1) (N : ℝ) (hN : 0 < N) :
    gW W N = N * (Real.log N - 1) * meanW W + N * KW W := by
  induction W with
  | nil => simp [gW, meanW, KW]
  | cons p W ih =>
    have hd : (0 : ℝ) < p.1 := by exact_mod_cast hW p (by simp)
    simp only [gW, meanW, KW]
    rw [ih (fun q hq => hW q (List.mem_cons_of_mem _ hq)), g, Real.log_div hN.ne' hd.ne']
    field_simp
    ring

theorem CW_ge (W : Weights) (hW : ∀ p ∈ W, 1 ≤ p.1) (N : ℕ) (hN : 1 ≤ N) :
    gW W N - absW W * (Real.log N + 1) ≤ CW W N := by
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  induction W with
  | nil => simp [gW, absW, CW]
  | cons p W ih =>
    have ih' := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    simp only [gW, absW, CW]
    have h1 := T_div_ge N p.1 hN (hW p (by simp))
    have h2 := T_div_le N p.1 hN (hW p (by simp))
    rcases le_or_gt 0 (p.2 : ℝ) with hc | hc
    · rw [abs_of_nonneg hc]
      nlinarith
    · rw [abs_of_neg hc]
      nlinarith

theorem CW_le (W : Weights) (hW : ∀ p ∈ W, 1 ≤ p.1) (N : ℕ) (hN : 1 ≤ N) :
    CW W N ≤ gW W N + absW W * (Real.log N + 1) := by
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  induction W with
  | nil => simp [gW, absW, CW]
  | cons p W ih =>
    have ih' := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    simp only [gW, absW, CW]
    have h1 := T_div_ge N p.1 hN (hW p (by simp))
    have h2 := T_div_le N p.1 hN (hW p (by simp))
    rcases le_or_gt 0 (p.2 : ℝ) with hc | hc
    · rw [abs_of_nonneg hc]
      nlinarith
    · rw [abs_of_neg hc]
      nlinarith

theorem meanW_mul (W : Weights) (P : ℕ) (hP : ∀ p ∈ W, p.1 ∣ P) (hW : ∀ p ∈ W, 0 < p.1) :
    (P : ℝ) * meanW W = fW W P := by
  induction W with
  | nil => simp [meanW, fW]
  | cons p W ih =>
    simp only [meanW, fW, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [mul_add, ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hW q (List.mem_cons_of_mem _ hq)),
      Nat.cast_div (hP p (by simp)) (by exact_mod_cast (hW p (by simp)).ne')]
    have hd : (0 : ℝ) < p.1 := by exact_mod_cast hW p (by simp)
    field_simp

/-- With mean zero (`fW W P = 0`), the weighted sum is `K_W · N` up to `O(log N)`. -/
theorem CW_bounds (W : Weights) (P : ℕ) (hP0 : 0 < P) (hP : ∀ p ∈ W, p.1 ∣ P)
    (hW : ∀ p ∈ W, 1 ≤ p.1) (h0 : fW W P = 0) (N : ℕ) (hN : 1 ≤ N) :
    KW W * N - absW W * (Real.log N + 1) ≤ CW W N ∧
    CW W N ≤ KW W * N + absW W * (Real.log N + 1) := by
  have hW0 : ∀ p ∈ W, 0 < p.1 := fun p hp => hW p hp
  have hm : meanW W = 0 := by
    have := meanW_mul W P hP hW0
    rw [h0] at this
    have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP0.ne'
    simpa [hP'] using this
  have hg := gW_eq W hW0 N (by exact_mod_cast hN)
  rw [hm] at hg
  have a := CW_ge W hW N hN
  have b := CW_le W hW N hN
  constructor <;> nlinarith

end Nagura

/-! ## Interval `(x, 7x/6]`: one bootstrap round with weights on divisors of 210 -/

namespace Nagura

theorem exp_one_ge : (2.71813 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le

theorem log_le_sqrt' (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ 7359 / 10000 * Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsq : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0.le).symm
  have he : (271813 / 100000 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos hs hepos)
  rw [Real.log_div hs.ne' hepos.ne', Real.log_exp] at h
  have h2 : Real.sqrt N / Real.exp 1 ≤ Real.sqrt N / (271813 / 100000) :=
    div_le_div_of_nonneg_left hs.le (by norm_num) he
  have h3 : Real.log (Real.sqrt N) ≤ Real.sqrt N / (271813 / 100000) := by linarith
  have h4 : Real.log N = 2 * Real.log (Real.sqrt N) := by
    conv_lhs => rw [hsq]
    rw [Real.log_pow]; push_cast; ring
  rw [h4]; linarith

theorem log_pow_ratio (p a b : ℕ) (hp : 0 < p) :
    1 - (2 : ℝ) ^ b / (p : ℝ) ^ a ≤ a * Real.log p - b * Real.log 2 ∧
    a * Real.log p - b * Real.log 2 ≤ (p : ℝ) ^ a / 2 ^ b - 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : (0 : ℝ) < (p : ℝ) ^ a / 2 ^ b := by positivity
  have hl : Real.log ((p : ℝ) ^ a / 2 ^ b) = a * Real.log p - b * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hr
    rw [hl, inv_div] at this; exact this
  · have := Real.log_le_sub_one_of_pos hr
    rw [hl] at this; exact this


theorem log3_lo : (1098612247 : ℝ) / 1000000000 ≤ Real.log 3 := by
  have h := log_pow_ratio 3 53 84 (by norm_num)
  norm_num at h
  linarith [h.1, Real.log_two_gt_d9]

theorem log3_hi : Real.log 3 ≤ (1098612331 : ℝ) / 1000000000 := by
  have h := log_pow_ratio 3 53 84 (by norm_num)
  norm_num at h
  linarith [h.2, Real.log_two_lt_d9]

theorem log5_lo : (201179719 : ℝ) / 125000000 ≤ Real.log 5 := by
  have h := log_pow_ratio 5 59 137 (by norm_num)
  norm_num at h
  linarith [h.1, Real.log_two_gt_d9]

theorem log5_hi : Real.log 5 ≤ (201179759 : ℝ) / 125000000 := by
  have h := log_pow_ratio 5 59 137 (by norm_num)
  norm_num at h
  linarith [h.2, Real.log_two_lt_d9]

theorem log7_lo : (389181887 : ℝ) / 200000000 ≤ Real.log 7 := by
  have h := log_pow_ratio 7 26 73 (by norm_num)
  norm_num at h
  linarith [h.1, Real.log_two_gt_d9]

theorem log7_hi : Real.log 7 ≤ (97295543 : ℝ) / 50000000 := by
  have h := log_pow_ratio 7 26 73 (by norm_num)
  norm_num at h
  linarith [h.2, Real.log_two_lt_d9]

theorem log2_lo' : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
theorem log2_hi' : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le

theorem log_6 : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_10 : Real.log 10 = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_14 : Real.log 14 = Real.log 2 + Real.log 7 := by
  rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_21 : Real.log 21 = Real.log 3 + Real.log 7 := by
  rw [show (21 : ℝ) = 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

theorem log_35 : Real.log 35 = Real.log 5 + Real.log 7 := by
  rw [show (35 : ℝ) = 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_42 : Real.log 42 = Real.log 2 + Real.log 3 + Real.log 7 := by
  rw [show (42 : ℝ) = 2 * 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

theorem log_70 : Real.log 70 = Real.log 2 + Real.log 5 + Real.log 7 := by
  rw [show (70 : ℝ) = 2 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

theorem log_105 : Real.log 105 = Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (105 : ℝ) = 3 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

theorem log_210 : Real.log 210 = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (210 : ℝ) = 2 * 3 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

def WU6 : Weights := [(1, 1), (2, -1), (3, -1), (5, -1), (7, -1), (10, 1), (14, 1), (30, 1), (42, -1), (210, -1)]
def WL6 : Weights := [(1, 3), (2, -3), (3, -3), (5, -3), (6, 2), (7, -3), (10, 1), (14, 1), (21, 1), (35, 1), (42, -1), (70, -2), (105, -1), (210, 2)]
def RU6a : Runs := [(1, 6, 1)]
def RU6 : Runs := [(1, 6, 1), (13, 15, 1), (29, 36, 1)]
def RL6 : Runs := [(1, 13, 2), (6, 11, 1), (14, 19, 2), (20, 23, 1), (20, 40, 1), (24, 29, 1)]

theorem WU6_pos : ∀ p ∈ WU6, 1 ≤ p.1 := by decide
theorem WU6_pos0 : ∀ p ∈ WU6, 0 < p.1 := by decide
theorem WU6_dvd : ∀ p ∈ WU6, p.1 ∣ 210 := by decide
set_option maxRecDepth 100000 in
theorem WU6_mean : fW WU6 210 = 0 := by decide

theorem WL6_pos : ∀ p ∈ WL6, 1 ≤ p.1 := by decide
theorem WL6_pos0 : ∀ p ∈ WL6, 0 < p.1 := by decide
theorem WL6_dvd : ∀ p ∈ WL6, p.1 ∣ 210 := by decide
set_option maxRecDepth 100000 in
theorem WL6_mean : fW WL6 210 = 0 := by decide

theorem RU6a_ok : ∀ r ∈ RU6a, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

theorem RU6_ok : ∀ r ∈ RU6, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

theorem RL6_ok : ∀ r ∈ RL6, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

set_option maxRecDepth 100000 in
theorem ptU6a : ∀ k, 1 ≤ k → hR RU6a k ≤ fW WU6 k :=
  upper_pt WU6 RU6a 210 6 (by norm_num) WU6_dvd WU6_mean (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem ptU6 : ∀ k, 1 ≤ k → hR RU6 k ≤ fW WU6 k :=
  upper_pt WU6 RU6 210 36 (by norm_num) WU6_dvd WU6_mean (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem ptL6 : ∀ k, 1 ≤ k → fW WL6 k + hR RL6 k ≤ 5 :=
  lower_pt WL6 RL6 5 210 40 (by norm_num) WL6_dvd WL6_mean (by decide) (by decide) (by decide)

theorem absW_WU6 : absW WU6 = 10 := by simp [absW, WU6]; norm_num
theorem absW_WL6 : absW WL6 = 27 := by simp [absW, WL6]; norm_num

theorem KW_WU6_le : KW WU6 ≤ ((894973 : ℝ) / 1000000) := by
  simp only [KW, WU6]
  push_cast
  simp only [Real.log_one]
  simp only [log_6, log_10, log_14, log_21, log_30, log_35, log_42, log_70, log_105, log_210]
  linarith [log2_lo', log2_hi', log3_lo, log3_hi, log5_lo, log5_hi, log7_lo, log7_hi]

theorem KW_WL6_ge : ((575831 : ℝ) / 200000) ≤ KW WL6 := by
  simp only [KW, WL6]
  push_cast
  simp only [Real.log_one]
  simp only [log_6, log_10, log_14, log_21, log_30, log_35, log_42, log_70, log_105, log_210]
  linarith [log2_lo', log2_hi', log3_lo, log3_hi, log5_lo, log5_hi, log7_lo, log7_hi]

end Nagura

namespace Nagura

theorem A_ge' : (92129 / 100000 : ℝ) ≤ A := by
  unfold A; linarith [log2_lo', log3_lo, log5_lo]

theorem one_le_sqrt_nat (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Real.sqrt N :=
  Real.one_le_sqrt.mpr (by exact_mod_cast hN)

theorem floor_le (N d : ℕ) : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le

theorem S_le_U0 (N : ℕ) : S N ≤ ((53699 : ℝ) / 50000) * N + 31 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := upper_struct WU6 RU6a WU6_pos0 RU6a_ok ptU6a N
  simp only [SR, RU6a, Nat.div_one, Nat.cast_one, one_mul, add_zero] at hs
  have hc := (CW_bounds WU6 210 (by norm_num) WU6_dvd WU6_pos WU6_mean N hN).2
  rw [absW_WU6] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WU6_le hN0
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hc hK ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem S_ge_L1 (N : ℕ) : ((9361 : ℝ) / 10000) * N - 48 * Real.sqrt N ≤ S N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := lower_struct WL6 RL6 5 WL6_pos0 RL6_ok ptL6 N
  simp only [SR, RL6, Nat.div_one, add_zero] at hs
  have hc := (CW_bounds WL6 210 (by norm_num) WL6_dvd WL6_pos WL6_mean N hN).1
  rw [absW_WL6] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WL6_ge hN0
  have i6 := S_ge (N / 6)
  have a6 : ((92129 : ℝ) / 100000) * ((N / 6 : ℕ) : ℝ) ≤ A * ((N / 6 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i14 := S_ge (N / 14)
  have a14 : ((92129 : ℝ) / 100000) * ((N / 14 : ℕ) : ℝ) ≤ A * ((N / 14 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i20 := S_ge (N / 20)
  have a20 : ((92129 : ℝ) / 100000) * ((N / 20 : ℕ) : ℝ) ≤ A * ((N / 20 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i24 := S_ge (N / 24)
  have a24 : ((92129 : ℝ) / 100000) * ((N / 24 : ℕ) : ℝ) ≤ A * ((N / 24 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have u11 := S_le_U0 (N / 11)
  have u13 := S_le_U0 (N / 13)
  have u19 := S_le_U0 (N / 19)
  have u23 := S_le_U0 (N / 23)
  have u29 := S_le_U0 (N / 29)
  have u40 := S_le_U0 (N / 40)
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m11 : ((N / 11 : ℕ) : ℝ) ≤ (N : ℝ) / 11 := by
    have := floor_le N 11; push_cast at this; exact this
  have q11 : Real.sqrt ((N / 11 : ℕ) : ℝ) ≤ ((3017 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m13 : ((N / 13 : ℕ) : ℝ) ≤ (N : ℝ) / 13 := by
    have := floor_le N 13; push_cast at this; exact this
  have q13 : Real.sqrt ((N / 13 : ℕ) : ℝ) ≤ ((111 : ℝ) / 400) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m14 : ((N / 14 : ℕ) : ℝ) ≤ (N : ℝ) / 14 := by
    have := floor_le N 14; push_cast at this; exact this
  have q14 : Real.sqrt ((N / 14 : ℕ) : ℝ) ≤ ((1337 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m19 : ((N / 19 : ℕ) : ℝ) ≤ (N : ℝ) / 19 := by
    have := floor_le N 19; push_cast at this; exact this
  have q19 : Real.sqrt ((N / 19 : ℕ) : ℝ) ≤ ((287 : ℝ) / 1250) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m20 : ((N / 20 : ℕ) : ℝ) ≤ (N : ℝ) / 20 := by
    have := floor_le N 20; push_cast at this; exact this
  have q20 : Real.sqrt ((N / 20 : ℕ) : ℝ) ≤ ((1119 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m23 : ((N / 23 : ℕ) : ℝ) ≤ (N : ℝ) / 23 := by
    have := floor_le N 23; push_cast at this; exact this
  have q23 : Real.sqrt ((N / 23 : ℕ) : ℝ) ≤ ((2087 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m24 : ((N / 24 : ℕ) : ℝ) ≤ (N : ℝ) / 24 := by
    have := floor_le N 24; push_cast at this; exact this
  have q24 : Real.sqrt ((N / 24 : ℕ) : ℝ) ≤ ((2043 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m29 : ((N / 29 : ℕ) : ℝ) ≤ (N : ℝ) / 29 := by
    have := floor_le N 29; push_cast at this; exact this
  have q29 : Real.sqrt ((N / 29 : ℕ) : ℝ) ≤ ((929 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m40 : ((N / 40 : ℕ) : ℝ) ≤ (N : ℝ) / 40 := by
    have := floor_le N 40; push_cast at this; exact this
  have q40 : Real.sqrt ((N / 40 : ℕ) : ℝ) ≤ ((1583 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have g6 : (N : ℝ) / 6 - 1 < ((N / 6 : ℕ) : ℝ) := by
    have := cast_div_gt N 6; push_cast at this; exact this
  have l6 : Real.log ((N / 6 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 6)
  have g14 : (N : ℝ) / 14 - 1 < ((N / 14 : ℕ) : ℝ) := by
    have := cast_div_gt N 14; push_cast at this; exact this
  have l14 : Real.log ((N / 14 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 14)
  have g20 : (N : ℝ) / 20 - 1 < ((N / 20 : ℕ) : ℝ) := by
    have := cast_div_gt N 20; push_cast at this; exact this
  have l20 : Real.log ((N / 20 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 20)
  have g24 : (N : ℝ) / 24 - 1 < ((N / 24 : ℕ) : ℝ) := by
    have := cast_div_gt N 24; push_cast at this; exact this
  have l24 : Real.log ((N / 24 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 24)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hs hc hK ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem S_le_U1' (N : ℕ) : S N ≤ ((6691 : ℝ) / 6250) * N + 94 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := upper_struct WU6 RU6 WU6_pos0 RU6_ok ptU6 N
  simp only [SR, RU6, Nat.div_one, Nat.cast_one, one_mul, add_zero] at hs
  have hc := (CW_bounds WU6 210 (by norm_num) WU6_dvd WU6_pos WU6_mean N hN).2
  rw [absW_WU6] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WU6_le hN0
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have i13 := S_ge_L1 (N / 13)
  have u15 := S_le_U0 (N / 15)
  have i29 := S_ge_L1 (N / 29)
  have u36 := S_le_U0 (N / 36)
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m13 : ((N / 13 : ℕ) : ℝ) ≤ (N : ℝ) / 13 := by
    have := floor_le N 13; push_cast at this; exact this
  have q13 : Real.sqrt ((N / 13 : ℕ) : ℝ) ≤ ((111 : ℝ) / 400) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m15 : ((N / 15 : ℕ) : ℝ) ≤ (N : ℝ) / 15 := by
    have := floor_le N 15; push_cast at this; exact this
  have q15 : Real.sqrt ((N / 15 : ℕ) : ℝ) ≤ ((2583 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m29 : ((N / 29 : ℕ) : ℝ) ≤ (N : ℝ) / 29 := by
    have := floor_le N 29; push_cast at this; exact this
  have q29 : Real.sqrt ((N / 29 : ℕ) : ℝ) ≤ ((929 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m36 : ((N / 36 : ℕ) : ℝ) ≤ (N : ℝ) / 36 := by
    have := floor_le N 36; push_cast at this; exact this
  have q36 : Real.sqrt ((N / 36 : ℕ) : ℝ) ≤ ((417 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have g13 : (N : ℝ) / 13 - 1 < ((N / 13 : ℕ) : ℝ) := by
    have := cast_div_gt N 13; push_cast at this; exact this
  have l13 : Real.log ((N / 13 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 13)
  have g29 : (N : ℝ) / 29 - 1 < ((N / 29 : ℕ) : ℝ) := by
    have := cast_div_gt N 29; push_cast at this; exact this
  have l29 : Real.log ((N / 29 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 29)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hs hc hK ⊢
  linarith

end Nagura

namespace Nagura

theorem nagura7_large (N : ℕ) (hN : 100000000 ≤ N) : ∃ p, p.Prime ∧ N < p ∧ 6 * p ≤ 7 * N := by
  by_contra hcon
  push_neg at hcon
  set M := 7 * N / 6 with hMdef
  have hNM : N ≤ M := by omega
  have hth : Chebyshev.theta M = Chebyshev.theta N :=
    theta_eq_of_no_prime N M hNM (fun p hp hlt => by have := hcon p hp hlt; omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have h1 := Chebyshev.psi_sub_theta_le hM1
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  rw [psi_nat] at h1 h2
  have hL := S_ge_L1 M
  have hU := S_le_U1' N
  have hN0 : (100000000 : ℝ) ≤ N := by exact_mod_cast hN
  set s := Real.sqrt (N : ℝ) with hs
  have hsN : (N : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hs4 : (10000 : ℝ) ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hMle : (M : ℝ) ≤ 7 / 6 * N := by
    have : 6 * M ≤ 7 * N := by omega
    have : (6 : ℝ) * M ≤ 7 * N := by exact_mod_cast this
    linarith
  have hMge : (7 * N - 5 : ℝ) / 6 ≤ M := by
    have : 7 * N ≤ 6 * M + 5 := by omega
    have : (7 : ℝ) * N ≤ 6 * M + 5 := by exact_mod_cast this
    linarith
  have hsqM : Real.sqrt (M : ℝ) ≤ 10802 / 10000 * s :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlogM2 : Real.log M ≤ Real.log 2 + Real.log N := by
    have : M ≤ 2 * N := by omega
    have h := log_nat_mono this
    push_cast at h
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  have hspos : 0 < s := by linarith
  have hlogN : Real.log N = 2 * Real.log s := by
    rw [hsN, Real.log_pow]; push_cast; ring
  have hlog10000 : Real.log 10000 ≤ 4 * (Real.log 2 + Real.log 5) := by
    rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow, log_10]; push_cast; linarith
  have hlogs : Real.log s ≤ Real.log 10000 + (s / 10000 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 10000 by positivity)
    rw [Real.log_div hspos.ne' (by norm_num)] at h
    linarith
  have hlogMb : Real.log M ≤ 1712 / 100 + s / 5000 := by
    linarith [log2_hi', log5_hi]
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt (M : ℝ) * Real.log M ≤ (10802 / 10000 * s) * (1712 / 100 + s / 5000) :=
    mul_le_mul hsqM hlogMb hlogM0 (by positivity)
  have hss : 10000 * s ≤ s * s := by nlinarith
  rw [hsN] at hMge hU
  nlinarith

/-- Generic prime chain with ratio `u / v`. -/
def chainR (u v : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: t => decide (v * b ≤ u * a) && chainR u v b t

theorem chainR_cover (u v : ℕ) (l : List ℕ) : ∀ a : ℕ, (∀ p ∈ l, p.Prime) → chainR u v a l = true →
    ∀ x, a ≤ x → (∃ p ∈ l, x < p) → ∃ p, p.Prime ∧ x < p ∧ v * p ≤ u * x := by
  induction l with
  | nil => intro a _ _ x _ ⟨p, hp, _⟩; simp at hp
  | cons b t ih =>
    intro a hpr hch x hax hex
    simp only [chainR, Bool.and_eq_true, decide_eq_true_eq] at hch
    by_cases hxb : x < b
    · exact ⟨b, hpr b (by simp), hxb, le_trans hch.1 (Nat.mul_le_mul_left u hax)⟩
    · push_neg at hxb
      apply ih b (fun p hp => hpr p (by simp [hp])) hch.2 x hxb
      obtain ⟨p, hp, hxp⟩ := hex
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact ⟨p, hp, hxp⟩

def primeChain7 : List ℕ := [37, 43, 47, 53, 61, 71, 79, 89, 103, 113, 131, 151, 173, 199, 229, 263, 293, 337, 389, 449, 523, 607, 701, 811, 941, 1097, 1279, 1489, 1733, 2017, 2351, 2741, 3191, 3719, 4337, 5059, 5897, 6871, 8011, 9343, 10891, 12703, 14813, 17257, 20129, 23473, 27367, 31907, 37223, 43411, 50627, 59063, 68903, 80369, 93763, 109387, 127609, 148873, 173683, 202627, 236387, 275783, 321743, 375359, 437909, 510889, 596027, 695347, 811231, 946417, 1104139, 1288117, 1502801, 1753249, 2045441, 2386313, 2784007, 3247987, 3789293, 4420837, 5157629, 6017213, 7020077, 8190067, 9555061, 11147561, 13005457, 15173029, 17701867, 20652157, 24094181, 28109869, 32794843, 38260643, 44637401, 52076963, 60756431, 70882499, 82696231, 96478933, 112558753]

theorem primeChain7_prime : ∀ p ∈ primeChain7, p.Prime := by
  simp only [primeChain7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

theorem primeChain7_chain : chainR 7 6 32 primeChain7 = true := by decide

/-- For every natural number `x ≥ 32` there is a prime `p` with `x < p ≤ 7x/6`. -/
theorem nagura7 (x : ℕ) (hx : 32 ≤ x) : ∃ p, p.Prime ∧ x < p ∧ 6 * p ≤ 7 * x := by
  rcases lt_or_ge x 100000000 with h | h
  · exact chainR_cover 7 6 primeChain7 32 primeChain7_prime primeChain7_chain x hx
      ⟨112558753, by simp [primeChain7], by omega⟩
  · exact nagura7_large x h

end Nagura

/-! ## Interval `(x, 8x/7]` (tag 7): one bootstrap round, weights on divisors of 420 -/

namespace Nagura

theorem log_20 : Real.log 20 = Real.log 2 + Real.log 2 + Real.log 5 := by
  rw [show (20 : ℝ) = 2 * 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

theorem log_420 : Real.log 420 = Real.log 2 + Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (420 : ℝ) = 2 * 2 * 3 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]

def WU7 : Weights := [(1, 1), (2, -1), (3, -1), (5, -1), (7, -1), (10, 1), (14, 1), (20, -1), (21, 1), (30, 1), (42, -1), (420, -1)]
def WL7 : Weights := [(1, 3), (2, -3), (3, -3), (5, -3), (6, 2), (7, -3), (10, 1), (14, 1), (21, 1), (35, 1), (42, -1), (70, -2), (105, -1), (210, 2)]
def RU7a : Runs := [(1, 6, 1)]
def RU7 : Runs := [(1, 6, 1), (13, 15, 1), (29, 35, 1), (31, 36, 1)]
def RL7 : Runs := [(1, 13, 2), (6, 11, 1), (14, 17, 2), (15, 17, 1), (15, 19, 2), (20, 23, 1), (20, 40, 1), (24, 29, 1)]

theorem WU7_pos : ∀ p ∈ WU7, 1 ≤ p.1 := by decide
theorem WU7_pos0 : ∀ p ∈ WU7, 0 < p.1 := by decide
theorem WU7_dvd : ∀ p ∈ WU7, p.1 ∣ 420 := by decide
set_option maxRecDepth 100000 in
theorem WU7_mean : fW WU7 420 = 0 := by decide

theorem WL7_pos : ∀ p ∈ WL7, 1 ≤ p.1 := by decide
theorem WL7_pos0 : ∀ p ∈ WL7, 0 < p.1 := by decide
theorem WL7_dvd : ∀ p ∈ WL7, p.1 ∣ 420 := by decide
set_option maxRecDepth 100000 in
theorem WL7_mean : fW WL7 420 = 0 := by decide

theorem RU7a_ok : ∀ r ∈ RU7a, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

theorem RU7_ok : ∀ r ∈ RU7, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

theorem RL7_ok : ∀ r ∈ RL7, 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by decide

set_option maxRecDepth 100000 in
theorem ptU7a : ∀ k, 1 ≤ k → hR RU7a k ≤ fW WU7 k :=
  upper_pt WU7 RU7a 420 6 (by norm_num) WU7_dvd WU7_mean (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem ptU7 : ∀ k, 1 ≤ k → hR RU7 k ≤ fW WU7 k :=
  upper_pt WU7 RU7 420 36 (by norm_num) WU7_dvd WU7_mean (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem ptL7 : ∀ k, 1 ≤ k → fW WL7 k + hR RL7 k ≤ 5 :=
  lower_pt WL7 RL7 5 420 40 (by norm_num) WL7_dvd WL7_mean (by decide) (by decide) (by decide)

theorem absW_WU7 : absW WU7 = 12 := by simp [absW, WU7]; norm_num
theorem absW_WL7 : absW WL7 = 27 := by simp [absW, WL7]; norm_num

theorem KW_WU7_le : KW WU7 ≤ ((8887 : ℝ) / 10000) := by
  simp only [KW, WU7]
  push_cast
  simp only [Real.log_one, log_6, log_10, log_14, log_20, log_21, log_30, log_35, log_42, log_70, log_105, log_210, log_420]
  linarith [log2_lo', log2_hi', log3_lo, log3_hi, log5_lo, log5_hi, log7_lo, log7_hi]

theorem KW_WL7_ge : ((1439579 : ℝ) / 500000) ≤ KW WL7 := by
  simp only [KW, WL7]
  push_cast
  simp only [Real.log_one, log_6, log_10, log_14, log_20, log_21, log_30, log_35, log_42, log_70, log_105, log_210, log_420]
  linarith [log2_lo', log2_hi', log3_lo, log3_hi, log5_lo, log5_hi, log7_lo, log7_hi]

set_option maxHeartbeats 4000000 in
theorem S_le_U0_7 (N : ℕ) : S N ≤ ((21329 : ℝ) / 20000) * N + 37 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := upper_struct WU7 RU7a WU7_pos0 RU7a_ok ptU7a N
  simp only [SR, RU7a, Nat.div_one, Nat.cast_one, one_mul, add_zero] at hs
  have hc := (CW_bounds WU7 420 (by norm_num) WU7_dvd WU7_pos WU7_mean N hN).2
  rw [absW_WU7] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WU7_le hN0
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hc hK ⊢
  linarith

set_option maxHeartbeats 8000000 in
theorem S_ge_L1_7 (N : ℕ) : ((11699 : ℝ) / 12500) * N - 66 * Real.sqrt N ≤ S N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := lower_struct WL7 RL7 5 WL7_pos0 RL7_ok ptL7 N
  simp only [SR, RL7, Nat.div_one, add_zero] at hs
  have hc := (CW_bounds WL7 420 (by norm_num) WL7_dvd WL7_pos WL7_mean N hN).1
  rw [absW_WL7] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WL7_ge hN0
  have i6 := S_ge (N / 6)
  have a6 : ((92129 : ℝ) / 100000) * ((N / 6 : ℕ) : ℝ) ≤ A * ((N / 6 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i14 := S_ge (N / 14)
  have a14 : ((92129 : ℝ) / 100000) * ((N / 14 : ℕ) : ℝ) ≤ A * ((N / 14 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i15 := S_ge (N / 15)
  have a15 : ((92129 : ℝ) / 100000) * ((N / 15 : ℕ) : ℝ) ≤ A * ((N / 15 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i20 := S_ge (N / 20)
  have a20 : ((92129 : ℝ) / 100000) * ((N / 20 : ℕ) : ℝ) ≤ A * ((N / 20 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have i24 := S_ge (N / 24)
  have a24 : ((92129 : ℝ) / 100000) * ((N / 24 : ℕ) : ℝ) ≤ A * ((N / 24 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right A_ge' (Nat.cast_nonneg _)
  have u11 := S_le_U0_7 (N / 11)
  have u13 := S_le_U0_7 (N / 13)
  have u17 := S_le_U0_7 (N / 17)
  have u19 := S_le_U0_7 (N / 19)
  have u23 := S_le_U0_7 (N / 23)
  have u29 := S_le_U0_7 (N / 29)
  have u40 := S_le_U0_7 (N / 40)
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m11 : ((N / 11 : ℕ) : ℝ) ≤ (N : ℝ) / 11 := by
    have := floor_le N 11; push_cast at this; exact this
  have q11 : Real.sqrt ((N / 11 : ℕ) : ℝ) ≤ ((3017 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m13 : ((N / 13 : ℕ) : ℝ) ≤ (N : ℝ) / 13 := by
    have := floor_le N 13; push_cast at this; exact this
  have q13 : Real.sqrt ((N / 13 : ℕ) : ℝ) ≤ ((111 : ℝ) / 400) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m14 : ((N / 14 : ℕ) : ℝ) ≤ (N : ℝ) / 14 := by
    have := floor_le N 14; push_cast at this; exact this
  have q14 : Real.sqrt ((N / 14 : ℕ) : ℝ) ≤ ((1337 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m15 : ((N / 15 : ℕ) : ℝ) ≤ (N : ℝ) / 15 := by
    have := floor_le N 15; push_cast at this; exact this
  have q15 : Real.sqrt ((N / 15 : ℕ) : ℝ) ≤ ((2583 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m17 : ((N / 17 : ℕ) : ℝ) ≤ (N : ℝ) / 17 := by
    have := floor_le N 17; push_cast at this; exact this
  have q17 : Real.sqrt ((N / 17 : ℕ) : ℝ) ≤ ((2427 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m19 : ((N / 19 : ℕ) : ℝ) ≤ (N : ℝ) / 19 := by
    have := floor_le N 19; push_cast at this; exact this
  have q19 : Real.sqrt ((N / 19 : ℕ) : ℝ) ≤ ((287 : ℝ) / 1250) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m20 : ((N / 20 : ℕ) : ℝ) ≤ (N : ℝ) / 20 := by
    have := floor_le N 20; push_cast at this; exact this
  have q20 : Real.sqrt ((N / 20 : ℕ) : ℝ) ≤ ((1119 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m23 : ((N / 23 : ℕ) : ℝ) ≤ (N : ℝ) / 23 := by
    have := floor_le N 23; push_cast at this; exact this
  have q23 : Real.sqrt ((N / 23 : ℕ) : ℝ) ≤ ((2087 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m24 : ((N / 24 : ℕ) : ℝ) ≤ (N : ℝ) / 24 := by
    have := floor_le N 24; push_cast at this; exact this
  have q24 : Real.sqrt ((N / 24 : ℕ) : ℝ) ≤ ((2043 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m29 : ((N / 29 : ℕ) : ℝ) ≤ (N : ℝ) / 29 := by
    have := floor_le N 29; push_cast at this; exact this
  have q29 : Real.sqrt ((N / 29 : ℕ) : ℝ) ≤ ((929 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m40 : ((N / 40 : ℕ) : ℝ) ≤ (N : ℝ) / 40 := by
    have := floor_le N 40; push_cast at this; exact this
  have q40 : Real.sqrt ((N / 40 : ℕ) : ℝ) ≤ ((1583 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have g6 : (N : ℝ) / 6 - 1 < ((N / 6 : ℕ) : ℝ) := by
    have := cast_div_gt N 6; push_cast at this; exact this
  have l6 : Real.log ((N / 6 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 6)
  have g14 : (N : ℝ) / 14 - 1 < ((N / 14 : ℕ) : ℝ) := by
    have := cast_div_gt N 14; push_cast at this; exact this
  have l14 : Real.log ((N / 14 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 14)
  have g15 : (N : ℝ) / 15 - 1 < ((N / 15 : ℕ) : ℝ) := by
    have := cast_div_gt N 15; push_cast at this; exact this
  have l15 : Real.log ((N / 15 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 15)
  have g20 : (N : ℝ) / 20 - 1 < ((N / 20 : ℕ) : ℝ) := by
    have := cast_div_gt N 20; push_cast at this; exact this
  have l20 : Real.log ((N / 20 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 20)
  have g24 : (N : ℝ) / 24 - 1 < ((N / 24 : ℕ) : ℝ) := by
    have := cast_div_gt N 24; push_cast at this; exact this
  have l24 : Real.log ((N / 24 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 24)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hs hc hK ⊢
  linarith

set_option maxHeartbeats 8000000 in
theorem S_le_U1_7 (N : ℕ) : S N ≤ ((106253 : ℝ) / 100000) * N + 150 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have hs := upper_struct WU7 RU7 WU7_pos0 RU7_ok ptU7 N
  simp only [SR, RU7, Nat.div_one, Nat.cast_one, one_mul, add_zero] at hs
  have hc := (CW_bounds WU7 420 (by norm_num) WU7_dvd WU7_pos WU7_mean N hN).2
  rw [absW_WU7] at hc
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK := mul_le_mul_of_nonneg_right KW_WU7_le hN0
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have i13 := S_ge_L1_7 (N / 13)
  have u15 := S_le_U0_7 (N / 15)
  have i29 := S_ge_L1_7 (N / 29)
  have u35 := S_le_U0_7 (N / 35)
  have i31 := S_ge_L1_7 (N / 31)
  have u36 := S_le_U0_7 (N / 36)
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := floor_le N 6; push_cast at this; exact this
  have q6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ ((1021 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m13 : ((N / 13 : ℕ) : ℝ) ≤ (N : ℝ) / 13 := by
    have := floor_le N 13; push_cast at this; exact this
  have q13 : Real.sqrt ((N / 13 : ℕ) : ℝ) ≤ ((111 : ℝ) / 400) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m15 : ((N / 15 : ℕ) : ℝ) ≤ (N : ℝ) / 15 := by
    have := floor_le N 15; push_cast at this; exact this
  have q15 : Real.sqrt ((N / 15 : ℕ) : ℝ) ≤ ((2583 : ℝ) / 10000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m29 : ((N / 29 : ℕ) : ℝ) ≤ (N : ℝ) / 29 := by
    have := floor_le N 29; push_cast at this; exact this
  have q29 : Real.sqrt ((N / 29 : ℕ) : ℝ) ≤ ((929 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m31 : ((N / 31 : ℕ) : ℝ) ≤ (N : ℝ) / 31 := by
    have := floor_le N 31; push_cast at this; exact this
  have q31 : Real.sqrt ((N / 31 : ℕ) : ℝ) ≤ ((899 : ℝ) / 5000) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m35 : ((N / 35 : ℕ) : ℝ) ≤ (N : ℝ) / 35 := by
    have := floor_le N 35; push_cast at this; exact this
  have q35 : Real.sqrt ((N / 35 : ℕ) : ℝ) ≤ ((423 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have m36 : ((N / 36 : ℕ) : ℝ) ≤ (N : ℝ) / 36 := by
    have := floor_le N 36; push_cast at this; exact this
  have q36 : Real.sqrt ((N / 36 : ℕ) : ℝ) ≤ ((417 : ℝ) / 2500) * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have g13 : (N : ℝ) / 13 - 1 < ((N / 13 : ℕ) : ℝ) := by
    have := cast_div_gt N 13; push_cast at this; exact this
  have l13 : Real.log ((N / 13 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 13)
  have g29 : (N : ℝ) / 29 - 1 < ((N / 29 : ℕ) : ℝ) := by
    have := cast_div_gt N 29; push_cast at this; exact this
  have l29 : Real.log ((N / 29 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 29)
  have g31 : (N : ℝ) / 31 - 1 < ((N / 31 : ℕ) : ℝ) := by
    have := cast_div_gt N 31; push_cast at this; exact this
  have l31 : Real.log ((N / 31 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 31)
  have hlog := log_le_sqrt' N hN
  have hs1 := one_le_sqrt_nat N hN
  push_cast at hs hc hK ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem nagura_7_large (N : ℕ) (hN : 1600000000 ≤ N) : ∃ p, p.Prime ∧ N < p ∧ 7 * p ≤ 8 * N := by
  by_contra hcon
  push_neg at hcon
  set M := 8 * N / 7 with hMdef
  have hNM : N ≤ M := by omega
  have hth : Chebyshev.theta M = Chebyshev.theta N :=
    theta_eq_of_no_prime N M hNM (fun p hp hlt => by have := hcon p hp hlt; omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have h1 := Chebyshev.psi_sub_theta_le hM1
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  rw [psi_nat] at h1 h2
  have hL := S_ge_L1_7 M
  have hU := S_le_U1_7 N
  have hN0 : (1600000000 : ℝ) ≤ N := by exact_mod_cast hN
  set s := Real.sqrt (N : ℝ) with hs
  have hsN : (N : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hs4 : (40000 : ℝ) ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hMle : (M : ℝ) ≤ 8 / 7 * N := by
    have : 7 * M ≤ 8 * N := by omega
    have : (7 : ℝ) * M ≤ 8 * N := by exact_mod_cast this
    linarith
  have hMge : (8 * N - 6 : ℝ) / 7 ≤ M := by
    have : 8 * N ≤ 7 * M + 6 := by omega
    have : (8 : ℝ) * N ≤ 7 * M + 6 := by exact_mod_cast this
    linarith
  have hsqM : Real.sqrt (M : ℝ) ≤ ((2673 : ℝ) / 2500) * s :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlogM2 : Real.log M ≤ Real.log 2 + Real.log N := by
    have : M ≤ 2 * N := by omega
    have h := log_nat_mono this
    push_cast at h
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  have hspos : 0 < s := by linarith
  have hlogN : Real.log N = 2 * Real.log s := by
    rw [hsN, Real.log_pow]; push_cast; ring
  have hlogs0 : Real.log 40000 ≤ 6 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (40000 : ℝ) = 2 ^ 6 * 5 ^ 4 by norm_num, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; linarith
  have hlogs : Real.log s ≤ Real.log 40000 + (s / 40000 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 40000 by positivity)
    rw [Real.log_div hspos.ne' (by norm_num)] at h
    linarith
  have hlogMb : Real.log M ≤ ((199 : ℝ) / 10) + s / 20000 := by
    linarith [log2_hi', log5_hi]
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt (M : ℝ) * Real.log M ≤ (((2673 : ℝ) / 2500) * s) * (((199 : ℝ) / 10) + s / 20000) :=
    mul_le_mul hsqM hlogMb hlogM0 (by positivity)
  have hss : 40000 * s ≤ s * s := by nlinarith
  rw [hsN] at hMge hU
  nlinarith

def primeChain_7 : List ℕ := [37, 41, 43, 47, 53, 59, 67, 73, 83, 89, 101, 113, 127, 139, 157, 179, 199, 227, 257, 293, 331, 373, 421, 479, 547, 619, 701, 797, 907, 1033, 1171, 1327, 1511, 1723, 1951, 2221, 2531, 2887, 3299, 3769, 4297, 4909, 5591, 6389, 7297, 8329, 9511, 10867, 12413, 14177, 16193, 18503, 21143, 24151, 27583, 31517, 36017, 41161, 47041, 53759, 61417, 70183, 80209, 91639, 104729, 119689, 136777, 156307, 178627, 204143, 233297, 266603, 304687, 348209, 397951, 454799, 519769, 593993, 678833, 775807, 886619, 1013267, 1158011, 1323437, 1512493, 1728547, 1975481, 2257691, 2580203, 2948797, 3370051, 3851459, 4401667, 5030471, 5749091, 6570379, 7509001, 8581693, 9807649, 11208733, 12809969, 14639953, 16731371, 19121551, 21853147, 24974993, 28542821, 32620349, 37280381, 42606127, 48692671, 55648759, 63598573, 72684083, 83067521, 94934309, 108496319, 123995771, 141709367, 161953553, 185089757, 211531139, 241749847, 276285539, 315754877, 360862699, 412414511, 471330859, 538663837, 615615811, 703560919, 804069593, 918936673, 1050213331, 1200243787, 1371707137, 1567665287, 1791617449]

set_option maxRecDepth 1000000 in
theorem primeChain_7_prime : ∀ p ∈ primeChain_7, p.Prime := by
  simp only [primeChain_7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

theorem primeChain_7_chain : chainR 8 7 33 primeChain_7 = true := by decide

/-- For every natural number `x ≥ 33` there is a prime `p` with `x < p ≤ 8x/7`. -/
theorem nagura_7 (x : ℕ) (hx : 33 ≤ x) : ∃ p, p.Prime ∧ x < p ∧ 7 * p ≤ 8 * x := by
  rcases lt_or_ge x 1600000000 with h | h
  · exact chainR_cover 8 7 primeChain_7 33 primeChain_7_prime primeChain_7_chain x hx
      ⟨1791617449, by simp [primeChain_7], by omega⟩
  · exact nagura_7_large x h

end Nagura


/-! Small cases `n m < 25`, `m ≤ 5`, `m < n`: a prime in `[n m, n (m+1)]`, by `decide`. -/

namespace OMASmall

theorem small_cases_table : ∀ n ∈ Finset.range 25, ∀ m ∈ Finset.range 6,
    (0 < m ∧ m < n ∧ n * m < 25) → ∃ p ∈ Finset.Icc (n * m) (n * (m + 1)), p.Prime := by
  decide

theorem small_cases (n m : ℕ) (hn : n < 25) (hm : m < 6) (h0 : 0 < m) (hmn : m < n)
    (h25 : n * m < 25) : ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  obtain ⟨p, hp, hpr⟩ := small_cases_table n (Finset.mem_range.mpr hn) m
    (Finset.mem_range.mpr hm) ⟨h0, hmn, h25⟩
  rw [Finset.mem_Icc] at hp
  exact ⟨p, hpr, hp.1, hp.2⟩

end OMASmall

namespace OMASmall

/-- Small cases `n m < 32`, `m ≤ 6`, `m < n`. -/
theorem small_cases_table7 : ∀ n ∈ Finset.range 32, ∀ m ∈ Finset.range 7,
    (0 < m ∧ m < n ∧ n * m < 32) → ∃ p ∈ Finset.Icc (n * m) (n * (m + 1)), p.Prime := by
  decide

theorem small_cases7 (n m : ℕ) (hn : n < 32) (hm : m < 7) (h0 : 0 < m) (hmn : m < n)
    (h32 : n * m < 32) : ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  obtain ⟨p, hp, hpr⟩ := small_cases_table7 n (Finset.mem_range.mpr hn) m
    (Finset.mem_range.mpr hm) ⟨h0, hmn, h32⟩
  rw [Finset.mem_Icc] at hp
  exact ⟨p, hpr, hp.1, hp.2⟩

end OMASmall

namespace OMASmall

/-- Small cases `n m < 33`, `m ≤ 7`, `m < n`. -/
theorem small_cases_table8 : ∀ n ∈ Finset.range 33, ∀ m ∈ Finset.range 8,
    (0 < m ∧ m < n ∧ n * m < 33) → ∃ p ∈ Finset.Icc (n * m) (n * (m + 1)), p.Prime := by
  decide

theorem small_cases8 (n m : ℕ) (hn : n < 33) (hm : m < 8) (h0 : 0 < m) (hmn : m < n)
    (h33 : n * m < 33) : ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  obtain ⟨p, hp, hpr⟩ := small_cases_table8 n (Finset.mem_range.mpr hn) m
    (Finset.mem_range.mpr hm) ⟨h0, hmn, h33⟩
  rw [Finset.mem_Icc] at hp
  exact ⟨p, hpr, hp.1, hp.2⟩

end OMASmall


namespace OMAPartial

/-- The `m ≤ 7` cases: for `1 ≤ m ≤ 7` and `m < n` there is a prime in `[n m, n (m+1)]`. -/
theorem prime_in_window8 (n m : ℕ) (hm0 : 0 < m) (hm7 : m ≤ 7) (hmn : m < n) :
    ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  by_cases hbig : 33 ≤ n * m
  · obtain ⟨p, hp, h1, h2⟩ := Nagura.nagura_7 (n * m) hbig
    refine ⟨p, hp, h1.le, ?_⟩
    have : 8 * (n * m) ≤ 7 * (n * (m + 1)) := by nlinarith
    omega
  · have hn33 : n < 33 := by nlinarith
    exact OMASmall.small_cases8 n m hn33 (by omega) hm0 hmn (by omega)

end OMAPartial

theorem OMA.solution : OMA.R_OeisA110835_conjecture_R2.H1 :=
  fun n m h1 h7 hmn => OMAPartial.prime_in_window8 n m h1 h7 hmn
