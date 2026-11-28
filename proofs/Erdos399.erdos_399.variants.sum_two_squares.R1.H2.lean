import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1
import Mathlib

-- Step Erdos399.erdos_399.variants.sum_two_squares.R1.H2: hypothesis H2 of reduction Erdos399.erdos_399.variants.sum_two_squares.R1
-- Credit: Tzu-You (Aaron) Lin (@AkizumiFox)
-- H2 := for every n > 100 there is a prime q = 3 (mod 4) with n/2 < q <= n.
--
-- Proof sketch (Chebyshev-style, in the spirit of Breusch / Erdos):
--   R(N) := prod {k <= N, k = 3 mod 4} k / prod {k <= N/2, k odd} k.
--   Writing log k = sum_{d | k} Lambda(d), the quantity log R(n) - log R(n/5) equals
--   sum_d Lambda(d) * W(d), where W(d) <= 1 always, and W(d) <= 0 unless
--   11 d <= n, or (d = 3 mod 4 and n/2 < d <= n)  (lemma oma_weight).
--   Elementary bounds give log R(n) - log R(n/5) >= (n/5 - 1) log 2 - 2 log n, while
--   Mathlib's Chebyshev bounds give psi(n/11) <= log 4 * n/11 + ..., psi - theta <= 2 sqrt n log n.
--   So for n >= 2^28 some prime q = 3 mod 4 lies in (n/2, n] (lemma oma_key).
--   For 100 < n < 2^28 an explicit chain of 23 primes does it (lemma oma_chain).

open Finset ArithmeticFunction

lemma oma_cnt3 (Y : ℕ) : ((range (Y+1)).filter (fun t => t % 4 = 3)).card = (Y+1)/4 := by
  induction Y with
  | zero => decide
  | succ Y ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

lemma oma_cnt1 (Y : ℕ) : ((range (Y+1)).filter (fun t => t % 4 = 1)).card = (Y+3)/4 := by
  induction Y with
  | zero => decide
  | succ Y ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

lemma oma_cnto (Y : ℕ) : ((range (Y+1)).filter (fun t => t % 2 = 1)).card = (Y+1)/2 := by
  induction Y with
  | zero => decide
  | succ Y ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

lemma oma_cnt_mul (P : ℕ → Prop) [DecidablePred P] (N d : ℕ) (hd : 0 < d) :
    ((range (N+1)).filter (fun k => P k ∧ d ∣ k)).card
      = ((range (N/d+1)).filter (fun t => P (d*t))).card := by
  symm
  apply Finset.card_bij (fun t _ => d*t)
  · intro t ht
    simp only [mem_filter, mem_range] at ht ⊢
    have h1 : t ≤ N/d := by omega
    have h2 := (Nat.le_div_iff_mul_le hd).mp h1
    refine ⟨?_, ht.2, dvd_mul_right d t⟩
    rw [mul_comm]; omega
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    obtain ⟨hk1, hP, t, rfl⟩ := hk
    refine ⟨t, ?_, rfl⟩
    simp only [mem_filter, mem_range]
    have : t ≤ N/d := (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm]; omega)
    exact ⟨by omega, hP⟩

lemma oma_c3 (N d : ℕ) (hd : 0 < d) :
    ((range (N+1)).filter (fun k => k % 4 = 3 ∧ d ∣ k)).card
      = if d % 4 = 1 then (N/d+1)/4 else if d % 4 = 3 then (N/d+3)/4 else 0 := by
  rw [oma_cnt_mul (fun k => k % 4 = 3) N d hd]
  split_ifs with h1 h3
  · rw [← oma_cnt3]; congr 1; apply filter_congr; intro t _
    show (d * t) % 4 = 3 ↔ t % 4 = 3
    rw [Nat.mul_mod, h1]; omega
  · rw [← oma_cnt1]; congr 1; apply filter_congr; intro t _
    show (d * t) % 4 = 3 ↔ t % 4 = 1
    rw [Nat.mul_mod, h3]; omega
  · apply card_eq_zero.mpr; apply filter_eq_empty_iff.mpr; intro t _
    show ¬ (d * t) % 4 = 3
    rw [Nat.mul_mod]
    have : d % 4 = 0 ∨ d % 4 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> omega

lemma oma_co (N d : ℕ) (hd : 0 < d) :
    ((range (N+1)).filter (fun k => k % 2 = 1 ∧ d ∣ k)).card
      = if d % 2 = 1 then (N/d+1)/2 else 0 := by
  rw [oma_cnt_mul (fun k => k % 2 = 1) N d hd]
  split_ifs with h1
  · rw [← oma_cnto]; congr 1; apply filter_congr; intro t _
    show (d * t) % 2 = 1 ↔ t % 2 = 1
    rw [Nat.mul_mod, h1]; omega
  · apply card_eq_zero.mpr; apply filter_eq_empty_iff.mpr; intro t _
    show ¬ (d * t) % 2 = 1
    rw [Nat.mul_mod]
    have : d % 2 = 0 := by omega
    rw [this]; omega

lemma oma_weight (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    ((range (n+1)).filter (fun k => k % 4 = 3 ∧ d ∣ k)).card
      + ((range (n/10+1)).filter (fun k => k % 2 = 1 ∧ d ∣ k)).card
    ≤ ((range (n/2+1)).filter (fun k => k % 2 = 1 ∧ d ∣ k)).card
      + ((range (n/5+1)).filter (fun k => k % 4 = 3 ∧ d ∣ k)).card
      + (if 11 * d ≤ n then 1 else 0) + (if d % 4 = 3 ∧ n < 2 * d then 1 else 0) := by
  rw [oma_c3 n d hd, oma_c3 (n/5) d hd, oma_co (n/2) d hd, oma_co (n/10) d hd]
  have e2 : n / 2 / d = n / d / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  have e5 : n / 5 / d = n / d / 5 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  have e10 : n / 10 / d = n / d / 10 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  rw [e2, e5, e10]
  have hY : 1 ≤ n / d := (Nat.one_le_div_iff hd).mpr hdn
  have h11 : 11 * d ≤ n ↔ 11 ≤ n / d := by rw [Nat.le_div_iff_mul_le hd]
  have h2 : n < 2 * d ↔ n / d < 2 := (Nat.div_lt_iff_lt_mul hd).symm
  simp only [h11, h2]
  generalize n / d = Y at *
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 20 ∧ Y = 20 * q + r :=
    ⟨Y / 20, Y % 20, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod Y 20).symm⟩
  interval_cases r <;> split_ifs <;> omega

lemma oma_sum_log (N : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k ∧ k ≤ N) :
    ∑ k ∈ S, Real.log k = ∑ d ∈ Icc 1 N, Λ d * ((S.filter (fun k => d ∣ k)).card : ℝ) := by
  have h1 : ∀ k ∈ S, Real.log k = ∑ d ∈ Icc 1 N, if d ∣ k then Λ d else 0 := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := hS k hk
    rw [← vonMangoldt_sum, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hkN⟩, hd⟩
    · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

lemma oma_T3 (N : ℕ) : ∑ k ∈ (range (N+1)).filter (fun k => k % 4 = 3), Real.log k
    = ∑ i ∈ range ((N+1)/4), Real.log (4*i+3) := by
  induction N with
  | zero =>
    rw [show (range (0+1)).filter (fun k => k % 4 = 3) = ∅ by decide]; simp
  | succ N ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp), ih]
      have e : (N+1+1)/4 = (N+1)/4 + 1 := by omega
      rw [e, sum_range_succ, add_comm]
      congr 2
      have e2 : N + 1 = 4 * ((N+1)/4) + 3 := by omega
      exact_mod_cast e2
    · rw [ih]; have e : (N+1+1)/4 = (N+1)/4 := by omega
      rw [e]

lemma oma_Ao (N : ℕ) : ∑ k ∈ (range (N+1)).filter (fun k => k % 2 = 1), Real.log k
    = ∑ i ∈ range ((N+1)/2), Real.log (2*i+1) := by
  induction N with
  | zero =>
    rw [show (range (0+1)).filter (fun k => k % 2 = 1) = ∅ by decide]; simp
  | succ N ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp), ih]
      have e : (N+1+1)/2 = (N+1)/2 + 1 := by omega
      rw [e, sum_range_succ, add_comm]
      congr 2
      have e2 : N + 1 = 2 * ((N+1)/2) + 1 := by omega
      exact_mod_cast e2
    · rw [ih]; have e : (N+1+1)/2 = (N+1)/2 := by omega
      rw [e]

lemma oma_lowerR (M H : ℕ) (hH : H ≤ M + 1) :
    (M:ℝ) * Real.log 2 - Real.log (2*M+1) ≤
      ∑ i ∈ range M, Real.log (4*i+3) - ∑ i ∈ range H, Real.log (2*i+1) := by
  have h1 : ∑ i ∈ range H, Real.log (2*(i:ℝ)+1) ≤ ∑ i ∈ range (M+1), Real.log (2*(i:ℝ)+1) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [mem_range] at hi ⊢; omega
    · intro i _ _; apply Real.log_nonneg
      have : (0:ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  rw [sum_range_succ] at h1
  have h2 : (M:ℝ) * Real.log 2 ≤ ∑ i ∈ range M, (Real.log (4*i+3) - Real.log (2*i+1)) := by
    have h3 : ∀ i ∈ range M, Real.log 2 ≤ Real.log (4*(i:ℝ)+3) - Real.log (2*i+1) := by
      intro i _
      have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
      rw [le_sub_iff_add_le, ← Real.log_mul (by norm_num) (by linarith)]
      apply Real.log_le_log (by linarith) (by linarith)
    calc (M:ℝ) * Real.log 2 = ∑ i ∈ range M, Real.log 2 := by simp
      _ ≤ _ := sum_le_sum h3
  rw [sum_sub_distrib] at h2
  linarith

lemma oma_upperR (M H : ℕ) (hH : M ≤ H) :
    ∑ i ∈ range M, Real.log (4*i+3) - ∑ i ∈ range H, Real.log (2*i+1) ≤
      (M:ℝ) * Real.log 2 + Real.log (M+1) := by
  have h1 : ∑ i ∈ range M, Real.log (2*(i:ℝ)+1) ≤ ∑ i ∈ range H, Real.log (2*(i:ℝ)+1) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [mem_range] at hi ⊢; omega
    · intro i _ _; apply Real.log_nonneg
      have : (0:ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  have h2 : ∀ m : ℕ, ∑ i ∈ range m, (Real.log (4*i+3) - Real.log (2*i+1))
      ≤ (m:ℝ) * Real.log 2 + Real.log (m+1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
      have h3 : Real.log (4*(m:ℝ)+3) + Real.log ((m:ℝ)+1)
          ≤ Real.log 2 + Real.log ((m:ℝ)+1+1) + Real.log (2*(m:ℝ)+1) := by
        rw [← Real.log_mul (by linarith) (by linarith), ← Real.log_mul (by norm_num) (by linarith),
          ← Real.log_mul (by nlinarith) (by linarith)]
        apply Real.log_le_log (by nlinarith) (by nlinarith)
      push_cast
      linarith
  have h4 := h2 M
  rw [sum_sub_distrib] at h4
  linarith

lemma oma_key (n : ℕ) (hn : 268435456 ≤ n)
    (hno : ∀ q : ℕ, q.Prime → q % 4 = 3 → n < 2 * q → q ≤ n → False) : False := by
  have hS3 : ∀ N, N ≤ n → ∀ k ∈ (range (N+1)).filter (fun k => k % 4 = 3), 1 ≤ k ∧ k ≤ n := by
    intro N hN k hk; simp only [mem_filter, mem_range] at hk; omega
  have hSo : ∀ N, N ≤ n → ∀ k ∈ (range (N+1)).filter (fun k => k % 2 = 1), 1 ≤ k ∧ k ≤ n := by
    intro N hN k hk; simp only [mem_filter, mem_range] at hk; omega
  have i1 := oma_sum_log n _ (hS3 n le_rfl)
  have i2 := oma_sum_log n _ (hSo (n/2) (Nat.div_le_self _ _))
  have i3 := oma_sum_log n _ (hS3 (n/5) (Nat.div_le_self _ _))
  have i4 := oma_sum_log n _ (hSo (n/10) (Nat.div_le_self _ _))
  simp only [filter_filter] at i1 i2 i3 i4
  have hup : ∑ k ∈ (range (n+1)).filter (fun k => k % 4 = 3), Real.log k
      - ∑ k ∈ (range (n/2+1)).filter (fun k => k % 2 = 1), Real.log k
      - ∑ k ∈ (range (n/5+1)).filter (fun k => k % 4 = 3), Real.log k
      + ∑ k ∈ (range (n/10+1)).filter (fun k => k % 2 = 1), Real.log k
      ≤ ∑ d ∈ Icc 1 n, (if 11 * d ≤ n then Λ d else 0)
        + ∑ d ∈ Icc 1 n, (if d % 4 = 3 ∧ n < 2 * d then Λ d else 0) := by
    rw [i1, i2, i3, i4]
    simp only [← sum_sub_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    rw [mem_Icc] at hd
    have hw := (Nat.cast_le (α := ℝ)).mpr (oma_weight n d hd.1 hd.2)
    push_cast at hw
    have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
    have hw2 := mul_le_mul_of_nonneg_left hw hΛ
    split_ifs at hw2 ⊢ <;> linarith
  have hS1 : ∑ d ∈ Icc 1 n, (if 11 * d ≤ n then Λ d else 0)
      ≤ Chebyshev.psi ((n/11 : ℕ) : ℝ) := by
    rw [← sum_filter, Chebyshev.psi, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd; simp only [mem_filter, mem_Icc, mem_Ioc] at hd ⊢; omega
    · intro _ _ _; exact vonMangoldt_nonneg
  have hS2 : ∑ d ∈ Icc 1 n, (if d % 4 = 3 ∧ n < 2 * d then Λ d else 0)
      ≤ Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
    rw [← sum_filter, Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd; simp only [mem_filter, mem_Icc, mem_Ioc] at hd ⊢
      exact ⟨⟨by omega, hd.1.2⟩, fun hp => hno d hp hd.2.1 hd.2.2 hd.1.2⟩
    · intro _ _ _; exact vonMangoldt_nonneg
  have hm1 : (1:ℝ) ≤ ((n/11 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n/11)
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hψ1 := Chebyshev.psi_le hm1
  have hψ2 := Chebyshev.psi_sub_theta_le hn1
  rw [oma_T3, oma_Ao, oma_T3, oma_Ao] at hup
  have hlo := oma_lowerR ((n+1)/4) ((n/2+1)/2) (by omega)
  have hup2 := oma_upperR ((n/5+1)/4) ((n/10+1)/2) (by omega)
  have hM : (n:ℝ) ≤ 4 * (((n+1)/4 : ℕ) : ℝ) + 2 := by
    exact_mod_cast (by omega : n ≤ 4*((n+1)/4)+2)
  have hM' : 20 * (((n/5+1)/4 : ℕ) : ℝ) ≤ (n:ℝ) + 5 := by
    exact_mod_cast (by omega : 20*((n/5+1)/4) ≤ n+5)
  have hm : 11 * ((n/11 : ℕ) : ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (by omega : 11*(n/11) ≤ n)
  have hmx : ((n/11 : ℕ) : ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (by omega : n/11 ≤ n)
  have h2M : 2 * (((n+1)/4 : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by
    exact_mod_cast (by omega : 2*((n+1)/4)+1 ≤ n)
  have hM'1 : (((n/5+1)/4 : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by
    exact_mod_cast (by omega : (n/5+1)/4+1 ≤ n)
  have hx0 : (268435456:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hl1 : Real.log (2 * (((n+1)/4 : ℕ) : ℝ) + 1) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by positivity) h2M
  have hl2 : Real.log ((((n/5+1)/4 : ℕ) : ℝ) + 1) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by positivity) hM'1
  have hl3 : Real.log ((n/11 : ℕ) : ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by linarith) hmx
  have hl3' : 0 ≤ Real.log ((n/11 : ℕ) : ℝ) := Real.log_nonneg hm1
  have hs3 : √((n/11 : ℕ) : ℝ) ≤ √(n:ℝ) := Real.sqrt_le_sqrt hmx
  have hsm : 2 * √((n/11 : ℕ) : ℝ) * Real.log ((n/11 : ℕ) : ℝ)
      ≤ 2 * √(n:ℝ) * Real.log (n:ℝ) := by
    have := mul_le_mul hs3 hl3 hl3' (Real.sqrt_nonneg (n:ℝ))
    linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = √(n:ℝ) := ⟨_, rfl⟩
  rw [← hsdef] at hsm hψ2
  have hs : (16384:ℝ) ≤ s := by
    rw [hsdef]; apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have hss : s * s = (n:ℝ) := by rw [hsdef]; exact Real.mul_self_sqrt (by linarith)
  have hL : Real.log (n:ℝ) = 2 * Real.log s := by
    rw [← hss, Real.log_mul (by linarith) (by linarith)]; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have e14 : Real.log 16384 = 14 * Real.log 2 := by
    rw [show (16384:ℝ) = 2^14 by norm_num, Real.log_pow]; norm_num
  have hU : Real.log s ≤ s/16384 - 1 + 14 * Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0:ℝ) < s) (by norm_num : (0:ℝ) < 16384))
    rw [Real.log_div (by linarith) (by norm_num), e14] at h
    linarith
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hLs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have a1 : s * Real.log s ≤ s * (s/16384 - 1 + 14 * Real.log 2) :=
    mul_le_mul_of_nonneg_left hU (by linarith)
  have a2 : ((n:ℝ) - 2)/4 * Real.log 2 ≤ (((n+1)/4 : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have a3 : (((n/5+1)/4 : ℕ) : ℝ) * Real.log 2 ≤ ((n:ℝ)+5)/20 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have a4 : Real.log 2 * ((n/11 : ℕ) : ℝ) ≤ Real.log 2 * ((n:ℝ)/11) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a5 : (n:ℝ) * 0.6931 ≤ (n:ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a6 : s * Real.log 2 ≤ s * 0.6932 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a7 : 16384 * s ≤ (n:ℝ) := by
    rw [← hss]; exact mul_le_mul_of_nonneg_right hs (by linarith)
  have b1 : 2 * s * Real.log (n:ℝ) = 4 * (s * Real.log s) := by rw [hL]; ring
  rw [h4] at hψ1
  have a1' : s * Real.log s ≤ (n:ℝ)/16384 - s + 14 * (s * Real.log 2) := by
    have e : s * (s/16384 - 1 + 14 * Real.log 2) = (s*s)/16384 - s + 14 * (s * Real.log 2) := by
      ring
    rw [e, hss] at a1
    exact a1
  linarith

lemma K {n : ℕ} (q : ℕ) (hq : q.Prime := by norm_num) (h4 : q % 4 = 3 := by norm_num)
    (h2 : n < 2 * q := by omega) (hle : q ≤ n := by omega) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := ⟨q, hq, h4, h2, hle⟩

lemma oma_chain (n : ℕ) (h100 : 100 < n) (hn : n < 268435456) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
  by_cases h : n < 134
  · exact K 67
  by_cases h : n < 262
  · exact K 131
  by_cases h : n < 502
  · exact K 251
  by_cases h : n < 998
  · exact K 499
  by_cases h : n < 1982
  · exact K 991
  by_cases h : n < 3958
  · exact K 1979
  by_cases h : n < 7894
  · exact K 3947
  by_cases h : n < 15766
  · exact K 7883
  by_cases h : n < 31478
  · exact K 15739
  by_cases h : n < 62782
  · exact K 31391
  by_cases h : n < 125486
  · exact K 62743
  by_cases h : n < 250942
  · exact K 125471
  by_cases h : n < 501838
  · exact K 250919
  by_cases h : n < 1003654
  · exact K 501827
  by_cases h : n < 2007262
  · exact K 1003631
  by_cases h : n < 4014518
  · exact K 2007259
  by_cases h : n < 8029006
  · exact K 4014503
  by_cases h : n < 16057966
  · exact K 8028983
  by_cases h : n < 32115838
  · exact K 16057919
  by_cases h : n < 64231598
  · exact K 32115799
  by_cases h : n < 128463094
  · exact K 64231547
  by_cases h : n < 256926182
  · exact K 128463091
  exact K 256926143

theorem oma_main : ∀ n : ℕ, 100 < n →
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
  intro n h100
  rcases lt_or_ge n 268435456 with h | h
  · exact oma_chain n h100 h
  · by_contra hc
    exact oma_key n h (fun q hq h4 h2 hle => hc ⟨q, hq, h4, h2, hle⟩)

theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H2 := oma_main
