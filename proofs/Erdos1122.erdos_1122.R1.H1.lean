import OMAReductions.R_Erdos1122_erdos_1122_R1

/-!
# Proof of `Erdos1122.erdos_1122.R1.H1`

Proves Erdős's 1946 theorem: every nondecreasing additive function `f : ℕ → ℝ` (satisfying
`f (a * b) = f a + f b` for coprime `a, b > 0` and `f n ≤ f (n + 1)` for `n ≥ 1`) has the form
`f n = c * Real.log n` for all `n > 0`.

Proof outline:
1. `f 1 = 0` from `f (1 * 1) = f 1 + f 1`, and monotonicity extends to `1 ≤ m ≤ n → f m ≤ f n`.
2. For any `k ≥ 2`, `seqA k 0 = 1, seqA k (r + 1) = k * seqA k r + 1` satisfies
   `k.Coprime (seqA k r)`, `seqA k r ≤ k ^ (r + 1)`, and `r * f k ≤ f (seqA k r) ≤ f (k ^ (r + 1))`.
3. `seqB k 0 = 2, seqB k (r + 1) = k * seqB k r - 1` satisfies `k.Coprime (seqB k r)` for `r ≥ 1`,
   `k ^ r ≤ seqB k r`, and `f (k ^ r) ≤ f (seqB k r) ≤ (r - 1) * f k + f (2 * k - 1)`.
4. For any `n ≥ 2` and any `r ≥ 2`, taking `s = Nat.log 2 (n ^ r)` gives `2 ^ s ≤ n ^ r < 2 ^ (s + 1)`.
   Combining the two-sided power bounds yields `r * |f n - c * Real.log n| ≤ C` (independent of `r`),
   forcing `f n = c * Real.log n` with `c = f 2 / Real.log 2`.
-/

namespace Erdos1122R1H1Proof

private lemma mono_of_step {f : ℕ → ℝ} (hstep : ∀ n ≥ 1, f n ≤ f (n + 1)) :
    ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n := by
  intro m n hm hmn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction d with
  | zero => simp
  | succ d ih =>
    calc f m ≤ f (m + d) := ih (by omega)
      _ ≤ f (m + d + 1) := hstep (m + d) (by omega)

private def seqA (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => k * seqA k r + 1

private lemma seqA_pos (k : ℕ) : ∀ r : ℕ, 0 < seqA k r
  | 0 => by simp [seqA]
  | r + 1 => by simp [seqA]

private lemma seqA_coprime (k : ℕ) : ∀ r : ℕ, k.Coprime (seqA k r)
  | 0 => Nat.coprime_one_right k
  | r + 1 => by
    unfold seqA
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : k.gcd (k * seqA k r + 1) ∣ k := Nat.gcd_dvd_left _ _
    have hd2 : k.gcd (k * seqA k r + 1) ∣ k * seqA k r + 1 := Nat.gcd_dvd_right _ _
    have hd3 : k.gcd (k * seqA k r + 1) ∣ k * seqA k r := dvd_mul_of_dvd_left hd1 _
    have hd4 : k.gcd (k * seqA k r + 1) ∣ (k * seqA k r + 1) - k * seqA k r := Nat.dvd_sub hd2 hd3
    rw [show k * seqA k r + 1 - k * seqA k r = 1 by omega] at hd4
    exact Nat.dvd_one.mp hd4

private lemma seqA_le {k : ℕ} (hk : 2 ≤ k) : ∀ r : ℕ, seqA k r + 1 ≤ 2 * k ^ r
  | 0 => by simp [seqA]
  | r + 1 => by
    unfold seqA
    have ih := seqA_le hk r
    rw [pow_succ']
    nlinarith

private lemma seqA_le_pow_succ {k : ℕ} (hk : 2 ≤ k) (r : ℕ) : seqA k r ≤ k ^ (r + 1) := by
  have h1 := seqA_le hk r
  have h2 : 2 * k ^ r ≤ k * k ^ r := Nat.mul_le_mul_right (k ^ r) hk
  rw [pow_succ']
  omega

private lemma mul_le_f_seqA {f : ℕ → ℝ}
    (hadd : ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ r : ℕ, (r : ℝ) * f k ≤ f (seqA k r) := by
  have hf1 : f 1 = 0 := by
    have h := hadd 1 (by decide) 1 (by decide) (Nat.coprime_one_left 1)
    simp only [mul_one] at h
    linarith
  intro r
  induction r with
  | zero =>
    simp [seqA, hf1]
  | succ r ih =>
    unfold seqA
    have hstep : f (k * seqA k r) ≤ f (k * seqA k r + 1) :=
      hmono (Nat.mul_pos (by omega) (seqA_pos k r)) (Nat.le_succ _)
    have hmul : f (k * seqA k r) = f k + f (seqA k r) :=
      hadd k (by omega) (seqA k r) (seqA_pos k r) (seqA_coprime k r)
    push_cast
    linarith

private lemma lower_pow_bound {f : ℕ → ℝ}
    (hadd : ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n)
    {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    ((r - 1 : ℕ) : ℝ) * f k ≤ f (k ^ r) := by
  have h1 := mul_le_f_seqA hadd hmono hk (r - 1)
  have h2 : f (seqA k (r - 1)) ≤ f (k ^ r) := by
    have hle := seqA_le_pow_succ hk (r - 1)
    rw [Nat.sub_add_cancel hr] at hle
    exact hmono (seqA_pos k (r - 1)) hle
  linarith

private def seqB (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | r + 1 => k * seqB k r - 1

private lemma seqB_ge {k : ℕ} (hk : 2 ≤ k) : ∀ r : ℕ, k ^ r + 1 ≤ seqB k r
  | 0 => by simp [seqB]
  | r + 1 => by
    unfold seqB
    have ih := seqB_ge hk r
    rw [pow_succ']
    have hkr : 1 ≤ k ^ r := Nat.one_le_pow _ _ (by omega)
    have hmul : k * k ^ r + k ≤ k * seqB k r := by
      have := Nat.mul_le_mul_left k ih
      linarith
    omega

private lemma seqB_coprime {k : ℕ} (hk : 2 ≤ k) : ∀ r : ℕ, 1 ≤ r → k.Coprime (seqB k r)
  | 0, h => by omega
  | r + 1, _ => by
    unfold seqB
    have hpos : 1 ≤ k * seqB k r := by
      have h1 := seqB_ge hk r
      have h2 : 1 ≤ k ^ r := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have heq : (k * seqB k r - 1) + 1 = k * seqB k r := Nat.sub_add_cancel hpos
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : k.gcd (k * seqB k r - 1) ∣ k := Nat.gcd_dvd_left _ _
    have hd2 : k.gcd (k * seqB k r - 1) ∣ k * seqB k r - 1 := Nat.gcd_dvd_right _ _
    have hd3 : k.gcd (k * seqB k r - 1) ∣ k * seqB k r := dvd_mul_of_dvd_left hd1 _
    have hd4 : k.gcd (k * seqB k r - 1) ∣ (k * seqB k r) - (k * seqB k r - 1) := Nat.dvd_sub hd3 hd2
    rw [show k * seqB k r - (k * seqB k r - 1) = 1 by omega] at hd4
    exact Nat.dvd_one.mp hd4

private lemma f_seqB_le {f : ℕ → ℝ}
    (hadd : ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ r : ℕ, 1 ≤ r → f (seqB k r) ≤ ((r - 1 : ℕ) : ℝ) * f k + f (2 * k - 1) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    simp [seqB, mul_comm]
  | succ m hm ih =>
    unfold seqB
    have hm_pos : 0 < seqB k m := by have := seqB_ge hk m; omega
    have hmul_pos : 1 ≤ k * seqB k m - 1 := by
      have h1 := seqB_ge hk m
      have h2 : 1 ≤ k ^ m := Nat.one_le_pow _ _ (by omega)
      have h3 : 2 ≤ k * seqB k m := by nlinarith
      omega
    have hle : f (k * seqB k m - 1) ≤ f (k * seqB k m) :=
      hmono hmul_pos (Nat.sub_le _ 1)
    have hcop : k.Coprime (seqB k m) := seqB_coprime hk m hm
    have heq : f (k * seqB k m) = f k + f (seqB k m) :=
      hadd k (by omega) (seqB k m) hm_pos hcop
    have hcast : ((m + 1 - 1 : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show m + 1 - 1 = (m - 1) + 1 by omega)
    rw [hcast]
    linarith

private lemma upper_pow_bound {f : ℕ → ℝ}
    (hadd : ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n)
    {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    f (k ^ r) ≤ ((r - 1 : ℕ) : ℝ) * f k + f (2 * k - 1) := by
  have h1 := f_seqB_le hadd hmono hk r hr
  have h2 : f (k ^ r) ≤ f (seqB k r) :=
    hmono (Nat.one_le_pow r k (by omega)) (by have := seqB_ge hk r; omega)
  linarith

end Erdos1122R1H1Proof

theorem OMA.solution : OMA.R_Erdos1122_erdos_1122_R1.H1 := by
  intro f hadd hstep
  have hmono : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → f m ≤ f n :=
    Erdos1122R1H1Proof.mono_of_step hstep
  have hf1 : f 1 = 0 := by
    have h := hadd 1 (by decide) 1 (by decide) (Nat.coprime_one_left 1)
    simp only [mul_one] at h
    linarith
  have hf2_nn : 0 ≤ f 2 := by
    have := hmono (by decide : 1 ≤ 1) (by decide : 1 ≤ 2)
    linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨f 2 / Real.log 2, fun n hn => ?_⟩
  by_cases hn1 : n = 1
  · subst hn1; simp [hf1]
  have hn2 : 2 ≤ n := by omega
  set c : ℝ := f 2 / Real.log 2
  have hc_nn : 0 ≤ c := div_nonneg hf2_nn hlog2_pos.le
  -- Bound |f n - c * Real.log n| ≤ C / r for every r ≥ 2
  have hbound : ∀ r : ℕ, 2 ≤ r →
      |f n - c * Real.log (n : ℝ)| * (r : ℝ) ≤
        (|f n| + 2 * f 2 + |f 3| + |f (2 * n - 1)|) := by
    intro r hr
    set s := Nat.log 2 (n ^ r)
    have hnr_pos : 0 < n ^ r := pow_pos (by omega) r
    have h2s_le : 2 ^ s ≤ n ^ r := Nat.pow_log_le_self 2 hnr_pos.ne'
    have hnr_lt : n ^ r < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n ^ r)
    have hs1 : 1 ≤ s := by
      have h2le : 2 ^ 1 ≤ n ^ r := by
        calc 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ n ^ r := Nat.pow_le_pow_left hn2 r
      exact Nat.le_log_of_pow_le (by decide : 1 < 2) h2le
    -- Log inequalities: s * log 2 ≤ r * log n < (s + 1) * log 2
    have hlog_le : (s : ℝ) * Real.log 2 ≤ (r : ℝ) * Real.log (n : ℝ) := by
      have h1 : ((2 ^ s : ℕ) : ℝ) ≤ ((n ^ r : ℕ) : ℝ) := by exact_mod_cast h2s_le
      have h2 := Real.log_le_log (by positivity) h1
      simpa [Nat.cast_pow, Real.log_pow] using h2
    have hlog_lt : (r : ℝ) * Real.log (n : ℝ) < ((s + 1 : ℕ) : ℝ) * Real.log 2 := by
      have h1 : ((n ^ r : ℕ) : ℝ) < ((2 ^ (s + 1) : ℕ) : ℝ) := by exact_mod_cast hnr_lt
      have h2 := Real.log_lt_log (by positivity) h1
      simpa [Nat.cast_pow, Real.log_pow] using h2
    -- Upper bound on f n - c * log n
    have hfn_le : ((r - 1 : ℕ) : ℝ) * f n ≤ (s : ℝ) * f 2 + f 3 := by
      have h1 := Erdos1122R1H1Proof.lower_pow_bound hadd hmono hn2 (by omega : 1 ≤ r)
      have h2 : f (n ^ r) ≤ f (2 ^ (s + 1)) := hmono hnr_pos hnr_lt.le
      have h3 := Erdos1122R1H1Proof.upper_pow_bound hadd hmono (by decide : 2 ≤ 2) (by omega : 1 ≤ s + 1)
      have h4 : (s + 1 - 1 : ℕ) = s := by omega
      have h5 : 2 * 2 - 1 = 3 := by decide
      rw [h4, h5] at h3
      linarith
    have hfn_ge : ((s - 1 : ℕ) : ℝ) * f 2 ≤ ((r - 1 : ℕ) : ℝ) * f n + f (2 * n - 1) := by
      have h1 := Erdos1122R1H1Proof.lower_pow_bound hadd hmono (by decide : 2 ≤ 2) hs1
      have h2 : f (2 ^ s) ≤ f (n ^ r) := hmono (Nat.one_le_pow s 2 (by decide)) h2s_le
      have h3 := Erdos1122R1H1Proof.upper_pow_bound hadd hmono hn2 (by omega : 1 ≤ r)
      linarith
    have hsf2_le : (s : ℝ) * f 2 ≤ c * ((r : ℝ) * Real.log (n : ℝ)) := by
      have h1 : (s : ℝ) ≤ (r : ℝ) * Real.log (n : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2_pos).mpr hlog_le
      have h2 := mul_le_mul_of_nonneg_right h1 hf2_nn
      have heq : (r : ℝ) * Real.log (n : ℝ) / Real.log 2 * f 2 =
          c * ((r : ℝ) * Real.log (n : ℝ)) := by dsimp [c]; ring
      linarith
    have hsf2_ge : c * ((r : ℝ) * Real.log (n : ℝ)) - 2 * f 2 ≤ ((s - 1 : ℕ) : ℝ) * f 2 := by
      have h1 : (r : ℝ) * Real.log (n : ℝ) / Real.log 2 ≤ ((s + 1 : ℕ) : ℝ) :=
        (div_le_iff₀ hlog2_pos).mpr hlog_lt.le
      have hs_eq : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
        rw [Nat.cast_sub hs1, Nat.cast_one]
      have h2 : (r : ℝ) * Real.log (n : ℝ) / Real.log 2 - 2 ≤ ((s - 1 : ℕ) : ℝ) := by
        push_cast at h1
        linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hf2_nn
      have heq : ((r : ℝ) * Real.log (n : ℝ) / Real.log 2 - 2) * f 2 =
          c * ((r : ℝ) * Real.log (n : ℝ)) - 2 * f 2 := by dsimp [c]; ring
      linarith
    have hr_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    rw [hr_cast] at hfn_le hfn_ge
    have h_abs_fn : f n ≤ |f n| ∧ -f n ≤ |f n| := ⟨le_abs_self _, neg_le_abs _⟩
    have h_abs_f3 : f 3 ≤ |f 3| := le_abs_self _
    have h_abs_f2n : f (2 * n - 1) ≤ |f (2 * n - 1)| := le_abs_self _
    have h_nn1 : 0 ≤ |f 3| := abs_nonneg _
    have h_nn2 : 0 ≤ |f (2 * n - 1)| := abs_nonneg _
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    rw [← abs_of_nonneg hr_nn, ← abs_mul, abs_le]
    constructor
    · nlinarith
    · nlinarith
  by_contra hne
  have hpos : 0 < |f n - c * Real.log (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C := |f n| + 2 * f 2 + |f 3| + |f (2 * n - 1)|
  obtain ⟨r0, hr0⟩ := exists_nat_gt (C / |f n - c * Real.log (n : ℝ)|)
  set r := max r0 2
  have hr2 : 2 ≤ r := le_max_right r0 2
  have hrb : C / |f n - c * Real.log (n : ℝ)| < (r : ℝ) :=
    lt_of_lt_of_le hr0 (Nat.cast_le.mpr (le_max_left r0 2))
  have hgt : C < |f n - c * Real.log (n : ℝ)| * (r : ℝ) := by
    have := (div_lt_iff₀ hpos).mp hrb
    linarith
  have hle := hbound r hr2
  linarith
