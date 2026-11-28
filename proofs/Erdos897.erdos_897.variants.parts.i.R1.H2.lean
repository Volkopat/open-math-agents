import OMAReductions.R_Erdos897_erdos_897_variants_parts_i_R1

/-! A square identity controls the drop of the first difference. Summing two
consecutive differences on a dyadic interval then bounds its negative part. -/

namespace OMA.Erdos897Differences

open Real

/-- Write the function as the sum of its prime weights, counted with multiplicity. -/
private theorem complete_of_prime_powers (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a*b) = f a + f b)
    (hpow : ∀ k p : ℕ, p.Prime → f (p^k) = k * f p) :
    ∀ a b : ℕ, 0 < a → 0 < b → f (a*b) = f a + f b := by
  let g (a : ℕ) : ℝ := a.factorization.sum fun p k => (k : ℝ) * f p
  have gm (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : g (a*b) = g a + g b := by
    unfold g
    rw [Nat.factorization_mul ha.ne' hb.ne', Finsupp.sum_add_index']
    · simp
    · intros
      push_cast
      ring
  have fg (a : ℕ) : 0 < a → f a = g a := by
    induction a using Nat.recOnPrimeCoprime with
    | zero => omega
    | prime_pow p k hp =>
      intro _
      rw [hpow k p hp]
      simp [g, hp.factorization_pow, Finsupp.sum_single_index]
    | coprime a b ha hb hab ia ib =>
      intro _
      rw [hadd a b (by omega) (by omega) hab, gm a b (by omega) (by omega),
        ia (by omega), ib (by omega)]
  intro a b ha hb
  rw [fg (a*b) (Nat.mul_pos ha hb), gm a b ha hb, fg a ha, fg b hb]

/-- The difference at (i+1)²-1 bounds how far two consecutive differences can fall. -/
private theorem square_step (f : ℕ → ℝ)
    (hm : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b) = f a + f b)
    (C : ℝ) (hC : 0 ≤ C)
    (upper : ∀ n : ℕ, 2 ≤ n → f (n+1) - f n ≤ C * log n)
    (i : ℕ) (hi : 1 ≤ i) :
    f (i+1) - f i ≤ (f (i+2) - f (i+1)) + 2 * C * log (i+1 : ℕ) := by
  have he : i*(i+2)+1 = (i+1)*(i+1) := by ring
  have u := upper (i*(i+2)) (by nlinarith)
  rw [he, hm _ _ (by omega) (by omega), hm _ _ (by omega) (by omega)] at u
  have leSq : (i*(i+2) : ℕ) ≤ (i+1)^2 := by nlinarith
  have L := Real.log_le_log (show 0 < ((i*(i+2) : ℕ) : ℝ) by positivity)
    (show ((i*(i+2) : ℕ) : ℝ) ≤ (((i+1 : ℕ) : ℝ)^2) by exact_mod_cast leSq)
  rw [Real.log_pow] at L
  have h := mul_le_mul_of_nonneg_left L hC
  norm_num at h
  push_cast at u ⊢
  linarith only [u, h]

private theorem lower_of_upper (f : ℕ → ℝ)
    (hm : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b) = f a + f b)
    (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n : ℕ, 2 ≤ n → f (n+1) - f n ≤ C * log n) :
    ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n → -(K * log n) ≤ f (n+1) - f n := by
  let d (n : ℕ) := f (n+1) - f n
  let T := |d 1| + |d 2|
  have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have monotoneLog {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
      log a ≤ log b := Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  have step (i n : ℕ) (hi : 1 ≤ i) (hin : i+1 ≤ n) :
      d i ≤ d (i+1) + 2*C*log n := by
    have h := square_step f hm C hC hu i hi
    have hlog := mul_le_mul_of_nonneg_left (monotoneLog (by omega) hin)
      (show 0 ≤ 2*C by positivity)
    dsimp [d]
    linarith
  have pair (m : ℕ) (hmpos : 0 < m) : d (2*m) + d (2*m+1) = d m := by
    dsimp [d]
    rw [show 2*m+1+1 = 2*(m+1) by omega,
      hm 2 (m+1) (by decide) (by omega), hm 2 m (by decide) hmpos]
    ring
  have lower (n : ℕ) : 1 ≤ n → -(T + 6*C*log n) ≤ d n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hlog : 0 ≤ 6*C*log n :=
        mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))
      by_cases hs : n ≤ 2
      · interval_cases n <;> dsimp [T] at * <;>
          linarith [neg_abs_le (d 1), neg_abs_le (d 2), abs_nonneg (d 1), abs_nonneg (d 2)]
      let m := (n-1)/2
      have hmpos : 0 < m := by dsimp [m]; omega
      have hmn : m < n := by dsimp [m]; omega
      have lowerM := ih m hmn hmpos
      have hlogM := mul_le_mul_of_nonneg_left (monotoneLog hmpos hmn.le)
        (show 0 ≤ 6*C by positivity)
      have hp := pair m hmpos
      have hs₁ := step (2*m) n (by omega) (by dsimp [m]; omega)
      rcases (show n = 2*m+1 ∨ n = 2*m+2 by dsimp [m]; omega) with he | he
      · rw [← he] at hs₁ hp
        linarith
      · have hs₂ := step (2*m+1) n (by omega) (by omega)
        rw [show 2*m+1+1 = n by omega] at hs₂
        linarith
  refine ⟨6*C + T/log 2, ?_⟩
  intro n hn
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hl : log 2 ≤ log n := monotoneLog (by decide : 0 < (2:ℕ)) hn
  have h := mul_le_mul_of_nonneg_left hl (div_nonneg hT h2.le)
  have hcancel : T / log 2 * log 2 = T := div_mul_cancel₀ T h2.ne'
  rw [hcancel] at h
  have z := lower n (by omega)
  change _ ≤ d n
  linarith

end OMA.Erdos897Differences

theorem OMA.solution : OMA.R_Erdos897_erdos_897_variants_parts_i_R1.H2 := by
  intro f ha hp h
  obtain ⟨C, hC⟩ := h
  apply OMA.Erdos897Differences.lower_of_upper f
    (OMA.Erdos897Differences.complete_of_prime_powers f ha hp) (max 0 C) (le_max_left _ _)
  intro n hn
  exact (hC n hn).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
