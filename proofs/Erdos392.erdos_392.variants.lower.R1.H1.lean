import OMAReductions.R_Erdos392_erdos_392_variants_lower_R1

open Real
-- Step Erdos392.erdos_392.variants.lower.R1.H1: hypothesis H1 of reduction Erdos392.erdos_392.variants.lower.R1
-- Credit: @senamakel
-- H1 := ∀ n : ℕ, 2 ≤ n → ∀ (t : ℕ) (a : Fin (t + 1) → ℕ), (n)! = ∏ i, a i → (∀ i, a i ≤ n) →     (n : ℝ) - n / log n ≤ t + 1  -- Upper half: for all large n there is a monotone factorisation of n! into factors at most n -- with at most n - n / log n + ε n / log n factors.


open scoped Nat

theorem OMA.solution : OMA.R_Erdos392_erdos_392_variants_lower_R1.H1 := by
  intro n hn t a hprod hb
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < log n := log_pos hn1
  have hapos : ∀ i, 0 < a i := fun i => by
    rcases Nat.eq_zero_or_pos (a i) with h | h
    · exfalso
      have : (n)! = 0 := by rw [hprod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h
      exact Nat.factorial_ne_zero n this
    · exact h
  -- log n! ≤ (t+1) log n
  have hup : log ((n)! : ℝ) ≤ (t + 1) * log n := by
    rw [hprod, Nat.cast_prod, log_prod]
    · calc ∑ i, log (a i : ℝ) ≤ ∑ _i : Fin (t + 1), log n := by
            apply Finset.sum_le_sum
            intro i _
            exact log_le_log (by exact_mod_cast hapos i) (by exact_mod_cast hb i)
        _ = (t + 1) * log n := by simp
    · intro i _
      exact_mod_cast (hapos i).ne'
  -- n^n / n! ≤ e^n
  have hexp := pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg _) n
  have hfpos : (0 : ℝ) < (n)! := by exact_mod_cast Nat.factorial_pos n
  have hlow : (n : ℝ) * log n - n ≤ log ((n)! : ℝ) := by
    have h := log_le_log (by positivity) hexp
    rw [log_div (by positivity) hfpos.ne', log_pow, log_exp] at h
    linarith
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hlog]
  nlinarith
