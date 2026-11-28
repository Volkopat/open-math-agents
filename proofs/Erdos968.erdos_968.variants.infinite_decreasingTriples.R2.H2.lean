import OMAReductions.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2

/-!
Proof of `OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2.H2`:
the primes have density zero.

Chebyshev's bound `π(x) ≤ (log 4 + 1) x / log x` holds for all large `x`
(`Chebyshev.eventually_primeCounting_le`), and `log x → ∞`, so eventually
`(log 4 + 1) / log x < δ`.
-/

open Filter

theorem OMA.solution : OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2.H2 := by
  intro δ hδ
  have h1 := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have h2 : ∀ᶠ n : ℕ in atTop, (Real.log 4 + 1) / δ < Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn hlog hn1
  rw [Nat.floor_natCast] at hn
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 < Real.log 4 + 1 := by linarith
  have hL : 0 < Real.log n := lt_trans (div_pos hA hδ) hlog
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : Real.log 4 + 1 < Real.log n * δ := (div_lt_iff₀ hδ).mp hlog
  calc (n.primeCounting : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := hn
    _ < δ * n := by
      rw [div_lt_iff₀ hL]
      nlinarith
