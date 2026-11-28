import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R1

/-!
Step `Erdos420.erdos_420.variants.pow_four_ninths.R1.H2.R1.H2`: with `h = ⌊n ^ (4/9)⌋`,
`log C(n + h, h) ≤ (5/9 + ε) h log n` for all large `n`.

`C(n+h, h) ≤ (n+h)^h / h! ≤ (n+h)^h e^h / h^h` (using `x^h / h! ≤ e^x` at `x = h`), so
`log C(n+h, h) ≤ h (log (n+h) + 1 - log h)`. Since `h ≤ n`, `log (n+h) ≤ log 2 + log n`, and since
`h ≥ n^(4/9) / 2`, `log h ≥ (4/9) log n - log 2`. This gives `(5/9) log n + 2 log 2 + 1`, which is
at most `(5/9 + ε) log n` once `ε log n ≥ 2 log 2 + 1`.
-/

open Filter Real

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R1.H2 := by
  intro ε hε
  have hlog : ∀ᶠ n : ℕ in atTop, (2 * Real.log 2 + 1) / ε ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog, eventually_ge_atTop 512] with n hL hn
  intro h
  have hh : h = ⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ := rfl
  have hn' : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  set y : ℝ := (n : ℝ) ^ ((4 : ℝ) / 9) with hy
  have hy16 : (16 : ℝ) ≤ y := by
    have h1 : (512 : ℝ) ^ ((4 : ℝ) / 9) ≤ y :=
      Real.rpow_le_rpow (by norm_num) hn' (by norm_num)
    have h2 : (512 : ℝ) ^ ((4 : ℝ) / 9) = 16 := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hyn : y ≤ n := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 (show (4 : ℝ) / 9 ≤ 1 by norm_num)
    simpa [hy] using this
  have hlogy : Real.log y = (4 / 9) * Real.log n := by rw [hy, Real.log_rpow hnpos]
  have hh_le : (h : ℝ) ≤ y := by rw [hh]; exact Nat.floor_le (by linarith)
  have hh_gt : y - 1 < (h : ℝ) := by rw [hh]; have := Nat.lt_floor_add_one y; linarith
  have hhalf : y / 2 ≤ (h : ℝ) := by linarith
  have hhpos : (0 : ℝ) < h := by linarith
  have hhn : (h : ℝ) ≤ n := le_trans hh_le hyn
  -- the binomial bound
  have hchoose : (((n + h).choose h : ℕ) : ℝ) ≤ ((n : ℝ) + h) ^ h / (h.factorial : ℝ) := by
    have := Nat.choose_le_pow_div (α := ℝ) h (n + h)
    push_cast at this
    exact this
  have hfact : (h : ℝ) ^ h / (h.factorial : ℝ) ≤ Real.exp h :=
    Real.pow_div_factorial_le_exp _ (by positivity) h
  have hfpos : (0 : ℝ) < (h.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hpow : (0 : ℝ) < (h : ℝ) ^ h := by positivity
  have hB : ((n : ℝ) + h) ^ h / (h.factorial : ℝ) ≤ ((n : ℝ) + h) ^ h * Real.exp h / (h : ℝ) ^ h := by
    rw [div_le_div_iff₀ hfpos hpow]
    have := (div_le_iff₀ hfpos).mp hfact
    have hnh : (0 : ℝ) ≤ ((n : ℝ) + h) ^ h := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hnh]
  have hCpos : (0 : ℝ) < (((n + h).choose h : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlogC : Real.log (((n + h).choose h : ℕ) : ℝ) ≤
      Real.log (((n : ℝ) + h) ^ h * Real.exp h / (h : ℝ) ^ h) :=
    Real.log_le_log hCpos (le_trans hchoose hB)
  have hnh0 : (0 : ℝ) < (n : ℝ) + h := by linarith
  rw [Real.log_div (by positivity) hpow.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp, Real.log_pow] at hlogC
  -- bounds on the logarithms
  have hl1 : Real.log ((n : ℝ) + h) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hnpos.ne']
    exact Real.log_le_log hnh0 (by linarith)
  have hl2 : (4 / 9) * Real.log n - Real.log 2 ≤ Real.log h := by
    have := Real.log_le_log (by linarith) hhalf
    rw [Real.log_div (by linarith) (by norm_num), hlogy] at this
    linarith
  have hεL : 2 * Real.log 2 + 1 ≤ ε * Real.log n := by
    have := (div_le_iff₀ hε).mp hL
    linarith
  have inner : Real.log ((n : ℝ) + h) + 1 - Real.log h ≤ (5 / 9 + ε) * Real.log n := by
    nlinarith
  calc Real.log (((n + h).choose h : ℕ) : ℝ)
      ≤ (h : ℝ) * Real.log ((n : ℝ) + h) + h - (h : ℝ) * Real.log h := hlogC
    _ = (h : ℝ) * (Real.log ((n : ℝ) + h) + 1 - Real.log h) := by ring
    _ ≤ (h : ℝ) * ((5 / 9 + ε) * Real.log n) := mul_le_mul_of_nonneg_left inner hhpos.le
    _ = (5 / 9 + ε) * (h : ℝ) * Real.log n := by ring
