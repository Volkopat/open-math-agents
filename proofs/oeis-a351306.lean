import OMAStatements.S_oeis_a351306

namespace OMA.A351306

theorem scale (n : ℕ) (hn : 0 < n) :
    ∃ L : ℚ, 0 < L ∧ 32 * L ^ 4 ≤ n ∧ (n : ℚ) ≤ 48 * L ^ 4 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let root (x : ℝ) := Real.sqrt (Real.sqrt x)
  have root_pow (x : ℝ) (hx : 0 ≤ x) : (root x) ^ 4 = x := by
    unfold root
    rw [show 4 = 2 * 2 by decide, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]
  have hgap : root ((n : ℝ) / 48) < root ((n : ℝ) / 32) := by
    apply Real.sqrt_lt_sqrt (Real.sqrt_nonneg _)
    apply Real.sqrt_lt_sqrt (by positivity)
    linarith
  obtain ⟨L, hlow, hupp⟩ := exists_rat_btwn hgap
  have hp : 0 < (L : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hlow
  have hl := pow_le_pow_left₀ (Real.sqrt_nonneg _) hlow.le 4
  have hu := pow_le_pow_left₀ hp.le hupp.le 4
  rw [root_pow _ (by positivity)] at hl hu
  refine ⟨L, by exact_mod_cast hp, ?_, ?_⟩
  · exact_mod_cast (show 32 * (L : ℝ) ^ 4 ≤ n by linarith)
  · exact_mod_cast (show (n : ℝ) ≤ 48 * (L : ℝ) ^ 4 by linarith)

end OMA.A351306

-- We use R. Norrie's fourth-power identity with b = 1 and c = 2 in the notation of
-- Geoffrey B. Campbell, Sums of like powers for any rational number, AustMS Gazette
-- 52 (2025), pp. 159–160. https://austms.org.au/wp-content/uploads/2025/10/524Web_2.pdf
-- To obtain Zhi-Wei Sun's bound, scale the input into [32, 48]. On this interval
-- both subtracted fourth powers have bases of absolute value at most 2.
theorem OMA.solution : type_of% @OMA.S_oeis_a351306.main := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact ⟨0, 0, 0, 0, by norm_num, by norm_num⟩
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨L, hL, hlo, hhi⟩ := OMA.A351306.scale n hn'
  let s : ℚ := n / L ^ 4
  have hL₄ : (0 : ℚ) < L ^ 4 := by positivity
  have hslo : 32 ≤ s := (le_div_iff₀ hL₄).2 hlo
  have hshi : s ≤ 48 := (div_le_iff₀ hL₄).2 hhi
  have hs : s * L ^ 4 = n := div_mul_cancel₀ _ hL₄.ne'
  refine ⟨(2 + 4 * s / 255) * L, (8 * s / 255 - 1 / 4) * L,
    (8 * s / 255 + 1 / 4) * L, (4 * s / 255 - 2) * L, ?_, ?_⟩
  · calc
      (n : ℚ) = s * L ^ 4 := hs.symm
      _ = _ := by ring
  · have bound (z : ℚ) (hz : |z| ≤ 2) : (z * L) ^ 4 ≤ 16 * L ^ 4 := by
      have h := pow_le_pow_left₀ (abs_nonneg z) hz 4
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z ^ 4)] at h
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by norm_num at h ⊢; exact h) hL₄.le
    have hx := bound (8 * s / 255 + 1 / 4) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hy := bound (4 * s / 255 - 2) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hn₁ : (1 : ℚ) ≤ n := by exact_mod_cast hn'
    have hn₂ : (n : ℚ) ≤ (n : ℚ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn₁) (show (0 : ℚ) ≤ n by positivity)]
    linarith
