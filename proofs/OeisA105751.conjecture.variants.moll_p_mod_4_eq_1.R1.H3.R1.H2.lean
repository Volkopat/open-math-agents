import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1_H3_R1

-- Step OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H3.R1.H2: hypothesis H2 of reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H3.R1
-- Credit: @luciusacarr
-- H2 := ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ ε : ℚ, 0 < ε →     ∀ᶠ n : ℕ in atTop,       ((n : ℚ) + ((p - 1 : ℚ) * ((Nat.log p (n + 1) : ℚ) + 1))) / (n : ℚ) ≤ 1 + ε

/-! With `L = Nat.log p (n+1)` we have `2^L ≤ p^L ≤ n+1`, so `L log 2 ≤ log (n+1)`, and
`log = o(id)` gives `log (n+1) ≤ c (n+1)` eventually. Choosing `c = ε log 2 / (4(p-1))`
yields `(p-1)(L+1) ≤ ε (n+1)/4 + (p-1) ≤ ε n` for large `n`. -/

open Filter

namespace OMA.S105751H2

theorem key (p : ℕ) (hp : 2 ≤ p) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ((p : ℝ) - 1) * ((Nat.log p (n + 1) : ℝ) + 1) ≤ e * n := by
  set K : ℝ := (p : ℝ) - 1 with hKdef
  have hK : 1 ≤ K := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := e * Real.log 2 / (4 * K) with hcdef
  have hc : 0 < c := by positivity
  have h1 := Real.isLittleO_log_id_atTop.bound hc
  have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := ht.eventually h1
  filter_upwards [h2, eventually_ge_atTop ⌈(4 * K + e) / (3 * e)⌉₊] with n hn hN
  set L := Nat.log p (n + 1) with hL
  have hpow : p ^ L ≤ n + 1 := Nat.pow_log_le_self p (by omega)
  have h2L : 2 ^ L ≤ n + 1 := le_trans (Nat.pow_le_pow_left hp L) hpow
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlogL : (L : ℝ) * Real.log 2 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2L
  have hn' : Real.log ((n + 1 : ℕ) : ℝ) ≤ c * ((n + 1 : ℕ) : ℝ) := by
    have := hn
    simp only [Real.norm_eq_abs, id] at this
    rw [abs_of_pos hpos] at this
    exact (le_abs_self _).trans this
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hn'
  have hLb : (L : ℝ) * Real.log 2 ≤ e * Real.log 2 / (4 * K) * ((n : ℝ) + 1) := by
    rw [hcast] at hlogL
    linarith
  have hKL : K * (L : ℝ) ≤ e * ((n : ℝ) + 1) / 4 := by
    have h4K : 0 < 4 * K := by linarith
    have : (L : ℝ) * Real.log 2 * (4 * K) ≤ e * Real.log 2 * ((n : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_right hLb h4K.le
      rw [show e * Real.log 2 / (4 * K) * ((n : ℝ) + 1) * (4 * K)
        = e * Real.log 2 * ((n : ℝ) + 1) by field_simp] at this
      exact this
    have : (L : ℝ) * (4 * K) ≤ e * ((n : ℝ) + 1) := by
      have h' : Real.log 2 * ((L : ℝ) * (4 * K)) ≤ Real.log 2 * (e * ((n : ℝ) + 1)) := by
        linarith
      exact le_of_mul_le_mul_left h' hl2
    linarith
  have hNr : (4 * K + e) / (3 * e) ≤ (n : ℝ) := (Nat.ceil_le).mp hN
  have hNr' : 4 * K + e ≤ 3 * e * n := by
    rw [div_le_iff₀ (by positivity)] at hNr
    linarith
  nlinarith

end OMA.S105751H2

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1_H3_R1.H2 := by
  intro p hp _ ε hε
  have hk := OMA.S105751H2.key p hp.two_le (ε : ℝ) (by exact_mod_cast hε)
  filter_upwards [hk, eventually_ge_atTop 1] with n hn h1
  have hq : ((p : ℚ) - 1) * ((Nat.log p (n + 1) : ℚ) + 1) ≤ ε * n := by
    have : ((((p : ℚ) - 1) * ((Nat.log p (n + 1) : ℚ) + 1) : ℚ) : ℝ) ≤ ((ε * n : ℚ) : ℝ) := by
      push_cast
      exact hn
    exact_mod_cast this
  have hn0 : (0 : ℚ) < n := by exact_mod_cast h1
  rw [div_le_iff₀ hn0]
  nlinarith
