import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R3 of step Erdos142.erdos_142.variants.lower.R1.H2.R2.H1
-- Credit: @pmcao

/-!
# Asymptotic quasipolynomial van der Waerden reduction for polylogarithmic palettes

Unlike density-based pigeonhole reductions, this reduction preserves the coloring structure
of step `lower.R1.H2.R2.H1` directly along the quasipolynomial van der Waerden threshold
`W_q(k) ≤ ⌈exp(C (log q)^A)⌉₊` (OpenAI 2026, section 1.4, equation (1.3)), while:

1. Separating the quadratic Fourier regime (`k = 4`, `H1`) from the higher-order nilsequence
   regime (`k ≥ 5`, `H2`).
2. Requiring the coloring threshold only eventually (`∀ᶠ q in atTop`) and for arbitrary positive
   constants `C > 0`, `A > 0`, eliminating small-palette calibration (`q = 1, 2` and `A ≥ 1`).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R3

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- Asymptotic quasipolynomial van der Waerden bound for 4-term progressions. -/
def H1 : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ᶠ q : ℕ in atTop,
    ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < 4,
      a + i * d ∈ Finset.Icc 1 ⌈Real.exp (C * Real.log (q : ℝ) ^ A)⌉₊ ∧
        c (a + i * d) = c a

/-- Asymptotic quasipolynomial van der Waerden bound for progressions of length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ᶠ q : ℕ in atTop,
    ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
      a + i * d ∈ Finset.Icc 1 ⌈Real.exp (C * Real.log (q : ℝ) ^ A)⌉₊ ∧
        c (a + i * d) = c a

/-- The polylogarithmic palette size `(⌈log N⌉₊ + 1) ^ 4` tends to infinity with `N`. -/
lemma tendsto_palette_atTop :
    Tendsto (fun N : ℕ => (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlogN.eventually_ge_atTop (b : ℝ))
  refine ⟨N₀, fun N hN => ?_⟩
  have hb : b ≤ ⌈Real.log (N : ℝ)⌉₊ := by
    exact_mod_cast (hN₀ N hN).trans (Nat.le_ceil _)
  have h1 : b ≤ ⌈Real.log (N : ℝ)⌉₊ + 1 := hb.trans (Nat.le_succ _)
  have hpow : ⌈Real.log (N : ℝ)⌉₊ + 1 ≤ (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 :=
    Nat.le_self_pow (by decide) _
  exact h1.trans hpow

/-- For any positive constants `C` and `A`, the quasipolynomial Ramsey scale at
`q = (⌈log N⌉₊ + 1) ^ 4` is eventually at most `N`. -/
lemma eventual_quasipoly_palette_le (C A : ℝ) (hC : 0 < C) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ⌈Real.exp (C * Real.log (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) ^ A)⌉₊ ≤ N := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth :
      (fun x : ℝ => (C * (8 : ℝ) ^ A) * Real.log x ^ A) =o[atTop] (fun x => x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).const_mul_left (C * (8 : ℝ) ^ A)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlogN.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hlogN).eventually_ge_atTop 1,
    hlogN.eventually (hgrowth.def zero_lt_one)] with N hN hx hlogx hlin
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  set x : ℝ := Real.log (N : ℝ)
  change 1 ≤ Real.log x at hlogx
  let y : ℝ := (⌈x⌉₊ : ℝ) + 1
  have hy1 : 1 ≤ y := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hy_sq : y ≤ x ^ 2 := by
    have hx0 : 0 ≤ x := by linarith
    have hceil := Nat.ceil_lt_add_one hx0
    have hprod : 0 ≤ (x - 2) * (x + 1) := mul_nonneg (by linarith) (by positivity)
    dsimp [y]
    nlinarith
  have hlogy : Real.log y ≤ 2 * Real.log x := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hy_pos hy_sq
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  apply Nat.ceil_le.mpr
  rw [← Real.le_log_iff_exp_le hN0]
  change C * Real.log (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) ^ A ≤ x
  calc
    C * Real.log (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) ^ A
        = C * (4 * Real.log y) ^ A := by
          simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow, Nat.cast_ofNat, y]
    _ ≤ C * (8 * Real.log x) ^ A :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (by linarith) hA.le) hC.le
    _ = (C * (8 : ℝ) ^ A) * Real.log x ^ A := by
          rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hlogx), mul_assoc]
    _ ≤ x := by
          refine (le_abs_self _).trans ?_
          simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (show 0 ≤ x by linarith)] using hlin

/-- An eventual quasipolynomial coloring bound for length `k` implies the palette coloring
condition at length `k`. -/
lemma coloring_of_eventual_ramsey {k : ℕ}
    (h : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ᶠ q : ℕ in atTop,
      ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
        a + i * d ∈ Finset.Icc 1 ⌈Real.exp (C * Real.log (q : ℝ) ^ A)⌉₊ ∧
          c (a + i * d) = c a) :
    ∀ᶠ N : ℕ in atTop,
      ∀ c : ℕ → Fin ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4), ∃ a d : ℕ, 0 < d ∧
        ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  obtain ⟨C, A, hC, hA, hq⟩ := h
  filter_upwards [tendsto_palette_atTop.eventually hq,
    eventual_quasipoly_palette_le C A hC hA] with N hmono hle c
  obtain ⟨a, d, hd, hap⟩ := hmono c
  refine ⟨a, d, hd, fun i hi => ?_⟩
  obtain ⟨hmem, hcol⟩ := hap i hi
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
  exact ⟨Finset.mem_Icc.mpr ⟨h1, h2.trans hle⟩, hcol⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H1 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact coloring_of_eventual_ramsey h4
  · exact coloring_of_eventual_ramsey (h5 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R3
