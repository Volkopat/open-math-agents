import OMAReductions.R_oeis_a002387_R1

/-!
# Proof of `oeis-a002387.R1.H1`

For `k > 0`, let `d k = H_k - log (k + 1/2)` and `u k = d k - 1 / (24 * k^2)`.
Both sequences converge to `eulerMascheroniConstant` as `k → ∞`.
For `x = 1 / (2 * (k + 1)) ∈ (0, 1/4]`, we have
`d k - d (k + 1) = log ((1 + x) / (1 - x)) - 2 * x`.
Differentiating shows `0 < log ((1 + x) / (1 - x)) - 2 * x < 2 * x^3 / (3 * (1 - x^2))` for all
`x ∈ (0, 1)`. Thus `d` is strictly decreasing on `k ≥ 1` (giving `d k > γ`), and
`2 * x^3 / (3 * (1 - x^2)) < 1 / (24 * k^2) - 1 / (24 * (k + 1)^2)` shows `u` is strictly
increasing on `k ≥ 1` (giving `u k < γ`).
-/

open Real Filter
open scoped Topology

private lemma log_ratio_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < log ((1 + x) / (1 - x)) - 2 * x ∧
    log ((1 + x) / (1 - x)) - 2 * x < 2 * x ^ 3 / (3 * (1 - x ^ 2)) := by
  let f : ℝ → ℝ := fun t => log (1 + t) - log (1 - t) - 2 * t
  let g : ℝ → ℝ := fun t => 2 * t ^ 3 / (3 * (1 - t ^ 2)) - f t
  have hf_eq : ∀ t : ℝ, 0 ≤ t → t < 1 → f t = log ((1 + t) / (1 - t)) - 2 * t := by
    intro t ht0 ht1
    dsimp only [f]
    rw [log_div (by linarith) (by linarith)]
  have hf_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (2 * t ^ 2 / (1 - t ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t)
      rwa [zero_sub] at h
    have hl1 : HasDerivAt (fun s : ℝ => log (1 + s)) (1 / (1 + t)) t := by
      simpa using h1.log (by linarith [ht.1])
    have hl2 : HasDerivAt (fun s : ℝ => log (1 - s)) ((-1) / (1 - t)) t := by
      simpa using h2.log (by linarith [ht.2])
    have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have hsub : HasDerivAt f (1 / (1 + t) - (-1) / (1 - t) - 2) t :=
      (hl1.sub hl2).sub hlin
    have hval : 1 / (1 + t) - (-1) / (1 - t) - 2 = 2 * t ^ 2 / (1 - t ^ 2) := by
      have h1p : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
      have h1m : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
      have h1s : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
      field_simp
      ring
    rwa [hval] at hsub
  have hf_cont : ContinuousOn f (Set.Icc 0 x) := by
    refine ((ContinuousOn.log ?_ ?_).sub (ContinuousOn.log ?_ ?_)).sub ?_
    · exact continuousOn_const.add continuousOn_id
    · intro t ht; linarith [ht.1]
    · exact continuousOn_const.sub continuousOn_id
    · intro t ht; linarith [ht.2]
    · exact continuousOn_const.mul continuousOn_id
  have hf_mono : StrictMonoOn f (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) hf_cont ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hf_deriv t ⟨ht.1, ht.2.trans hx1⟩).deriv]
    have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h2 : 0 < 2 * t ^ 2 := by nlinarith [ht.1]
    exact div_pos h2 h1
  have hf_pos : 0 < f x := by
    have h0 : f 0 = 0 := by simp [f]
    rw [← h0]
    exact hf_mono ⟨le_rfl, hx0.le⟩ ⟨hx0.le, le_rfl⟩ hx0
  have hg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (4 * t ^ 4 / (3 * (1 - t ^ 2) ^ 2)) t := by
    intro t ht
    have hnum : HasDerivAt (fun s : ℝ => 2 * s ^ 3) (6 * t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).const_mul (2 : ℝ)
      have hv : (2 : ℝ) * ((3 : ℕ) * t ^ (3 - 1)) = 6 * t ^ 2 := by norm_num; ring
      rwa [hv] at h
    have hden : HasDerivAt (fun s : ℝ => 3 * (1 - s ^ 2)) (-6 * t) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have hsub1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (0 - 2 * t) t :=
        (hasDerivAt_const t (1 : ℝ)).sub hsq
      have h := hsub1.const_mul (3 : ℝ)
      have hv : (3 : ℝ) * (0 - 2 * t) = -6 * t := by ring
      rwa [hv] at h
    have hden_ne : 3 * (1 - t ^ 2) ≠ 0 := by nlinarith [ht.1, ht.2]
    have hq := hnum.div hden hden_ne
    have hsub : HasDerivAt g
        ((6 * t ^ 2 * (3 * (1 - t ^ 2)) - 2 * t ^ 3 * (-6 * t)) / (3 * (1 - t ^ 2)) ^ 2 -
          2 * t ^ 2 / (1 - t ^ 2)) t :=
      hq.sub (hf_deriv t ht)
    have hval : (6 * t ^ 2 * (3 * (1 - t ^ 2)) - 2 * t ^ 3 * (-6 * t)) / (3 * (1 - t ^ 2)) ^ 2 -
        2 * t ^ 2 / (1 - t ^ 2) = 4 * t ^ 4 / (3 * (1 - t ^ 2) ^ 2) := by
      have h1s : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
      field_simp
      ring
    rwa [hval] at hsub
  have hg_cont : ContinuousOn g (Set.Icc 0 x) := by
    refine ContinuousOn.sub ?_ hf_cont
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul (continuousOn_id.pow 3)
    · exact continuousOn_const.mul (continuousOn_const.sub (continuousOn_id.pow 2))
    · intro t ht; nlinarith [ht.1, ht.2]
  have hg_mono : StrictMonoOn g (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) hg_cont ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hg_deriv t ⟨ht.1, ht.2.trans hx1⟩).deriv]
    have ht0 : 0 < t := ht.1
    have h1s : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : 0 < 3 * (1 - t ^ 2) ^ 2 := by positivity
    have h2 : 0 < 4 * t ^ 4 := by positivity
    exact div_pos h2 h1
  have hg_pos : 0 < g x := by
    have h0 : g 0 = 0 := by simp [g, f]
    rw [← h0]
    exact hg_mono ⟨le_rfl, hx0.le⟩ ⟨hx0.le, le_rfl⟩ hx0
  rw [← hf_eq x hx0.le hx1]
  exact ⟨hf_pos, by dsimp only [g] at hg_pos; linarith⟩

private lemma tendsto_harmonic_sub_log_half :
    Tendsto (fun k : ℕ => (harmonic k : ℝ) - log ((k : ℝ) + 1 / 2))
      atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun k : ℕ => log ((k : ℝ) + 1 / 2) - log (k : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log (1 / 2)).comp tendsto_natCast_atTop_atTop
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr fun k => ?_
  ring

private lemma strictAnti_from_step {seq : ℕ → ℝ} (hstep : ∀ k : ℕ, 1 ≤ k → seq (k + 1) < seq k) :
    ∀ k m : ℕ, 1 ≤ k → k < m → seq m < seq k := by
  intro k m hk hkm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases heq : k = m
    · subst heq; exact hstep k hk
    · exact (hstep m (by omega)).trans (ih (by omega))

private lemma strictMono_from_step {seq : ℕ → ℝ} (hstep : ∀ k : ℕ, 1 ≤ k → seq k < seq (k + 1)) :
    ∀ k m : ℕ, 1 ≤ k → k < m → seq k < seq m := by
  intro k m hk hkm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases heq : k = m
    · subst heq; exact hstep k hk
    · exact (ih (by omega)).trans (hstep m (by omega))

theorem OMA.solution : OMA.R_oeis_a002387_R1.H1 := by
  let d : ℕ → ℝ := fun k => (harmonic k : ℝ) - log ((k : ℝ) + 1 / 2)
  let u : ℕ → ℝ := fun k => d k - 1 / (24 * (k : ℝ) ^ 2)
  have hd_diff : ∀ k : ℕ, 1 ≤ k →
      d k - d (k + 1) = log ((1 + 1 / (2 * ((k : ℝ) + 1))) / (1 - 1 / (2 * ((k : ℝ) + 1)))) -
        2 * (1 / (2 * ((k : ℝ) + 1))) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp only [d]
    rw [harmonic_succ]
    push_cast
    have hratio : ((k : ℝ) + 1 + 1 / 2) / ((k : ℝ) + 1 / 2) =
        (1 + 1 / (2 * ((k : ℝ) + 1))) / (1 - 1 / (2 * ((k : ℝ) + 1))) := by
      have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by linarith
      have h2 : 2 * ((k : ℝ) + 1) ≠ 0 := by linarith
      have h4 : 1 - 1 / (2 * ((k : ℝ) + 1)) ≠ 0 := by
        rw [sub_ne_zero]
        have : 1 / (2 * ((k : ℝ) + 1)) < 1 := by
          rw [div_lt_one (by linarith)]; linarith
        linarith
      rw [div_eq_div_iff h1 h4]
      field_simp
      ring
    have hlog : log ((k : ℝ) + 1 + 1 / 2) - log ((k : ℝ) + 1 / 2) =
        log (((k : ℝ) + 1 + 1 / 2) / ((k : ℝ) + 1 / 2)) :=
      (log_div (by linarith) (by linarith)).symm
    have h2x : 2 * (1 / (2 * ((k : ℝ) + 1))) = ((k : ℝ) + 1)⁻¹ := by
      have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
      field_simp
    rw [← hratio, ← hlog, h2x]
    ring
  have hd_step : ∀ k : ℕ, 1 ≤ k → d (k + 1) < d k := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hx0 : 0 < 1 / (2 * ((k : ℝ) + 1)) := by positivity
    have hx1 : 1 / (2 * ((k : ℝ) + 1)) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have hpos := (log_ratio_bounds hx0 hx1).1
    rw [← hd_diff k hk] at hpos
    linarith
  have hu_step : ∀ k : ℕ, 1 ≤ k → u k < u (k + 1) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    set x : ℝ := 1 / (2 * ((k : ℝ) + 1))
    have hx0 : 0 < x := by positivity
    have hx1 : x < 1 := by
      dsimp only [x]; rw [div_lt_one (by linarith)]; linarith
    have hub := (log_ratio_bounds hx0 hx1).2
    rw [← hd_diff k hk] at hub
    have hgap : 2 * x ^ 3 / (3 * (1 - x ^ 2)) <
        1 / (24 * (k : ℝ) ^ 2) - 1 / (24 * ((k : ℝ) + 1) ^ 2) := by
      have h1 : 0 < 1 - x ^ 2 := by nlinarith
      have h2 : (k : ℝ) ≠ 0 := by linarith
      have h3 : (k : ℝ) + 1 ≠ 0 := by linarith
      have h4 : 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith
      have hsimp : 2 * x ^ 3 / (3 * (1 - x ^ 2)) =
          1 / (3 * ((k : ℝ) + 1) * (4 * ((k : ℝ) + 1) ^ 2 - 1)) := by
        dsimp only [x]
        rw [div_eq_div_iff (by positivity) (by positivity)]
        field_simp
        ring
      rw [hsimp, ← sub_pos]
      set D : ℝ := 24 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * (4 * ((k : ℝ) + 1) ^ 2 - 1)
      have hD : 0 < D := by positivity
      have ht1 : 1 / (24 * (k : ℝ) ^ 2) * D =
          ((k : ℝ) + 1) ^ 2 * (4 * ((k : ℝ) + 1) ^ 2 - 1) := by
        dsimp only [D]
        have : 24 * (k : ℝ) ^ 2 ≠ 0 := by positivity
        field_simp
      have ht2 : 1 / (24 * ((k : ℝ) + 1) ^ 2) * D =
          (k : ℝ) ^ 2 * (4 * ((k : ℝ) + 1) ^ 2 - 1) := by
        dsimp only [D]
        have : 24 * ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
        field_simp
      have ht3 : 1 / (3 * ((k : ℝ) + 1) * (4 * ((k : ℝ) + 1) ^ 2 - 1)) * D =
          8 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) := by
        dsimp only [D]
        have : 3 * ((k : ℝ) + 1) * (4 * ((k : ℝ) + 1) ^ 2 - 1) ≠ 0 := by positivity
        rw [show 24 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * (4 * ((k : ℝ) + 1) ^ 2 - 1) =
          (3 * ((k : ℝ) + 1) * (4 * ((k : ℝ) + 1) ^ 2 - 1)) * (8 * (k : ℝ) ^ 2 * ((k : ℝ) + 1))
          by ring]
        rw [one_div, inv_mul_cancel_left₀ this]
      have hmul : (1 / (24 * (k : ℝ) ^ 2) - 1 / (24 * ((k : ℝ) + 1) ^ 2) -
          1 / (3 * ((k : ℝ) + 1) * (4 * ((k : ℝ) + 1) ^ 2 - 1))) * D =
          12 * (k : ℝ) ^ 2 + 14 * (k : ℝ) + 3 := by
        rw [sub_mul, sub_mul, ht1, ht2, ht3]
        ring
      have hnum : 0 < 12 * (k : ℝ) ^ 2 + 14 * (k : ℝ) + 3 := by nlinarith
      exact pos_of_mul_pos_left (by rw [hmul]; exact hnum) hD.le
    dsimp only [u]
    push_cast
    linarith
  have hd_tend : Tendsto d atTop (𝓝 eulerMascheroniConstant) := tendsto_harmonic_sub_log_half
  have hu_tend : Tendsto u atTop (𝓝 eulerMascheroniConstant) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (24 * (k : ℝ) ^ 2)) atTop (𝓝 0) := by
      have hinf : Tendsto (fun k : ℕ => (24 : ℝ) * (k : ℝ) ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 24)
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
      exact tendsto_const_nhds.div_atTop hinf
    have hsub := hd_tend.sub h0
    rw [sub_zero] at hsub
    exact hsub
  intro k hk
  have hd_ge : eulerMascheroniConstant ≤ d (k + 1) := by
    refine le_of_tendsto hd_tend ?_
    filter_upwards [eventually_gt_atTop (k + 1)] with m hm
    exact (strictAnti_from_step hd_step (k + 1) m (by omega) hm).le
  have hu_le : u (k + 1) ≤ eulerMascheroniConstant := by
    refine ge_of_tendsto hu_tend ?_
    filter_upwards [eventually_gt_atTop (k + 1)] with m hm
    exact (strictMono_from_step hu_step (k + 1) m (by omega) hm).le
  have h1 : eulerMascheroniConstant < d k := lt_of_le_of_lt hd_ge (hd_step k hk)
  have h2 : u k < eulerMascheroniConstant := lt_of_lt_of_le (hu_step k hk) hu_le
  dsimp only [u, d] at h1 h2
  exact ⟨by linarith, by linarith⟩
