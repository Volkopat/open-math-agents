import OMAReductions.R_Bloch_blochConstant_upper_bound_R1
import Mathlib

-- Step H3 of Bloch.blochConstant_upper_bound.R1.
-- Credit: @LordMike

open Set Metric Filter Topology

/-- An eventually constant function is not injective near a point. -/
lemma bloch_H3_no_const (f : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S) (z0 : ℂ) (hz0 : z0 ∈ S)
    (hinj : InjOn f S) (h : ∀ᶠ z in 𝓝 z0, f z = f z0) : False := by
  have hSe : ∀ᶠ z in 𝓝 z0, z ∈ S := hS.mem_nhds hz0
  have h1 : ∀ᶠ z in 𝓝[≠] z0, f z = f z0 ∧ z ∈ S ∧ z ≠ z0 :=
    (eventually_nhdsWithin_of_eventually_nhds h).and
      ((eventually_nhdsWithin_of_eventually_nhds hSe).and self_mem_nhdsWithin)
  obtain ⟨z1, h1f, h1S, h1ne⟩ := h1.exists
  exact h1ne (hinj h1S hz0 h1f)

/-- If `f z = f z0 + φ z ^ n` near `z0` with `φ z0 = 0`, `n ≥ 2`, and `φ` analytic, then `f` is
not injective on any open set containing `z0`. -/
lemma bloch_H3_local (f : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S) (z0 : ℂ) (hz0 : z0 ∈ S)
    (hinj : InjOn f S) (n : ℕ) (hn : 2 ≤ n) (φ : ℂ → ℂ) (hφa : AnalyticAt ℂ φ z0)
    (hφ0 : φ z0 = 0) (hid : ∀ᶠ z in 𝓝 z0, f z = f z0 + φ z ^ n) : False := by
  have hn0 : n ≠ 0 := by omega
  have hSe : ∀ᶠ z in 𝓝 z0, z ∈ S := hS.mem_nhds hz0
  rcases hφa.eventually_constant_or_nhds_le_map_nhds_aux with hc | hnhds
  · refine bloch_H3_no_const f S hS z0 hz0 hinj ?_
    filter_upwards [hc, hid] with z hz1 hz2
    rw [hz2, hz1, hφ0, zero_pow hn0, add_zero]
  · rw [hφ0] at hnhds
    have key : ∀ U ∈ 𝓝 z0, φ '' U ∈ 𝓝 (0 : ℂ) := fun U hU =>
      (Filter.le_def.1 hnhds) _
        (Filter.mem_map.2 (Filter.mem_of_superset hU (Set.subset_preimage_image φ U)))
    obtain ⟨ε, hε, hboth⟩ := Metric.eventually_nhds_iff.1 (hid.and hSe)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (key (ball z0 ε) (ball_mem_nhds z0 hε))
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn0⟩
    have hζ1 : ‖ζ‖ = 1 := hζ.norm'_eq_one hn0
    obtain ⟨w, hwδ, hw0⟩ : ∃ w : ℂ, ‖w‖ < δ ∧ w ≠ 0 :=
      ⟨((δ / 2 : ℝ) : ℂ), by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith,
        Complex.ofReal_ne_zero.2 (half_pos hδ).ne'⟩
    obtain ⟨z1, hz1, hφ1⟩ :=
      hsub (show w ∈ ball (0 : ℂ) δ from by rw [mem_ball, dist_zero_right]; exact hwδ)
    obtain ⟨z2, hz2, hφ2⟩ :=
      hsub (show ζ * w ∈ ball (0 : ℂ) δ from by
        rw [mem_ball, dist_zero_right, norm_mul, hζ1, one_mul]; exact hwδ)
    have e1 := hboth (mem_ball.1 hz1)
    have e2 := hboth (mem_ball.1 hz2)
    have hpow : (ζ * w) ^ n = w ^ n := by rw [mul_pow, hζ.pow_eq_one, one_mul]
    have hf12 : f z1 = f z2 := by
      rw [e1.1, e2.1, hφ1, hφ2, hpow]
    have heq : z1 = z2 := hinj e1.2 e2.2 hf12
    have hφeq : φ z1 = φ z2 := by rw [heq]
    rw [hφ1, hφ2] at hφeq
    exact hζ.ne_one (by omega) (mul_right_cancel₀ hw0 (by rw [one_mul]; exact hφeq.symm))

/-- A holomorphic function injective on an open set has nonvanishing derivative there. -/
lemma bloch_H3_key (f : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S) (hf : DifferentiableOn ℂ f S)
    (hinj : InjOn f S) (z0 : ℂ) (hz0 : z0 ∈ S) (hd : deriv f z0 = 0) : False := by
  have hfa : AnalyticAt ℂ f z0 := hf.analyticAt (hS.mem_nhds hz0)
  have hga : AnalyticAt ℂ (fun z => f z - f z0) z0 := hfa.sub analyticAt_const
  have h2 : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z0) z0 := by
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) hga).2 ?_
    · exact_mod_cast this
    · intro i hi
      interval_cases i
      · simp
      · simpa [iteratedDeriv_one, deriv_sub_const] using hd
  by_cases htop : analyticOrderAt (fun z => f z - f z0) z0 = ⊤
  · have he := analyticOrderAt_eq_top.1 htop
    exact bloch_H3_no_const f S hS z0 hz0 hinj (he.mono fun z hz => sub_eq_zero.1 hz)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hn2 : 2 ≤ n := by
    have := h2
    rw [← hn] at this
    exact_mod_cast this
  obtain ⟨F, hFa, hFne, hFe⟩ := (hga.analyticOrderAt_eq_natCast (n := n)).1 hn.symm
  have hFe' : ∀ᶠ z in 𝓝 z0, f z - f z0 = (z - z0) ^ n * F z :=
    hFe.mono fun z hz => by simp only [smul_eq_mul] at hz; exact hz
  have hn0 : n ≠ 0 := by omega
  have hQa : AnalyticAt ℂ (fun z => F z / F z0) z0 := hFa.div_const
  have hQm : (fun z => F z / F z0) z0 ∈ Complex.slitPlane := by
    simp only [div_self hFne]
    exact Complex.one_mem_slitPlane
  have hRa : AnalyticAt ℂ (fun z => (F z / F z0) ^ ((n : ℂ)⁻¹)) z0 :=
    hQa.cpow analyticAt_const hQm
  have hφa : AnalyticAt ℂ
      (fun z => (z - z0) * (F z0 ^ ((n : ℂ)⁻¹) * (F z / F z0) ^ ((n : ℂ)⁻¹))) z0 :=
    (analyticAt_id.sub analyticAt_const).mul (analyticAt_const.mul hRa)
  have hκ : (F z0 ^ ((n : ℂ)⁻¹)) ^ n = F z0 := Complex.cpow_nat_inv_pow _ hn0
  have hid : ∀ᶠ z in 𝓝 z0, f z =
      f z0 + ((z - z0) * (F z0 ^ ((n : ℂ)⁻¹) * (F z / F z0) ^ ((n : ℂ)⁻¹))) ^ n := by
    filter_upwards [hFe'] with z hz
    have e : ((z - z0) * (F z0 ^ ((n : ℂ)⁻¹) * (F z / F z0) ^ ((n : ℂ)⁻¹))) ^ n
        = (z - z0) ^ n * F z := by
      rw [mul_pow, mul_pow, hκ, Complex.cpow_nat_inv_pow _ hn0]
      congr 1
      field_simp
    rw [e]
    linear_combination hz
  exact bloch_H3_local f S hS z0 hz0 hinj n hn2 _ hφa (by simp) hid

theorem OMA.solution : OMA.R_Bloch_blochConstant_upper_bound_R1.H3 := by
  unfold OMA.R_Bloch_blochConstant_upper_bound_R1.H3
  intro f S hS hf hinj z hz hd
  exact bloch_H3_key f S hS hf hinj z hz hd
