import OMAStatements.S_mo_243978
import Mathlib

open OMA.S_mo_243978
open Set

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_243978.main) := by
  rintro ⟨γ, hγ, g, f, g', h', hall⟩
  have hε0 : 0 < Real.exp (-2 / γ) := Real.exp_pos _
  have hε1 : Real.exp (-2 / γ) < 1 :=
    by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (by norm_num) hγ)
  set ε := Real.exp (-2 / γ) with hε
  have hderiv : ∀ x ∈ Ioo ε 1, HasDerivAt
      (fun y => (y * g y - g y * f y) / y - γ * Real.log y)
      ((g x * f x - γ * x) / x ^ 2) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hε0 hx.1
    have hmem : Icc (0:ℝ) 1 ∈ nhds x := Icc_mem_nhds hx0 hx.2
    obtain ⟨_, _, hg, hh, hode, _⟩ := hall x ⟨hx0.le, hx.2.le⟩
    have hg' := hg.hasDerivAt hmem
    have hh' := hh.hasDerivAt hmem
    have h1 := ((hasDerivAt_id' x).mul hg').sub hh'
    have h2 := h1.div (hasDerivAt_id' x) hx0.ne'
    have h3 := (Real.hasDerivAt_log hx0.ne').const_mul γ
    have h4 := h2.sub h3
    have h5 : HasDerivAt (fun y => (y * g y - g y * f y) / y - γ * Real.log y) _ x := h4
    refine h5.congr_deriv ?_
    have e : h' x = x * g' x := by linarith
    rw [e]; simp only [Pi.mul_apply, Pi.sub_apply]; field_simp; ring
  have hcont : ContinuousOn (fun y => (y * g y - g y * f y) / y - γ * Real.log y) (Icc ε 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε0 hx.1
    obtain ⟨_, _, hg, hh, _, _⟩ := hall x ⟨hx0.le, hx.2⟩
    have hsub : Icc ε 1 ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hε0.le le_rfl
    have cg := hg.continuousWithinAt.mono hsub
    have ch := hh.continuousWithinAt.mono hsub
    have cid : ContinuousWithinAt (fun y : ℝ => y) (Icc ε 1) x := continuousWithinAt_id
    have clog : ContinuousWithinAt Real.log (Icc ε 1) x :=
      (Real.continuousAt_log hx0.ne').continuousWithinAt
    exact (((cid.mul cg).sub ch).div cid hx0.ne').sub (clog.const_smul γ)
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ε 1) hcont
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hε0 hx.1
      obtain ⟨_, _, _, _, _, hb⟩ := hall x ⟨hx0.le, hx.2.le⟩
      exact div_nonneg (by linarith) (sq_nonneg _))
  have hle := hmono ⟨le_rfl, hε1.le⟩ ⟨hε1.le, le_rfl⟩ hε1.le
  simp only at hle
  obtain ⟨⟨hg0, hg1⟩, ⟨hf0, hf1⟩, _, _, _, _⟩ := hall ε ⟨hε0.le, hε1.le⟩
  obtain ⟨⟨hg0', hg1'⟩, ⟨hf0', hf1'⟩, _, _, _, hb1⟩ := hall 1 ⟨zero_le_one, le_rfl⟩
  rw [Real.log_one, hε, Real.log_exp] at hle
  have hA : 0 ≤ (ε * g ε - g ε * f ε) / ε := by
    apply div_nonneg _ hε0.le
    nlinarith
  rw [← hε] at hle
  have hB : γ * (-2 / γ) = -2 := by field_simp
  nlinarith
