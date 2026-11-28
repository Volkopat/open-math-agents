import OMAStatements.S_mo_140460
import Mathlib

namespace OMA.Helpers_mo_140460

open Matrix OMA.S_mo_140460

theorem col_sum {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (i : Fin N) :
    ∑ k, ‖U k i‖ ^ 2 = 1 := by
  have h : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have h2 : (star U * U) i i = ((∑ k, ‖U k i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.star_eq_conjTranspose]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [h, Matrix.one_apply_eq] at h2
  exact_mod_cast h2.symm

theorem entry_bound {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) : ‖U i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary hU i j

theorem fourier_norm (N : ℕ) (i j : Fin N) : ‖OMA.S_mo_140460.fourier N i j‖ = (Real.sqrt N)⁻¹ := by
  unfold OMA.S_mo_140460.fourier
  rw [norm_mul, norm_pow, norm_inv, norm_inv, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I / N).re = 0 := by
    have : (2 * (Real.pi : ℂ) * Complex.I / N) = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
  rw [hre, Real.exp_zero, inv_one, one_pow, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem fourier_col {N : ℕ} (hN : 0 < N) (j : Fin N) : ∑ k, ‖OMA.S_mo_140460.fourier N k j‖ ^ 2 = 1 := by
  simp only [fourier_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem cross {N : ℕ} (hN : 0 < N) {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) :
    ‖∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖ ≤ 1 := by
  calc ‖∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖
      ≤ ∑ k, ‖star (OMA.S_mo_140460.fourier N k j) * U k i‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖OMA.S_mo_140460.fourier N k j‖ ^ 2 + ‖U k i‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖OMA.S_mo_140460.fourier N k j‖ - ‖U k i‖)]
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, col_sum hU, fourier_col hN]
        norm_num

theorem trace_bound {N : ℕ} (hN : 0 < N) (f g : Fin N → ℂ) {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖((diagonal f * OMA.S_mo_140460.fourier N * diagonal g * (OMA.S_mo_140460.fourier N).conjTranspose) * U).trace‖ ≤
      (Real.sqrt N)⁻¹ * (∑ i, ‖f i‖) * (∑ j, ‖g j‖) := by
  have htr : ((diagonal f * OMA.S_mo_140460.fourier N * diagonal g * (OMA.S_mo_140460.fourier N).conjTranspose) * U).trace =
      ∑ i, ∑ j, f i * OMA.S_mo_140460.fourier N i j * g j * ∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i := by
    have e1 : ∀ i j, (diagonal f * OMA.S_mo_140460.fourier N * diagonal g) i j =
        f i * OMA.S_mo_140460.fourier N i j * g j := fun i j => by
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    generalize diagonal f * OMA.S_mo_140460.fourier N * diagonal g = B at e1 ⊢
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, e1,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [htr]
  calc ‖∑ i, ∑ j, f i * OMA.S_mo_140460.fourier N i j * g j * ∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖
      ≤ ∑ i, ‖∑ j, f i * OMA.S_mo_140460.fourier N i j * g j * ∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖f i * OMA.S_mo_140460.fourier N i j * g j * ∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖f i‖ * (Real.sqrt N)⁻¹ * ‖g j‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, norm_mul, fourier_norm]
        have h1 := cross hN hU i j
        have h2 : 0 ≤ ‖f i‖ * (Real.sqrt N)⁻¹ * ‖g j‖ := by positivity
        calc ‖f i‖ * (Real.sqrt N)⁻¹ * ‖g j‖ * ‖∑ k, star (OMA.S_mo_140460.fourier N k j) * U k i‖
            ≤ ‖f i‖ * (Real.sqrt N)⁻¹ * ‖g j‖ * 1 := mul_le_mul_of_nonneg_left h1 h2
          _ = _ := mul_one _
    _ = (Real.sqrt N)⁻¹ * (∑ i, ‖f i‖) * (∑ j, ‖g j‖) := by
        rw [mul_assoc, Finset.sum_mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

theorem diag_trace_bound {N : ℕ} (d : Fin N → ℂ) {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖(diagonal d * U).trace‖ ≤ ∑ i, ‖d i‖ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  calc ‖∑ i, d i * U i i‖ ≤ ∑ i, ‖d i * U i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖d i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        have := entry_bound hU i i
        have := norm_nonneg (d i)
        nlinarith

theorem bdd {N : ℕ} (d : Fin N → ℂ) :
    BddAbove {r | ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, r = ‖(diagonal d * U).trace‖} := by
  refine ⟨∑ i, ‖d i‖, ?_⟩
  rintro r ⟨U, hU, rfl⟩
  exact diag_trace_bound d hU

noncomputable def phase (z : ℂ) : ℂ := if z = 0 then 1 else star z / (‖z‖ : ℂ)

theorem phase_norm (z : ℂ) : phase z * star (phase z) = 1 := by
  unfold phase
  split_ifs with h
  · simp
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    rw [star_div₀, star_star, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

theorem phase_mul (z : ℂ) : z * phase z = (‖z‖ : ℂ) := by
  unfold phase
  split_ifs with h
  · simp [h]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    rw [mul_div_assoc', Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

theorem lower {N : ℕ} (d : Fin N → ℂ) : (∑ i, ‖d i‖) ≤ traceNorm (diagonal d) := by
  unfold traceNorm
  refine le_csSup (bdd d) ⟨diagonal (fun i => phase (d i)), ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact phase_norm (d i)
  · simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [phase_mul]
    rw [← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]

theorem result : type_of% @OMA.S_mo_140460.main := by
  intro N hN f g _
  have hS : traceNorm (diagonal f * OMA.S_mo_140460.fourier N * diagonal g * (OMA.S_mo_140460.fourier N).conjTranspose) ≤
      (Real.sqrt N)⁻¹ * (∑ i, ‖f i‖) * (∑ j, ‖g j‖) := by
    unfold traceNorm
    refine csSup_le ⟨_, 1, one_mem _, rfl⟩ ?_
    rintro r ⟨U, hU, rfl⟩
    exact trace_bound hN f g hU
  refine hS.trans ?_
  have h1 := lower f
  have h2 := lower g
  have h3 : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
  have h4 : 0 ≤ ∑ i, ‖f i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h5 : 0 ≤ ∑ j, ‖g j‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  calc (Real.sqrt N)⁻¹ * (∑ i, ‖f i‖) * (∑ j, ‖g j‖)
      ≤ (Real.sqrt N)⁻¹ * traceNorm (diagonal f) * (∑ j, ‖g j‖) := by gcongr
    _ ≤ (Real.sqrt N)⁻¹ * traceNorm (diagonal f) * traceNorm (diagonal g) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 (h4.trans h1))

end OMA.Helpers_mo_140460

theorem OMA.solution : type_of% @OMA.S_mo_140460.main := OMA.Helpers_mo_140460.result
