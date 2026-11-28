import OMAStatements.S_mo_346020
import Mathlib

open Set MeasureTheory

open OMA.S_mo_346020

private def cubicValue (x : ℝ) : ℝ := x^3-x

private def cubicOneDimension (p : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => cubicValue (p 0)

private theorem cubic_is_analytic : AnalyticOnNhd ℝ cubicOneDimension univ := by
  intro x _
  have h : AnalyticAt ℝ (fun y : Fin 1 → ℝ => y 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).analyticAt x
  change AnalyticAt ℝ (fun y (i : Fin 1) => (y 0 : ℝ)^3-y 0) x
  exact AnalyticAt.pi (fun _ => (h.pow 3).sub h)

private theorem cubic_factor (x y : ℝ) :
    cubicValue y-cubicValue x = (y-x)*(y^2+x*y+x^2-1) := by
  unfold cubicValue
  ring

private theorem far_fibre_singleton (x : Fin 1 → ℝ) (hx : 2 < x 0) :
    (AnalyticFibre cubicOneDimension x).Subsingleton := by
  have unique (y : Fin 1 → ℝ) (hy : y ∈ AnalyticFibre cubicOneDimension x) : y = x := by
    have he : cubicValue (y 0) = cubicValue (x 0) :=
      congrFun hy (0 : Fin 1)
    have hFactor := cubic_factor (x 0) (y 0)
    rw [he,sub_self] at hFactor
    have hp : 0 < (y 0)^2+x 0*y 0+(x 0)^2-1 := by
      nlinarith [sq_nonneg (y 0+x 0/2),mul_pos (sub_pos.mpr hx) (show 0 < x 0+2 by linarith)]
    have hAt : y 0 = x 0 := sub_eq_zero.mp ((mul_eq_zero.mp hFactor.symm).resolve_right hp.ne')
    funext i
    fin_cases i
    exact hAt
  intro y hy z hz
  exact (unique y hy).trans (unique z hz).symm

private theorem middle_fibre_multiple (x : Fin 1 → ℝ)
    (hx : -(1/4 : ℝ) < x 0 ∧ x 0 < 1/4) :
    ¬ (AnalyticFibre cubicOneDimension x).Subsingleton := by
  let a := x 0
  have ha : a^2 < 1/16 := by
    change -(1/4 : ℝ) < a ∧ a < 1/4 at hx
    nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0 < 1/4+a by linarith [hx.1])]
  let d := Real.sqrt (4-3*a^2)
  have hd : d^2 = 4-3*a^2 := Real.sq_sqrt (by linarith)
  let b := (-a+d)/2
  have hb : b^2+a*b+a^2-1 = 0 := by
    dsimp only [b]
    nlinarith only [hd]
  have hba : b ≠ a := by
    intro he
    rw [he] at hb
    nlinarith
  let y : Fin 1 → ℝ := fun _ => b
  have hy : y ∈ AnalyticFibre cubicOneDimension x := by
    change cubicOneDimension y = cubicOneDimension x
    funext i
    change cubicValue b = cubicValue a
    have he := cubic_factor a b
    rw [hb,mul_zero] at he
    exact sub_eq_zero.mp he
  intro h
  have hEq := h hy (show x ∈ AnalyticFibre cubicOneDimension x from rfl)
  exact hba (congrFun hEq (0 : Fin 1))

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_346020.main) := by
  intro h
  obtain ⟨U,hU,hConst⟩ := h 1 1 cubicOneDimension cubic_is_analytic
  have hAE : ∀ᵐ p ∂volume, p ∈ U := by
    rw [ae_iff]
    exact hU
  let M : Set (Fin 1 → ℝ) := (fun p => p 0) ⁻¹' Ioo (-1/4) (1/4)
  let R : Set (Fin 1 → ℝ) := (fun p => p 0) ⁻¹' Ioi 2
  have hMOpen : IsOpen M := isOpen_Ioo.preimage (continuous_apply 0)
  have hROpen : IsOpen R := isOpen_Ioi.preimage (continuous_apply 0)
  have hMNonempty : M.Nonempty :=
    ⟨fun _ => 0,by norm_num [M]⟩
  have hRNonempty : R.Nonempty := ⟨fun _ => 3,by norm_num [R]⟩
  obtain ⟨p,hpM,hpU⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hMOpen.measure_pos volume hMNonempty).ne' (ae_restrict_of_ae hAE)
  obtain ⟨q,hqR,hqU⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hROpen.measure_pos volume hRNonempty).ne' (ae_restrict_of_ae hAE)
  have hRight := (Cardinal.mk_le_one_iff_set_subsingleton).2 (far_fibre_singleton q hqR)
  rw [← hConst p hpU q hqU] at hRight
  have hpRange : -(1/4 : ℝ) < p 0 ∧ p 0 < 1/4 := by
    simpa [M,neg_div] using hpM
  exact middle_fibre_multiple p hpRange ((Cardinal.mk_le_one_iff_set_subsingleton).1 hRight)
