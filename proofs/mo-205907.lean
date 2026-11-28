import OMAStatements.S_mo_205907

open Polynomial Polynomial.Chebyshev

private noncomputable def affine (a b : ℝ) : ℝ[X] := C b - C a * X

private theorem affine_eval (a b x : ℝ) : (affine a b).eval x = b-a*x := by
  simp [affine]

private theorem affine_comp_degree (f : ℝ[X]) (a b : ℝ) :
    (f.comp (affine a b)).natDegree ≤ f.natDegree := by
  have ha : (affine a b).natDegree ≤ 1 := by
    unfold affine
    exact (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  exact natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left f.natDegree ha)

private theorem degree_criterion (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (d : ℕ) :
    (2/a ≤ (T ℝ d).eval (1/a)) ↔
      ⌈Real.arcosh (2/a) / Real.arcosh (1/a)⌉₊ ≤ d := by
  have h₁ : 1 < 1/a := (lt_div_iff₀ ha).2 (by linarith)
  have h₂ : 1 ≤ 2/a := (le_div_iff₀ ha).2 (by linarith)
  have hp := Real.arcosh_pos h₁
  have ht : (T ℝ d).eval (1/a) = Real.cosh ((d:ℝ)*Real.arcosh (1/a)) := by
    calc
      _ = (T ℝ d).eval (Real.cosh (Real.arcosh (1/a))) := by rw [Real.cosh_arcosh h₁.le]
      _ = _ := by simp [T_real_cosh]
  rw [Nat.ceil_le, div_le_iff₀ hp, ht]
  conv_lhs => lhs; rw [← Real.cosh_arcosh h₂]
  rw [Real.cosh_le_cosh, abs_of_nonneg (Real.arcosh_nonneg h₂), abs_of_nonneg (by positivity)]

theorem OMA.solution : type_of% @OMA.S_mo_205907.main := by
  intro a ha ha₁ d
  rw [← degree_criterion a ha ha₁ d]
  have h₁ : 1 ≤ 1/a := (le_div_iff₀ ha).2 (by linarith)
  constructor
  · rintro ⟨f,hdeg,hzero,hband⟩
    let P : ℝ[X] := C (2/a) * (1 - f.comp (affine a 1))
    have hPdeg : P.degree ≤ d := degree_le_of_natDegree_le (by
      apply (natDegree_C_mul_le _ _).trans
      exact (natDegree_sub_le _ _).trans (max_le (by simp) ((affine_comp_degree f a 1).trans hdeg)))
    have hPbnd : ∀ t ∈ Set.Icc (-1) 1, |P.eval t| ≤ 1 := by
      intro t ht
      have hx : 1-a*t ∈ Set.Icc (1-a) (1+a) := by
        constructor
        · nlinarith [mul_le_mul_of_nonneg_left ht.2 ha.le]
        · nlinarith [mul_le_mul_of_nonneg_left ht.1 ha.le]
      have hy := hband _ hx
      have habs : |1-f.eval (1-a*t)| ≤ a/2 :=
        abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
      simp only [P, eval_mul, eval_C, eval_sub, eval_one, eval_comp, affine_eval]
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2/a)]
      calc
        _ ≤ (2/a)*(a/2) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ = 1 := by field_simp
    have heval : P.eval (1/a) = 2/a := by
      have harg : 1-a*(1/a) = 0 := by field_simp; ring
      simp only [P, eval_mul, eval_C, eval_sub, eval_one, eval_comp, affine_eval, harg, hzero,
        sub_zero, mul_one]
    have h := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) h₁ hPdeg hPbnd
    change P.eval (1/a) ≤ (T ℝ d).eval (1/a) at h
    rwa [heval] at h
  · intro hd
    let D := (T ℝ d).eval (1/a)
    have hD : 0 < D := lt_of_lt_of_le (by positivity) hd
    let f : ℝ[X] := 1 - C D⁻¹ * (T ℝ d).comp (affine (1/a) (1/a))
    refine ⟨f, ?_, ?_, ?_⟩
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · apply (natDegree_C_mul_le _ _).trans
        apply (affine_comp_degree _ _ _).trans
        simp [natDegree_T]
    · simp only [f, eval_sub, eval_one, eval_mul, eval_C, eval_comp, affine_eval,
        mul_zero, sub_zero]
      change 1-D⁻¹*D = 0
      rw [inv_mul_cancel₀ hD.ne', sub_self]
    · intro x hx
      let t := 1/a-(1/a)*x
      have ht : a*t = 1-x := by dsimp [t]; field_simp
      have ht1 : |t| ≤ 1 := by
        apply abs_le.mpr
        constructor
        · apply le_of_mul_le_mul_left _ ha
          rw [ht]
          linarith [hx.2]
        · apply le_of_mul_le_mul_left _ ha
          rw [ht]
          linarith [hx.1]
      have hT := abs_eval_T_real_le_one (d:ℤ) ht1
      have hInv : D⁻¹ ≤ a/2 := by
        rw [inv_eq_one_div, div_le_iff₀ hD]
        have hmul := mul_le_mul_of_nonneg_right hd (show 0 ≤ a/2 by positivity)
        have he : (2/a)*(a/2) = 1 := by field_simp
        rw [he] at hmul
        linarith
      have hErr : |D⁻¹*(T ℝ d).eval t| ≤ a/2 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hD)]
        exact (mul_le_of_le_one_right (by positivity) hT).trans hInv
      simp only [f, eval_sub, eval_one, eval_mul, eval_C, eval_comp, affine_eval]
      change 1-D⁻¹*(T ℝ d).eval t ∈ Set.Icc (1-a/2) (1+a/2)
      exact ⟨by linarith [(abs_le.mp hErr).2], by linarith [(abs_le.mp hErr).1]⟩