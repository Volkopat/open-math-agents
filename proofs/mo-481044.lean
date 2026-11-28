import OMAStatements.S_mo_481044
import Mathlib

open Finset

open OMA.S_mo_481044



theorem OMA.solution : type_of% @OMA.S_mo_481044.main := by
  intro d hd
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  have h₀₁ : i₀ ≠ i₁ := by
    intro h
    have he := congrArg Fin.val h
    change 0 = 1 at he
    omega
  let u (t : ℝ) (x : Fin d → ℝ) (i : Fin d) :=
    if i = i₀ then Real.sin ((2 * Real.pi) * (x i₁ - t))
    else if i = i₁ then 1 else 0
  let C (t : ℝ) (x : Fin d → ℝ) :=
    (2 * Real.pi) * Real.cos ((2 * Real.pi) * (x i₁ - t))
  have hut (t : ℝ) (x : Fin d → ℝ) (i : Fin d) :
      deriv (fun s => u s x i) t = if i = i₀ then -C t x else 0 := by
    by_cases hi : i = i₀
    · simp only [u, hi, if_true, C]
      have harg : HasDerivAt (fun s => (2 * Real.pi) * (x i₁ - s)) (-(2 * Real.pi)) t := by
        simpa using (((hasDerivAt_id t).const_sub (x i₁)).const_mul (2 * Real.pi))
      convert harg.sin.deriv using 1
      ring
    · by_cases hi' : i = i₁
      · subst i
        simp [u, h₀₁.symm]
      · simp [u, hi, hi']
  have hux (t : ℝ) (x : Fin d → ℝ) (i j : Fin d) :
      partialSpace u t x i j = if i = i₀ ∧ j = i₁ then C t x else 0 := by
    by_cases hi : i = i₀
    · by_cases hj : j = i₁
      · subst j
        simp only [partialSpace, u, hi, if_true, true_and, Function.update_self, C]
        have harg : HasDerivAt (fun s => (2 * Real.pi) * (s - t)) (2 * Real.pi) (x i₁) := by
          simpa using (((hasDerivAt_id (x i₁)).sub_const t).const_mul (2 * Real.pi))
        convert harg.sin.deriv using 1
        ring
      · simp [partialSpace, u, hi, hj, Function.update_of_ne (Ne.symm hj)]
    · by_cases hi' : i = i₁
      · subst i
        simp [partialSpace, u, h₀₁.symm]
      · simp [partialSpace, u, hi, hi']
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · simp only [u, hi, if_true]
      fun_prop
    · by_cases hi' : i = i₁
      · subst i
        simpa only [u, h₀₁.symm, if_false, if_true] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)))
      · simpa only [u, hi, hi', if_false] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)))
  · intro t x k
    funext i
    by_cases hi : i = i₀
    · simp only [u, hi, if_true]
      rw [show (2 * Real.pi) * (x i₁ + ↑(k i₁) - t) =
        (2 * Real.pi) * (x i₁ - t) + ↑(k i₁) * (2 * Real.pi) by ring,
        Real.sin_add_int_mul_two_pi]
    · simp [u, hi]
  · intro t x i
    rw [hut]
    simp_rw [hux]
    by_cases hi : i = i₀
    · have hu₁ : u t x i₁ = 1 := by simp [u, h₀₁.symm]
      simp [hi, mul_ite, hu₁]
    · simp [hi]
  · intro t x
    apply sum_eq_zero
    intro i _
    rw [hux]
    split
    · rename_i h
      exact (h₀₁ (h.1.symm.trans h.2)).elim
    · rfl
  · refine ⟨0, fun _ => 0, i₀, ?_⟩
    have hh : deriv (fun s => u s (fun _ : Fin d => 0) i₀) 0 = -(2 * Real.pi) := by
      simpa [C] using hut 0 (fun _ => 0) i₀
    rw [hh]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_pos.ne')
