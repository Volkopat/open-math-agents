import FormalConjectures.ErdosProblems.«91»

open Erdos91 EuclideanGeometry

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.dissimilar_circleSeven_wheelSeven := by
  rintro ⟨f, hf⟩
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let c : ℝ² := !₂[r * Real.cos (Real.pi / 7), r * Real.sin (4 * Real.pi / 7)]
  have h (u : ℝ) (hu : !₂[u, Real.sqrt 3 / 2] ∈ wheelSeven) :
      (u - f c 0)^2 + (Real.sqrt 3 / 2 - f c 1)^2 = (Dilation.ratio f * r)^2 := by
    obtain ⟨q, hq, eq⟩ : !₂[u, Real.sqrt 3 / 2] ∈ f '' (circleSeven : Set ℝ²) := hf ▸ hu
    have hd := congrArg (· ^ 2) (Dilation.dist_eq f q c)
    rw [eq, mul_pow] at hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, c] at hd
    linear_combination hd + (Dilation.ratio f : ℝ)^2 * r^2 *
      Real.sin_sq_add_cos_sq (2 * Real.pi * k / 7)
  nlinarith [h 0 (by simp [wheelSeven]), h 1 (by simp [wheelSeven]), h 2 (by simp [wheelSeven])]
