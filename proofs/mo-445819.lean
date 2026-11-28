import OMAStatements.S_mo_445819

open OMA.S_mo_445819
open Metric

private theorem coord_sq_of_mem_sphere (x : E 1) (hx : x ∈ sphere (0 : E 1) 1) :
    x 0 ^ 2 = 1 := by
  have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
  simpa [Fin.sum_univ_one, hn] using (EuclideanSpace.real_norm_sq_eq x).symm

private theorem eq_zero_of_orthogonal (x v : E 1) (hx : x ∈ sphere (0 : E 1) 1)
    (h : inner ℝ x v = 0) : v = 0 := by
  have hx0 : x 0 ≠ 0 := by
    intro hx0
    simpa [hx0] using coord_sq_of_mem_sphere x hx
  have hv : v 0 * x 0 = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_one, mul_comm]
      using h
  have hv0 := (mul_eq_zero.mp hv).resolve_right hx0
  ext i
  fin_cases i
  exact hv0

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_445819.main) := by
  intro h
  let u : E 1 := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by simp [EuclideanSpace.real_norm_sq_eq, u]
    nlinarith [norm_nonneg u]
  let f : E 1 → E 1 := fun _ => u
  have hf : IsRPEmbedding (n := 0) (N := 0) f := by
    refine ⟨contDiff_const, fun _ _ => ⟨hu, rfl⟩, ?_, ?_⟩
    · intro x hx y hy _
      have hsq : (y 0 - x 0) * (y 0 + x 0) = 0 := by
        nlinarith [coord_sq_of_mem_sphere x hx, coord_sq_of_mem_sphere y hy]
      rcases mul_eq_zero.mp hsq with hsame | hopp
      · left
        ext i
        fin_cases i
        exact sub_eq_zero.mp hsame
      · right
        ext i
        fin_cases i
        change y 0 = -(x 0)
        linarith
    · intro x hx v hv _
      exact eq_zero_of_orthogonal x v hx hv
  obtain ⟨x, hx, v, hv, hperp, _⟩ := h 0 0 f hf
  rw [eq_zero_of_orthogonal x v hx hperp, norm_zero] at hv
  norm_num at hv