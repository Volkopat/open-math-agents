import OMAReductions.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1

/-! Circle inversion about a point of S on the circle maps the circle to a line and preserves rational distances. -/

open Set Module EuclideanGeometry AffineSubspace

theorem OMA.solution :
    OMA.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1.H2 := by
  intro line S hd c ρ hρ many
  obtain ⟨a, ha, hac⟩ := many.nonempty
  have hca : c ≠ a := fun h => by subst h; simp at hac; linarith
  let F := inversion a (1 : ℝ)
  have hi : Function.Injective F := inversion_injective a one_ne_zero
  let L := perpBisector a (F c)
  have hL : finrank ℝ L.direction ≤ 1 := by
    rw [direction_perpBisector]
    have h := (ℝ ∙ (F c -ᵥ a)).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton (vsub_ne_zero.mpr fun h => hca ((inversion_eq_center one_ne_zero).mp h)),
      finrank_euclideanSpace_fin] at h
    omega
  have hcl {x} (hx : x ≠ a) : F x ∈ L ↔ dist x c = ρ := by
    simpa only [F, L, dist_comm c a, hac] using
      inversion_mem_perpBisector_inversion_iff (R := (1 : ℝ)) one_ne_zero hx hca
  refine (finite_image_iff hi.injOn).mp ((line (F '' (S \ {a})) ?_ L hL ?_).subset ?_)
  · rintro _ ⟨x, ⟨hx, hxa⟩, rfl⟩ _ ⟨y, ⟨hy, hya⟩, rfl⟩
    obtain ⟨u, hu⟩ := hd x hx a ha; obtain ⟨v, hv⟩ := hd y hy a ha; obtain ⟨w, hw⟩ := hd x hx y hy
    exact ⟨w / (u * v), by
      rw [dist_inversion_inversion hxa hya, hu, hv, hw]; push_cast; simp [div_eq_inv_mul]⟩
  · refine ((many.sdiff (finite_singleton a)).image hi.injOn).mono ?_
    rintro _ ⟨x, ⟨⟨hx, h⟩, hxa⟩, rfl⟩
    exact ⟨⟨x, ⟨hx, hxa⟩, rfl⟩, (hcl hxa).mpr h⟩
  · rintro _ ⟨x, ⟨hx, h⟩, rfl⟩
    have hxa : x ≠ a := fun e => h (e ▸ hac)
    exact ⟨⟨x, ⟨hx, hxa⟩, rfl⟩, fun hm => h ((hcl hxa).mp hm)⟩
