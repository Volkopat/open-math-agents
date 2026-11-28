import OMAReductions.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1
import Mathlib

/-! Inversion about a point on the circle sends the remaining points of the circle to a line and keeps pairwise distances rational after removing the center. -/

open Set Module EuclideanGeometry AffineSubspace

theorem OMA.solution :
    OMA.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1.H2 := by
  intro line S hd c ρ hρ many
  obtain ⟨a, ha, hac⟩ := many.nonempty
  have hca : c ≠ a := by
    intro h
    subst c
    rw [dist_self] at hac
    linarith
  let F := inversion a 1
  have hinj : Function.Injective F := inversion_injective a one_ne_zero
  let L := perpBisector a (F c)
  have hFa : F c ≠ a := fun h => hca ((inversion_eq_center one_ne_zero).mp h)
  have hL : finrank ℝ L.direction ≤ 1 := by
    let V := ℝ ∙ (F c -ᵥ a)
    have hV : finrank ℝ V = 1 := finrank_span_singleton (vsub_ne_zero.mpr hFa)
    have hsum := V.finrank_add_finrank_orthogonal
    rw [hV, finrank_euclideanSpace_fin] at hsum
    change finrank ℝ (perpBisector a (F c)).direction ≤ 1
    rw [direction_perpBisector]
    change finrank ℝ Vᗮ ≤ 1
    omega
  have circleLine {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ a) :
      F x ∈ L ↔ dist x c = ρ := by
    have h := inversion_mem_perpBisector_inversion_iff
      (R := (1 : ℝ)) one_ne_zero hx hca
    simpa only [F, L, dist_comm c a, hac] using h
  let T := F '' (S \ {a})
  have hrat : ∀ x ∈ T, ∀ y ∈ T, ∃ q : ℚ, dist x y = (q : ℝ) := by
    rintro _ ⟨x, ⟨hx, hxa⟩, rfl⟩ _ ⟨y, ⟨hy, hya⟩, rfl⟩
    obtain ⟨u, hu⟩ := hd x hx a ha
    obtain ⟨v, hv⟩ := hd y hy a ha
    obtain ⟨w, hw⟩ := hd x hx y hy
    refine ⟨1 / (u * v) * w, ?_⟩
    change dist (inversion a 1 x) (inversion a 1 y) = _
    rw [dist_inversion_inversion (by simpa using hxa) (by simpa using hya), hu, hv, hw]
    push_cast
    simp
  have hmany : (T ∩ (L : Set _)).Infinite := by
    apply ((many.sdiff (finite_singleton a)).image hinj.injOn).mono
    rintro _ ⟨x, ⟨⟨hx, hdist⟩, hxa⟩, rfl⟩
    exact ⟨⟨x, ⟨hx, hxa⟩, rfl⟩, (circleLine (by simpa using hxa)).mpr hdist⟩
  apply (finite_image_iff hinj.injOn).mp
  apply (line T hrat L hL hmany).subset
  rintro _ ⟨x, ⟨hx, hdist⟩, rfl⟩
  have hxa : x ≠ a := fun h => hdist (h.symm ▸ hac)
  exact ⟨⟨x, ⟨hx, by simpa using hxa⟩, rfl⟩, fun hm => hdist ((circleLine hxa).mp hm)⟩