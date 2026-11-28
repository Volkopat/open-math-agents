import FormalConjectures.ErdosProblems.«1069»

/-! Rows and columns are the level sets of the two coordinate projections on the grid. -/

open EuclideanGeometry

private def coords (u : Fin 2 → ℝ) : ℝ² := WithLp.toLp 2 u

private noncomputable abbrev project (i : Fin 2) : ℝ² →ₗ[ℝ] ℝ := EuclideanSpace.projₗ i

private noncomputable def axis (i : Fin 2) (r : ℝ) : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' (coords fun _ => r) (project i).ker

private lemma mem_axis (i : Fin 2) (r : ℝ) (p : ℝ²) : p ∈ axis i r ↔ p i = r := by
  simp [axis, coords, AffineSubspace.mem_mk', vsub_eq_sub, sub_eq_zero]

private lemma axis_line (i : Fin 2) (r : ℝ) : IsLine (axis i r) := by
  have surj : Function.Surjective (project i) := fun y => ⟨coords (fun _ => y), rfl⟩
  have rank := (project i).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace, Fintype.card_fin] at rank
  unfold IsLine axis
  rw [AffineSubspace.direction_mk']
  omega

private lemma rev_ne (i : Fin 2) : i.rev ≠ i := by
  fin_cases i <;> decide

theorem OMA.solution : type_of% @Erdos1069.erdos_1069.variants.lattice := by
  classical
  intro m hm
  let point (u : Fin 2 → Fin m) := coords (fun i => ((u i).val : ℝ))
  have hinj : Function.Injective point := by
    intro u v huv
    funext i
    exact Fin.ext (Nat.cast_injective (congrArg (fun p : ℝ² => p i) huv))
  let grid := Finset.univ.map ⟨point, hinj⟩
  refine ⟨grid, by simp [grid], ?_⟩
  let line (u : Fin 2 × Fin m) := axis u.1 u.2.val
  have linj : Function.Injective line := by
    rintro ⟨i, u⟩ ⟨j, v⟩ h
    have test (y : ℝ) : (if j = i then (u.val : ℝ) else y) = (v.val : ℝ) := by
      let p := coords (fun t => if t = i then (u.val : ℝ) else y)
      have hu : p ∈ line (i, u) := (mem_axis i _ p).mpr (by simp [p, coords])
      have hv : p ∈ line (j, v) := h ▸ hu
      exact (mem_axis j _ p).mp hv
    have hv : (u.val : ℝ) = v.val := by simpa using test u.val
    refine Prod.ext ?_ (Fin.ext (by exact_mod_cast hv))
    by_contra hij
    have he := test (v.val + 1)
    simp [Ne.symm hij] at he
  have subset : Set.range line ⊆ Erdos1069.richLines grid m := by
    rintro _ ⟨⟨i, u⟩, rfl⟩
    refine ⟨axis_line _ _, ?_⟩
    let row (v : Fin m) (j : Fin 2) := if j = i then u else v
    have rinj : Function.Injective row := by
      intro v w h
      simpa [row, rev_ne] using congrFun h i.rev
    have included : Set.range (point ∘ row) ⊆ (grid : Set ℝ²) ∩ (line (i, u) : Set ℝ²) := by
      rintro _ ⟨v, rfl⟩
      exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ (row v)),
        (mem_axis i _ _).mpr (by simp [point, row, coords, PiLp.toLp_apply])⟩
    simpa [Set.ncard_range_of_injective (hinj.comp rinj), Nat.card_eq_fintype_card] using
      Set.ncard_le_ncard included ((Finset.finite_toSet grid).inter_of_left _)
  simpa [Set.ncard_range_of_injective linj, Nat.card_eq_fintype_card] using
    Set.ncard_le_ncard subset (Erdos1069.richLines_finite grid hm)
