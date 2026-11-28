import OMAStatements.S_opg_outward_reloid_of_composition_vs_composition_of_outward_reloids

open OMA.S_opg_outward_reloid_of_composition_vs_composition_of_outward_reloids

private def left (X : Set ℕ) (Y : Set Unit) : Prop :=
  X.Infinite ∧ () ∈ Y

private def right (Y : Set Unit) (Z : Set ℕ) : Prop :=
  () ∈ Y ∧ Z.Infinite

private theorem left_isFuncoid : IsFuncoid left := by
  refine ⟨fun Y => ?_, fun X => ?_, fun X X' Y => ?_, fun X Y Y' => ?_⟩ <;>
    simp [left, Set.infinite_union, or_and_right, and_or_left]

private theorem right_isFuncoid : IsFuncoid right := by
  refine ⟨fun Z => ?_, fun Y => ?_, fun Y Y' Z => ?_, fun Y Z Z' => ?_⟩ <;>
    simp [right, Set.infinite_union, or_and_right, and_or_left]

private theorem left_cofinite :
    Filter.map (fun n : ℕ => (n, ())) Filter.cofinite ≤ rldOut left := by
  apply Filter.le_generate_iff.mpr
  intro K hK
  change {n : ℕ | (n, ()) ∈ K} ∈ Filter.cofinite
  rw [Filter.mem_cofinite]
  by_contra h
  let X : Set ℕ := {n : ℕ | (n, ()) ∈ K}ᶜ
  obtain ⟨⟨n, u⟩, hrect, hn⟩ := hK X Set.univ ⟨h, Set.mem_univ ()⟩
  cases u
  exact hrect.1 hn

private theorem right_cofinite :
    Filter.map (fun n : ℕ => ((), n)) Filter.cofinite ≤ rldOut right := by
  apply Filter.le_generate_iff.mpr
  intro K hK
  change {n : ℕ | ((), n) ∈ K} ∈ Filter.cofinite
  rw [Filter.mem_cofinite]
  by_contra h
  let Z : Set ℕ := {n : ℕ | ((), n) ∈ K}ᶜ
  obtain ⟨⟨u, n⟩, hrect, hn⟩ := hK Set.univ Z ⟨Set.mem_univ (), h⟩
  cases u
  exact hrect.2 hn

private theorem cofinite_prod_le :
    (Filter.cofinite : Filter ℕ) ×ˢ (Filter.cofinite : Filter ℕ) ≤
      rldComp (rldOut right) (rldOut left) := by
  apply Filter.le_generate_iff.mpr
  rintro K ⟨F, hF, G, hG, rfl⟩
  have hX : {n : ℕ | (n, ()) ∈ F} ∈ Filter.cofinite := left_cofinite hF
  have hZ : {n : ℕ | ((), n) ∈ G} ∈ Filter.cofinite := right_cofinite hG
  exact Filter.mem_of_superset (Filter.prod_mem_prod hX hZ) fun _ hp =>
    ⟨(), hp.1, hp.2⟩

private def offDiagonal : Set (ℕ × ℕ) := {p | p.1 ≠ p.2}

private theorem offDiagonal_mem : offDiagonal ∈ rldOut (fcdComp right left) := by
  apply Filter.mem_generate_of_mem
  intro X Z h
  have hX : X.Infinite :=
    ((h ∅).resolve_right (by simp [right])).1
  have hZ : Z.Infinite :=
    ((h Set.univ).resolve_left (by simp [left])).2
  obtain ⟨x, hx⟩ := hX.nonempty
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ Z, z ∉ ({x} : Set ℕ) := by
    by_contra hn
    apply hZ
    apply (Set.finite_singleton x).subset
    intro z hz
    by_contra hz'
    exact hn ⟨z, hz, hz'⟩
  exact ⟨(x, z), ⟨hx, hz⟩, Ne.symm (by simpa using hzx)⟩

private theorem offDiagonal_not_mem :
    offDiagonal ∉ (Filter.cofinite : Filter ℕ) ×ˢ (Filter.cofinite : Filter ℕ) := by
  intro h
  obtain ⟨X, hX, Z, hZ, hsub⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨n, hn⟩ := Filter.nonempty_of_mem (Filter.inter_mem hX hZ)
  exact hsub (show (n, n) ∈ X ×ˢ Z from ⟨hn.1, hn.2⟩) rfl

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_outward_reloid_of_composition_vs_composition_of_outward_reloids.main) := by
  intro h
  exact offDiagonal_not_mem
    (cofinite_prod_le ((h ℕ Unit ℕ left right left_isFuncoid right_isFuncoid) offDiagonal_mem))
