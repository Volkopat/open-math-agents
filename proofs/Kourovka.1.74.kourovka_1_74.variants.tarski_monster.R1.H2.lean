import OMAReductions.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1
import Mathlib.Topology.Algebra.FilterBasis

open Set Filter
open scoped Pointwise

theorem OMA.solution : OMA.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1.H2 := by
  intro G _ 𝓕 hOne hMul hInv hConj hNondiscrete hProper
  let B : GroupFilterBasis G :=
    { sets := 𝓕.sets
      nonempty := ⟨univ, univ_mem⟩
      inter_sets := fun hu hv => ⟨_, inter_mem hu hv, Subset.rfl⟩
      one' := hOne _
      mul' := by
        intro U hU
        obtain ⟨V, hV, hv⟩ := hMul U hU
        refine ⟨V, hV, ?_⟩
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
        exact hv x hx y hy
      inv' := fun hU => ⟨_, hInv _ hU, Subset.rfl⟩
      conj' := by
        intro g U hU
        exact ⟨_, hConj g U hU, Subset.rfl⟩ }
  letI := B.topology
  have hNhds : nhds (1 : G) = 𝓕 := by
    rw [B.nhds_one_eq]
    apply Filter.ext
    intro U
    rw [FilterBasis.mem_filter_iff]
    exact ⟨fun ⟨V, hV, hVU⟩ => mem_of_superset hV hVU, fun hU => ⟨U, hU, Subset.rfl⟩⟩
  refine ⟨B.topology, B.isTopologicalGroup, ?_, ?_⟩
  · intro h
    letI := h
    exact hNondiscrete (hNhds.symm.trans (congrFun (nhds_discrete G) 1))
  · obtain ⟨U, hU, hUne⟩ := hProper
    have hOneInterior : (1 : G) ∈ interior U :=
      mem_interior_iff_mem_nhds.mpr (hNhds.symm ▸ hU)
    refine ⟨interior U, isOpen_interior, ⟨1, hOneInterior⟩, ?_⟩
    intro hall
    apply hUne
    exact eq_univ_of_univ_subset (hall ▸ interior_subset)