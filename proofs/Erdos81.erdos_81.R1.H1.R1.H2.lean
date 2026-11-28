import OMAReductions.R_Erdos81_erdos_81_R1_H1_R1

/-!
Step `Erdos81.erdos_81.R1.H1.R1.H2`: two nonadjacent vertices `a, b` of `S` have a minimal
`a`–`b` separator `C` inside `S`, with `S = L ∪ R ∪ C` and no edges between `L` and `R`.

`S \ {a, b}` separates (every `a`–`b` walk has a second vertex, which is neither `a` nor `b`),
so a separator `C` of least cardinality exists, and it is inclusion-minimal. Let `L` be the set
of vertices reachable from `a` inside `S \ C` and `R = (S \ C) \ L`. Then `b ∈ R` because `C`
separates, and an edge from `L` to `R` would extend a walk and put its endpoint in `L`.
-/

open Finset SimpleGraph

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1_H1_R1.H2 := by
  classical
  intro n G S a b ha hb hab hnadj
  intro sep
  have hsep : ∀ D, sep D ↔ (D ⊆ S ∧ a ∉ D ∧ b ∉ D ∧
      ∀ w : G.Walk a b, (∀ x ∈ w.support, x ∈ S) → ∃ x ∈ w.support, x ∈ D) := fun D => Iff.rfl
  -- a first separator: everything in `S` except `a` and `b`
  have hD0 : sep ((S.erase a).erase b) := by
    rw [hsep]
    refine ⟨fun x hx => (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2, by simp, by simp, ?_⟩
    intro w hw
    cases w with
    | nil => exact absurd rfl hab
    | cons h p =>
      rename_i v
      refine ⟨v, by simp, ?_⟩
      have hvS : v ∈ S := hw v (by simp)
      have hva : v ≠ a := (G.ne_of_adj h).symm
      have hvb : v ≠ b := fun hvb => hnadj (hvb ▸ h)
      simp [Finset.mem_erase, hva, hvb, hvS]
  -- a separator of least cardinality
  set F := S.powerset.filter (fun D => sep D) with hF
  have hD0F : (S.erase a).erase b ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x hx => (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2, hD0⟩
  obtain ⟨C, hCF, hCmin⟩ := Finset.exists_min_image F Finset.card ⟨_, hD0F⟩
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hCF
  obtain ⟨hCS, hCsep⟩ := hCF
  have hC := (hsep C).mp hCsep
  obtain ⟨_, haC, hbC, hCwalk⟩ := hC
  have hminimal : ∀ D : Finset (Fin n), D ⊆ C → sep D → C ⊆ D := by
    intro D hDC hD
    have hDF : D ∈ F := by
      rw [hF, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hDC.trans hCS, hD⟩
    have := hCmin D hDF
    exact (Finset.eq_of_subset_of_card_le hDC this).symm ▸ le_refl _
  -- the side of `a`
  set L := S.filter (fun v => v ∉ C ∧ ∃ w : G.Walk a v, ∀ x ∈ w.support, x ∈ S ∧ x ∉ C) with hL
  set R := (S \ C) \ L with hR
  have hLS : ∀ v ∈ L, v ∈ S ∧ v ∉ C := by
    intro v hv
    rw [hL, Finset.mem_filter] at hv
    exact ⟨hv.1, hv.2.1⟩
  refine ⟨L, R, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hCsep, hminimal⟩
  · ext v
    simp only [Finset.mem_union, hR, Finset.mem_sdiff]
    constructor
    · intro hv
      by_cases hvC : v ∈ C
      · exact Or.inr hvC
      · by_cases hvL : v ∈ L
        · exact Or.inl (Or.inl hvL)
        · exact Or.inl (Or.inr ⟨⟨hv, hvC⟩, hvL⟩)
    · rintro ((hv | ⟨⟨hv, _⟩, _⟩) | hv)
      · exact (hLS v hv).1
      · exact hv
      · exact hCS hv
  · rw [hR]; exact Finset.disjoint_sdiff
  · rw [Finset.disjoint_left]
    intro v hv hvC
    exact (hLS v hv).2 hvC
  · rw [Finset.disjoint_left]
    intro v hv hvC
    rw [hR, Finset.mem_sdiff, Finset.mem_sdiff] at hv
    exact hv.1.2 hvC
  · rw [hL, Finset.mem_filter]
    refine ⟨ha, haC, Walk.nil, ?_⟩
    intro x hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ⟨ha, haC⟩
  · rw [hR, Finset.mem_sdiff, Finset.mem_sdiff]
    refine ⟨⟨hb, hbC⟩, ?_⟩
    intro hbL
    rw [hL, Finset.mem_filter] at hbL
    obtain ⟨_, _, w, hw⟩ := hbL
    obtain ⟨x, hx, hxC⟩ := hCwalk w (fun x hx => (hw x hx).1)
    exact (hw x hx).2 hxC
  · intro x hx y hy hxy
    rw [hR, Finset.mem_sdiff, Finset.mem_sdiff] at hy
    obtain ⟨⟨hyS, hyC⟩, hyL⟩ := hy
    apply hyL
    rw [hL, Finset.mem_filter] at hx ⊢
    obtain ⟨_, _, w, hw⟩ := hx
    refine ⟨hyS, hyC, w.concat hxy, ?_⟩
    intro z hz
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hw z hz
    · exact ⟨hyS, hyC⟩
