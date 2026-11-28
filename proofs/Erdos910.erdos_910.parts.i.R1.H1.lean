import OMAReductions.R_Erdos910_erdos_910_parts_i_R1

/-!
Shorter compactness-transfer proof for the line-segment case of Erdos 910.
Original construction by @luciusacarr, PR #26526, written with Claude Code.
The construction is unchanged: use a half-open segment when X is compact,
and a closed segment otherwise. @rodolfoquint shortened only the helper
using Mathlib's invariance of compactness under a homeomorphism.
-/

namespace OMA.E910H1

variable {n : ℕ}

theorem not_homeo_of_compact {X Y : Set (EuclideanSpace ℝ (Fin n))}
    (hY : IsCompact Y ↔ ¬ IsCompact X) : ¬ Nonempty (Y ≃ₜ X) := by
  rintro ⟨e⟩
  have h : IsCompact Y ↔ IsCompact X := by
    rw [isCompact_iff_isCompact_univ (s := Y), isCompact_iff_isCompact_univ (s := X)]
    simpa only [Set.preimage_univ] using (e.isCompact_preimage (s := Set.univ))
  tauto

end OMA.E910H1

open OMA.E910H1 in
theorem OMA.solution : OMA.R_Erdos910_erdos_910_parts_i_R1.H1 := by
  intro n X _hX _hnt ⟨a, b, hab, hseg⟩
  set L := AffineMap.lineMap (k := ℝ) a b with hL
  have hLc : Continuous L := AffineMap.lineMap_continuous
  have hinj : Function.Injective L := AffineMap.lineMap_injective ℝ hab
  have hsegL : segment ℝ a b = L '' Set.Icc 0 1 := segment_eq_image_lineMap ℝ a b
  have hL0 : L 0 = a := AffineMap.lineMap_apply_zero a b
  have hL1 : L 1 = b := AffineMap.lineMap_apply_one a b
  by_cases hX : IsCompact X
  · -- the half-open segment
    refine ⟨L '' Set.Ico 0 1, ?_, ?_, ?_, ?_⟩
    · exact (Set.image_mono Set.Ico_subset_Icc_self).trans (hsegL ▸ hseg)
    · exact (isConnected_Ico (by norm_num : (0 : ℝ) < 1)).image _ hLc.continuousOn
    · refine ⟨L 0, ⟨0, by norm_num, rfl⟩, L (1 / 2), ⟨1 / 2, by norm_num, rfl⟩, ?_⟩
      intro h
      have := hinj h
      norm_num at this
    · apply not_homeo_of_compact
      refine ⟨fun h => absurd hX ?_, fun h => absurd hX h⟩
      intro _
      -- b is in the closure of L '' [0,1) but not in it
      have hcl : b ∈ closure (L '' Set.Ico 0 1) := by
        have hsub : L '' closure (Set.Ico (0 : ℝ) 1) ⊆ closure (L '' Set.Ico 0 1) :=
          image_closure_subset_closure_image hLc
        apply hsub
        refine ⟨1, ?_, hL1⟩
        rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
        exact ⟨by norm_num, le_refl _⟩
      rw [h.isClosed.closure_eq] at hcl
      obtain ⟨t, ht, hteq⟩ := hcl
      rw [← hL1] at hteq
      have := hinj hteq
      exact absurd ht.2 (by rw [this]; exact lt_irrefl 1)
  · -- the closed segment
    refine ⟨segment ℝ a b, hseg, ?_, ⟨a, left_mem_segment ℝ a b, b, right_mem_segment ℝ a b, hab⟩, ?_⟩
    · rw [hsegL]
      exact (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image _ hLc.continuousOn
    · apply not_homeo_of_compact
      refine ⟨fun _ => hX, fun _ => ?_⟩
      rw [hsegL]
      exact isCompact_Icc.image hLc
