import FormalConjectures.ErdosProblems.«757»

/-! A finite certificate for the strict upper bound in Erdős problem 757. -/

open scoped Pointwise
namespace SidonWitness

-- The fourteen-point block of Ma and Tang, arXiv:2602.23282, Lemma 5.1.
def block : Finset ℤ :=
  {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_check :
    ∀ t ∈ block.powersetCard 4, 11 ≤ (t - t).card := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nine_check : ∀ t ∈ block.powersetCard 9,
    ∃ x ∈ t, ∃ y ∈ t, x < y ∧ 2 * y - x ∈ t := by decide +kernel

def realBlock : Set ℝ := (fun z : ℤ => (z : ℝ)) '' (block : Set ℤ)

theorem lift_subset {s : Set ℝ} (hs : s ⊆ realBlock) :
    ∃ t : Finset ℤ, t ⊆ block ∧ s = (fun z : ℤ => (z : ℝ)) '' (t : Set ℤ) := by
  obtain ⟨u, hu, rfl⟩ := Set.subset_image_iff.1 hs
  exact ⟨_, (block.finite_toSet.subset hu).toFinset_subset.2 hu, by simp⟩

theorem four_diffs (s : Set ℝ) (hs : s ⊆ realBlock) (hc : s.ncard = 4) :
    11 ≤ (s - s).ncard := by
  obtain ⟨t, ht, rfl⟩ := lift_subset hs
  rw [Set.ncard_image_of_injective _ Int.cast_injective, Set.ncard_coe_finset] at hc
  erw [← Set.image_sub (Int.castAddHom ℝ), ← Finset.coe_sub,
    Set.ncard_image_of_injective _ Int.cast_injective, Set.ncard_coe_finset]
  exact four_check t (Finset.mem_powersetCard.mpr ⟨ht, hc⟩)

theorem sidon_bound (s : Set ℝ) (hs : s ⊆ realBlock) (hSidon : IsSidon s) :
    s.ncard ≤ 8 := by
  obtain ⟨t, ht, rfl⟩ := lift_subset hs
  rw [Set.ncard_image_of_injective _ Int.cast_injective, Set.ncard_coe_finset]
  by_contra! h
  obtain ⟨u, hu, huc⟩ := Finset.exists_subset_card_eq (show 9 ≤ t.card by omega)
  obtain ⟨x, hx, y, hy, hxy, hz⟩ := nine_check u
    (Finset.mem_powersetCard.mpr ⟨hu.trans ht, huc⟩)
  have member (z : ℤ) (hz : z ∈ u) :
      (z : ℝ) ∈ (fun w : ℤ => (w : ℝ)) '' (t : Set ℤ) := ⟨z, hu hz, rfl⟩
  have he : (x : ℝ) + ((2 * y - x : ℤ) : ℝ) = y + y := by push_cast; ring
  have hne : (x : ℝ) ≠ y := by exact_mod_cast hxy.ne
  rcases hSidon _ (member x hx) _ (member y hy) _ (member _ hz) _ (member y hy) he with hh | hh <;>
    exact hne hh.1

end SidonWitness

open SidonWitness in
theorem OMA.solution : type_of% @Erdos757.erdos_757.variants.upperBound := by
  intro A
  have hnon : {c : ℝ | Erdos757.IsAdmissible c}.Nonempty :=
    ⟨0, fun _ _ => ⟨∅, Set.empty_subset _, by simp [IsSidon], by simp⟩⟩
  apply lt_of_le_of_lt (csSup_le hnon ?_) (show (4/7 : ℝ) < 3/5 by norm_num)
  intro c hc
  change Erdos757.IsAdmissible c at hc
  obtain ⟨s, hs, hSidon, hlarge⟩ := hc (A := realBlock) (block.finite_toSet.image _) four_diffs
  have hsmall : (s.ncard : ℝ) ≤ 8 := by exact_mod_cast sidon_bound s hs hSidon
  change c * realBlock.ncard ≤ _ at hlarge
  rw [realBlock, Set.ncard_image_of_injective _ Int.cast_injective, Set.ncard_coe_finset,
    show block.card = 14 by decide +kernel] at hlarge
  norm_num at hlarge
  linarith
