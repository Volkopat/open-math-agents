import OMAStatements.S_mo_222329

-- Retains @Genbox’s proof #29879; finite eventual conjunction uses the standard filter API.

open Filter Matrix OMA.S_mo_222329
open scoped Topology BigOperators ComplexOrder

private theorem finite_right_translate {G : Type} [Group G] [DecidableEq G]
    (F : ℕ → Finset G) (hF : isLeftFolnerSequence F) (E : Finset G) :
    ∃ n a, ∀ e ∈ E, e * a ∈ F n := by
  let δ : ℝ := 1 / ((E.card : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have each (e : G) : ∀ᶠ n in atTop,
      ((folnerSymmetricDifference (F n) e).card : ℝ) / (F n).card < δ :=
    (hF.2 e).eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset E).mpr (fun e _ => each e)).exists
  let bad (e : G) := (F n).filter fun a => e * a ∉ F n
  have hbad (e : G) : (bad e).card ≤ (folnerSymmetricDifference (F n) e).card := by
    apply Finset.card_le_card_of_injOn (fun a => e * a)
    · intro a ha
      have ⟨ha', hnot⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨a, ha', rfl⟩, hnot⟩)
    · intro a _ b _ hab
      exact mul_left_cancel hab
  have hpos : (0 : ℝ) < (F n).card := by exact_mod_cast (hF.1 n).card_pos
  have hbound (e : G) (he : e ∈ E) : ((bad e).card : ℝ) ≤ δ * (F n).card :=
    (show ((bad e).card : ℝ) ≤ (folnerSymmetricDifference (F n) e).card by
      exact_mod_cast hbad e).trans ((div_lt_iff₀ hpos).mp (hn e he)).le
  have hprod : (E.card : ℝ) * δ < 1 := by
    dsimp [δ]
    rw [← mul_div_assoc, mul_one]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hcard : (E.biUnion bad).card < (F n).card := by
    have hle : (E.biUnion bad).card ≤ ∑ e ∈ E, (bad e).card := Finset.card_biUnion_le
    have hreal : ((E.biUnion bad).card : ℝ) < (F n).card := by
      calc
        _ ≤ ∑ e ∈ E, ((bad e).card : ℝ) := by exact_mod_cast hle
        _ ≤ ∑ e ∈ E, δ * (F n).card := Finset.sum_le_sum hbound
        _ = (E.card : ℝ) * δ * (F n).card := by simp [mul_assoc, nsmul_eq_mul]
        _ < (F n).card := by simpa using (mul_lt_mul_of_pos_right hprod hpos)
    exact_mod_cast hreal
  have hnon : ¬ F n ⊆ E.biUnion bad := fun hsub => (not_le_of_gt hcard) (Finset.card_le_card hsub)
  obtain ⟨a, ha, hnot⟩ := Finset.not_subset.mp hnon
  refine ⟨n, a, fun e he => ?_⟩
  by_contra hfail
  exact hnot (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨ha, hfail⟩⟩)

theorem OMA.solution : type_of% @OMA.S_mo_222329.main := by
  intro G _ _ _ F hF φ hφ E
  obtain ⟨n, a, ha⟩ := finite_right_translate F hF E
  let f : E → F n := fun e => ⟨(e : G) * a, ha e e.property⟩
  have hmat : (positiveGroupKernel φ (F n)).submatrix f f = positiveGroupKernel φ E := by
    ext u v
    change φ (((u : G) * a) * ((v : G) * a)⁻¹) = φ ((u : G) * (v : G)⁻¹)
    simp [mul_assoc]
  rw [← hmat]
  exact (hφ n).submatrix f