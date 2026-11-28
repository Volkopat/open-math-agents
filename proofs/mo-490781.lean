import OMAStatements.S_mo_490781

open OMA.S_mo_490781

private def weights : Fin 5 → ℤ := ![3, 3, -2, -2, -2]

private def realWeights (i : Fin 5) : ℝ := weights i

private theorem total_nonneg : 0 ≤ ∑ i, realWeights i := by
  suffices h : (0 : ℤ) ≤ ∑ i, weights i by
    unfold realWeights
    rw [← Int.cast_sum]
    exact_mod_cast h
  decide +kernel

private theorem three_nonnegative_triples : cnt 5 3 realWeights = 3 := by
  unfold cnt
  have hfilter :
      ((Finset.univ : Finset (Finset (Fin 5))).filter
        (fun S => S.card = 3 ∧ 0 ≤ ∑ i ∈ S, realWeights i)) =
      ((Finset.univ : Finset (Finset (Fin 5))).filter
        (fun S => S.card = 3 ∧ 0 ≤ ∑ i ∈ S, weights i)) := by
    ext S
    simp only [Finset.mem_filter, realWeights, ← Int.cast_sum]
    norm_cast
  rw [hfilter]
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_490781.main) := by
  intro h
  have hle : A 5 3 ≤ cnt 5 3 realWeights := Nat.sInf_le ⟨realWeights, total_nonneg, rfl⟩
  rw [three_nonnegative_triples, h.2 5 3 (by decide) (by decide) (by decide) (by decide)] at hle
  exact (by decide : ¬ (5 - 5 / 3).choose 3 ≤ 3) hle