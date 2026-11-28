import FormalConjectures.ErdosProblems.«138»

/-! Shorter proof of `Erdos138.monoAP_guarantee_set_nonempty` via Hales–Jewett. -/

theorem OMA.solution : type_of% @Erdos138.monoAP_guarantee_set_nonempty := by
  classical
  intro r k
  obtain ⟨ι, fi, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let := fi
  let N := 1 + Fintype.card ι * k
  refine ⟨N, fun coloring => ?_⟩
  let pt (w : ι → Fin k) : Finset.Icc 1 N := ⟨1 + ∑ i, (w i).val, Finset.mem_Icc.mpr ⟨by omega,
    Nat.add_le_add_left (by simpa [nsmul_eq_mul] using
      (Finset.sum_le_sum fun i _ => (w i).isLt.le : (∑ i, (w i).val) ≤ ∑ _ : ι, k)) 1⟩⟩
  obtain ⟨line, col, mono⟩ := hj fun w => coloring (pt w)
  let fx i : ℕ := ((line.idxFun i).map Fin.val).getD 0
  let wt i : ℕ := if line.idxFun i = none then 1 else 0
  let a := 1 + ∑ i, fx i
  let d := ∑ i, wt i
  have hd : 0 < d := by
    obtain ⟨i, hi⟩ := line.proper
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i, Finset.mem_univ i, by simp [wt, hi]⟩
  have val (j : Fin k) : (pt (line j)).val = a + j.val * d := by
    have dig i : (line j i).val = fx i + j.val * wt i := by
      cases h : line.idxFun i <;> simp [Combinatorics.Line.coe_apply, fx, wt, h]
    change 1 + ∑ i, (line j i).val = (1 + ∑ i, fx i) + j.val * ∑ i, wt i
    simp only [dig, Finset.sum_add_distrib, Finset.mul_sum, Nat.add_assoc]
  let f : Fin k → ↥(Finset.Icc 1 N) := fun j => pt (line j)
  have hf : Function.Injective f := fun i j h => Fin.ext <| by
    have := congrArg Subtype.val h; simp [f, val, hd.ne'] at this; exact this
  refine ⟨col, Set.range f, ⟨a, d, ?_, ?_⟩, by rintro _ ⟨j, rfl⟩; exact mono j⟩
  · rw [ENat.card_image_of_injective _ _ Subtype.val_injective,
      ← ENat.card_congr (Equiv.ofInjective f hf), ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext x; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by simpa [f, nsmul_eq_mul] using (val i).symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨f ⟨n, by exact_mod_cast hn⟩, ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩,
        by simpa [f, nsmul_eq_mul] using val ⟨n, by exact_mod_cast hn⟩⟩
