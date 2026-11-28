import OMAReductions.R_Erdos393_erdos_393_variants_berend_osgood_R1

/-!
Proof of `OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1.H2`.

`f n` is the infimum of the admissible gaps. If `f n = m ≥ 1` the set is nonempty (its infimum
would otherwise be `0`), so `m` itself is admissible: some `s ⊆ [a, a + m]` contains `a` and
`a + m` and has product `n!`. Shifting `s` down by `a` gives the required `S ⊆ [0, m]`.
-/

open scoped Nat

theorem OMA.solution : OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1.H2 := by
  intro m n hm hf
  unfold Erdos393.f at hf
  have hne : {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hf
    omega
  have hmem := Nat.sInf_mem hne
  rw [hf] at hmem
  obtain ⟨-, a, s, hs, ha, ham, hprod⟩ := hmem
  refine ⟨a, s.image (fun i => i - a), ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hi' := Finset.mem_Icc.mp (hs hi)
    rw [Finset.mem_Icc]
    omega
  · exact Finset.mem_image.mpr ⟨a, ha, by simp⟩
  · exact Finset.mem_image.mpr ⟨a + m, ham, by simp⟩
  · rw [Finset.prod_image]
    · rw [← hprod]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp (hs hi)
      show a + (i - a) = i
      omega
    · intro x hx y hy hxy
      have hx' := Finset.mem_Icc.mp (hs (Finset.mem_coe.mp hx))
      have hy' := Finset.mem_Icc.mp (hs (Finset.mem_coe.mp hy))
      have h : x - a = y - a := hxy
      omega
