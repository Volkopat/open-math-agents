import OMAReductions.R_opg_are_different_notions_of_the_crossing_number_the_same_R1

-- Step opg-are-different-notions-of-the-crossing-number-the-same.R1.H1: hypothesis H1 of reduction opg-are-different-notions-of-the-crossing-number-the-same.R1
-- Credit: @nnkostov

/-!
# Pach-Tóth Inequality Between Crossing Number and Pair-Crossing Number

Every admissible drawing `D` of a finite simple graph `G` in the plane maps each
crossing triple `(e₁, e₂, x)` of two distinct edges and a common interior point
onto its crossing pair `(e₁, e₂)`. Since `D.crossings` is finite for good drawings,
this projection yields `|D.crossingPairs| ≤ |D.crossings|`, hence `pcr G ≤ cr G`.
Furthermore, if `pcr G = 0`, any minimizing good drawing has an even, finite
crossing-pair set of cardinality `< 2`, forcing `D.crossingPairs = ∅`, hence
`D.crossings = ∅`, and therefore `cr G = 0`.
-/

open OMA.S_opg_are_different_notions_of_the_crossing_number_the_same

theorem OMA.solution :
    OMA.R_opg_are_different_notions_of_the_crossing_number_the_same_R1.H1 := by
  intro V _ G
  let proj : Sym2 V × Sym2 V × P → Sym2 V × Sym2 V := fun p => (p.1, p.2.1)
  have himg : ∀ D : Drawing G, proj '' D.crossings = D.crossingPairs := by
    intro D
    ext ⟨e₁, e₂⟩
    simp only [Set.mem_image, Drawing.crossings, Drawing.crossingPairs, Set.mem_ofPred_eq,
      Prod.mk.injEq, Set.Nonempty, proj]
    constructor
    · rintro ⟨⟨a, b, x⟩, ⟨ha, hb, hab, hx⟩, rfl, rfl⟩
      exact ⟨ha, hb, hab, x, hx⟩
    · rintro ⟨h1, h2, hne, x, hx⟩
      exact ⟨(e₁, e₂, x), ⟨h1, h2, hne, hx⟩, rfl, rfl⟩
  by_cases hgood : ∃ D : Drawing G, D.Good
  · obtain ⟨D₀, hD₀⟩ := hgood
    have hne_cr : {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}.Nonempty :=
      ⟨_, D₀, hD₀, rfl⟩
    have hne_pcr : {n | ∃ D : Drawing G, D.Good ∧ n = D.crossingPairs.ncard / 2}.Nonempty :=
      ⟨_, D₀, hD₀, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨D, hD, hcr⟩ := Nat.sInf_mem hne_cr
      change cr G = D.crossings.ncard / 2 at hcr
      have hpcr_le : pcr G ≤ D.crossingPairs.ncard / 2 := Nat.sInf_le ⟨D, hD, rfl⟩
      have hnc : D.crossingPairs.ncard ≤ D.crossings.ncard := by
        rw [← himg D]
        exact Set.ncard_image_le hD
      omega
    · intro hpcr0
      obtain ⟨D, hD, hpcr⟩ := Nat.sInf_mem hne_pcr
      change pcr G = D.crossingPairs.ncard / 2 at hpcr
      rw [hpcr0] at hpcr
      have hpairs_empty : D.crossingPairs = ∅ := by
        by_contra hne
        obtain ⟨⟨e₁, e₂⟩, hmem⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hmem_swap : (e₂, e₁) ∈ D.crossingPairs :=
          ⟨hmem.2.1, hmem.1, hmem.2.2.1.symm, by rw [Set.inter_comm]; exact hmem.2.2.2⟩
        have hpair_ne : (e₁, e₂) ≠ (e₂, e₁) := fun h => hmem.2.2.1 (congrArg Prod.fst h)
        have hfin_pairs : D.crossingPairs.Finite := by
          rw [← himg D]
          exact hD.image proj
        have hsub : ({(e₁, e₂), (e₂, e₁)} : Set (Sym2 V × Sym2 V)) ⊆ D.crossingPairs := by
          rintro p (rfl | rfl) <;> assumption
        have h2le : 2 ≤ D.crossingPairs.ncard := by
          rw [← Set.ncard_pair hpair_ne]
          exact Set.ncard_le_ncard hsub hfin_pairs
        omega
      have hcross_empty : D.crossings = ∅ :=
        Set.image_eq_empty.mp ((himg D).trans hpairs_empty)
      have hcr_le : cr G ≤ 0 :=
        Nat.sInf_le ⟨D, hD, by rw [hcross_empty, Set.ncard_empty]⟩
      exact Nat.eq_zero_of_le_zero hcr_le
  · have h1 : {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨D, hD, _⟩ => hgood ⟨D, hD⟩
    have h2 : {n | ∃ D : Drawing G, D.Good ∧ n = D.crossingPairs.ncard / 2} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨D, hD, _⟩ => hgood ⟨D, hD⟩
    unfold pcr cr
    rw [h1, h2, Nat.sInf_empty]
    exact ⟨le_rfl, fun _ => rfl⟩
