import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1_H1_R1

/-!
Subtract the density of the points satisfying the newly excluded event,
using the induction hypothesis inside that event and inside the full set.
-/

open Set Filter
open scoped Topology

private theorem relativeDensityDiff {S T R : Set ℕ} {s t : ℝ}
    (hTS : T ⊆ S) (hS : S.HasDensity s R) (hT : T.HasDensity t R) :
    (S \ T).HasDensity (s - t) R := by
  unfold Set.HasDensity at *
  refine (hS.sub hT).congr' (Eventually.of_forall fun b => ?_)
  dsimp [Set.partialDensity]
  have hcut : ((S \ T) ∩ R) ∩ Set.Iio b =
      ((S ∩ R) ∩ Set.Iio b) \ ((T ∩ R) ∩ Set.Iio b) := by
    ext n
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  have hsub : (T ∩ R) ∩ Set.Iio b ⊆ (S ∩ R) ∩ Set.Iio b :=
    fun _ hn => ⟨⟨hTS hn.1.1, hn.1.2⟩, hn.2⟩
  have hfinite : ((S ∩ R) ∩ Set.Iio b).Finite :=
    (Set.finite_Iio b).subset Set.inter_subset_right
  have hcard := Set.ncard_sdiff_add_ncard_of_subset hsub hfinite
  have hreal : ((((S ∩ R) ∩ Set.Iio b) \ ((T ∩ R) ∩ Set.Iio b)).ncard : ℝ) +
      ((((T ∩ R) ∩ Set.Iio b).ncard : ℕ) : ℝ) =
      ((((S ∩ R) ∩ Set.Iio b).ncard : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [hcut, ← sub_div]
  congr 1
  exact (eq_sub_of_add_eq hreal).symm

private theorem relativeComplementSieve (R : Set ℕ) (E : Nat.Primes → ℕ → Prop)
    (w : Nat.Primes → ℝ) (P : Finset Nat.Primes) :
    ∀ (A : Set ℕ) (c : ℝ),
      (∀ Q ⊆ P, {n ∈ A | ∀ q ∈ Q, E q n}.HasDensity (c * ∏ q ∈ Q, w q) R) →
      {n ∈ A | ∀ q ∈ P, ¬ E q n}.HasDensity (c * ∏ q ∈ P, (1 - w q)) R := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro A c h
    simpa using h ∅ (Finset.empty_subset _)
  | @insert q P hq ih =>
    intro A c h
    have hA := ih A c (fun Q hQP => h Q (hQP.trans (Finset.subset_insert q P)))
    let B : Set ℕ := {n ∈ A | E q n}
    have hB := ih B (c * w q) (by
      intro Q hQP
      have hqQ : q ∉ Q := fun hq' => hq (hQP hq')
      have hEq : {n ∈ A | ∀ r ∈ insert q Q, E r n} =
          {n ∈ B | ∀ r ∈ Q, E r n} := by
        ext n
        simp only [B, Set.mem_ofPred_eq, Finset.forall_mem_insert]
        tauto
      have hj := h (insert q Q) (Finset.insert_subset_insert q hQP)
      rw [hEq, Finset.prod_insert hqQ, ← mul_assoc] at hj
      exact hj)
    have hsub : {n ∈ B | ∀ r ∈ P, ¬ E r n} ⊆ {n ∈ A | ∀ r ∈ P, ¬ E r n} :=
      fun _ hn => ⟨hn.1.1, hn.2⟩
    have hd := relativeDensityDiff hsub hA hB
    have hEq : {n ∈ A | ∀ r ∈ P, ¬ E r n} \ {n ∈ B | ∀ r ∈ P, ¬ E r n} =
        {n ∈ A | ∀ r ∈ insert q P, ¬ E r n} := by
      ext n
      simp only [B, Set.mem_sdiff, Set.mem_ofPred_eq, Finset.forall_mem_insert]
      tauto
    rw [hEq] at hd
    rw [Finset.prod_insert hq]
    convert hd using 1
    ring

theorem OMA.solution : OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1_H1_R1.H2 := by
  intro A R E w h P
  simpa using relativeComplementSieve R E w P A 1 (fun Q _ => by simpa using h Q)

