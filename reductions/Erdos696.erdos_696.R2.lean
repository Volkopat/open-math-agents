import FormalConjectures.ErdosProblems.«696»

/-! Erdős 696. The two inputs isolate the upper divisor-chain bound and the
lower prime-chain bound in sections 3 and 5 of David Turturean's
Normal orders of the Erdős chain functions h(n) and H(n).
For the latter, a positive proportion along a subsequence suffices. -/

namespace OMA.R_Erdos696_erdos_696_R2

open Erdos696 Filter Set

-- The finite-count union bound follows the proof in @marcusbuffett's Erdős 470 reduction.
private lemma cover_density {S A B : Set ℕ} (cover : S ⊆ A ∪ B) (x : ℕ) :
    S.partialDensity univ x ≤ A.partialDensity univ x + B.partialDensity univ x := by
  simp only [partialDensity, inter_univ, univ_inter, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : S ∩ Iio x ⊆ (A ∩ Iio x) ∪ (B ∩ Iio x) := by
    intro n hn
    obtain hA | hB := cover hn.1
    · exact Or.inl ⟨hA, hn.2⟩
    · exact Or.inr ⟨hB, hn.2⟩
  have hfin : ((A ∩ Iio x) ∪ (B ∩ Iio x)).Finite :=
    ((finite_Iio x).subset inter_subset_right).union ((finite_Iio x).subset inter_subset_right)
  exact_mod_cast (ncard_le_ncard hsub hfin).trans (ncard_union_le _ _)

def H1 : Prop :=
  ∀ᶠ x : ℕ in atTop,
    {n : ℕ | 2 * Real.iteratedLog n < H n}.partialDensity univ x ≤ 1 / 8

def H2 : Prop :=
  ∃ᶠ x : ℕ in atTop,
    {n : ℕ | 4 * h n < Real.iteratedLog n}.partialDensity univ x ≤ 3 / 4

theorem main : H1 → H2 → type_of% @Erdos696.erdos_696 := by
  intro upper lower diverges
  let S := {n : ℕ | (0 : ℝ) < h n ∧ (H n : ℝ) / h n > 8}
  let A := {n : ℕ | 2 * Real.iteratedLog n < H n}
  let B := {n : ℕ | 4 * h n < Real.iteratedLog n}
  have cover : S ⊆ A ∪ B := by
    intro n hn
    obtain ⟨hp, hr⟩ := hn
    have hlt : 8 * h n < H n := by exact_mod_cast (lt_div_iff₀ hp).mp hr
    change 2 * Real.iteratedLog n < H n ∨ 4 * h n < Real.iteratedLog n
    omega
  have hd : S.HasDensity 1 := diverges 8
  have large : ∀ᶠ x : ℕ in atTop, 7 / 8 < S.partialDensity univ x :=
    (show Tendsto _ _ _ from hd).eventually (eventually_gt_nhds (by norm_num : (7 / 8 : ℝ) < 1))
  change ∀ᶠ x : ℕ in atTop, A.partialDensity univ x ≤ 1 / 8 at upper
  change ∃ᶠ x : ℕ in atTop, B.partialDensity univ x ≤ 3 / 4 at lower
  obtain ⟨x, hB, hA, hS⟩ := (lower.and_eventually (upper.and large)).exists
  have hcover := cover_density cover x
  change A.partialDensity univ x ≤ 1 / 8 at hA
  change B.partialDensity univ x ≤ 3 / 4 at hB
  linarith

end OMA.R_Erdos696_erdos_696_R2
