import OMAReductions.R_Erdos835_johnson_chromaticNumber_R2

/-! Incidence counts for two block families, followed by inclusion-exclusion on a fixed trace. -/

namespace OMA.ExactDesignTraces

open Finset

variable {α : Type*} [DecidableEq α]

private def containing (Q : Finset (Finset α)) (J : Finset α) : Finset (Finset α) :=
  Q.filter (J ⊆ ·)

-- Count a block containing J once for each of its elements outside J.
private theorem extension_count [Fintype α] {Q : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (J : Finset α) :
    ∑ a ∈ univ \ J, (containing Q (insert a J)).card =
      (k - J.card) * (containing Q J).card := by
  have hex (a : α) :
      containing Q (insert a J) = (containing Q J).filter (a ∈ ·) := by
    ext B
    simp only [containing, mem_filter, insert_subset_iff]
    tauto
  calc
    _ = ∑ a ∈ univ \ J, ∑ B ∈ containing Q J, if a ∈ B then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro a _
      rw [hex, ← sum_filter]
      simp
    _ = ∑ B ∈ containing Q J, ∑ a ∈ univ \ J, if a ∈ B then (1 : ℕ) else 0 := sum_comm
    _ = ∑ _B ∈ containing Q J, (k - J.card) := by
      apply sum_congr rfl
      intro B hB
      have hJB := (mem_filter.mp hB).2
      have hBc := hQ B (mem_filter.mp hB).1
      have hsd := card_sdiff_add_card_eq_card hJB
      rw [← sum_filter, show ((univ \ J).filter (· ∈ B)) = B \ J by
        ext a
        simp only [mem_filter, mem_sdiff, mem_univ, true_and, and_comm]]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      change (B \ J).card = k - J.card
      rw [← hBc, ← hsd, Nat.add_sub_cancel]
    _ = _ := by simp [mul_comm]

private theorem proper_counts [Fintype α] {Q R : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hR : ∀ B ∈ R, B.card = k)
    (hcov : ∀ J : Finset α, J.card = k - 1 →
      (containing Q J).card = 1 ∧ (containing R J).card = 1)
    (J : Finset α) (hJ : J.card < k) : (containing Q J).card = (containing R J).card := by
  let P (d : ℕ) := ∀ T : Finset α, k - T.card = d → T.card < k →
    (containing Q T).card = (containing R T).card
  suffices ∀ d, P d from this (k - J.card) J rfl hJ
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro T hTd hTk
    by_cases hOne : d = 1
    · exact (hcov T (by omega)).1.trans (hcov T (by omega)).2.symm
    have hsum :
        ∑ a ∈ (univ \ T), (containing Q (insert a T)).card =
          ∑ a ∈ (univ \ T), (containing R (insert a T)).card := by
      apply sum_congr rfl
      intro a ha
      have hna := (mem_sdiff.mp ha).2
      have hcard := card_insert_of_notMem hna
      exact ih (k - (insert a T).card) (by omega) (insert a T) rfl (by omega)
    rw [extension_count hQ, extension_count hR] at hsum
    exact (Nat.mul_left_cancel_iff (by omega : 0 < k - T.card)).mp hsum

private theorem alternating_subsets (X : Finset α) :
    ∑ J ∈ X.powerset, (-1 : ℤ) ^ J.card = if X = ∅ then 1 else 0 := by
  have hx := (Finset.prod_add (fun _ : α => (-1 : ℤ)) (fun _ => (1 : ℤ)) X).symm
  simp only [prod_const, one_pow, mul_one, neg_add_cancel] at hx
  by_cases h : X = ∅
  · subst X
    simp
  · rw [if_neg h, hx]
    exact zero_pow (by simpa using h)

private theorem alternating_counts (Q : Finset (Finset α)) (A I : Finset α)
    (hI : I ⊆ A) :
    ∑ J ∈ (A \ I).powerset, (-1 : ℤ) ^ J.card * ((containing Q (I ∪ J)).card : ℤ) =
      ((Q.filter (fun B => A ∩ B = I)).card : ℤ) := by
  let R := containing Q I
  have hfilter (J : Finset α) :
      containing Q (I ∪ J) = R.filter (J ⊆ ·) := by
    ext B
    simp only [R, containing, mem_filter, union_subset_iff]
    tauto
  have hzero {B : Finset α} (hB : B ∈ R) : (A \ I) ∩ B = ∅ ↔ A ∩ B = I := by
    have hIB : I ⊆ B := (mem_filter.mp hB).2
    constructor
    · intro hempty
      apply Subset.antisymm
      · intro x hx
        by_contra hn
        obtain ⟨ha, hb⟩ := mem_inter.mp hx
        have hm : x ∈ (A \ I) ∩ B := mem_inter.mpr ⟨mem_sdiff.mpr ⟨ha, hn⟩, hb⟩
        simp [hempty] at hm
      · exact subset_inter hI hIB
    · intro heq
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases mem_inter.mp hx with ⟨hd, hb⟩
      rcases mem_sdiff.mp hd with ⟨ha, hnot⟩
      exact hnot (heq ▸ mem_inter.mpr ⟨ha, hb⟩)
  calc
    _ = ∑ J ∈ (A \ I).powerset, ∑ B ∈ R, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 := by
      apply sum_congr rfl
      intro J _
      rw [hfilter, ← sum_filter]
      simp [mul_comm]
    _ = ∑ B ∈ R, ∑ J ∈ (A \ I).powerset, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 :=
      sum_comm
    _ = ∑ B ∈ R, if A ∩ B = I then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro B hB
      rw [← sum_filter, show ((A \ I).powerset.filter (· ⊆ B)) = ((A \ I) ∩ B).powerset by
        ext J
        simp only [mem_filter, mem_powerset, Finset.subset_inter_iff], alternating_subsets]
      simp only [hzero hB]
    _ = _ := by
      rw [← sum_filter, show R.filter (fun B => A ∩ B = I) = Q.filter (fun B => A ∩ B = I) by
        ext B
        simp only [R, containing, mem_filter, and_assoc]
        exact and_congr_right (fun _ => and_iff_right_of_imp (fun e => e ▸ inter_subset_right))]
      simp

private theorem top_count {Q : Finset (Finset α)} {A : Finset α} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hA : A.card = k) :
    ((containing Q A).card : ℤ) = if A ∈ Q then 1 else 0 := by
  have hf : containing Q A = Q.filter (· = A) := by
    ext B
    simp only [containing, mem_filter]
    exact and_congr_right fun hb =>
      ⟨fun h => (eq_of_subset_of_card_le h (by rw [hQ B hb, hA])).symm,
        fun h => h ▸ Subset.rfl⟩
  rw [hf]
  by_cases h : A ∈ Q
  · rw [if_pos h, show Q.filter (· = A) = {A} by
      ext B
      simp only [mem_filter, mem_singleton]
      exact ⟨And.right, fun e => ⟨e.symm ▸ h, e⟩⟩]
    simp
  · rw [if_neg h, show Q.filter (· = A) = ∅ by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hBQ, rfl⟩ := mem_filter.mp hB
      exact h hBQ]
    simp

end OMA.ExactDesignTraces

open Finset OMA.ExactDesignTraces in
theorem OMA.solution : OMA.R_Erdos835_johnson_chromaticNumber_R2.H2 := by
  classical
  intro n k F G hF hG hc A I hA hI
  rw [← alternating_counts F A I hI, ← alternating_counts G A I hI, ← sum_sub_distrib]
  rw [sum_eq_single (A \ I)]
  · rw [← mul_sub_left_distrib, union_sdiff_of_subset hI, top_count hF hA, top_count hG hA]
    congr 2
    have := card_sdiff_add_card_eq_card hI
    omega
  · intro J hJ hne
    have hs := mem_powerset.mp hJ
    have hu : I ∪ J ⊆ A := union_subset hI (hs.trans sdiff_subset)
    have hlt : (I ∪ J).card < k := by
      rw [← hA]
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hu, ?_⟩
      intro heq
      apply hne
      apply Subset.antisymm hs
      intro x hx
      obtain ⟨hxA, hxI⟩ := mem_sdiff.mp hx
      exact (mem_union.mp (heq.symm ▸ hxA)).resolve_left hxI
    rw [proper_counts hF hG hc _ hlt, sub_self]
  · intro hm
    exact (hm (mem_powerset.mpr Subset.rfl)).elim
