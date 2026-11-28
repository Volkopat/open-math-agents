import OMAStatements.S_oeis_a340524

/-! Count the parts of each size and take the first difference of the totals. -/
-- Credit: @STARDUSTLC666
-- The fixed-part counting and removal-of-one arguments are adapted from our A340426 proof.

namespace PartitionPartCount

open Finset Nat.Partition OMA.S_oeis_a340524

private def partitions (n : ℕ) := Fintype.card n.Partition
private def occurrences (n d : ℕ) := ∑ p : n.Partition, p.parts.count d
private def residuals (n d : ℕ) :=
  ∑ j ∈ range n, if d ∣ n-j then partitions j else 0

private lemma erase_one {n d : ℕ} (hd : 0 < d) (hn : d ≤ n) :
    occurrences n d = occurrences (n-d) d + partitions (n-d) := by
  classical
  let e := partitionWithPartEquiv (n := n) hd hn
  have split := Fintype.sum_subtype_add_sum_subtype
    (fun p : n.Partition => d ∈ p.parts) (fun p => p.parts.count d)
  have empty : (∑ p : {p : n.Partition // d ∉ p.parts}, p.val.parts.count d) = 0 := by
    apply sum_eq_zero
    intro p _
    exact Multiset.count_eq_zero.mpr p.property
  rw [empty, add_zero] at split
  calc
    occurrences n d = ∑ p : {p : n.Partition // d ∈ p.parts}, p.val.parts.count d := split.symm
    _ = ∑ q : (n-d).Partition, (e.symm q).val.parts.count d :=
      (e.symm.sum_comp (fun p => p.val.parts.count d)).symm
    _ = _ := by simp [e, occurrences, partitions, sum_add_distrib]

private lemma residual_step (m d : ℕ) (hd : 0 < d) :
    residuals (m+d) d = residuals m d + partitions m := by
  classical
  unfold residuals
  rw [sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have h := mem_range.mp hj
    rw [show m+d-j = (m-j)+d by omega]
    simp
  · rw [sum_eq_single_of_mem 0 (mem_range.mpr hd)]
    · simp
    · intro j hj hj0
      have hjd := mem_range.mp hj
      have no : ¬ d ∣ d-j := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [show m+d-(m+j) = d-j by omega, no]

private lemma count_parts (n d : ℕ) (hd : 0 < d) : occurrences n d = residuals n d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : d ≤ n
    · rw [erase_one hd hn, ih (n-d) (by omega)]
      simpa [Nat.sub_add_cancel hn] using (residual_step (n-d) d hd).symm
    · have no : occurrences n d = 0 := by
        apply sum_eq_zero
        intro p _
        apply Multiset.count_eq_zero.mpr
        exact fun h => hn (le_of_mem_parts h)
      rw [no, residuals]
      symm
      apply sum_eq_zero
      intro j hj
      have h := mem_range.mp hj
      simp [Nat.not_dvd_of_pos_of_lt (show 0 < n-j by omega) (show n-j < d by omega)]

private lemma part_count {n : ℕ} (p : n.Partition) :
    p.parts.card = ∑ d ∈ Icc 1 n, p.parts.count d := by
  exact (Multiset.sum_count_eq_card
    (fun d hd => mem_Icc.mpr ⟨p.parts_pos hd, le_of_mem_parts hd⟩)).symm

-- At residual size j, each divisor of n-j contributes one copy of each partition of j.
private lemma convolution (n : ℕ) :
    A006128 n = ∑ j ∈ range n, (n-j).divisors.card * partitions j := by
  classical
  calc
    A006128 n = ∑ p : n.Partition, ∑ d ∈ Icc 1 n, p.parts.count d := by
      unfold A006128
      exact sum_congr rfl (fun p _ => part_count p)
    _ = ∑ d ∈ Icc 1 n, occurrences n d := sum_comm
    _ = ∑ d ∈ Icc 1 n, ∑ j ∈ range n, if d ∣ n-j then partitions j else 0 := by
      exact sum_congr rfl (fun d hd => count_parts n d (mem_Icc.mp hd).1)
    _ = ∑ j ∈ range n, ∑ d ∈ Icc 1 n, if d ∣ n-j then partitions j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have h := mem_range.mp hj
      have pos : 0 < n-j := by omega
      have same : (Icc 1 n).filter (fun d => d ∣ n-j) = (n-j).divisors := by
        ext d
        simp only [mem_filter, mem_Icc, Nat.mem_divisors]
        constructor
        · exact fun hu => ⟨hu.2, pos.ne'⟩
        · intro hu
          have le := Nat.le_of_dvd pos hu.1
          have dp := Nat.pos_of_dvd_of_pos hu.1 pos
          exact ⟨⟨dp, by omega⟩, hu.1⟩
      rw [← sum_filter, same]
      simp

-- The partitions containing a one are counted by deleting that one.
private lemma no_ones (j : ℕ) : partitions (j+1) = A002865 (j+1) + partitions j := by
  classical
  let e := partitionWithPartEquiv (n := j+1) (a := 1) (by omega) (by omega)
  have hc : (univ.filter fun p : (j+1).Partition => 1 ∈ p.parts).card = partitions j := by
    rw [← Fintype.card_subtype]
    simpa [partitions] using Fintype.card_congr e
  have h := univ.card_filter_add_card_filter_not (fun p : (j+1).Partition => 1 ∈ p.parts)
  rw [hc] at h
  simpa [A002865, partitions, add_comm] using h.symm

private lemma row_indices (n : ℕ) :
    ∑ k ∈ Icc 1 n, T n k = ∑ j ∈ range n, (n-j).divisors.card * A002865 j := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 n, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl
  intro j hj
  have h := mem_range.mp hj
  simp [T, show n-(1+j)+1 = n-j by omega]

private lemma adjacent (m : ℕ) :
    A006128 (m+1) = (∑ j ∈ range (m+1), (m+1-j).divisors.card * A002865 j) + A006128 m := by
  rw [convolution (m+1), convolution m]
  rw [sum_range_succ' (fun j => (m+1-j).divisors.card * partitions j),
    sum_range_succ' (fun j => (m+1-j).divisors.card * A002865 j)]
  have base : A002865 0 = partitions 0 := by simp [A002865, partitions]
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, base, no_ones, Nat.mul_add, sum_add_distrib]
  omega

end PartitionPartCount

open PartitionPartCount OMA.S_oeis_a340524

theorem OMA.solution : type_of% @OMA.S_oeis_a340524.main := by
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [row_indices, A138137, show m.succ-1 = m by omega]
  simp only [Nat.succ_eq_add_one]
  have h := adjacent m
  omega
