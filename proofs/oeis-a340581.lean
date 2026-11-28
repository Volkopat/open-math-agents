import OMAStatements.S_oeis_a340581

namespace PartitionCounts

noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

def countParts (n d : ℕ) : ℕ := ∑ q : Nat.Partition n, q.parts.count d

lemma countParts_eq_subtype (n d : ℕ) :
    countParts n d = ∑ q : {q : Nat.Partition n // d ∈ q.parts}, q.val.parts.count d := by
  classical
  unfold countParts
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : Nat.Partition n => d ∈ q.parts),
        q.parts.count d := by
      symm
      apply Finset.sum_filter_of_ne
      intro q hq hne
      exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)
    _ = _ := Finset.sum_subtype _ (by simp) _

lemma countParts_rec {n d : ℕ} (hd : 0 < d) (hn : d ≤ n) :
    countParts n d = p (n-d) + countParts (n-d) d := by
  classical
  let e := Nat.Partition.partitionWithPartEquiv hd hn
  rw [countParts_eq_subtype]
  calc
    _ = ∑ q : Nat.Partition (n-d), (e.symm q).val.parts.count d := by
      symm
      exact e.symm.sum_comp (fun q : {q : Nat.Partition n // d ∈ q.parts} => q.val.parts.count d)
    _ = ∑ q : Nat.Partition (n-d), (q.parts.count d + 1) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [e]
    _ = _ := by simp [Finset.sum_add_distrib, countParts, p, Nat.add_comm]

lemma countParts_eq_zero_of_lt {n d : ℕ} (hn : n < d) : countParts n d = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  apply Multiset.count_eq_zero.mpr
  intro hmem
  exact Nat.not_le_of_lt hn (Nat.Partition.le_of_mem_parts hmem)

lemma countParts_zero (n : ℕ) : countParts n 0 = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  apply Multiset.count_eq_zero.mpr
  intro hmem
  exact Nat.lt_irrefl 0 (q.parts_pos hmem)

lemma p_pos (n : ℕ) : 0 < p n := Fintype.card_pos

lemma p_zero : p 0 = 1 := Fintype.card_unique

lemma p_succ_le (n : ℕ) : p n ≤ p (n+1) := by
  classical
  have he := Fintype.card_congr (Nat.Partition.partitionWithPartEquiv (n := n+1) (a := 1)
    (by omega) (by omega))
  have hl := Fintype.card_le_of_injective
    (fun q : {q : Nat.Partition (n+1) // 1 ∈ q.parts} => q.val) Subtype.val_injective
  simpa [p, he] using hl

lemma p_mono : Monotone p := monotone_nat_of_le_succ p_succ_le

end PartitionCounts

noncomputable def OMA.rowStart (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  sInf {r : ℕ | j ≤ f r}

lemma OMA.rowStart_bounds (f : ℕ → ℕ) (hzero : f 0 = 0)
    {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ f n) :
    1 ≤ OMA.rowStart f j ∧ OMA.rowStart f j ≤ n := by
  have hs : ({r : ℕ | j ≤ f r} : Set ℕ).Nonempty := ⟨n, hjn⟩
  have hm : j ≤ f (OMA.rowStart f j) := csInf_mem hs
  have hb : OMA.rowStart f j ≤ n := csInf_le' hjn
  refine ⟨?_, hb⟩
  by_contra h
  have he : OMA.rowStart f j = 0 := by omega
  rw [he, hzero] at hm
  omega

lemma OMA.rowStart_eq_iff (f : ℕ → ℕ) (hf : Monotone f)
    {j n r : ℕ} (hjn : j ≤ f n) (hr : 1 ≤ r) :
    OMA.rowStart f j = r ↔ f (r - 1) < j ∧ j ≤ f r := by
  rw [OMA.rowStart, csInf_eq_iff (show ({a : ℕ | j ≤ f a} : Set ℕ).Nonempty from ⟨n, hjn⟩)]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hj, hmin⟩
    refine ⟨?_, hj⟩
    by_contra h
    have hb := hmin (r - 1) (by omega)
    omega
  · rintro ⟨hlt, hle⟩
    refine ⟨hle, ?_⟩
    intro a ha
    by_contra h
    have ham : a ≤ r - 1 := by omega
    have hfm := hf ham
    omega

lemma OMA.row_filter (f : ℕ → ℕ) (hf : Monotone f) (hzero : f 0 = 0)
    {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    (Finset.Icc 1 (f n)).filter (fun j => n - OMA.rowStart f j + 1 = t) =
      Finset.Ioc (f (n - t)) (f (n - t + 1)) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hj, hjn⟩, he⟩
    have hs := OMA.rowStart_bounds f hzero hj hjn
    have hstart : OMA.rowStart f j = n - t + 1 := by omega
    have hr : 1 ≤ n - t + 1 := by omega
    have hspec := (OMA.rowStart_eq_iff f hf hjn hr).mp hstart
    simpa only [Nat.add_sub_cancel] using hspec
  · rintro ⟨hlo, hhi⟩
    have hj : 1 ≤ j := by omega
    have hbn : n - t + 1 ≤ n := by omega
    have hjn : j ≤ f n := le_trans hhi (hf hbn)
    refine ⟨⟨hj, hjn⟩, ?_⟩
    have hspec : f (n - t + 1 - 1) < j ∧ j ≤ f (n - t + 1) := by
      simpa only [Nat.add_sub_cancel] using And.intro hlo hhi
    have hstart := (OMA.rowStart_eq_iff f hf hjn (show 1 ≤ n - t + 1 by omega)).mpr hspec
    omega

lemma OMA.row_histogram (f : ℕ → ℕ) (hf : Monotone f) (hzero : f 0 = 0)
    {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    ((Finset.Icc 1 (f n)).filter (fun j => n - OMA.rowStart f j + 1 = t)).card =
      f (n - t + 1) - f (n - t) := by
  rw [OMA.row_filter f hf hzero ht htn, Nat.card_Ioc]

lemma OMA.row_multiset_count (f : ℕ → ℕ) (hf : Monotone f) (hzero : f 0 = 0)
    {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    ((Finset.Icc 1 (f n)).val.map (fun j => n - OMA.rowStart f j + 1)).count t =
      f (n - t + 1) - f (n - t) := by
  classical
  rw [Multiset.count_map]
  change ((Finset.Icc 1 (f n)).filter (fun j => t = n - OMA.rowStart f j + 1)).card = _
  simpa only [eq_comm] using OMA.row_histogram f hf hzero ht htn

lemma OMA.row_multiset_support (f : ℕ → ℕ) (hzero : f 0 = 0)
    {n t : ℕ}
    (ht : t ∈ (Finset.Icc 1 (f n)).val.map (fun j => n - OMA.rowStart f j + 1)) :
    1 ≤ t ∧ t ≤ n := by
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp ht
  have hj' : j ∈ Finset.Icc 1 (f n) := hj
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj'
  have hs := OMA.rowStart_bounds f hzero hjlo hjhi
  omega

open Finset

lemma F07.sum_shift (f : ℕ → ℕ) (d n : ℕ) (hd : 0 < d) (hn : d ≤ n)
    (hz : ∀ j, 1 ≤ j → j < d → f j = 0) :
    (∑ j ∈ Icc 1 n, f j) = ∑ k ∈ range (n - d + 1), f (k + d) := by
  calc
    (∑ j ∈ Icc 1 n, f j) = ∑ j ∈ Icc d n, f j := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [mem_Icc] at *
        omega
      · intro j hj hnot
        apply hz j (mem_Icc.mp hj).1
        simp only [mem_Icc] at *
        omega
    _ = ∑ k ∈ range (n - d + 1), f (k + d) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      have he : n + 1 - d = n - d + 1 := by omega
      simp only [he, Nat.add_comm d]

lemma F07.sum_zero_to_Icc (f : ℕ → ℕ) (n : ℕ) (h0 : f 0 = 0) :
    (∑ k ∈ range (n + 1), f k) = ∑ k ∈ Icc 1 n, f k := by
  rw [sum_range_eq_add_Ico f (by omega), h0, zero_add,
    Finset.Ico_add_one_right_eq_Icc]

lemma F07.cumulative_step (p C : ℕ → ℕ) (d n : ℕ) (hd : 0 < d) (hn : d ≤ n)
    (hz : ∀ j < d, C j = 0)
    (hr : ∀ j, d ≤ j → C j = p (j - d) + C (j - d)) :
    (∑ j ∈ Icc 1 n, C j) =
      (∑ i ∈ range (n - d + 1), p i) + ∑ j ∈ Icc 1 (n - d), C j := by
  rw [F07.sum_shift C d n hd hn (fun j _ hj => hz j hj)]
  calc
    (∑ k ∈ range (n - d + 1), C (k + d)) =
        ∑ k ∈ range (n - d + 1), (p k + C k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Nat.add_sub_cancel] using hr (k + d) (by omega)
    _ = _ := by
      rw [sum_add_distrib, F07.sum_zero_to_Icc C (n - d) (hz 0 hd)]

def F07.divisorConvolution (p : ℕ → ℕ) (d n : ℕ) : ℕ :=
  ∑ t ∈ Icc 1 n, if d ∣ t then ∑ i ∈ range (n - t + 1), p i else 0

lemma F07.divisorConvolution_small (p : ℕ → ℕ) (d n : ℕ) (hn : n < d) :
    F07.divisorConvolution p d n = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  simp only [mem_Icc] at ht
  have hnot : ¬ d ∣ t := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < t) h
    omega
  simp [hnot]

lemma F07.divisorConvolution_step (p : ℕ → ℕ) (d n : ℕ)
    (hd : 0 < d) (hn : d ≤ n) :
    F07.divisorConvolution p d n =
      (∑ i ∈ range (n - d + 1), p i) + F07.divisorConvolution p d (n - d) := by
  unfold F07.divisorConvolution
  rw [F07.sum_shift _ d n hd hn]
  · rw [Finset.sum_range_succ']
    simp only [zero_add, dvd_refl, if_true]
    rw [Nat.add_comm]
    congr 1
    have hconvert : ∀ k ∈ range (n - d),
        (if d ∣ k + 1 + d then ∑ i ∈ range (n - (k + 1 + d) + 1), p i else 0) =
        (if d ∣ k + 1 then ∑ i ∈ range (n - d - (k + 1) + 1), p i else 0) := by
      intro k hk
      have hsub : n - (k + 1 + d) = n - d - (k + 1) := by omega
      simp only [Nat.dvd_add_self_right, hsub]
    calc
      _ = ∑ k ∈ range (n - d),
          if d ∣ k + 1 then ∑ i ∈ range (n - d - (k + 1) + 1), p i else 0 :=
        Finset.sum_congr rfl hconvert
      _ = ∑ t ∈ Icc 1 (n - d),
          if d ∣ t then ∑ i ∈ range (n - d - t + 1), p i else 0 := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  · intro t hpos ht
    have hnot : ¬ d ∣ t := by
      intro h
      have := Nat.le_of_dvd (by omega : 0 < t) h
      omega
    simp [hnot]


lemma F07.cumulative_convolution (p C : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
    (hz : ∀ j < d, C j = 0)
    (hr : ∀ j, d ≤ j → C j = p (j - d) + C (j - d)) (n : ℕ) :
    (∑ j ∈ Icc 1 n, C j) =
      ∑ t ∈ Icc 1 n, if d ∣ t then ∑ i ∈ range (n - t + 1), p i else 0 := by
  change (∑ j ∈ Icc 1 n, C j) = F07.divisorConvolution p d n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : d ≤ n
    · rw [F07.cumulative_step p C d n hd hn hz hr,
        F07.divisorConvolution_step p d n hd hn, ih (n - d) (by omega)]
    · have hn' : n < d := by omega
      rw [F07.divisorConvolution_small p d n hn']
      apply Finset.sum_eq_zero
      intro j hj
      exact hz j (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hn')

namespace F07
open OMA.S_oeis_a340581

lemma L_eq_sum (n : ℕ) : L n = ∑ i ∈ Finset.range n, A000070 i := by
  cases n with
  | zero => simp [L]
  | succ n => simp [L, A014153]

lemma L_zero : L 0 = 0 := by simp [L]

lemma L_succ (n : ℕ) : L (n+1) = L n + A000070 n := by
  simp [L_eq_sum, Finset.sum_range_succ]

lemma L_mono : Monotone L := by
  apply monotone_nat_of_le_succ
  intro n
  rw [L_succ]
  omega

lemma L_gap (n : ℕ) : L (n+1) - L n = A000070 n := by
  rw [L_succ, Nat.add_sub_cancel_left]

lemma count_rhs (n d : ℕ) :
    Multiset.count d (∑ j ∈ Finset.Icc 1 n,
      (Finset.univ : Finset (Nat.Partition j)).val.bind (fun p => p.parts)) =
    ∑ j ∈ Finset.Icc 1 n, ∑ p : Nat.Partition j, p.parts.count d := by
  rw [Multiset.count_sum']
  apply Finset.sum_congr rfl
  intro j hj
  rw [Multiset.count_bind]
  rfl

lemma sum_map_by_counts (m : Multiset ℕ) (s : Finset ℕ) (f : ℕ → ℕ)
    (hs : ∀ t ∈ m, t ∈ s) :
    (m.map f).sum = ∑ t ∈ s, m.count t * f t := by
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro t ht
    exact hs t (by simpa using ht)
  · intro t ht htm
    have hz : m.count t = 0 := Multiset.count_eq_zero.mpr (by simpa using htm)
    simp [hz]

lemma count_divisors (t d : ℕ) (ht : 0 < t) :
    Multiset.count d t.divisors.val = if d ∣ t then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup t.divisors.nodup]
  simp [Nat.mem_divisors, Nat.ne_of_gt ht]

lemma count_lhs (n d : ℕ)
    (hs : ∀ t ∈ row n, t ∈ Finset.Icc 1 n)
    (hc : ∀ t ∈ Finset.Icc 1 n, (row n).count t = A000070 (n-t)) :
    Multiset.count d ((row n).bind (fun t => t.divisors.val)) =
      ∑ t ∈ Finset.Icc 1 n, if d ∣ t then A000070 (n-t) else 0 := by
  rw [Multiset.count_bind, sum_map_by_counts (row n) (Finset.Icc 1 n) _ hs]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hc t ht, count_divisors t d (Finset.mem_Icc.mp ht).1]
  split_ifs <;> simp

lemma target_of_counts (n : ℕ)
    (hs : ∀ t ∈ row n, t ∈ Finset.Icc 1 n)
    (hc : ∀ t ∈ Finset.Icc 1 n, (row n).count t = A000070 (n-t))
    (hz : ∀ j, (∑ p : Nat.Partition j, p.parts.count 0) = 0)
    (hconv : ∀ d, 0 < d →
      (∑ j ∈ Finset.Icc 1 n, ∑ p : Nat.Partition j, p.parts.count d) =
      ∑ t ∈ Finset.Icc 1 n, if d ∣ t then A000070 (n-t) else 0) :
    (row n).bind (fun t => t.divisors.val) =
      ∑ j ∈ Finset.Icc 1 n, (Finset.univ : Finset (Nat.Partition j)).val.bind
        (fun p => p.parts) := by
  apply Multiset.ext.mpr
  intro d
  rw [count_lhs n d hs hc, count_rhs]
  by_cases hd : d = 0
  · subst d
    have hleft : (∑ t ∈ Finset.Icc 1 n,
        if 0 ∣ t then A000070 (n-t) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have ht0 : t ≠ 0 := by have := (Finset.mem_Icc.mp ht).1; omega
      simp [ht0]
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j
  · exact (hconv d (Nat.pos_of_ne_zero hd)).symm


lemma row_support (n : ℕ) : ∀ t ∈ row n, t ∈ Finset.Icc 1 n := by
  intro t ht
  exact Finset.mem_Icc.mpr (OMA.row_multiset_support L L_zero ht)

lemma row_count (n : ℕ) : ∀ t ∈ Finset.Icc 1 n,
    (row n).count t = A000070 (n-t) := by
  intro t ht
  calc
    (row n).count t = L (n-t+1) - L (n-t) :=
      OMA.row_multiset_count L L_mono L_zero (Finset.mem_Icc.mp ht).1
        (Finset.mem_Icc.mp ht).2
    _ = A000070 (n-t) := L_gap (n-t)

lemma target_of_partition_convolution (n : ℕ)
    (hconv : ∀ d, 0 < d →
      (∑ j ∈ Finset.Icc 1 n, PartitionCounts.countParts j d) =
      ∑ t ∈ Finset.Icc 1 n, if d ∣ t then A000070 (n-t) else 0) :
    (row n).bind (fun t => t.divisors.val) =
      ∑ j ∈ Finset.Icc 1 n, (Finset.univ : Finset (Nat.Partition j)).val.bind
        (fun p => p.parts) := by
  exact target_of_counts n (row_support n) (row_count n)
    PartitionCounts.countParts_zero hconv

end F07

theorem OMA.solution : type_of% @OMA.S_oeis_a340581.main := by
  intro n hn
  apply F07.target_of_partition_convolution n
  intro d hd
  simpa only [OMA.S_oeis_a340581.A000070, OMA.S_oeis_a340581.A000041,
    PartitionCounts.p] using
    F07.cumulative_convolution PartitionCounts.p
      (fun j => PartitionCounts.countParts j d) d hd
      (fun j hj => PartitionCounts.countParts_eq_zero_of_lt hj)
      (fun j hj => PartitionCounts.countParts_rec hd hj) n
