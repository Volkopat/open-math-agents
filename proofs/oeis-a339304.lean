import OMAStatements.S_oeis_a339304


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



open Finset

namespace PartitionCounts

def totalParts (n : ℕ) : ℕ := ∑ q : Nat.Partition n, q.parts.card

lemma totalParts_eq_sum_counts (n : ℕ) :
    totalParts n = ∑ d ∈ Icc 1 n, countParts n d := by
  classical
  unfold totalParts countParts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  symm
  apply Multiset.sum_count_eq_card
  intro d hd
  exact Finset.mem_Icc.mpr ⟨q.parts_pos hd, Nat.Partition.le_of_mem_parts hd⟩

def divisorSum (p : ℕ → ℕ) (d n : ℕ) : ℕ :=
  ∑ t ∈ Icc 1 n, if d ∣ t then p (n-t) else 0

lemma divisorSum_small (p : ℕ → ℕ) (d n : ℕ) (hn : n < d) :
    divisorSum p d n = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  simp only [mem_Icc] at ht
  have hnot : ¬ d ∣ t := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < t) h
    omega
  simp [hnot]

lemma divisorSum_step (p : ℕ → ℕ) (d n : ℕ) (hd : 0 < d) (hn : d ≤ n) :
    divisorSum p d n = p (n-d) + divisorSum p d (n-d) := by
  unfold divisorSum
  rw [F07.sum_shift _ d n hd hn]
  · rw [Finset.sum_range_succ']
    simp only [zero_add, dvd_refl, if_true]
    rw [Nat.add_comm]
    congr 1
    have hconvert : ∀ k ∈ range (n-d),
        (if d ∣ k+1+d then p (n-(k+1+d)) else 0) =
        (if d ∣ k+1 then p (n-d-(k+1)) else 0) := by
      intro k hk
      have hsub : n-(k+1+d) = n-d-(k+1) := by omega
      simp only [Nat.dvd_add_self_right, hsub]
    calc
      _ = ∑ k ∈ range (n-d), if d ∣ k+1 then p (n-d-(k+1)) else 0 :=
        Finset.sum_congr rfl hconvert
      _ = ∑ t ∈ Icc 1 (n-d), if d ∣ t then p (n-d-t) else 0 := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  · intro t hpos ht
    have hnot : ¬ d ∣ t := by
      intro h
      have := Nat.le_of_dvd (by omega : 0 < t) h
      omega
    simp [hnot]

lemma countParts_divisorSum (n d : ℕ) (hd : 0 < d) :
    countParts n d = ∑ t ∈ Icc 1 n, if d ∣ t then p (n-t) else 0 := by
  change countParts n d = divisorSum p d n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : d ≤ n
    · rw [countParts_rec hd hn, divisorSum_step p d n hd hn, ih (n-d) (by omega)]
    · have hn' : n < d := by omega
      rw [countParts_eq_zero_of_lt hn', divisorSum_small p d n hn']

lemma divisors_filter_Icc (n t : ℕ) (ht : t ∈ Icc 1 n) :
    (Icc 1 n).filter (fun d => d ∣ t) = t.divisors := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, hdn⟩, hdt⟩
    exact ⟨hdt, by have := (mem_Icc.mp ht).1; omega⟩
  · rintro ⟨hdt, ht0⟩
    have htpos : 0 < t := by have := (mem_Icc.mp ht).1; omega
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdt htpos,
      (Nat.le_of_dvd htpos hdt).trans (mem_Icc.mp ht).2⟩, hdt⟩

lemma totalParts_convolution (n : ℕ) :
    totalParts n = ∑ t ∈ Icc 1 n, t.divisors.card * p (n-t) := by
  classical
  rw [totalParts_eq_sum_counts]
  calc
    (∑ d ∈ Icc 1 n, countParts n d) =
        ∑ d ∈ Icc 1 n, ∑ t ∈ Icc 1 n, if d ∣ t then p (n-t) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact countParts_divisorSum n d (mem_Icc.mp hd).1
    _ = ∑ t ∈ Icc 1 n, ∑ d ∈ Icc 1 n, if d ∣ t then p (n-t) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter, divisors_filter_Icc n t ht]
      simp

end PartitionCounts


open Finset

namespace F07

lemma sum_weighted_diff (f w : ℕ → ℕ) (hf : Monotone f) (h0 : f 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ t ∈ Icc 1 n, w t * (f (n-t+1) - f (n-t))) +
      (∑ t ∈ Icc 1 (n-1), w t * f (n-t)) =
        ∑ t ∈ Icc 1 n, w t * f (n-t+1) := by
  have hprev : (∑ t ∈ Icc 1 (n-1), w t * f (n-t)) =
      ∑ t ∈ Icc 1 n, w t * f (n-t) := by
    apply Finset.sum_subset
    · intro t ht
      simp only [mem_Icc] at *
      omega
    · intro t ht hnot
      have htn : t = n := by
        simp only [mem_Icc] at *
        omega
      subst t
      simp [h0]
  rw [hprev, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Nat.mul_add, Nat.sub_add_cancel (hf (by omega : n-t ≤ n-t+1))]

end F07


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


namespace F07B

open OMA.S_oeis_a339304
open Finset

def f (r : ℕ) : ℕ := if r = 0 then 0 else A000041 (r - 1)

lemma f_zero : f 0 = 0 := by simp [f]

lemma f_succ (r : ℕ) : f (r + 1) = A000041 r := by simp [f]

lemma f_mono : Monotone f := by
  apply monotone_nat_of_le_succ
  intro r
  cases r with
  | zero => simp [f]
  | succ r => simpa [f, A000041, PartitionCounts.p] using PartitionCounts.p_succ_le r

lemma f_eq (r : ℕ) (hr : 1 ≤ r) : f r = A000041 (r - 1) := by
  simp [f, show r ≠ 0 by omega]

lemma start_eq (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ A000041 (n - 1)) :
    OMA.rowStart f k = c k + 1 := by
  have hm : k ≤ A000041 (c k) := csInf_mem (show ({j | k ≤ A000041 j} : Set ℕ).Nonempty from ⟨n - 1, hkn⟩)
  have hfn : k ≤ f n := by rw [f_eq n hn]; exact hkn
  apply (OMA.rowStart_eq_iff f f_mono hfn (show 1 ≤ c k + 1 by omega)).mpr
  simp only [Nat.add_sub_cancel, f_succ]
  refine ⟨?_, hm⟩
  by_cases hc : c k = 0
  · simpa [hc, f_zero] using (show 0 < k by omega)
  · rw [f_eq (c k) (by omega)]
    by_contra h
    have hlo : k ≤ A000041 (c k - 1) := by omega
    have hb : c k ≤ c k - 1 := csInf_le' hlo
    omega

lemma row_multiset_eq (n : ℕ) (hn : 1 ≤ n) :
    (rowA336811 n : Multiset ℕ) =
      (Icc 1 (f n)).val.map (fun j => n - OMA.rowStart f j + 1) := by
  classical
  rw [Nat.Icc_eq_range']
  simp only [Nat.add_sub_cancel, List.range'_eq_map_range, Multiset.map_coe, List.map_map,
    Function.comp_apply, rowA336811, f_eq n hn]
  apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
  apply List.map_congr_left
  intro i hi
  have hib : i < A000041 (n - 1) := List.mem_range.mp hi
  have he := start_eq n (i + 1) hn (by omega) (by omega)
  have hb : c (i + 1) ≤ n - 1 := csInf_le' (show i + 1 ≤ A000041 (n - 1) by omega)
  change n - c (i + 1) = n - OMA.rowStart f (1 + i) + 1
  rw [Nat.add_comm 1 i, he]
  omega

lemma sum_map_by_counts (m : Multiset ℕ) (s : Finset ℕ) (g : ℕ → ℕ)
    (hs : ∀ t ∈ m, t ∈ s) :
    (m.map g).sum = ∑ t ∈ s, m.count t * g t := by
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro t ht
    exact hs t (by simpa using ht)
  · intro t ht htm
    have hz : m.count t = 0 := Multiset.count_eq_zero.mpr (by simpa using htm)
    simp [hz]

lemma row_sum (n : ℕ) (hn : 1 ≤ n) :
    (row n).sum = ∑ t ∈ Icc 1 n, t.divisors.card * (f (n - t + 1) - f (n - t)) := by
  classical
  change (((rowA336811 n : Multiset ℕ).map (fun t => t.divisors.card)).sum) = _
  rw [row_multiset_eq n hn]
  rw [sum_map_by_counts _ (Icc 1 n) _ (fun t ht =>
    Finset.mem_Icc.mpr (OMA.row_multiset_support f f_zero ht))]
  apply Finset.sum_congr rfl
  intro t ht
  rw [OMA.row_multiset_count f f_mono f_zero (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2]
  exact Nat.mul_comm _ _

lemma totalParts_new (n : ℕ) :
    A006128 n = ∑ t ∈ Icc 1 n, t.divisors.card * f (n - t + 1) := by
  change PartitionCounts.totalParts n = _
  rw [PartitionCounts.totalParts_convolution]
  simp only [f_succ]
  rfl

lemma totalParts_prev (n : ℕ) (hn : 1 ≤ n) :
    A006128 (n - 1) = ∑ t ∈ Icc 1 (n - 1), t.divisors.card * f (n - t) := by
  change PartitionCounts.totalParts (n - 1) = _
  rw [PartitionCounts.totalParts_convolution]
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t ≤ n - 1 := (Finset.mem_Icc.mp ht).2
  rw [f_eq (n - t) (by omega)]
  have hs : n - t - 1 = n - 1 - t := by omega
  rw [hs]
  rfl

theorem target : ∀ n : ℕ, 1 ≤ n → (((row n).sum : ℕ) : ℤ) = A138137 n := by
  intro n hn
  have h := F07.sum_weighted_diff f (fun t => t.divisors.card) f_mono f_zero n hn
  rw [← row_sum n hn, ← totalParts_prev n hn, ← totalParts_new n] at h
  unfold A138137
  omega


end F07B

theorem OMA.solution : type_of% @OMA.S_oeis_a339304.main := by
  exact F07B.target
