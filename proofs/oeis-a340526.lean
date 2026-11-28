import OMAStatements.S_oeis_a340526

namespace OMA.S_oeis_a340526

open Finset

private theorem copies_le {d j : ℕ} {s : Multiset ℕ} (h : j ≤ s.count d) :
    Multiset.replicate j d ≤ s := by
  apply Multiset.le_iff_count.mpr
  intro e
  by_cases he : d = e
  · subst e
    simpa using h
  · simp [Multiset.count_replicate, he]

private theorem copies_sum (j d : ℕ) : (Multiset.replicate j d).sum = j * d := by
  simp [Multiset.sum_replicate]

private theorem copies_mass {n d : ℕ} (p : Nat.Partition n) : p.parts.count d * d ≤ n := by
  have hrep : Multiset.replicate (p.parts.count d) d ≤ p.parts := copies_le le_rfl
  have he := congrArg Multiset.sum (tsub_add_cancel_of_le hrep)
  simp only [Multiset.sum_add, copies_sum, p.parts_sum] at he
  omega

private theorem marked_count {n d : ℕ} (p : Nat.Partition n) (hd : 0 < d) :
    ((range n).filter (fun k => d ∣ n - k ∧ n - k ≤ p.parts.count d * d)).card =
      p.parts.count d := by
  conv_rhs => rw [← card_range (p.parts.count d)]
  symm
  refine card_bij (fun j _ => n - (j + 1) * d) ?_ ?_ ?_
  · intro j hj
    have hj' : j + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hj)
    have hm := Nat.mul_le_mul_right d hj'
    have hb := copies_mass (d := d) p
    have hp : 0 < (j + 1) * d := by positivity
    have he : n - (n - (j + 1) * d) = (j + 1) * d := by omega
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    rw [he]
    exact ⟨⟨j + 1, Nat.mul_comm _ _⟩, hm⟩
  · intro i hi j hj h
    have hi' : i + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hi)
    have hj' : j + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hj)
    have ha := Nat.mul_le_mul_right d hi'
    have hb := Nat.mul_le_mul_right d hj'
    have hc := copies_mass (d := d) p
    have hm : (i + 1) * d = (j + 1) * d := by omega
    have he : i + 1 = j + 1 := by
      simpa only [Nat.mul_div_cancel _ hd] using congrArg (fun m : ℕ => m / d) hm
    omega
  · intro k hk
    obtain ⟨hk, hkd, hkc⟩ := mem_filter.mp hk
    have hk' : k < n := mem_range.mp hk
    let j := (n - k) / d
    have he : j * d = n - k := Nat.div_mul_cancel hkd
    have hj : 0 < j := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at he
      omega
    have hj' : j ≤ p.parts.count d := by
      calc
        j ≤ (p.parts.count d * d) / d := Nat.div_le_div_right hkc
        _ = p.parts.count d := Nat.mul_div_cancel _ hd
    refine ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel (show 1 ≤ j by omega), he]
    omega

private theorem count_partitions {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) (hdiv : d ∣ n - k) :
    ((univ : Finset (Nat.Partition n)).filter (fun p => n - k ≤ p.parts.count d * d)).card =
      A000041 k := by
  classical
  let j := (n - k) / d
  let r := Multiset.replicate j d
  have hr : r.sum = n - k := by
    rw [show r.sum = j * d from copies_sum j d]
    exact Nat.div_mul_cancel hdiv
  let P := {p : Nat.Partition n // n - k ≤ p.parts.count d * d}
  have hsub (p : P) : r ≤ p.val.parts := by
    apply copies_le
    exact Nat.div_le_of_le_mul (p.property.trans_eq (Nat.mul_comm _ _))
  let cut (p : P) : Nat.Partition k :=
    ⟨p.val.parts - r,
      fun {_} h => p.val.parts_pos (Multiset.mem_of_le tsub_le_self h),
      by
        have he := congrArg Multiset.sum (tsub_add_cancel_of_le (hsub p))
        simp only [Multiset.sum_add, hr, p.val.parts_sum] at he
        omega⟩
  let glueParts (p : Nat.Partition k) : Nat.Partition n :=
    ⟨p.parts + r,
      fun {_} h => by
        rcases Multiset.mem_add.mp h with h | h
        · exact p.parts_pos h
        · exact (Multiset.mem_replicate.mp h).2.symm ▸ hd,
      by simp only [Multiset.sum_add, p.parts_sum, hr]; omega⟩
  let glue (p : Nat.Partition k) : P := ⟨glueParts p, by
    change n - k ≤ (p.parts + r).count d * d
    simp only [Multiset.count_add, r, Multiset.count_replicate_self, Nat.add_mul]
    have he : j * d = n - k := Nat.div_mul_cancel hdiv
    omega⟩
  let e : P ≃ Nat.Partition k :=
    ⟨cut, glue,
      fun p => Subtype.ext (Nat.Partition.ext (tsub_add_cancel_of_le (hsub p))),
      fun p => Nat.Partition.ext (add_tsub_cancel_right p.parts r)⟩
  change _ = Fintype.card (Nat.Partition k)
  rw [← Fintype.card_congr e]
  exact (Fintype.card_of_subtype _ (fun p => by simp)).symm

private theorem partition_convolution (n : ℕ) :
    (∑ i ∈ range n, A000041 i * (n - i).divisors.card) = A006128 n := by
  unfold A006128
  calc
    _ = ∑ k ∈ range n, ∑ d ∈ Icc 1 n, if d ∣ n - k then A000041 k else 0 := by
      apply sum_congr rfl
      intro k hk
      have hk' : k < n := mem_range.mp hk
      have hdivisors : (n - k).divisors = (Icc 1 n).filter (fun d => d ∣ n - k) := by
        ext d
        constructor
        · intro hd
          have hdvd := Nat.dvd_of_mem_divisors hd
          have hpos := Nat.pos_of_mem_divisors hd
          have hle := Nat.le_of_dvd (show 0 < n - k by omega) hdvd
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, by omega⟩, hdvd⟩
        · intro hd
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, by omega⟩
      rw [← sum_filter, ← hdivisors]
      simp [Nat.mul_comm]
    _ = ∑ d ∈ Icc 1 n, ∑ k ∈ range n, if d ∣ n - k then A000041 k else 0 := sum_comm
    _ = ∑ d ∈ Icc 1 n, ∑ p : Nat.Partition n, p.parts.count d := by
      apply sum_congr rfl
      intro d hd
      have hd' : 0 < d := (mem_Icc.mp hd).1
      have he : ∑ p : Nat.Partition n, p.parts.count d =
          ∑ p : Nat.Partition n, ∑ k ∈ range n, if
            d ∣ n - k ∧ n - k ≤ p.parts.count d * d then 1 else 0 := by
        apply sum_congr rfl
        intro p _
        rw [sum_boole]
        exact (marked_count p hd').symm
      rw [he, sum_comm]
      apply sum_congr rfl
      intro k hk
      by_cases hdiv : d ∣ n - k
      · simp only [hdiv, if_true, true_and, sum_boole]
        exact (count_partitions (mem_range.mp hk).le hd' hdiv).symm
      · simp [hdiv]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      exact Multiset.sum_count_eq_card
        (fun d hd => mem_Icc.mpr ⟨p.parts_pos hd, Nat.Partition.le_of_mem_parts hd⟩)

private theorem entry_convolution {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    T n k = ∑ m ∈ Icc k n, A000041 (k - 1) * (m - k + 1).divisors.card := by
  unfold T A006218
  rw [Nat.mul_comm, mul_sum]
  refine sum_bij' (fun i _ => i + k - 1) (fun m _ => m - k + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have h := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro m hm
    have h := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi
    have h := mem_Icc.mp hi
    omega
  · intro m hm
    have h := mem_Icc.mp hm
    omega
  · intro i hi
    have h := mem_Icc.mp hi
    rw [show i + k - 1 - k + 1 = i by omega]

private theorem partition_count_row (m : ℕ) :
    (∑ k ∈ Icc 1 m, A000041 (k - 1) * (m - k + 1).divisors.card) = A006128 m := by
  rw [← partition_convolution m]
  refine sum_bij' (fun k _ => k - 1) (fun j _ => j + 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have h := mem_Icc.mp hk
    exact mem_range.mpr (by omega)
  · intro j hj
    have h := mem_range.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k hk
    have h := mem_Icc.mp hk
    omega
  · intro j _
    omega
  · intro k hk
    have h := mem_Icc.mp hk
    rw [show m - (k - 1) = m - k + 1 by omega]

end OMA.S_oeis_a340526

open Finset OMA.S_oeis_a340526 in
theorem OMA.solution : type_of% @OMA.S_oeis_a340526.main := by
  constructor
  · intro n k hk hkn
    rw [entry_convolution hk hkn]
    apply sum_congr rfl
    intro m _
    simp [block, List.sum_replicate]
  · intro n _
    unfold A284870
    calc
      (∑ k ∈ Icc 1 n, T n k) =
          ∑ k ∈ Icc 1 n, ∑ m ∈ Icc 1 n,
            if k ≤ m then A000041 (k - 1) * (m - k + 1).divisors.card else 0 := by
        apply sum_congr rfl
        intro k hk
        obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
        rw [entry_convolution hk1 hkn, ← sum_filter]
        have hs : ((Icc 1 n).filter (fun m => k ≤ m)) = Icc k n := by
          ext m
          simp only [mem_filter, mem_Icc]
          omega
        rw [hs]
      _ = ∑ m ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
            if k ≤ m then A000041 (k - 1) * (m - k + 1).divisors.card else 0 := sum_comm
      _ = ∑ m ∈ Icc 1 n, A006128 m := by
        apply sum_congr rfl
        intro m hm
        have hmn := (mem_Icc.mp hm).2
        rw [← sum_filter]
        have hs : ((Icc 1 n).filter (fun k => k ≤ m)) = Icc 1 m := by
          ext k
          simp only [mem_filter, mem_Icc]
          omega
        rw [hs, partition_count_row]
