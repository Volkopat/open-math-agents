import OMAStatements.S_oeis_a212652

/-!
# First appearances and least largest parts in A212652

The column c in raw row m corresponds to the lower triangular index
k=m-c. The same k gives exactly the consecutive parts k+1 through m.
The minimum is attained because the one-part partition always exists.
Deleting earlier rows therefore keeps n precisely at its minimum row.

Daniel Forgues recorded the consecutive-sum identity in A212652 (2016).
H. F. W. Hoft proved the related divisor formula for the row index in
A209260 (2016). Sources: https://oeis.org/A212652, https://oeis.org/A141419
and https://oeis.org/A209260. Credit: @Solitude1312
-/

open OMA.S_oeis_a212652

namespace OMA.A212652

private lemma tri_step (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  rw [tri, Finset.sum_range_succ]
  rfl

private lemma interval_sum (k m : ℕ) (h : k ≤ m) :
    (∑ j ∈ Finset.Icc (k + 1) m, j) = tri m - tri k := by
  have hi : Finset.Icc (k + 1) m = Finset.Ico (k + 1) (m + 1) := by
    ext j
    simp
  rw [hi]
  have ht := Finset.sum_range_add_sum_Ico (fun j : ℕ => j) (Nat.succ_le_succ h)
  change tri k + (∑ j ∈ Finset.Ico (k + 1) (m + 1), j) = tri m at ht
  omega

private lemma exists_endpoint (n : ℕ) (hn : 0 < n) : admissible n n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine ⟨by omega, k, by omega, ?_⟩
  rw [tri_step]
  omega

private lemma raw_iff (n m : ℕ) (hn : 0 < n) : n ∈ rawRow m ↔ admissible n m := by
  unfold rawRow admissible
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hv⟩
    have h := Finset.mem_Icc.mp hc
    exact ⟨by omega, m - c, Nat.sub_le _ _, hv.symm⟩
  · rintro ⟨_, k, hk, he⟩
    have hlt : k < m := by
      by_contra! hh
      have hm : k = m := by omega
      rw [hm, Nat.sub_self] at he
      omega
    refine ⟨m - k, Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩, ?_⟩
    simpa only [Nat.sub_sub_self hk] using he.symm

private lemma largest_iff (n m : ℕ) (hn : 0 < n) : m ∈ largestParts n ↔ admissible n m := by
  constructor
  · rintro ⟨l, hl, hlm, hsum⟩
    have he := interval_sum (l - 1) m (by omega)
    rw [show l - 1 + 1 = l by omega] at he
    exact ⟨by omega, l - 1, by omega, hsum.symm.trans he⟩
  · rintro ⟨_, k, hk, he⟩
    have hlt : k < m := by
      by_contra! hh
      have hm : k = m := by omega
      rw [hm, Nat.sub_self] at he
      omega
    exact ⟨k + 1, by omega, by omega, (interval_sum k m hk).trans he.symm⟩

lemma both (n : ℕ) (hn : 0 < n) :
    n ∈ freshRow (a n) ∧ IsLeast (largestParts n) (a n) := by
  have ha : admissible n (a n) := Nat.sInf_mem (s := {m | admissible n m}) ⟨n, exists_endpoint n hn⟩
  have minimal (m : ℕ) (hm : admissible n m) : a n ≤ m :=
    Nat.sInf_le (s := {m | admissible n m}) hm
  constructor
  · rw [freshRow, Finset.mem_sdiff, Finset.mem_biUnion]
    refine ⟨(raw_iff n _ hn).mpr ha, ?_⟩
    rintro ⟨r, hr, hraw⟩
    exact (not_lt_of_ge (minimal r ((raw_iff n r hn).mp hraw))) (Finset.mem_range.mp hr)
  · exact ⟨(largest_iff n _ hn).mpr ha, fun m hm => minimal m ((largest_iff n m hn).mp hm)⟩

end OMA.A212652

theorem OMA.solution : type_of% @OMA.S_oeis_a212652.main := by
  exact OMA.A212652.both
