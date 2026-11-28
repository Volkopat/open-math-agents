import OMAStatements.S_oeis_a221650

-- Problem: A221650: Tetrahedron P(n,j,k) = T(j,k)*p(n-j), where T(j,k) = 1 if k divides j otherwise 0.
-- Upstream: formal-conjectures statements/oeis-a221650.lean:0 (declaration OMA.S_oeis_a221650.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if m * k <= n with k >= 1, removing m copies of k is a bijection from the
-- partitions of n with at least m parts equal to k onto the partitions of n - m*k (its inverse
-- adds m copies of k). With m = j/k and m*k = j this is Conjecture 1. In Conjecture 2 a
-- partition with c parts of size k contributes #{i in [1, c] : i = m}, which is 1 if m <= c and
-- 0 otherwise (m >= 1), so the sum is the number of partitions counted in Conjecture 1.
-- If k does not divide j, then T(j,k) = 0 and P(n,j,k) = 0.

namespace P1A221650

open OMA.S_oeis_a221650

theorem rep_le {n k m : ℕ} (p : n.Partition) (h : m ≤ p.parts.count k) :
    Multiset.replicate m k ≤ p.parts :=
  Multiset.le_count_iff_replicate_le.mp h

theorem sum_sub_rep {n k m : ℕ} (p : n.Partition) (h : m ≤ p.parts.count k) :
    (p.parts - Multiset.replicate m k).sum = n - m * k := by
  have h1 := congrArg Multiset.sum (Multiset.sub_add_cancel (rep_le p h))
  rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, p.parts_sum] at h1
  omega

theorem sum_add_rep {n k m : ℕ} (hmk : m * k ≤ n) (q : (n - m * k).Partition) :
    (q.parts + Multiset.replicate m k).sum = n := by
  rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, q.parts_sum]
  omega

theorem pos_add_rep {n k m : ℕ} (hk : 1 ≤ k) (q : n.Partition) {i : ℕ}
    (hi : i ∈ q.parts + Multiset.replicate m k) : 0 < i := by
  rcases Multiset.mem_add.mp hi with h | h
  · exact q.parts_pos h
  · rw [Multiset.eq_of_mem_replicate h]
    omega

theorem count_add_rep {n k m : ℕ} (q : n.Partition) :
    m ≤ (q.parts + Multiset.replicate m k).count k := by
  rw [Multiset.count_add, Multiset.count_replicate_self]
  omega

/-- Removing m copies of k. -/
def remEquiv {n k m : ℕ} (hk : 1 ≤ k) (hmk : m * k ≤ n) :
    {p : n.Partition // m ≤ p.parts.count k} ≃ (n - m * k).Partition where
  toFun p := ⟨p.1.parts - Multiset.replicate m k,
    fun hi => p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
    sum_sub_rep p.1 p.2⟩
  invFun q := ⟨⟨q.parts + Multiset.replicate m k, fun hi => pos_add_rep hk q hi,
    sum_add_rep hmk q⟩, count_add_rep q⟩
  left_inv p := Subtype.ext (Nat.Partition.ext (Multiset.sub_add_cancel (rep_le p.1 p.2)))
  right_inv _ := Nat.Partition.ext Multiset.add_sub_cancel_right

theorem count_eq (n k m : ℕ) (hk : 1 ≤ k) (hmk : m * k ≤ n) :
    ((Finset.univ : Finset n.Partition).filter (fun q => m ≤ q.parts.count k)).card =
      Fintype.card (n - m * k).Partition := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (remEquiv hk hmk)

theorem icc_filter (c m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 c).filter (fun i => i = m)).card = if m ≤ c then 1 else 0 := by
  rw [Finset.filter_eq']
  by_cases h : m ≤ c
  · have hp : m ∈ Finset.Icc 1 c := Finset.mem_Icc.mpr ⟨hm, h⟩
    rw [if_pos hp, if_pos h, Finset.card_singleton]
  · have hn : m ∉ Finset.Icc 1 c := fun h' => h (Finset.mem_Icc.mp h').2
    rw [if_neg hn, if_neg h, Finset.card_empty]

end P1A221650

open OMA.S_oeis_a221650 P1A221650 in
theorem OMA.solution : type_of% @OMA.S_oeis_a221650.main := by
  intro n j k _hn _hj hjn hk hkj
  have hzero : ¬ k ∣ j → P n j k = 0 := by
    intro h
    simp only [P, T, if_neg h, zero_mul]
  have hone : k ∣ j → P n j k = ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun q => j / k ≤ q.parts.count k)).card := by
    intro h
    have hj' : j / k * k = j := Nat.div_mul_cancel h
    have hle : j / k * k ≤ n := by
      rw [hj']
      exact hjn
    rw [count_eq n k (j / k) hk hle, hj']
    simp only [P, T, if_pos h, one_mul]
  have htwo : k ∣ j → P n j k = ∑ q : Nat.Partition n,
      ((Finset.Icc 1 (q.parts.count k)).filter (fun i => i = j / k)).card := by
    intro h
    have hpos : 0 < j / k := Nat.div_pos hkj (by omega)
    rw [hone h, Finset.card_filter]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [icc_filter (q.parts.count k) (j / k) (by omega)]
  exact ⟨⟨hone, hzero⟩, ⟨htwo, hzero⟩⟩
