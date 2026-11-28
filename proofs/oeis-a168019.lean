import OMAStatements.S_oeis_a168019

namespace OMA.A168019Proof

/-- Multiply every part of a partition of `m` by `d > 0`. -/
def scale (d m : ℕ) (hd : 0 < d) (p : Nat.Partition m) : Nat.Partition (d * m) where
  parts := p.parts.map (d * ·)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact Nat.mul_pos hd (p.parts_pos hj)
  parts_sum := by
    rw [Multiset.sum_map_mul_left, Multiset.map_id', p.parts_sum]

lemma card_eq (d m : ℕ) (hd : 0 < d) :
    ((Finset.univ : Finset (Nat.Partition (d * m))).filter
      (fun p => ∀ i ∈ p.parts, d ∣ i)).card = Fintype.card (Nat.Partition m) := by
  symm
  rw [← Finset.card_univ]
  apply Finset.card_bij (fun p _ => scale d m hd p)
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    simp only [scale, Multiset.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Dvd.intro j rfl
  · intro p _ q _ h
    have h' : p.parts.map (d * ·) = q.parts.map (d * ·) := congrArg Nat.Partition.parts h
    apply Nat.Partition.ext
    exact Multiset.map_injective (fun a b hab => Nat.eq_of_mul_eq_mul_left hd hab) h'
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨{ parts := q.parts.map (· / d), parts_pos := ?_, parts_sum := ?_ }, Finset.mem_univ _, ?_⟩
    · intro i hi
      rw [Multiset.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact Nat.div_pos (Nat.le_of_dvd (q.parts_pos hj) (hq j hj)) hd
    · have h1 : q.parts.map (fun j => d * (j / d)) = q.parts := by
        conv_rhs => rw [← Multiset.map_id q.parts]
        apply Multiset.map_congr rfl
        intro j hj
        exact Nat.mul_div_cancel' (hq j hj)
      have h2 := congrArg Multiset.sum h1
      rw [Multiset.sum_map_mul_left, q.parts_sum] at h2
      exact Nat.eq_of_mul_eq_mul_left hd h2
    · apply Nat.Partition.ext
      simp only [scale, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id q.parts]
      apply Multiset.map_congr rfl
      intro j hj
      exact Nat.mul_div_cancel' (hq j hj)

end OMA.A168019Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a168019.main := by
  intro n k
  unfold OMA.S_oeis_a168019.A
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m (Nat.succ_pos k)]
    exact OMA.A168019Proof.card_eq (k + 1) m (Nat.succ_pos k)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply h
    rw [← p.parts_sum]
    exact Multiset.dvd_sum hp
