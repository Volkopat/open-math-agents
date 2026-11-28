import OMAStatements.S_oeis_a394694

open Finset OMA.S_oeis_a394694

namespace A394694Proof

private lemma entries (m : ℕ) (hm : 0 < m) :
    a (m+1) = (m.divisorsAntidiagonal.filter fun p => p.2 ≤ p.1+1).card := by
  unfold a
  apply Finset.card_nbij' (fun p => (p.1-1,p.2)) (fun p => (p.1+1,p.2))
  · rintro ⟨i,j⟩ h
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_Icc] at h
    rcases h with ⟨⟨⟨hi, _⟩, ⟨hj, _⟩⟩, hji, ht⟩
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simp [T] at ht
    simpa [Nat.mem_divisorsAntidiagonal, hm.ne', Nat.mul_succ] using
      (show i*j+i=m ∧ j+1 ≤ i+1 from ⟨by omega,hji⟩)
  · rintro ⟨u,v⟩ h
    rcases mem_filter.mp h with ⟨hp,hvu⟩
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hu := Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp))
    have hv := Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp))
    have hvp := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    change v ≤ u+1 at hvu
    change u*v=m at he
    change v ≠ 0 at hvp
    obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hvp
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.succ_pos u, Nat.succ_le_succ hu⟩, mem_Icc.mpr ⟨Nat.succ_pos v, hv.trans (Nat.le_succ m)⟩⟩, hvu, ?_⟩
    simp only [T, Nat.add_sub_cancel, Nat.succ_sub_one]
    simp only [Prod.fst,Prod.snd] at hu hv ⊢
    rw [Nat.mul_succ] at he
    omega
  · rintro ⟨i,j⟩ h
    have hi := (mem_Icc.mp (mem_product.mp (mem_filter.mp h).1).1).1
    exact Prod.ext (by dsimp; omega) rfl
  · rintro ⟨u,v⟩ _
    simp

private lemma split_counts (s : Finset (ℕ × ℕ)) :
    (s.filter fun p => p.2 ≤ p.1+1).card =
      (s.filter fun p => p.2 < p.1).card + (s.filter fun p => p.2 = p.1).card +
      (s.filter fun p => p.2 = p.1+1).card ∧
    s.card = (s.filter fun p => p.2 < p.1).card + (s.filter fun p => p.2 = p.1).card +
      (s.filter fun p => p.1 < p.2).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    simp only [filter_insert,card_insert_of_notMem hp]
    split_ifs <;> simp_all [card_insert_of_notMem, Finset.notMem_mono (filter_subset _ _)] <;> omega

open Classical in
private lemma unique_factor (m d : ℕ) (hm : 0 < m) :
    (m.divisorsAntidiagonal.filter fun p => p.2 = p.1+d).card =
      (if ∃ k, m = k*(k+d) then 1 else 0) := by
  classical
  split_ifs with h
  · obtain ⟨k,hk⟩ := h
    have hset : (m.divisorsAntidiagonal.filter fun p => p.2 = p.1+d) = {(k,k+d)} := by
      ext ⟨u,v⟩
      simp only [mem_filter,Nat.mem_divisorsAntidiagonal,hm.ne',and_true,mem_singleton,Prod.mk.injEq]
      constructor
      · rintro ⟨hu,rfl⟩
        have h : u = k := by
          rcases lt_trichotomy u k with h | h | h
          · nlinarith [Nat.mul_self_lt_mul_self_iff.mpr h, Nat.mul_le_mul_right d h.le]
          · exact h
          · nlinarith [Nat.mul_self_lt_mul_self_iff.mpr h, Nat.mul_le_mul_right d h.le]
        simp [h]
      · rintro ⟨rfl,rfl⟩
        exact ⟨⟨hk.symm, hm.ne'⟩, rfl⟩
    simp [hset]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨u,v⟩ hp
    obtain ⟨hu,hv⟩ := mem_filter.mp hp
    exact h ⟨u, by simpa [← hv] using (Nat.mem_divisorsAntidiagonal.mp hu).1.symm⟩

end A394694Proof

open A394694Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a394694.main := by
  classical
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < m := by omega
  have ⟨hc, ht⟩ := split_counts m.divisorsAntidiagonal
  have hs : (m.divisorsAntidiagonal.filter fun p => p.2 < p.1).card =
      (m.divisorsAntidiagonal.filter fun p => p.1 < p.2).card := by
    apply card_nbij' Prod.swap Prod.swap <;> intro p hp
    · simpa [mul_comm] using hp
    · simpa [mul_comm] using hp
    · rfl
    · rfl
  have he := unique_factor m 0 hm
  have hp := unique_factor m 1 hm
  simp only [Nat.add_zero] at he
  have hcard : m.divisorsAntidiagonal.card = m.divisors.card := by
    rw [← Nat.map_div_right_divisors,card_map]
  rw [hcard] at ht
  rw [← hs, he] at ht
  rw [entries m hm, hc, he, hp]
  unfold e
  simp only [Nat.succ_sub_one]
  by_cases hsq : ∃ k, m = k*k
  · have hnp : ¬ ∃ k, m = k*(k+1) := by
      obtain ⟨j,hj⟩ := hsq
      rintro ⟨k,hk⟩
      by_cases h : j ≤ k
      · nlinarith [Nat.mul_self_le_mul_self h]
      · have h' : k+1 ≤ j := by omega
        nlinarith [Nat.mul_self_le_mul_self h']
    rw [if_pos (show IsSquare m from hsq)]
    simp only [if_pos hsq, if_neg hnp, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at ht ⊢
    have hh := congrArg (Nat.cast : ℕ → ℚ) ht
    push_cast at hh
    linarith
  · rw [if_neg (show ¬IsSquare m from hsq)]
    unfold IsPronic
    by_cases hpr : ∃ k, m = k*(k+1)
    all_goals simp [hsq, hpr] at ht ⊢
    all_goals have hh := congrArg (Nat.cast : ℕ → ℚ) ht
    all_goals push_cast at hh
    all_goals linarith
