import OMAStatements.S_oeis_a108954

theorem OMA.solution : type_of% @OMA.S_oeis_a108954.main := by
  ext n
  simp only [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [if_neg hn.ne', OMA.S_oeis_a108954.a]
  have h2 : Nat.primeCounting (2 * n) =
      Nat.primeCounting n + Nat.count (fun k => Nat.Prime (n + 1 + k)) n := by
    simp only [Nat.primeCounting, Nat.primeCounting']
    rw [show 2 * n + 1 = (n + 1) + n by ring, Nat.count_add]
  rw [h2, Nat.add_sub_cancel_left, Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun k _ => k + 1) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨by omega, by omega⟩, by rw [show k + 1 + n = n + 1 + k by ring]; exact hk.2⟩
  · intro a _ b _ h
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hi ⊢
    exact ⟨i - 1, ⟨by omega, by rw [show n + 1 + (i - 1) = i + n by omega]; exact hi.2⟩, by omega⟩
