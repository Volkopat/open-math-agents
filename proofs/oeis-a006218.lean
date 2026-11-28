import OMAStatements.S_oeis_a006218

-- Credit: @oh-meh
open OMA.S_oeis_a006218 Finset

private theorem lengthCount {n x d : ℕ} (hx : x ∈ Icc 1 n) (hd : 0 < d) :
    ((Icc 2 n).filter fun l => x + (l-1)*d ≤ n).card = (n-x)/d := by
  obtain ⟨hx1,hxn⟩ := mem_Icc.mp hx
  have lengths : (Icc 2 n).filter (fun l => x + (l-1)*d ≤ n) =
      Icc 2 ((n-x)/d + 1) := by
    ext l
    simp only [mem_filter, mem_Icc]
    have hdiv := Nat.le_div_iff_mul_le hd (x := l-1) (y := n-x)
    have hb := Nat.div_le_self (n-x) d
    omega
  rw [lengths, Nat.card_Icc]
  generalize (n-x)/d = q
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a006218.main := by
  intro n hn
  calc
    (T n).card = ∑ x ∈ Icc 1 n, ∑ d ∈ Icc 1 n, (n-x)/d := by
      unfold T
      rw [card_filter, sum_product]
      apply sum_congr rfl
      intro x hx
      rw [sum_product]
      apply sum_congr rfl
      intro d hd
      simpa only [← card_filter] using lengthCount hx (mem_Icc.mp hd).1
    _ = ∑ x ∈ Icc 1 n, a (n-x) := by
      apply sum_congr rfl
      intro x hx
      unfold a
      symm
      apply sum_subset_zero_on_sdiff
      · intro k hk
        simp only [mem_Icc] at *
        omega
      · intro k hk
        apply Nat.div_eq_of_lt
        simp only [mem_sdiff, mem_Icc] at hk
        omega
      · simp
    _ = ∑ m ∈ range n, a m := by
      apply sum_bij (fun x _ => n-x)
      · intro x hx
        simp only [mem_Icc, mem_range] at *
        omega
      · intro x hx y hy h
        simp only [mem_Icc] at *
        omega
      · intro m hm
        refine ⟨n-m, ?_, ?_⟩ <;> simp only [mem_range, mem_Icc] at * <;> omega
      · simp
