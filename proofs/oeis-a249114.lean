import OMAStatements.S_oeis_a249114

-- Credit: @oh-meh
open OMA.S_oeis_a249114 Finset

private theorem lowerBound (n k : ℕ) (_hn : 1 ≤ n) (hk : 4 ≤ primeCount n k) : 6 ≤ k := by
  by_contra! h
  have sub : (Icc 1 k).filter (fun j => (n + j*(j+1)/2).Prime) ⊆
      (if n % 2 = 0 then {1,2,5} else {1,3,4} : Finset ℕ) := by
    intro j hj
    obtain ⟨hj, hp⟩ := mem_filter.mp hj
    obtain ⟨hl,hu⟩ := mem_Icc.mp hj
    have hj5 : j ≤ 5 := by omega
    have odd_or_two := hp.eq_two_or_odd
    interval_cases j <;> norm_num at odd_or_two ⊢ <;>
      split <;> simp_all <;> omega
  have hs := card_le_card sub
  unfold primeCount at hk
  split at hs <;> norm_num at hs <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a249114.main := by
  refine ⟨fun n hn k hk => lowerBound n k hn hk, 2, by decide, ?_⟩
  apply le_antisymm
  · exact Nat.sInf_le (show 0<6 ∧ 4 ≤ primeCount 2 6 by decide)
  · apply le_csInf
    · exact ⟨6, by decide⟩
    · exact fun k hk => lowerBound 2 k (by decide) hk.2
